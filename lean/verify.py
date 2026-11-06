"""Serial, memory-capped build, axiom audit, and sandboxed comparator for Theorem A.
No source downloads or dependency edits. Use cached pinned packages already installed.
"""
import argparse,ctypes,datetime,hashlib,json,os,pathlib,re,shutil,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parent
CAP=10_000_000_000
PIN='eb6cafb7290e8bd5f2937522d8d804f58f02bafc'

PRIMITIVE_TARGETS = ['Nat.add','Nat.sub','Nat.mul','Nat.pow','Nat.gcd','Nat.div','Nat.mod','Nat.beq','Nat.ble','Nat.land','Nat.lor','Nat.xor','Nat.shiftLeft','Nat.shiftRight','String.ofList','Char.ofNat','List','eagerReduce','Nat','String','String.mk','Char','optParam','autoParam','semiOutParam','outParam']
def export_targets(cfg):
    return ['Quot','Quot.mk','Quot.lift','Quot.ind']+cfg['theorem_names']+cfg['permitted_axioms']+PRIMITIVE_TARGETS

def comparator_lookup_path(env):
    # Pinned Lake's context does Unix `which git`/`which env` lookups even for
    # two supplied exports. No git process or dependency resolution is run.
    if os.name=='nt':
        base=pathlib.Path(os.environ.get('ProgramFiles',str(pathlib.Path(sys.executable).anchor))) / 'Git'
        additions=[p for p in (base/'usr/bin',base/'cmd') if p.is_dir()]
        env['PATH']=os.pathsep.join(map(str,additions))+os.pathsep+env['PATH']


def memory_cap():
    if os.name!='nt':
        # Bound resident memory, not the address space occupied by mapped proof files.
        import resource,threading,signal
        resource.setrlimit(resource.RLIMIT_CORE,(0,0))
        state={'peak':0}
        root_pid=os.getpid()
        def watch():
            while True:
                entries={}
                for d in pathlib.Path('/proc').iterdir():
                    if not d.name.isdigit():continue
                    try:
                        fields=dict(line.split(':',1) for line in (d/'status').read_text().splitlines() if ':' in line)
                        entries[int(d.name)]=(int(fields['PPid']),int(fields.get('VmRSS','0 kB').split()[0])*1024)
                    except (OSError,KeyError,ValueError):pass
                ids={root_pid};changed=True
                while changed:
                    new_ids={n for n,v in entries.items() if v[0] in ids};changed=not new_ids<=ids;ids|=new_ids
                rss=sum(entries.get(n,(0,0))[1] for n in ids);state['peak']=max(state['peak'],rss)
                if rss>=min(CAP-100000000,9000000000):
                    for n in ids-{root_pid}:
                        try:os.kill(n,signal.SIGKILL)
                        except ProcessLookupError:pass
                    os.kill(root_pid,signal.SIGTERM)
                    return
                time.sleep(.25)
        threading.Thread(target=watch,daemon=True).start()
        return lambda:state['peak']
    from ctypes import wintypes as w
    class Basic(ctypes.Structure):
        _fields_=[('PerProcessUserTimeLimit',ctypes.c_int64),('PerJobUserTimeLimit',ctypes.c_int64),('LimitFlags',w.DWORD),('MinimumWorkingSetSize',ctypes.c_size_t),('MaximumWorkingSetSize',ctypes.c_size_t),('ActiveProcessLimit',w.DWORD),('Affinity',ctypes.c_size_t),('PriorityClass',w.DWORD),('SchedulingClass',w.DWORD)]
    class IO(ctypes.Structure):
        _fields_=[(n,ctypes.c_uint64) for n in ('ReadOperationCount','WriteOperationCount','OtherOperationCount','ReadTransferCount','WriteTransferCount','OtherTransferCount')]
    class Extended(ctypes.Structure):
        _fields_=[('BasicLimitInformation',Basic),('IoInfo',IO),('ProcessMemoryLimit',ctypes.c_size_t),('JobMemoryLimit',ctypes.c_size_t),('PeakProcessMemoryUsed',ctypes.c_size_t),('PeakJobMemoryUsed',ctypes.c_size_t)]
    k=ctypes.WinDLL('kernel32',use_last_error=True)
    k.CreateJobObjectW.argtypes=[ctypes.c_void_p,w.LPCWSTR];k.CreateJobObjectW.restype=w.HANDLE
    k.SetInformationJobObject.argtypes=[w.HANDLE,ctypes.c_int,ctypes.c_void_p,w.DWORD];k.SetInformationJobObject.restype=w.BOOL
    k.AssignProcessToJobObject.argtypes=[w.HANDLE,w.HANDLE];k.AssignProcessToJobObject.restype=w.BOOL
    k.GetCurrentProcess.restype=w.HANDLE
    k.QueryInformationJobObject.argtypes=[w.HANDLE,ctypes.c_int,ctypes.c_void_p,w.DWORD,ctypes.c_void_p];k.QueryInformationJobObject.restype=w.BOOL
    job=k.CreateJobObjectW(None,None);lim=Extended();lim.BasicLimitInformation.LimitFlags=0x200;lim.JobMemoryLimit=CAP
    if not job or not k.SetInformationJobObject(job,9,ctypes.byref(lim),ctypes.sizeof(lim)) or not k.AssignProcessToJobObject(job,k.GetCurrentProcess()):raise ctypes.WinError(ctypes.get_last_error())
    def peak():
        stat=Extended()
        if not k.QueryInformationJobObject(job,9,ctypes.byref(stat),ctypes.sizeof(stat),None):raise ctypes.WinError(ctypes.get_last_error())
        return stat.PeakJobMemoryUsed
    return peak

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--incremental',action='store_true',help='reuse this verifier’s matching source/dependency hash records')
    ap.add_argument('--dependency-dir',type=pathlib.Path,help='directory containing cached mathlib and its sibling packages')
    ap.add_argument('--lean-bin',type=pathlib.Path,help='pinned Lean bin directory; otherwise use the active Lean toolchain')
    args=ap.parse_args();get_peak=memory_cap();begin=time.monotonic()
    out=ROOT/'work';out.mkdir(exist_ok=True)
    env=os.environ.copy();env['LEAN_NUM_THREADS']='1';env['PYTHONDONTWRITEBYTECODE']='1'
    for key in ('TEMP','TMP','MATHLIB_CACHE_DIR','LAKE_CACHE_DIR'):
        p=out/key.lower();p.mkdir(exist_ok=True);env[key]=str(p)
    ext='.exe' if os.name=='nt' else ''
    bindir=args.lean_bin
    if bindir is None:
        active_lean=shutil.which('lean')
        if not active_lean:raise RuntimeError('Pinned Lean is required on PATH, or pass --lean-bin.')
        prefix=subprocess.check_output([active_lean,'--print-prefix'],cwd=ROOT,env=env,text=True).strip()
        bindir=pathlib.Path(prefix)/'bin'
    lean=bindir/('lean'+ext);lake=bindir/('lake'+ext);exporter=bindir/('leanexport'+ext)
    version=subprocess.check_output([str(lean),'--version'],env=env,text=True).strip()
    if '4.35.0' not in version or PIN[:12] not in version:raise RuntimeError('Wrong pinned Lean: '+version)
    depdir=(args.dependency_dir or ROOT/'.lake/packages').resolve()
    if not (depdir/'mathlib/Mathlib').is_dir():raise RuntimeError('Install the pinned dependencies and Mathlib cache first; see README.')
    packages=[ROOT]+[p for p in depdir.iterdir() if p.is_dir()]
    env['PATH']=str(bindir)+os.pathsep+env['PATH']
    comparator_lookup_path(env)
    env['LEAN_PATH']=os.pathsep.join(str(p/'.lake/build/lib/lean') for p in packages)
    env['LEAN_SRC_PATH']=os.pathsep.join(map(str,packages))
    records=[];ordered=[];seen=set()
    def visit(name,own=False):
        if name in seen:return
        seen.add(name);rel=pathlib.Path(name.replace('.','/')+'.lean')
        pkg=next((p for p in packages if (p/rel).is_file()),None)
        if pkg is None:return
        artifact=pkg/'.lake/build/lib/lean'/rel.with_suffix('.olean')
        if pkg!=ROOT and artifact.exists():return
        source=pkg/rel
        for dep in re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_.]+)',source.read_text(encoding='utf-8-sig'),re.M):visit(dep)
        ordered.append((name,pkg,rel,artifact))
    for name in ('Challenge','Solution','Audit'):visit(name)
    def run(label,command,cwd=ROOT,stdout=None):
        start=time.monotonic();log=out/(label+'.log')
        with (pathlib.Path(stdout) if stdout else log).open('w',encoding='utf-8') as f:
            r=subprocess.run(list(map(str,command)),cwd=cwd,env=env,stdout=f,stderr=None if stdout else subprocess.STDOUT)
        record={'step':label,'exit':r.returncode,'seconds':round(time.monotonic()-start,3),'peak_tree_commit_bytes':get_peak()}
        records.append(record);print(json.dumps(record),flush=True)
        (out/'verification.json').write_text(json.dumps({'lean':version,'cap_bytes':CAP,'records':records,'total_seconds':time.monotonic()-begin,'peak_tree_commit_bytes':get_peak()},indent=2)+'\n')
        if r.returncode:
            if not stdout:print(log.read_text(encoding='utf-8'),flush=True)
            raise RuntimeError(label+' failed; see '+str(log))
    cachepath=out/'build-hashes.json'
    cache=json.loads(cachepath.read_text()) if args.incremental and cachepath.exists() else {}
    current={}
    for name,pkg,rel,artifact in ordered:
        sig=hashlib.sha256((pkg/rel).read_bytes()).hexdigest()
        current[name]=sig
        if args.incremental and pkg==ROOT and artifact.exists() and cache.get(name)==sig and not any((pkg/rel).stat().st_mtime > artifact.stat().st_mtime for _ in [0]):
            deps=re.findall(r'^import ([A-Za-z0-9_.]+)',(pkg/rel).read_text(encoding='utf-8'),re.M)
            if not any((ROOT/'.lake/build/lib/lean'/pathlib.Path(d.replace('.','/')+'.olean')).exists() and (ROOT/'.lake/build/lib/lean'/pathlib.Path(d.replace('.','/')+'.olean')).stat().st_mtime > artifact.stat().st_mtime for d in deps):
                continue
        artifact.parent.mkdir(parents=True,exist_ok=True)
        more=['-DmaxSynthPendingDepth=3'] if pkg.name=='mathlib' else []
        run(name.replace('.','_'),[lean,'-j1','-M6144','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-DautoImplicit=false',*more,'-o',artifact,rel],pkg)
        cachepath.write_text(json.dumps(current,indent=2)+'\n')
    cachepath.write_text(json.dumps(current,indent=2)+'\n')
    audit=(out/'Audit.log').read_text(encoding='utf-8')
    cfg=json.loads((ROOT/'comparator.json').read_text())
    lines=[s for s in audit.splitlines() if 'depends on axioms' in s or 'does not depend on any axioms' in s]
    audit_roots=json.loads((ROOT/'pins/AUDIT-ROOTS.json').read_text(encoding='utf-8')) if (ROOT/'pins/AUDIT-ROOTS.json').exists() else cfg['theorem_names']
    if len(lines)!=len(audit_roots):raise RuntimeError('Incomplete axiom audit')
    for name,line in zip(audit_roots,lines):
        if "'"+name+"'" not in line:raise RuntimeError('Unexpected audited root: '+line)
    permitted=set(cfg['permitted_axioms'])
    for line in lines:
        axioms=set(re.search(r'\[(.*?)\]',line).group(1).split(', ')) if 'depends on axioms' in line else set()
        if not axioms <= permitted:raise RuntimeError('Unpermitted axiom: '+line)
    (ROOT/'AXIOMS.txt').write_text('\n'.join(lines)+'\n',encoding='utf-8')
    for mod in ('Challenge','Solution'):
        run('export_'+mod,[exporter,mod,'--',*export_targets(cfg)],stdout=out/(mod+'.ndjson'))
    if sys.platform != 'linux':raise RuntimeError('Comparator requires Linux with bubblewrap; run lake comparator --config comparator.json there.')
    run('comparator',[lake,'comparator','--config',ROOT/'comparator.json'])
    print((out/'comparator.log').read_text(encoding='utf-8'),flush=True)
    print('Verified all '+str(len(cfg['theorem_names']))+' Theorem A challenge targets.',flush=True)
if __name__=='__main__':
    try:main()
    except Exception as e:print(str(e),file=sys.stderr);sys.exit(1)
