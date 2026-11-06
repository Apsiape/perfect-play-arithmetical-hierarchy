"""Build every project source in the audited union, serially; reuse pinned dependency cache."""
from pathlib import Path
import ctypes,hashlib,importlib.util,json,os,re,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1];LEAN=ROOT/'lean';LOG=Path(os.environ.get('SIGMA2_LOG_DIR',str(LEAN/'.lake/build-logs')));LOG.mkdir(exist_ok=True)
spec=importlib.util.spec_from_file_location('thin_verifier',LEAN/'verify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
peak=v.memory_cap();env=os.environ.copy();env['LEAN_NUM_THREADS']='1';env['PYTHONDONTWRITEBYTECODE']='1'
for key in ['TEMP','TMP','MATHLIB_CACHE_DIR','LAKE_CACHE_DIR','LAKE_HOME']:
 p=LOG/key.lower();p.mkdir(exist_ok=True);env.setdefault(key,str(p))
lean=Path(__import__('shutil').which('lean'));version=subprocess.check_output([lean,'--version'],env=env,text=True).strip()
assert '4.35.0' in version and v.PIN[:12] in version,version
DEP=Path(os.environ.get('SIGMA2_DEPENDENCY_DIR',str(LEAN/'vendor')))
OBJ=Path(os.environ.get('SIGMA2_OBJECT_DIR',str(LEAN/'.lake/build/lib/lean')))
packages=[LEAN]+sorted(p for p in DEP.iterdir() if p.is_dir())
env['LEAN_PATH']=os.pathsep.join([str(OBJ)]+[str(p/'.lake/build/lib/lean') for p in packages[1:]])
env['LEAN_SRC_PATH']=os.pathsep.join(map(str,packages))
seen=set();ordered=[]
def visit(name):
 if name in seen:return
 seen.add(name);rel=Path(name.replace('.','/')+'.lean');pkg=next((p for p in packages if (p/rel).is_file()),None)
 if pkg is None:
  if name.startswith('Sigma2.'):raise RuntimeError('Missing source '+name)
  return
 if pkg!=LEAN:
  assert (pkg/'.lake/build/lib/lean'/rel.with_suffix('.olean')).is_file(),'Missing dependency cache '+name
  return
 for dep in re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_.]+)',(pkg/rel).read_text(encoding='utf-8-sig'),re.M):visit(dep)
 ordered.append((name,rel))
for name in ['Audit','Sigma2.FinalProofAudit','Sigma2.AllAxioms','Solution','Challenge','PaperNames']:visit(name)
# Every shipped Sigma2 module must be built, including name-checking paper maps.
for p in sorted((LEAN/'Sigma2').rglob('*.lean')):visit('.'.join(p.relative_to(LEAN).with_suffix('').parts))
records=[];start=time.monotonic();sigfile=LOG/'completed-sources.json';completed={}
# Resume only our own successful sources with unchanged source/dependency digests.
if '--resume' in sys.argv and sigfile.exists():completed=json.loads(sigfile.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def other_lean_compilers():
 if os.name!='nt':return []
 from ctypes import wintypes as wt
 class ProcessEntry(ctypes.Structure):
  _fields_=[('dwSize',wt.DWORD),('cntUsage',wt.DWORD),('th32ProcessID',wt.DWORD),('th32DefaultHeapID',ctypes.c_size_t),('th32ModuleID',wt.DWORD),('cntThreads',wt.DWORD),('th32ParentProcessID',wt.DWORD),('pcPriClassBase',wt.LONG),('dwFlags',wt.DWORD),('szExeFile',wt.WCHAR*260)]
 kernel=ctypes.WinDLL('kernel32',use_last_error=True)
 kernel.CreateToolhelp32Snapshot.argtypes=[wt.DWORD,wt.DWORD];kernel.CreateToolhelp32Snapshot.restype=wt.HANDLE
 kernel.Process32FirstW.argtypes=[wt.HANDLE,ctypes.POINTER(ProcessEntry)];kernel.Process32FirstW.restype=wt.BOOL
 kernel.Process32NextW.argtypes=[wt.HANDLE,ctypes.POINTER(ProcessEntry)];kernel.Process32NextW.restype=wt.BOOL
 kernel.CloseHandle.argtypes=[wt.HANDLE];kernel.CloseHandle.restype=wt.BOOL
 snapshot=kernel.CreateToolhelp32Snapshot(2,0);entry=ProcessEntry();entry.dwSize=ctypes.sizeof(entry);found=[]
 try:
  ok=kernel.Process32FirstW(snapshot,ctypes.byref(entry))
  while ok:
   if entry.szExeFile.lower() in ['lean.exe','leanexport.exe','leanchecker.exe','nanoda_bin.exe','nanoda-stack128.exe','nanoda_bin-stack128.exe']:found.append(entry.th32ProcessID)
   ok=kernel.Process32NextW(snapshot,ctypes.byref(entry))
 finally:kernel.CloseHandle(snapshot)
 return found

for i,(name,rel) in enumerate(ordered,1):
 src=LEAN/rel;out=OBJ/rel.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 deps=re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_.]+)',src.read_text(encoding='utf-8-sig'),re.M)
 ds={}
 for d in deps:
  dr=Path(d.replace('.','/')).with_suffix('.olean');obj=next((p for p in [OBJ/dr]+[q/'.lake/build/lib/lean'/dr for q in packages[1:]] if p.is_file()),None)
  if obj:ds[d]=sha(obj)
 signature={'source':sha(src),'imports':ds}
 if completed.get(name)==signature and out.exists():continue
 if os.name=='nt':
  class Memory(ctypes.Structure):
   _fields_=[('length',ctypes.c_ulong),('load',ctypes.c_ulong)]+[(n,ctypes.c_uint64) for n in ['total','available','totalPage','availablePage','totalVirtual','availableVirtual','availableExtended']]
  while True:
   m=Memory();m.length=ctypes.sizeof(m);assert ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m))
   active=other_lean_compilers()
   if m.available>=4*1024**3 and not active:break
   print('Waiting for 4 GiB free memory and no other Lean compiler; active='+str(active),flush=True);time.sleep(5)
 command=[str(lean),'-j1','-M6144','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-DautoImplicit=false','-o',str(out),str(rel)]
 print(f'[{i}/{len(ordered)}] {name}',flush=True);t=time.monotonic();log=LOG/(name.replace('.','_')+'.log')
 with log.open('w',encoding='utf-8') as f:r=subprocess.run(command,cwd=LEAN,env=env,stdout=f,stderr=subprocess.STDOUT)
 record={'module':name,'exit':r.returncode,'seconds':round(time.monotonic()-t,3),('peak_job_commit_bytes' if os.name=='nt' else 'peak_tree_RSS_bytes'):peak(),'source_sha256':sha(src)};records.append(record)
 (LOG/'resources.json').write_text(json.dumps({'lean':version,'records':records,'seconds':round(time.monotonic()-start,3),('peak_job_commit_bytes' if os.name=='nt' else 'peak_tree_RSS_bytes'):peak()},indent=2)+'\n')
 if r.returncode:print(log.read_text(encoding='utf-8'),flush=True);raise SystemExit(r.returncode)
 completed[name]=signature;sigfile.write_text(json.dumps(completed,indent=2)+'\n')
audit=(LOG/'Audit.log').read_text(encoding='utf-8');lines=[l for l in audit.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l]
roots=json.loads((LEAN/'pins/AUDIT-ROOTS.json').read_text());assert len(lines)==len(roots)
for name,line in zip(roots,lines):
 assert "'"+name+"'" in line,line
 axioms=set(re.search(r'\[(.*?)\]',line).group(1).split(', ')) if 'depends on axioms' in line else set()
 assert axioms<=set(['propext','Classical.choice','Quot.sound']),line
axiom_text='\n'.join(lines)+'\n'
(LOG/'AXIOMS.txt').write_text(axiom_text,encoding='utf-8',newline='\n')
if '--read-only-source' not in sys.argv:
 (LEAN/'AXIOMS.txt').write_text(axiom_text,encoding='utf-8',newline='\n')
print('PASS: all project sources rebuilt; all listed roots and every imported project declaration audited.',flush=True)
