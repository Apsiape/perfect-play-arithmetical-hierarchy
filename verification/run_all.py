"""Run every merged finite check from a relocated copy into a fresh directory."""
from pathlib import Path
import argparse,subprocess,sys,os,json,time,shutil,hashlib
H=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output-dir',required=True,type=Path);ap.add_argument('--full-counts',action='store_true');ap.add_argument('--skip-expanded-count',action='store_true',help='with --full-counts, skip only the expanded count that exceeds 1.5 GB');args=ap.parse_args();out=args.output_dir.resolve()
assert out!=H and H not in out.parents,'output must be outside the verification source tree'
assert not out.exists() or not any(out.iterdir()),'output directory must be new or empty'
out.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONIOENCODING='utf-8',OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',MKL_NUM_THREADS='1')
results=[]
def run(name,script,*argv,cwd=None):
    start=time.monotonic();p=subprocess.run([sys.executable,'-I','-B',str(script),*map(str,argv)],cwd=cwd or out,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8')
    (out/'logs').mkdir(exist_ok=True);(out/'logs'/(name+'.log')).write_text(p.stdout,encoding='utf-8',newline='\n')
    # Some imported review programs report a failed condition instead of exiting.
    bad=any((line.startswith(('FAIL ','FAIL:','SOME FAIL')) or line == 'FAILURE') for line in p.stdout.splitlines())
    ok=p.returncode==0 and not bad
    results.append(dict(check=name,passed=ok,exit_code=p.returncode,seconds=round(time.monotonic()-start,2)))
    print(('PASS ' if ok else 'FAIL ')+name,flush=True)
    if not ok:print(p.stdout[-4000:],flush=True)
    return ok
run('base-suites',H/'run_base.py','--output-dir',out/'base')
for folder in ['ii-only','renyi','capacity']:
    for script in sorted((H/folder).glob('*.py')):run(folder+'-'+script.stem,script)
n=out/'nested';shutil.copytree(H/'nested',n)
if run('nested-generation',n/'generate_nested.py'):
    expected=json.loads((n/'expected-core-records.json').read_text());actual=json.loads((n/'compiler-counts.json').read_text())
    assert actual==expected,'regenerated nested core counts or byte hashes differ'
    results.append(dict(check='nested-reference-core-hashes-and-counts',passed=True))
    for script in ['check_instances.py','check_far_history.py','check_fibonacci_models.py','check_scaffold.py','check_hostile.py','check_programs.py','check_encoding_density.py']:
        run('nested-'+Path(script).stem,n/script)
    if run('nested-schema-generation',n/'generate_nested.py','--presentation',n/'schema-validation-input.json','--output-stem','schema-validation'):
        run('nested-schema-audit',n/'check_schema.py')
f=out/'full-compile';shutil.copytree(H/'full-compile',f)
run('full-compile-exact-small-audit',f/'exact_checks.py')
if args.full_counts:
    for variant,number in [('expanded',6191638087),('factored',8516580)]:
        if variant=='expanded' and args.skip_expanded_count:continue
        if run('full-'+variant+'-producer',f/variant/'full_compile.py'):
            run('full-'+variant+'-independent',f/variant/'independent_count.py')
            data=json.loads((f/variant/'counts_primary.json').read_text());assert data['questions_per_party']==number
# Absolute paths in generated text are made portable. Large cores stay only in the chosen output.
for p in out.rglob('*'):
    if p.is_file() and p.suffix in ['.json','.log','.txt','.tex'] and not p.name.endswith('-core.json'):
        t=p.read_text(encoding='utf-8')
        for base,mark in [(out,'<output>'),(H,'<verification>')]:
            for form in [str(base),base.as_posix()]:t=t.replace(form,mark).replace(json.dumps(form)[1:-1],mark)
        p.write_text(t,encoding='utf-8',newline='\n')
summary={'passed':all(r['passed'] for r in results),'checks':results,'full_dry_counts_rerun':args.full_counts and not args.skip_expanded_count,'factored_dry_count_rerun':args.full_counts,'expanded_dry_count_skipped':args.skip_expanded_count}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(summary,indent=2));sys.exit(0 if summary['passed'] else 1)
