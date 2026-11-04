"""Run all checks in a fresh directory, with captured output and nonzero failure status."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, importlib.metadata, json, os, platform, subprocess, sys, uuid
root=Path(__file__).resolve().parent
stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:8]
parser=argparse.ArgumentParser()
parser.add_argument('--output-directory',type=Path)
args=parser.parse_args()
out=args.output_directory.resolve() if args.output_directory else root/'runs'/stamp
out.mkdir(parents=True,exist_ok=False)
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONIOENCODING='utf-8')
results=[]
for name in ['thm1_fms.py','l2_pitfall.py','fock_catalan_numbers.py','exact_constants.py']:
    run=subprocess.run([sys.executable,'-B',str(root/name)],cwd=root,text=True,encoding='utf-8',capture_output=True,env=env)
    (out/(name+'.out')).write_text(run.stdout+run.stderr,encoding='utf-8',newline='\n')
    results.append(dict(script=name,exit_code=run.returncode,passed=run.returncode==0))
    print(('PASS' if run.returncode==0 else 'FAIL')+': '+name,flush=True)
versions={x:importlib.metadata.version(x) for x in ['numpy','networkx','sympy','mpmath']}
summary=dict(passed=all(x['passed'] for x in results),python=platform.python_version(),dependencies=versions,results=results)
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8',newline='\n')
print('Results: '+str(out),flush=True)
sys.exit(0 if summary['passed'] else 1)
