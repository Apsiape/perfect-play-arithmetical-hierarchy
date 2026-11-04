"""Far-index check ported from review work/mine/far_history.py.
Finite engine evidence for explicit honest histories, not an induction proof.
"""
from pathlib import Path
import json,runpy,sys,time,itertools,random,psutil
OUT=Path(__file__).resolve().parent
lib=runpy.run_path(str(OUT/'check_instances.py'));Model=lib['Model']
def check(name,bound=30):
    core=json.loads((OUT/(name+'-core.json')).read_text(encoding='utf-8'))
    mod=Model(core)
    rows=[p for p in core['polynomials'] if p['kind']=='application' and
          (p['name'].split('_')[0] in ['update','reject','left','right','next','initial'] or p['name'].endswith('_partition'))]
    rng=random.Random(7);start=time.time();n=0;points=0;nonzero={};max_t=0
    def pts():
        if core['name']=='quarter-plane':
            yield from ((x,t,1,j,()) for x in range(14) for t in range(30) for j in (0,1))
        else:
            for m in range(1,bound+1):
                for ell in range(mod.k(m)+1):
                    w=tuple(rng.randint(0,1) for _ in range(ell))
                    for x in range(min(m,ell)+4):
                        for t in range(2*min(m,ell)+6):yield x,t,m,0,w
    expected_reject='reject_'+str(mod.reject)
    for x,t,m,j,w in pts():
        points+=1;max_t=max(max_t,t)
        for p in rows:
            r=mod.apply(p['semantic_ast'],(0,0,x,t,m,j,w));n+=1
            expected=(name in ['uniform-no','uniform-lookup'] and p['name']==expected_reject and x==2 and t>=(5 if name=='uniform-no' else 6))
            assert bool(r)==expected,(name,p['name'],x,t,m,len(w),r)
            if r:
                z=nonzero.setdefault(p['name'],{'count':0,'examples':[]});z['count']+=1
                if len(z['examples'])<6:z['examples'].append([x,t,m,len(w)])
    result={'rows':len(rows),'points':points,'evaluations':n,'maximum_time_index':max_t,'maximum_successor_time_read':max_t+1,'maximum_m':bound if core['name']!='quarter-plane' else 1,'nonzero_rows':nonzero,'cut':None,'coverage':'one seeded word per legal (m,length); all indicated x,t; all selected head rows','elapsed_seconds':time.time()-start}
    print(name,result,flush=True);return result
if __name__=='__main__':
    names=sys.argv[1:] or ['uniform-no','uniform-yes','uniform-lookup','comb-constant','comb-linear']
    results={name:check(name) for name in names}
    peak=__import__('runpy').run_path(str(Path(__file__).resolve().parent/'memory.py'))['peak_bytes']();assert peak<1500000000
    results['peak_working_set_bytes']=peak
    (OUT/'far-history-validation.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
    print('PASS: finite far-index recurrence engine check; peak',peak)
