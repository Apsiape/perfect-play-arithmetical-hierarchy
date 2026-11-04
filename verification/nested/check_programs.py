from pathlib import Path
from fractions import Fraction as F
import json,runpy,itertools
OUT=Path(__file__).resolve().parent
lib=runpy.run_path(str(OUT/'check_instances.py'));Model=lib['Model'];step=lib['local_step']
results={}
for instance in ['uniform-no','uniform-yes','uniform-lookup']:
    core=json.loads((OUT/(instance+'-core.json')).read_text(encoding='utf-8'));model=Model(core);states=model.states
    configuration=[states.index('boot')]+[0]*7;history=[]
    for t in range(9):
        assert configuration==[model.state(x,t,1,()) for x in range(8)]
        history.append({'time':t,'head':[(x,states[c]) for x,c in enumerate(configuration) if c]})
        configuration=[step(instance,states,configuration[x-1] if x else 0,configuration[x],(int(x%2==0),),int(x==0)) for x in range(8)]
    if instance=='uniform-yes':
        assert history[5]['head']==[(2,'accept')];prob=F()
    else:
        start=5 if instance=='uniform-no' else 6
        assert history[start]['head']==[(2,'reject')];prob=F(1,8*2**start)
    results[instance]={'explicit_period_two_history':history,'absorbing_tail_certified':True,'exact_root_reject_probability':str(prob),'exact_lifted_reject_defect':str(prob/81),'one_oriented_row_zero_probability_before_Q_squared':str(prob/31104)}
for instance in ['comb-constant','comb-linear']:
    core=json.loads((OUT/(instance+'-core.json')).read_text(encoding='utf-8'));model=Model(core);states=model.states
    pairs=[(0,1,1),(0,0,0)] if instance=='comb-constant' else [(0,1,1),(1,1,0)]
    for bits in pairs:
        assert step(instance,states,0,states.index('scan'),bits,1 if instance=='comb-constant' else 0)==states.index('accept')
        wrong=bits[:2]+(1-bits[2],)
        assert step(instance,states,0,states.index('scan'),wrong,1 if instance=='comb-constant' else 0)==states.index('reject')
    if instance=='comb-linear':
        for d in [0,1]:assert step(instance,states,0,states.index('scan'),(0,0,d),0)==states.index('move')
    results[instance]={'all_legal_stop_order_cases_accept':pairs,'flipped_guard_cases_reject':True,'critical_index':'0' if instance=='comb-constant' else '1/2','spectrum_normalizer':'2' if instance=='comb-constant' else '3'}
# Genuine hostile guard: a constant-depth comb presented to the linear checker.
core=json.loads((OUT/'comb-linear-core.json').read_text(encoding='utf-8'));bad=Model(core,shape='1')
for m in [1,2,3]:
    for w in [(),(0,),(1,)]:
        for x,t in itertools.product(range(4),range(7)):
            for p in core['polynomials']:
                if p['kind']!='application':continue
                r=bad.apply(p['semantic_ast'],(0,0,x,t,m,0,w))
                if p['name'].startswith('reject_'):
                    expected=bool(m>=2 and len(w)==1 and x==1 and t>=4)
                    assert bool(r)==expected
                else:assert not r,(p['name'],m,w,x,t,r)
results['comb-linear-wrong-guard-model']={'actual_shape':'k_m=1','checker_program':'k_m=m','only_failing_application_row':'reject_5','reject_support':'m>=2, ell=1, x=1, t>=4','exact_root_reject_probability':'1/256','exact_lifted_reject_defect':'1/20736','other_application_rows_exact_on_explicit_boundary_cases':True,'tail_formula':'(comb fiber mass 1/4)*(checker x mass 1/4)*(time tail 1/16)=1/256'}
(OUT/'program-validation.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
print('PASS: uniform YES/NO/lookup histories; both comb decision branches; hostile wrong-guard model')
