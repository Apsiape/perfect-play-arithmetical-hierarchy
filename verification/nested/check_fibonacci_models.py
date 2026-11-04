"""Sparse complex Fibonacci Weyl/reader models q=F4,F5,F6.
Evaluates literal exported application ASTs, not Boolean game predicates.
Numerical algebra tolerance is recorded; no dense scaffold/game allocation.
"""
from pathlib import Path
from fractions import Fraction as F
import cmath,math,json,runpy,time,itertools,psutil
OUT=Path(__file__).resolve().parent
lib=runpy.run_path(str(OUT/'check_instances.py'));Base=lib['Model'];step=lib['local_step']
TOL=2e-12
class FibonacciModel(Base):
    def __init__(self,core,q,a,cut=None):
        super().__init__(core,cut=cut);self.q=q;self.a=a;self.z=cmath.exp(2j*math.pi*a/q);self.roundoff=0.0
    def zero(self,x):
        if isinstance(x,complex):
            if abs(x)<TOL:self.roundoff=max(self.roundoff,abs(x));return True
            return False
        return super().zero(x)
    def state(self,x,t,m,w):
        if t==0:return self.states.index('boot') if x==0 else 0
        if t<=2*self.q:
            pos=t//2
            status=('move'+str(min(pos+1,2)) if pos<2 else 'movebig') if t%2 else ('scan'+str(pos) if pos<3 else 'scanbig')
        else:pos=self.q;status='reject'
        return self.states.index(status) if x==pos else 0
    def diag(self,name,x,t,m,w):
        if name=='Z':return self.z
        if name=='W':return self.z**(x%self.q)
        if name=='Return':return int(x%self.q==0)
        if name=='Reader':return 0 if x%self.q==0 else float(F(1,2**(x+1)))/(self.z**(x%self.q)-1)
        return super().diag(name,x,t,m,w)
    def atom(self,node,v,adj=False):
        if node[0]!='label':return super().atom(node,v,adj)
        o,i,x,t,m,j,w=v;name,loc=node[1:];outer=0 if loc=='A' else 1
        if (o,i)!=(outer,0):return {}
        if name=='J':return {(o,i,x,t,m,(j+(-1 if adj else 1))%self.q,w):1}
        a=self.z**(-j) if name=='K' else self.diag(name,x,t,m,w)
        if adj and isinstance(a,complex):a=a.conjugate()
        return {} if self.zero(a) else {v:a}
def run(core,q,a):
    start=time.time();mod=FibonacciModel(core,q,a);nx=2*q+1;nt=2*q+3;apps=[p for p in core['polynomials'] if p['kind']=='application'];n=0
    # An independent local-rule evolution checks the explicit history formula.
    config=[mod.states.index('boot')]+[0]*(nx+1)
    for t in range(nt+2):
        assert config==[mod.state(x,t,1,()) for x in range(nx+2)]
        config=[step(mod.program,mod.states,config[x-1] if x else 0,config[x],(int(x%q==0),),int(x==0)) for x in range(nx+2)]
    for x,t,j in itertools.product(range(nx+1),range(nt+1),range(q)):
        for p in apps:
            for o in (0,1):
                r=mod.apply(p['semantic_ast'],(o,0,x,t,1,j,()));n+=1
                expected=p['name']=='reject_9' and x==q and t>=2*q+1 and o==0
                assert bool(r)==expected,(q,p['name'],x,t,j,o,r)
    # Repeat with exact shift cutoffs; all boundary residual supports are checked.
    trunc=FibonacciModel(core,q,a,cut=(nx,nt,1));defects={};finite_n=0
    for p in apps:
        norm=0.0
        for x,t,j in itertools.product(range(nx+1),range(nt+1),range(q)):
            weight=float(F(2**(nx-x),2**(nx+1)-1)*F(2**(nt-t),2**(nt+1)-1))/q
            for o in (0,1):
                r=trunc.apply(p['semantic_ast'],(o,0,x,t,1,j,()));finite_n+=1
                norm+=weight*(2**o)/81*sum(abs(c)**2 for c in r.values())
        if norm>1e-24:defects[p['name']]=norm
    rejection=F(2**(nx-q),2**(nx+1)-1)*F(2**(nt-(2*q+1)+1)-1,2**(nt+1)-1)
    expected={'S_isometry':float(F(1,81*(2**(nx+1)-1))),'T_isometry':float(F(1,81*(2**(nt+1)-1))),'reject_9':float(rejection/81)}
    assert defects.keys()==expected.keys(),(q,defects)
    assert all(abs(defects[k]-v)<2e-13 for k,v in expected.items()),(q,defects,expected)
    max_reader=max(abs(mod.diag('Reader',x,0,1,())) for x in range(1,4*q+1))
    assert max_reader<=9/32+TOL
    return {'q':q,'a':a,'z':[mod.z.real,mod.z.imag],'Weyl_convention':'J|j>=|j+1 mod q>, K|j>=z^(-j)|j>','application_rows':len(apps),'basis_cutoffs':[nx,nt],'infinite_model_row_actions':n,'finite_truncation_row_actions':finite_n,'infinite_nonzero_row':'reject_9 only: x=q,t>=2q+1','truncation_defects':defects,'expected_defects':expected,'exact_truncated_root_reject_probability':str(rejection),'exact_infinite_root_reject_probability':str(F(1,2**(3*q+2))),'reader_max_over_x_through_4q':max_reader,'largest_suppressed_complex_roundoff':max(mod.roundoff,trunc.roundoff),'tolerance':TOL,'elapsed_seconds':time.time()-start}
if __name__=='__main__':
    core=json.loads((OUT/'uniform-no-core.json').read_text(encoding='utf-8'));results={}
    for q,a in [(3,2),(5,3),(8,5)]:
        results[str(q)]=run(core,q,a);print(q,results[str(q)],flush=True)
    peak=__import__('runpy').run_path(str(Path(__file__).resolve().parent/'memory.py'))['peak_bytes']();assert peak<1500000000
    results['peak_working_set_bytes']=peak;results['scope']='numerical sparse application algebra and local histories; no Boolean game materialized; unbounded-q value-one limit is proof-only'
    (OUT/'fibonacci-model-validation.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
    print('PASS; peak',peak)
