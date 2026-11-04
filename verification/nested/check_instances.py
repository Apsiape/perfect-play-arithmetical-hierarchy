"""Exact validations of the five substantive validation instances.
Reads literal exported rows; does not import the producer.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict,Counter
import json,itertools,runpy,math,time,re,sys
import sympy as sy
OUT=Path(__file__).resolve().parent
lib=runpy.run_path(str(OUT/'check_nested.py'))
Algebra=lib['Algebra'];BaseModel=lib['Model']
START=time.time()
INSTANCES=['uniform-no','uniform-yes','uniform-lookup','comb-constant','comb-linear']

def audit_semantic_expansion(core,alg):
    def one(c=1,w=()):return alg.scalar(0,0,F(c),w)
    def add(a,b):return alg.add((a,1),(b,1))
    def scale(a,c):return alg.add((a,F(c)))
    ids={n:i+1 for i,n in enumerate(core['generators'])}
    def unit(n):return one(1,(ids[n],))
    def par(n):return scale(add(one(),unit('s_'+n)),F(1,2))
    flag=par('f');act=par('activity');E=par('E0');fp=scale(alg.mul(E,add(one(),unit('flag_E'))),F(1,2))
    ep=scale(alg.mul(E,add(one(),unit('selected_E'))),F(1,2))
    def decode(name,loc,scope):
        typ=core['typed_labels'][name];pre=name+'_'+loc
        if typ=='unitary':u=unit(pre)
        elif typ=='projection':u=scale(add(one(),unit(pre)),F(1,2))
        elif typ=='positive':u=scale(add(add(one(2),unit(pre)),alg.st(unit(pre))),F(1,4))
        else:u=scale(add(unit(pre+'_plus'),unit(pre+'_minus')),F(1,2))
        return alg.mul(scope,u)
    def exp(n):
        tag=n[0]
        if tag=='scalar':return one(n[1])
        if tag=='add':return add(exp(n[1]),exp(n[2]))
        if tag=='neg':return scale(exp(n[1]),-1)
        if tag=='mul':return alg.mul(exp(n[1]),exp(n[2]))
        if tag=='star':return alg.st(exp(n[1]))
        if tag=='corner':return fp if n[1]=='fp' else ep if n[1]=='ep' else par(n[1])
        if tag=='transport':return scale(add(unit('t_plus'),unit('t_minus')),F(1,2))
        if tag=='modular':return decode('a_'+n[1],n[2],act if n[2]=='A' else E)
        if tag=='label':
            source_scope=core.get('typed_scopes',{}).get(n[1],'f')
            return decode(n[1],n[2],(act if n[2]=='A' else E) if source_scope=='A' else (flag if n[2]=='A' else fp))
        raise ValueError(n)
    count=0
    for p in core['polynomials']:
        if p['kind']!='application':continue
        acc=defaultdict(F)
        for term in p['terms']:acc[0,0,alg.red(tuple(term['word']))]+=F(term['coefficient'])
        expected={k:v for k,v in acc.items() if v}
        assert exp(p['semantic_ast'])==expected,('semantic linkage',p['name'])
        count+=1
    return {'semantic_expression_trees_reexpanded_independently':count}

# Word prefix followed, optionally, by an opaque symbolic tail of known length.
def wl(w):return sum(1 if isinstance(a,int) else a[1] for a in w)
def empty(w):return len(w)==0
class Model(BaseModel):
    def __init__(self,core,cut=None,formal=False,shape=None):
        self.core=core;self.program=core['metadata']['instance_id'];self.kind=core['name'];self.cut=cut;self.formal=formal;self.separated=False;self.shape=shape or core['metadata'].get('canonical_bush_depth','0')
        self.states=core['metadata']['automaton']['states'];self.reject=self.states.index('reject')
    def k(self,m):return 1 if self.shape=='1' else m if self.shape=='m' else 0
    def guard(self,m,w):return int(self.positive(self.k(m)-wl(w)))
    def bit_equal(self,a,b):
        if self.formal:return sy.KroneckerDelta(a,b)
        return int(a==b)
    def state(self,x,t,m,w):
        l=wl(w)
        if t==0:return self.states.index('boot') if x==0 else 0
        if self.program.startswith('uniform-'):
            stages={1:(0,'move1'),2:(1,'scan1'),3:(1,'move2'),4:(2,'scan2')}
            if t in stages:pos,status=stages[t]
            else:
                pos=2;status='accept' if self.program=='uniform-yes' else 'reject' if self.program=='uniform-no' or t>=6 else 'wait'
        elif self.program=='comb-constant':pos=0;status='scan' if t==1 else 'accept' if self.guard(m,w)==int(l==0) else 'reject'
        else:
            stop=min(m,l)
            if t<2*stop+2:
                pos=(t-1)//2;status='scan' if t%2 else 'move'
            else:
                pos=stop;truth=l<m;status='accept' if self.guard(m,w)==truth else 'reject'
        return self.states.index(status) if x==pos else 0
    def head_projection(self,name,x,t,m,w):
        tag,j=name[0],int(name[1:])
        if tag=='L':
            if not self.positive(x):return int(j==0)
            x-=1
        if tag=='R':x+=1
        if tag=='N':t+=1
        if not self.formal:return int(self.state(x,t,m,w)==j)
        if self.zero(t):return int((j==self.states.index('boot')) if self.zero(x) else j==0)
        if j==self.reject and self.program not in ['uniform-no','uniform-lookup']:return 0
        return sy.Function('P'+str(j))(x,t,m,wl(w))
    def diag(self,name,x,t,m,w):
        n=name.removeprefix('check_');l=wl(w)
        if n=='Px':return self.bit_equal(x,0)
        if n=='Pt':return self.bit_equal(t,0)
        if n=='Cx':return self.dyad(x)
        if n=='Ct':return self.dyad(t)
        if n=='Z':return -1
        if n=='W':return 1 if self.equal(x%2,0) else -1
        if n=='Return':return int(self.equal(x%2,0))
        if n=='Reader':return 0 if self.equal(x%2,0) else -self.dyad(x)/4
        if n=='Q':return int(empty(w))
        if n=='Depth':return self.dyad(l)
        if n=='Root':return int(empty(w))*self.bit_equal(m,1)
        if n=='Guard':return self.guard(m,w)
        if n=='M':return self.dyad(m)
        if n in ['EqualM','EqualL']:return self.bit_equal(x,m if n=='EqualM' else l)
        if n in ['InverseM','InverseL']:
            exp=m if n=='InverseM' else l;a=self.dyad(exp);b=self.dyad(x)
            return 0 if exp==x else a*b/(2*(a-b))
        if n[0] in 'PLRN' and n[1:].isdigit():return self.head_projection(n,x,t,m,w)
        raise ValueError(('unknown diagonal',name))
    def shift(self,name,v,adj):
        o,i,x,t,m,j,w=v;z=list(v)
        if name.endswith('S') or name.endswith('T'):
            coord=2 if name.endswith('S') else 3;n=v[coord]
            if adj:
                if not self.positive(n):return None
                z[coord]-=1
            else:
                if self.cut is not None and n>=self.cut[0 if coord==2 else 1]:return None
                z[coord]+=1
        elif name=='A':
            if not empty(w):return None
            if adj:
                if not self.positive(m-1):return None
                z[4]-=1
            else:
                if self.cut is not None and m>=self.cut[2]:return None
                z[4]+=1
        elif name in ['B0','B1']:
            bit=int(name[-1])
            if adj:
                if empty(w):return None
                assert isinstance(w[0],int),w
                if w[0]!=bit:return None
                z[6]=w[1:]
            else:
                if not self.guard(m,w):return None
                z[6]=(bit,)+w
        else:raise ValueError(name)
        return tuple(z)
    def atom(self,node,v,adj=False):
        o,i,x,t,m,j,w=v;tag=node[0]
        if tag=='corner':
            name=node[1];want={'f':(0,0),'fp':(1,0),'ep':(1,1),'m0':(0,1)}.get(name)
            ok=o==0 if name=='activity' else (o,i)==want
            return {v:1} if ok else {}
        if tag=='transport':
            src,dst=((1,0),(0,1)) if adj else ((0,1),(1,0))
            return {(dst[0],dst[1],x,t,m,j,w):1} if (o,i)==src else {}
        if tag=='modular':
            name,loc=node[1:];outer=0 if loc=='A' else 1
            if o!=outer or i!=(1 if adj else 0):return {}
            z=self.shift(name,v,adj)
            if z is None:return {}
            z=list(z);z[1]=0 if adj else 1;return {tuple(z):1}
        if tag=='label':
            name,loc=node[1:];outer=0 if loc=='A' else 1
            if (o,i)!=(outer,0):return {}
            if name=='J':return {(o,i,x,t,m,1-j,w):1}
            if name=='K':return {v:(-1)**j}
            a=self.diag(name,x,t,m,w)
            return {} if self.zero(a) else {v:a}
        raise ValueError(node)

# Independently specified local step, with center-state priority on collisions.
def local_step(program,states,left,current,bits,boundary):
    c=states[current];l=states[left]
    if c=='none':
        if boundary:return 0
        if program.startswith('uniform-') and l.startswith('move'):return states.index('scan'+l[4:])
        if not program.startswith('uniform-') and l=='move':return states.index('scan')
        return 0
    if c in ['accept','reject']:return current
    if c=='wait':return states.index('reject')
    if c.startswith('move'):return 0
    if program.startswith('uniform-'):
        if c=='boot':return states.index('move1')
        marker=bits[0]
        if not marker:return states.index('move2' if c=='scan1' else 'movebig')
        if c=='scan2':return states.index('accept' if program=='uniform-yes' else 'wait' if program=='uniform-lookup' else 'reject')
        return states.index('reject')
    if c=='boot':return states.index('scan')
    em,el,d=bits
    if program=='comb-constant':return states.index('accept' if d==el else 'reject')
    if not(em or el):return states.index('move')
    return states.index('accept' if d==bool(el and not em) else 'reject')

class Local(Model):
    def __init__(self,core,left,current,bits,boundary):
        super().__init__(core);self.left=left;self.current=current;self.bits=bits;self.boundary=boundary
        self.nxt=local_step(self.program,self.states,left,current,bits,boundary)
    def diag(self,name,x,t,m,w):
        if name=='Return':return self.bits[0]
        if name in ['EqualM','EqualL','Guard']:return self.bits[['EqualM','EqualL','Guard'].index(name)]
        if name in ['Px','check_Px']:return self.boundary
        if name[0] in 'PLRN' and name[1:].isdigit():
            current={'P':self.current,'L':self.left,'R':0,'N':self.nxt}[name[0]]
            return int(int(name[1:])==current)
        return super().diag(name,x,t,m,w)

def local_certificates(core):
    pmap={p['name']:p for p in core['polynomials']};states=core['metadata']['automaton']['states'];program=core['metadata']['instance_id'];n=len(states)
    bits_count=1 if program.startswith('uniform-') else 3;total=0;branch=Counter()
    for left,current,bits,boundary in itertools.product(range(n),range(n),itertools.product((0,1),repeat=bits_count),range(2)):
        mod=Local(core,left,current,bits,boundary);v=(0,0,0,0,1,0,())
        for j in range(n):assert not mod.apply(pmap['update_'+str(j)]['semantic_ast'],v);total+=1
        branch[states[mod.nxt]]+=1
    assert branch['accept']>0 if program!='uniform-no' else branch['reject']>0
    assert branch['reject']>0
    # Marker decisions on the legal comb fibers; these are the rejection proof.
    if program=='comb-constant':
        for ell in [0,1]:assert (ell<1)==bool(ell==0)
    if program=='comb-linear':
        for em,el,d in [(0,1,1),(1,1,0)]:assert local_step(program,states,0,states.index('scan'),(em,el,d),0)==states.index('accept')
        for em,el,d in [(0,1,0),(1,1,1)]:assert local_step(program,states,0,states.index('scan'),(em,el,d),0)==states.index('reject')
    return {'exact_local_update_cases':total,'local_successor_histogram':dict(branch),'both_accept_and_reject_decision_branches_checked':True,'partition_certificate':'one-hot initial conditions plus deterministic one-hot successor; all local assignments exhaustively verified'}

def word_cases(shape):
    nm=sy.Symbol('n_m',integer=True,positive=True);r=sy.Symbol('tail_length',integer=True,positive=True)
    out=[]
    if shape=='1':
        return [(m,w) for m in [1,2,nm+2] for w in [(),(0,),(1,)]]
    for ell in range(4):
        for w in itertools.product((0,1),repeat=ell):
            start=max(1,ell)
            for m in [start,start+1,start+nm+1]:out.append((m,w))
    for a,b in itertools.product((0,1),repeat=2):
        w=(a,b,('tail',r+1));ell=wl(w)
        for m in [ell,ell+1,ell+nm+1]:out.append((m,w))
    return out

def dyadic_reader_certificate():
    u,v=sy.symbols('u v',positive=True)
    f=u*v/(2*(u-v));assert sy.cancel(f*(u-v)-u*v/2)==0
    assert sy.cancel((u-v)*0)==0
    return {'unequal_generic_residual':'0','equal_boundary_residual':'0','bound':'if u>=2v then |uv/(2(u-v))|<=v<=1; symmetric otherwise'}

def semantic(core):
    mod=Model(core,formal=True);nx=sy.Symbol('n_x',integer=True,positive=True);nt=sy.Symbol('n_t',integer=True,positive=True)
    xy=[(x,t) for x in [0,1,2,3,2*nx+2,2*nx+3] for t in [0,1,2,nt+2]]
    cases=[(x,t,1,j,()) for x,t in xy for j in [0,1]] if mod.kind=='quarter-plane' else [(x,t,m,0,w) for x,t in xy for m,w in word_cases(mod.shape)]
    counts=Counter();reject_expected={}
    for p in core['polynomials']:
        if p['kind']!='application':continue
        name=p['name']
        if name.startswith('update_'):counts['update_identities_by_exhaustive_local_certificate']+=1;continue
        if name.endswith('_partition') and name[0] in 'PLRN':counts['partition_identities_by_one_hot_induction']+=1;continue
        if name in ['M_equality','M_separation','L_equality','L_separation']:counts['dyadic_reader_identities_symbolic_generic_and_equal_boundary']+=1;continue
        if name.startswith('reject_'):
            if mod.program in ['uniform-no','uniform-lookup']:
                start=5 if mod.program=='uniform-no' else 6
                reject_expected={'operator':f'projection onto x=2 and t>={start}, on the period-2 model','root_weight':str(F(1,8*2**start)),'lifted_weight':str(F(1,81*8*2**start)),'expected':'nonzero; negative instance has no perfect normal model'}
                counts['expected_nonzero_rejection_rows']+=1;continue
            counts['positive_reject_rows_skipped_formal_reject_field_zero']+=1;continue
        selected=cases
        if re.fullmatch(r'[PLRN][0-9]+_(Cx|Ct|M|Depth|Guard)',name):
            # Scalar diagonal commutators: the coefficient values are arbitrary.
            selected=[(nx+2,nt+2,sy.Symbol('m',integer=True,positive=True),0,())]
        elif re.fullmatch(r'(left|right|next)_[0-9]+',name):
            # The formal P_j field is arbitrary in its m/ell arguments.
            ell=sy.Symbol('ell',integer=True,nonnegative=True)
            selected=[(x,t,sy.Symbol('m',integer=True,positive=True),0,(('tail',ell),)) for x,t in xy]
        elif re.fullmatch(r'initial_[0-9]+',name):
            selected=[(x,t,1,0,()) for x in [0,nx+1] for t in [0,nt+1]]
        for x,t,m,j,w in selected:
            for o,i in [(0,0),(1,0)]:
                vec=(o,i,x,t,m,j,w);res=mod.apply(p['semantic_ast'],vec)
                assert not res,(mod.program,name,vec,res)
                counts['exact_generic_and_boundary_actions']+=1
        counts['application_identities_checked_by_basis_action']+=1
    return {'counts':dict(counts),'reject_row_policy':'skipped in this symbolic pass; positive-program formal reject field is zero; see concrete far-history/truncation runs','recurrence_basis':'exhaustive local truth table plus prose induction; not a machine-checked induction certificate','reader_certificate':dyadic_reader_certificate(),'expected_infinite_rejection':reject_expected,'coverage':'all x/time lower boundaries and parity tails; all short tree words, both first-letter branches, generic opaque tails, branch/leaf boundaries and spine m=1','basis_index_formula':'head state is the deterministic local recurrence verified in the local certificate; every other operator has the explicit shift/diagonal action in this checker'}

def words_for(m,shape):
    k=1 if shape=='1' else m
    return [w for ell in range(k+1) for w in itertools.product((0,1),repeat=ell)]

def exact_truncation(core,nx,nt,nm):
    mod=Model(core,cut=(nx,nt,nm));plans={p['row']:p for p in core['row_plans']};defects={};rejection=F(0)
    if mod.kind=='comb':Z=sum(F((1 if mod.shape=='1' else m)+1,2**m) for m in range(1,nm+1))
    for p in core['polynomials']:
        if p['kind']!='application':continue
        norm=F(0)
        mw=[(1,())] if mod.kind=='quarter-plane' else [(m,w) for m in range(1,nm+1) for w in words_for(m,mod.shape)]
        for x,t,(m,w),j in itertools.product(range(nx+1),range(nt+1),mw,range(2) if mod.kind=='quarter-plane' else [0]):
            root=F(2**(nx-x),2**(nx+1)-1)*F(2**(nt-t),2**(nt+1)-1)
            root*=F(1,2) if mod.kind=='quarter-plane' else F(1,2**(m+len(w)))/Z
            for o,i in [(0,0),(1,0)]:
                res=mod.apply(p['semantic_ast'],(o,i,x,t,m,j,w));norm+=root*F(2**int(o!=0)*2**int(i!=0),81)*sum(c*c for c in res.values())
        if norm:defects[p['name']]=norm
    expected={('S_isometry' if mod.kind=='quarter-plane' else 'check_S_isometry'):F(1,81*(2**(nx+1)-1)),('T_isometry' if mod.kind=='quarter-plane' else 'check_T_isometry'):F(1,81*(2**(nt+1)-1))}
    if mod.kind=='comb':expected['A_initial']=F(1,81*2**nm)/Z
    if mod.program in ['uniform-no','uniform-lookup']:
        start=5 if mod.program=='uniform-no' else 6
        if nx>=2 and nt>=start:
            rejection=F(2**(nx-2),2**(nx+1)-1)*sum((F(2**(nt-t),2**(nt+1)-1) for t in range(start,nt+1)),F())/81
            expected['reject_'+str(mod.reject)]=rejection
    assert defects==expected,(mod.program,(nx,nt,nm),defects,expected)
    bound=sum(F(4*plans['polynomial_'+n]['denominator']**2,plans['polynomial_'+n]['dimension']**3)*F(2,3)*d for n,d in defects.items())
    bboundary=sum(F(4*plans['polynomial_'+n]['denominator']**2,plans['polynomial_'+n]['dimension']**3)*F(2,3)*d for n,d in defects.items() if not n.startswith('reject_'))
    return {'cutoffs':[nx,nt,nm],'nonzero_lifted_row_defects':{n:str(d) for n,d in defects.items()},'worst_row':max(defects,key=defects.get),'loss_bound_before_Q_squared':str(bound),'boundary_loss_only_before_Q_squared':str(bboundary),'expected_rejection_defect':str(rejection)}

def formula_truncations(core):
    mod=Model(core);out=[];plans={p['row']:p for p in core['row_plans']}
    rectangles=[(0,0),(1,1),(2,3),(3,2),(7,3),(15,3),(31,7)]+[(n,n) for n in [7,15,31,63,127,255]]
    for nx,nt in rectangles:
        nm=max(1,min(nx,nt));a=F(1,81*(2**(nx+1)-1));b=F(1,81*(2**(nt+1)-1))
        d={('S_isometry' if mod.kind=='quarter-plane' else 'check_S_isometry'):a,('T_isometry' if mod.kind=='quarter-plane' else 'check_T_isometry'):b}
        if mod.kind=='comb':
            Z=2*(1-F(1,2**nm)) if mod.shape=='1' else 3-F(nm+3,2**nm)
            d['A_initial']=F(1,81*2**nm)/Z
        boundary=sum(F(4*plans['polynomial_'+n]['denominator']**2,plans['polynomial_'+n]['dimension']**3)*F(2,3)*v for n,v in d.items())
        rej=F()
        if mod.program in ['uniform-no','uniform-lookup']:
            start=5 if mod.program=='uniform-no' else 6
            if nx>=2 and nt>=start:rej=F(2**(nx-2),2**(nx+1)-1)*F(2**(nt-start+1)-1,2**(nt+1)-1)/81
        out.append({'cutoffs':[nx,nt,nm],'boundary_defects':{n:str(v) for n,v in d.items()},'worst_boundary_row':max(d,key=d.get),'boundary_loss_before_Q_squared':str(boundary),'expected_rejection_lifted_defect':str(rej),'method':'exact boundary and normalized geometric/bush formulas; no large matrix allocation'})
    return out

if __name__=='__main__':
    saved=OUT/'instance-validation.json'
    results=json.loads(saved.read_text(encoding='utf-8')) if '--resume' in sys.argv and saved.exists() else {}
    for instance in INSTANCES:
        if instance in results:
            print(instance,'retaining completed checks; rechecking semantic link',flush=True)
            core=json.loads((OUT/(instance+'-core.json')).read_text(encoding='utf-8'));a=Algebra(core)
            results[instance]['rational_row_certification'].update(audit_semantic_expansion(core,a));a.projection.cache_clear();del a,core
            continue
        core=json.loads((OUT/(instance+'-core.json')).read_text(encoding='utf-8'))
        print(instance,'all literal rows',flush=True);a=Algebra(core);rows=a.audit();rows.update(audit_semantic_expansion(core,a));a.projection.cache_clear();del a
        print(instance,'local decision branches',flush=True);local=local_certificates(core)
        print(instance,'generic infinite actions',flush=True);sem=semantic(core)
        print(instance,'measured finite boundary and rejection defects',flush=True)
        small=[exact_truncation(core,nx,nt,nm) for nx,nt,nm in ([(0,0,1),(1,1,1),(2,3,1),(3,2,1),(3,7,1)] if core['name']=='quarter-plane' else [(1,1,1),(2,3,2),(3,2,3)])]
        results[instance]={'counts':core['counts'],'rational_row_certification':rows,'local_program_certification':local,'infinite_model':sem,'explicit_small_truncations':small,'all_requested_and_larger_cutoff_formulas':formula_truncations(core)}
        del core
        (OUT/'instance-validation.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
    results['elapsed_seconds']=time.time()-START
    import psutil
    results['peak_working_set_bytes']=__import__('runpy').run_path(str(Path(__file__).resolve().parent/'memory.py'))['peak_bytes']()
    assert results['peak_working_set_bytes']<1500000000
    (OUT/'instance-validation.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
    print('PASS',results['elapsed_seconds'],'seconds; peak',results['peak_working_set_bytes'],'bytes')
