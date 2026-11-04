"""Exact generic scaffold/unitary certificates for all structural input rows.
Root unitaries are free diagonal phases keyed by basis coordinate; projection phases are involutions.
Partial-isometry encodings are explicit monomial unitaries over Q(i).
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import json,itertools,re,runpy,hashlib,time
import sympy as sy
OUT=Path(__file__).resolve().parent
lib=runpy.run_path(str(OUT/'check_instances.py'));Model=lib['Model'];word_cases=lib['word_cases']

def ga(a,b):return (a[0]+b[0],a[1]+b[1])
def gm(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def conj(a):return (a[0],-a[1])
ONE=(F(1),F());ZERO=(F(),F())
def reduce_phase(w):
    z=[]
    for sign,key,involution in w:
        if involution:sign=1
        if z and z[-1][1]==key and (involution or z[-1][0]==-sign):z.pop()
        else:z.append((sign,key,involution))
    return tuple(z)

class Scaffold:
    def __init__(self,core,cut=None):
        self.core=core;self.names=core['generators'];self.model=Model(core,formal=True,cut=cut)
        self.blocks={r['block']:r for r in core['transport_refinements']}
    def generator(self,token,v):
        adj=token<0;gid=abs(token);name=self.names[gid-1];o,i,x,t,m,j,w=v
        if gid in self.blocks:
            r=self.blocks[gid]
            if 'unitaryA' in r:
                z=list(v);z[0]=0;u,c,ph=self.generator((-1 if adj else 1)*r['unitaryA'],tuple(z));u=list(u);u[0]=o
                return tuple(u),c,ph
            chosen=0 if r['name']=='flag' else 1
            return v,(F(1 if i==chosen else -1),F()),()
        if name.startswith('s_'):
            par=name[2:]
            if par=='f':ok=o==0 and i==0
            elif par=='activity':ok=o==0
            elif par.startswith('m') and par[1:].isdigit():ok=o==0 and i==int(par[1:])+1
            elif par.startswith('E') and par[1:].isdigit():ok=o==int(par[1:])+1
            elif par.startswith('positive_'):
                axis=par[len('positive_'):];magic=(o==0 and i>0) if axis.endswith('i') else o>0
                if not magic:return v,(F(-1),F()),()
                return self.axis(axis,v)
            else:raise ValueError(name)
            return v,(F(1 if ok else -1),F()),()
        if name in ['xi','zi','xo','zo']:return self.axis(name,v)
        if name in ['flag_E','selected_E']:
            chosen=0 if name=='flag_E' else 1
            return v,(F(1 if o!=1 or i==chosen else -1),F()),()
        if name in ['t_plus','t_minus']:
            phase=(F(),F(1 if name.endswith('plus') else -1));a=(o,i)
            if a==(0,1):
                z=(1,0,x,t,m,j,w);return z,conj(phase) if adj else ONE,()
            if a==(1,0):
                z=(0,1,x,t,m,j,w);return z,ONE if adj else phase,()
            return v,conj(phase) if adj else phase,()
        match=re.fullmatch(r'(.+)_(A|E)(_plus|_minus)?',name)
        if not match:raise ValueError(name)
        label,loc,choice=match.groups();outer=0 if loc=='A' else 1
        if o!=outer:return v,ONE,()
        if label.startswith('a_'):
            modular=label[2:];phase=(F(),F(1 if choice=='_plus' else -1))
            if i==0:
                z=self.model.shift(modular,v,False)
                if z is not None:
                    z=list(z);z[1]=1;return tuple(z),conj(phase) if adj else ONE,()
            if i==1:
                z=self.model.shift(modular,v,True)
                if z is not None:
                    z=list(z);z[1]=0;return tuple(z),ONE if adj else phase,()
            return v,conj(phase) if adj else phase,()
        if i!=0:return v,ONE,()
        typ=self.core['typed_labels'][label]
        key=(label,choice,x,t,m,j,w)
        return v,ONE,(((-1 if adj else 1),key,typ=='projection'),)
    def axis(self,name,v):
        o,i,x,t,m,j,w=v;z=list(v)
        if name.endswith('i'):
            if o==0 and i>0:z[1]=1+((i-1)^ (2 if name[0]=='x' else 1))
        else:
            if o>0:z[0]=1+((o-1)^ (2 if name[0]=='x' else 1))
        return tuple(z),ONE,()
    def word(self,word,v):
        c=ONE;phase=()
        for token in reversed(word):
            v,b,ph=self.generator(token,v);c=gm(b,c);phase=reduce_phase(ph+phase)
        return v,c,phase
    def polynomial(self,terms,v):
        out={}
        for term in terms:
            z,c,ph=self.word(term['word'],v);c=(c[0]*F(term['coefficient']),c[1]*F(term['coefficient']));key=(z,ph)
            out[key]=ga(out.get(key,ZERO),c)
        return {k:c for k,c in out.items() if c!=ZERO}
    def root_cases(self,gen_names):
        if self.model.cut is not None:
            nx,nt,nm=self.model.cut
            mw=[(1,())] if self.model.kind=='quarter-plane' else [(m,w) for m in range(1,nm+1) for w in lib['words_for'](m,self.model.shape)]
            return [(x,t,m,w) for x,t,(m,w) in itertools.product(range(nx+1),range(nt+1),mw)]
        nx=sy.Symbol('n_x',integer=True,positive=True);nt=sy.Symbol('n_t',integer=True,positive=True);nm=sy.Symbol('n_m',integer=True,positive=True)
        shifts=set()
        for name in gen_names:
            match=re.fullmatch(r'a_(.+)_(A|E)(_plus|_minus)',name)
            if match:shifts.add(match.group(1))
        if not shifts:return [(nx+2,nt+2,nm+2,())]
        if any(n.endswith('S') for n in shifts):return [(x,nt+2,nm+2,()) for x in [0,1,nx+2]]
        if any(n.endswith('T') for n in shifts):return [(nx+2,t,nm+2,()) for t in [0,1,nt+2]]
        if 'A' in shifts:return [(nx+2,nt+2,m,w) for m in [1,2,nm+2] for w in [(),(0,)]]
        return [(nx+2,nt+2,m,w) for m,w in word_cases(self.model.shape)]
    def audit(self):
        rows=0;actions=0;unitaryactions=0
        for p in self.core['polynomials']:
            if p['kind']!='structural':continue
            gids={abs(t) for term in p['terms'] for t in term['word']}
            # Include source unitary dependency when a block is the only token.
            gids.update(self.blocks[g]['unitaryA'] for g in list(gids) if g in self.blocks and 'unitaryA' in self.blocks[g])
            cases=self.root_cases([self.names[g-1] for g in gids])
            for o,i,(x,t,m,w) in itertools.product(range(5),range(5),cases):
                vec=(o,i,x,t,m,0,w);res=self.polynomial(p['terms'],vec)
                assert not res,('structural',self.model.program,p['name'],vec,res)
                actions+=1
            rows+=1
        for g,name in enumerate(self.names,1):
            deps=[name]
            if g in self.blocks and 'unitaryA' in self.blocks[g]:deps.append(self.names[self.blocks[g]['unitaryA']-1])
            for o,i,(x,t,m,w) in itertools.product(range(5),range(5),self.root_cases(deps)):
                vec=(o,i,x,t,m,0,w)
                for word in [[g,-g],[-g,g]]:
                    z,c,ph=self.word(word,vec)
                    assert z==vec and c==ONE and not ph,('unitarity',name,vec,z,c,ph)
                    unitaryactions+=1
        return {'structural_polynomial_rows_exact':rows,'generic_and_boundary_structural_actions':actions,'all_canonical_generators_unitary_actions':unitaryactions,'arithmetic':'Gaussian rationals and free diagonal phase words keyed by basis coordinate; projection phases are involutions','construction_scope':'root encodings are free diagonal phases keyed by basis coordinate; a_i and t explicit partial-isometry completions; all 25 scaffold corners','no_density_inverse':True}

if __name__=='__main__':
    results={};reuse={};start=time.time()
    for instance in ['uniform-no','uniform-yes','uniform-lookup','comb-constant','comb-linear']:
        core=json.loads((OUT/(instance+'-core.json')).read_text(encoding='utf-8'))
        structure=[p for p in core['polynomials'] if p['kind']=='structural']
        key=hashlib.sha256(json.dumps([structure,core['typed_labels'],core['metadata'].get('canonical_bush_depth')],sort_keys=True).encode()).hexdigest()
        print(instance,'exact scaffold',flush=True)
        if key in reuse:results[instance]=reuse[key]|{'reused_identical_structural_polynomials':True}
        else:
            results[instance]=Scaffold(core).audit()
            cuts=[(0,0,1),(2,3,1)] if core['name']=='quarter-plane' else [(1,1,1),(2,3,2)]
            results[instance]['finite_structural_checks']=[{'cutoffs':list(cut),**Scaffold(core,cut=cut).audit()} for cut in cuts]
            reuse[key]=results[instance]
    results['elapsed_seconds']=time.time()-start
    import psutil
    results['peak_working_set_bytes']=__import__('runpy').run_path(str(Path(__file__).resolve().parent/'memory.py'))['peak_bytes']()
    assert results['peak_working_set_bytes']<1500000000
    (OUT/'scaffold-validation.json').write_text(json.dumps(results,indent=2),encoding='utf-8');print(json.dumps(results,indent=2))
