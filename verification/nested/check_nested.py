"""Independent row audit and exact semantic-model checks; run with python -I.
The JSON has concrete validation instances, not supplied verifier programs.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict,Counter
from functools import lru_cache
import json,math,itertools,time,sys
import sympy as s
OUT=Path(__file__).resolve().parent
START=time.time()

# Free group ring with declared parameter involutions, independent of producer.
class Algebra:
    def __init__(self,core):
        self.core=core;self.words=[tuple(w) for w in core['words']]
        self.inv={i+1 for i,n in enumerate(core['generators']) if n.startswith('s_')}
        self.tri={r['name']:r for r in core['rows'] if 'words' in r}
        self.dtri={next(k for k in r['terms'] if k.startswith('D')):r for r in self.tri.values()}
        self.polys={p['name']:p for p in core['polynomials']}
        self.par={n:core['generators'].index('s_'+n)+1 for n in core['parameters']}
    def red(self,w):
        z=[]
        for t in w:
            if abs(t) in self.inv:t=abs(t)
            if z and (z[-1]==-t or t in self.inv and z[-1]==t):z.pop()
            else:z.append(t)
        return tuple(z)
    def add(self,*terms):
        out=defaultdict(F)
        for a,c in terms:
            for (i,j,w),v in a.items():out[i,j,self.red(w)]+=c*v
        return {k:v for k,v in out.items() if v}
    def mul(self,a,b):
        out=defaultdict(F)
        for (i,j,w),v in a.items():
            for (k,l,z),c in b.items():
                if j==k:out[i,l,self.red(w+z)]+=v*c
        return {k:v for k,v in out.items() if v}
    def st(self,a):return {(j,i,self.red(tuple(-x for x in w[::-1]))):v for (i,j,w),v in a.items()}
    def scalar(self,i,j,c=1,w=()):return {(i,j,self.red(w)):F(c)} if c else {}
    @lru_cache(1024)
    def projection(self,name):
        if name=='I':return self.add(*[(self.scalar(i,i),1) for i in range(3)])
        if name in ['F1','F2','F3']:return self.scalar(int(name[1])-1,int(name[1])-1)
        if name[0:2] in ['KG','KH']:
            g=name[1:];ij=g[1:3]
            return self.add((self.projection('F'+ij[0]),1),(self.projection('F'+ij[1]),1),(self.projection(g),-1))
        if name[0] in 'GH' and '_' in name and name[1:3] in ['12','13','23']:
            i,j=int(name[1])-1,int(name[2])-1;w=self.words[int(name.split('_')[1])]
            if name[0]=='G':a,b,c=F(1,2),F(1,2),F(1,2)
            else:a,b,c=F(4,5),F(1,5),F(2,5)
            return self.add((self.scalar(i,i,a),1),(self.scalar(j,j,b),1),(self.scalar(i,j,c,w),1),(self.scalar(j,i,c,tuple(-t for t in w[::-1])),1))
        if name in self.dtri:
            r=self.dtri[name];u,v,w=map(tuple,r['words'])
            assert self.red(u+v)==self.red(w)
            m={}
            for i in range(3):m.update(self.scalar(i,i,F(1,3)))
            for (i,j),z in [((0,1),u),((1,2),v),((0,2),w)]:m.update(self.scalar(i,j,F(1,3),z));m.update(self.scalar(j,i,F(1,3),tuple(-t for t in z[::-1])))
            return m
        # Parameter binding projections.
        for par,pid in self.par.items():
            e=self.add((self.projection('I'),F(1,2)),(self.add(*[(self.scalar(i,i,1,(pid,)),1) for i in range(3)]),F(1,2)))
            if name==par:return e
            if name.startswith(par+'_'):
                tail=name[len(par)+1:]
                if tail[0:1] in ['p','n'] and tail[1:] in '123' and len(tail)==2:
                    fi=self.projection('F'+tail[1]);ep=self.mul(e,fi)
                    return ep if tail[0]=='p' else self.add((fi,1),(ep,-1))
                ij,ab=tail.split('_');pi=self.add((self.projection('F'+ij[0]),1),(self.projection('F'+ij[1]),1))
                ep=self.mul(e,pi);g=self.projection('G'+ij+'_0')
                a=ep if ab[0]=='1' else self.add((pi,1),(ep,-1))
                b=g if ab[1]=='1' else self.add((pi,1),(g,-1))
                return self.mul(a,b)
        raise ValueError(name)
    def audit(self):
        done=Counter()
        for row in self.core['rows']:
            actual=self.add(*[(self.projection(n),F(c)) for n,c in row['terms'].items()])
            if 'polynomial' in row:
                p=self.polys[row['polynomial']];acc=defaultdict(F)
                for term in p['terms']:
                    w=tuple(term['word']);c=F(term['coefficient'])
                    acc[0,1,self.red(w)]+=c
                    acc[1,0,self.red(tuple(-t for t in w[::-1]))]+=c
                expected={k:v for k,v in acc.items() if v}
                assert actual==expected,('polynomial link',row['name'])
                done['polynomial_rows_linked']+=1
            else:
                assert not actual,('row identity',row['name'],actual)
                done['universal_rows_zero']+=1
        # Individual graph and triangle effects are actual projections.
        for r in self.core['rows']:
            if r['kind']=='graph' and r['name'].startswith('graphTilt_'):
                k=r['name'].split('_')[-1];ij=r['name'].split('_')[1]
                for a in ['G','H']:
                    z=self.projection(a+ij+'_'+k)
                    assert self.mul(z,z)==z and self.st(z)==z
                    done['graph_effects_projective']+=1
            if 'words' in r:
                name=next(n for n in r['terms'] if n.startswith('D'));z=self.projection(name)
                assert self.mul(z,z)==z and self.st(z)==z
                done['triangle_effects_projective']+=1
        return dict(done)

# A basis vector is (outer,inner,x,time,m,Weyl_index).
# Only decoded contractions occur in application certificates; their unitary
# encodings are supplied by the explicitly proved finite-density-block formula.
class Model:
    def __init__(self,kind,cut=None):self.kind=kind;self.cut=cut;self.symbolic=False
    def zero(self,x):return s.simplify(x)==0 if isinstance(x,s.Basic) else x==0
    def positive(self,x):
        if not isinstance(x,s.Basic):return x>0
        if x.is_positive is not None:return x.is_positive
        raise ValueError(('undecided positive boundary',x))
    def equal(self,a,b):
        d=s.simplify(a-b)
        if d==0:return True
        if d.is_zero is False or d.is_positive or d.is_negative:return False
        # The generic separated case explicitly excludes equality bands.
        if getattr(self,'separated',False):return False
        raise ValueError(('undecided equality boundary',a,b,d))
    def dyad(self,n):return s.Integer(2)**(-n) if isinstance(n,s.Basic) else F(1,2**n)
    def tracks(self,x,m):
        if self.kind=='quarter-plane':return [1 if self.equal(x%2,0) else 0]
        return [int(self.equal(x,m)),int(self.equal(x,0)),0]
    def diag(self,name,x,t,m):
        n=name.removeprefix('check_')
        if n=='Px':return int(self.equal(x,0))
        if n=='Pt':return int(self.equal(t,0))
        if n=='Cx':return self.dyad(x)
        if n=='Ct':return self.dyad(t)
        if n=='Z':return -1
        if n=='W':return 1 if self.equal(x%2,0) else -1
        if n=='Return':return int(self.equal(x%2,0))
        if n=='Reader':return 0 if self.equal(x%2,0) else -self.dyad(x)/4
        if n=='Q' or n=='Depth':return 1
        if n=='Root':return int(self.equal(m,1))
        if n=='Guard':return 0
        if n=='M':return self.dyad(m)
        if n in ['EqualM','EqualL','InverseM','InverseL']:
            a=self.dyad(m) if n.endswith('M') else 1;b=self.dyad(x);eq=self.equal(m if n.endswith('M') else 0,x)
            if n.startswith('Equal'):return int(eq)
            return 0 if eq else a*b/(2*(a-b))
        if n[0] in 'PLRN' and n[1:].isdigit():
            y=x
            if n[0]=='L':
                if not self.positive(x):bits=[0]*(1 if self.kind=='quarter-plane' else 3)
                else:bits=self.tracks(x-1,m)
            else:
                if n[0]=='R':y=x+1
                bits=self.tracks(y,m)
            j=0
            for bit in bits:j=2*j+bit
            return int(j==int(n[1:]))
        raise ValueError(('unknown label',name))
    def atom(self,node,v,adj=False):
        o,i,x,t,m,j=v;tag=node[0]
        if tag=='corner':
            name=node[1];want={'f':(0,0),'fp':(1,0),'ep':(1,1),'m0':(0,1)}.get(name)
            if name=='activity':ok=o==0
            elif want:ok=(o,i)==want
            else:raise ValueError(node)
            return {v:1} if ok else {}
        if tag=='transport':
            src,dst=((1,0),(0,1)) if adj else ((0,1),(1,0))
            return {(dst[0],dst[1],x,t,m,j):1} if (o,i)==src else {}
        if tag=='modular':
            name,loc=node[1:];outer=0 if loc=='A' else 1
            if o!=outer or i!=(1 if adj else 0):return {}
            coord=2 if name.endswith('S') else 3 if name.endswith('T') else 4 if name=='A' else None
            if coord is None:return {} # Both B_i vanish in the k_m=0 model.
            z=list(v);n=v[coord];lower=1 if coord==4 else 0
            if adj:
                if not self.positive(n-lower):return {}
                z[coord]-=1
            else:
                if self.cut is not None and n>=self.cut:return {}
                z[coord]+=1
            z[1]=0 if adj else 1;return {tuple(z):1}
        if tag=='label':
            name,loc=node[1:];outer=0 if loc=='A' else 1
            if (o,i)!=(outer,0):return {}
            if name=='J':return {(o,i,x,t,m,1-j):1}
            if name=='K':return {v:(-1)**j}
            a=self.diag(name,x,t,m)
            return {} if self.zero(a) else {v:a}
        raise ValueError(('bad semantic leaf',node))
    def apply(self,node,v,adj=False):
        tag=node[0]
        if tag=='scalar':
            c=F(node[1]);return {v:c} if c else {}
        if tag=='neg':return {w:-c for w,c in self.apply(node[1],v,adj).items()}
        if tag=='star':return self.apply(node[1],v,not adj)
        if tag=='add':
            z=defaultdict(lambda:0)
            for a in node[1:]:
                for w,c in self.apply(a,v,adj).items():z[w]+=c
            return {w:s.factor(c) if isinstance(c,s.Basic) else c for w,c in z.items() if not self.zero(c)}
        if tag=='mul':
            a,b=node[1:] if not adj else node[:0:-1]
            z=defaultdict(lambda:0)
            for u,c in self.apply(b,v,adj).items():
                for w,d in self.apply(a,u,adj).items():z[w]+=c*d
            return {w:s.factor(c) if isinstance(c,s.Basic) else c for w,c in z.items() if not self.zero(c)}
        return self.atom(node,v,adj)

def semantic(core):
    mod=Model(core['name']);nx=s.Symbol('n_x',integer=True,positive=True);nt=s.Symbol('n_t',integer=True,positive=True);nm=s.Symbol('n_m',integer=True,positive=True);ng=s.Symbol('gap',integer=True,positive=True)
    if core['name']=='quarter-plane':cases=[(x,t,1,j,False) for x in [0,1,2,3,2*nx+2,2*nx+3] for t in [0,1,2,nt+2] for j in [0,1]]
    else:
        pairs=[]
        for d in range(-3,4):
            pairs += [(m+d,m,False) for m in range(1,5) if m+d>=0]
            pairs.append((nm+4+d,nm+4,False))
        for m in list(range(1,5))+[nm+4]:pairs.append((m+ng+3,m,False))
        for x in list(range(4))+[nx+3]:pairs.append((x,x+ng+3,False))
        cases=[(x,t,m,0,sep) for x,m,sep in pairs for t in [0,1,2,nt+2]]
    count=0
    for p in core['polynomials']:
        if p['kind']!='application':continue
        ast=p['semantic_ast']
        for x,t,m,j,sep in cases:
            mod.separated=sep
            for o,i in [(0,0),(1,0)]:
                v=(o,i,x,t,m,j);res=mod.apply(ast,v)
                assert not res,(core['name'],p['name'],v,res)
                count+=1
    return {'application_identities':sum(p['kind']=='application' for p in core['polynomials']),'exact_basis_cases':count,'generic_indices':['n_x','n_t','n_m','gap'],'boundary_scope':'exhaustive 0/1/2/3 boundaries, two parity tails, equality bands -3..3 and both gap tails; no unresolved equality assumptions','instance_scope':core['metadata']}

def truncations(core):
    out=[];apps=[p for p in core['polynomials'] if p['kind']=='application'];plans={p['row']:p for p in core['row_plans']}
    # Exhaustive exact evaluation at small cutoffs; analytic defects extend it.
    for N in [0,1,2,3] if core['name']=='quarter-plane' else [1,2,3]:
        mod=Model(core['name'],N);mod.separated=False;defects={}
        for p in apps:
            norm=F(0)
            for x,t,m,j in itertools.product(range(N+1),range(N+1),[1] if core['name']=='quarter-plane' else range(1,N+1),range(2) if core['name']=='quarter-plane' else [0]):
                root=F(1,2**(x+t+2))/(1-F(1,2**(N+1)))**2
                root*=F(1,2) if core['name']=='quarter-plane' else F(1,2**m)/(1-F(1,2**N))
                for o,i in [(0,0),(1,0)]:
                    r=mod.apply(p['semantic_ast'],(o,i,x,t,m,j));norm+=root*F(2**int(o!=0)*2**int(i!=0),81)*sum(c*c for c in r.values())
            if norm:defects[p['name']]=norm
        expected={('S_isometry' if core['name']=='quarter-plane' else 'check_S_isometry'):F(1,81*(2**(N+1)-1)),('T_isometry' if core['name']=='quarter-plane' else 'check_T_isometry'):F(1,81*(2**(N+1)-1))}
        if core['name']=='comb':expected['A_initial']=F(1,81*(2**N-1))
        assert defects==expected,(N,defects,expected)
        bound=sum(F(4*plans['polynomial_'+n]['denominator']**2,plans['polynomial_'+n]['dimension']**3)*F(2,3)*d for n,d in defects.items())
        out.append({'N':N,'exact_nonzero_lifted_defects':{n:str(d) for n,d in defects.items()},'worst':max(defects,key=defects.get),'loss_bound_without_Q_squared':str(bound)})
    for N in [7,15,31,63,127,255]:
        tail=F(1,81*(2**(N+1)-1));d={'S_isometry':tail,'T_isometry':tail}
        if core['name']=='comb':d={'check_S_isometry':tail,'check_T_isometry':tail,'A_initial':F(1,81*(2**N-1))}
        bound=sum(F(4*plans['polynomial_'+n]['denominator']**2,plans['polynomial_'+n]['dimension']**3)*F(2,3)*v for n,v in d.items())
        out.append({'N':N,'method':'exact boundary formula, verified by symbolic shift action','worst_lifted_defect':str(max(d.values())),'loss_bound_without_Q_squared':str(bound)})
    return out

if __name__=='__main__':
    results={}
    for name in ['quarter-plane','comb']:
        core=json.loads((OUT/(name+'-core.json')).read_text(encoding='utf-8'))
        print(name,'auditing every rational row',flush=True)
        a=Algebra(core);audit=a.audit();a.projection.cache_clear();del a
        print(name,'exact infinite-model applications',flush=True)
        exact=semantic(core)
        print(name,'exact finite defects',flush=True)
        trunc=truncations(core)
        results[name]={'rows':audit,'infinite_model':exact,'truncations':trunc}
    results['elapsed_seconds']=time.time()-START
    try:
        import psutil
        results['peak_working_set_bytes']=__import__('runpy').run_path(str(Path(__file__).resolve().parent/'memory.py'))['peak_bytes']()
        assert results['peak_working_set_bytes']<1500000000
    except ImportError:pass
    (OUT/'validation.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
    print(json.dumps(results,indent=2))
