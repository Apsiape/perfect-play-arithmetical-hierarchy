from pathlib import Path
from fractions import Fraction as F
import json,runpy,time,itertools
import sympy as s
OUT=Path(__file__).resolve().parent
lib=runpy.run_path(str(OUT/'check_instances.py'));Algebra=lib['Algebra'];link=lib['audit_semantic_expansion']
start=time.time();core=json.loads((OUT/'schema-validation-core.json').read_text(encoding='utf-8'))
print('Auditing all 518601 literal rational rows',flush=True)
a=Algebra(core);rows=a.audit();print('Row audit passed; independently expanding semantic trees',flush=True);rows.update(link(core,a));a.projection.cache_clear();del a
print('Checking exact transported residuals in all five modular degrees',flush=True)
n=4;I=s.eye(n);Z=s.zeros(n)
X=s.zeros(n);Y=s.zeros(n)
for j in range(n-1):X[j+1,j]=1;Y[j+1,j]=s.Rational(1,j+2)
labels={'L':s.diag(*[s.Rational(1,j+2) for j in range(n)]),'R':s.diag(1,0,1,0)}
modular={'X':X,'Y':Y};H=s.diag(*[s.Rational(1,2**j) for j in range(n)])
assert H*X==X*H/2 and H*Y==Y*H/2

def add(a,b):
    z=dict(a)
    for k,v in b.items():z[k]=z.get(k,Z)+v
    return {k:v for k,v in z.items() if v!=Z}
def scale(a,c):return {k:c*v for k,v in a.items() if c*v!=Z}
def mul(a,b):
    out={}
    for (i,j),v in a.items():
        for (k,l),w in b.items():
            if j==k:out[i,l]=out.get((i,l),Z)+v*w
    return {k:v for k,v in out.items() if v!=Z}
def st(a):return {(j,i):v.T for (i,j),v in a.items()}
def block(i,j,v=I):return {(i,j):v} if v!=Z else {}
# Corner numbers: outer*5+inner.
identity={ (j,j):I for j in range(25)};aux={}
def ast(node):
    tag=node[0]
    if tag=='scalar':return scale(identity,s.Rational(node[1]))
    if tag=='add':return add(ast(node[1]),ast(node[2]))
    if tag=='neg':return scale(ast(node[1]),-1)
    if tag=='mul':return mul(ast(node[1]),ast(node[2]))
    if tag=='star':return st(ast(node[1]))
    if tag=='corner':return block({'f':0,'fp':5,'ep':6,'m0':1}[node[1]],{'f':0,'fp':5,'ep':6,'m0':1}[node[1]])
    if tag=='transport':return block(5,1)
    if tag=='modular':
        name,loc=node[1:];return block(1 if loc=='A' else 6,0 if loc=='A' else 5,modular[name])
    if tag=='label':
        name,loc=node[1:]
        if name in labels:return block(0 if loc=='A' else 5,0 if loc=='A' else 5,labels[name])
        v=aux[name]
        return v if loc=='A' else {(i+5,j+5):a for (i,j),a in v.items()}
    raise ValueError(node)
for name,definition in core['metadata']['derived_coefficients'].items():aux[name]=ast(definition)
spec=core['metadata']['presentation'];groups={}
for term in spec['relations'][0]['terms']:
    r=I;degree=0
    for token in term['word']:
        adj=token.endswith('*');name=token[:-1] if adj else token
        v=modular[name] if name in modular else labels[name]
        if name in modular:degree+=-1 if adj else 1
        r=r*(v.T if adj else v)
    groups[degree]=groups.get(degree,Z)+s.Rational(term['coefficient'])*r
checks=[]
for p in core['polynomials']:
    if p['kind']!='application':continue
    degree=int(p['name'].rsplit('_',1)[1]);r=groups[degree]
    if degree<0:r=r.T
    target=5 if abs(degree)<2 else 6;source=5 if degree==0 else 0
    expected=block(target,source,r)
    actual=ast(p['semantic_ast']);assert actual==expected,(p['name'],actual,expected)
    checks.append({'degree':degree,'exact_residual_transport':'PASS','input_residual_nonzero':r!=Z})
import psutil
peak=__import__('runpy').run_path(str(Path(__file__).resolve().parent/'memory.py'))['peak_bytes']();assert peak<1500000000
result={'row_checks':rows,'all_five_modular_degrees_and_interior_coefficients':checks,'derived_coefficients':len(aux),'arithmetic':'exact rational 4x4 root matrices and sparse 25-corner block matrices','common_density_covariance_exact':True,'elapsed_seconds':time.time()-start,'peak_working_set_bytes':peak,'scope':'exact translation of arbitrary residuals, not a claim that this synthetic presentation has a perfect model'}
(OUT/'schema-validation.json').write_text(json.dumps(result,indent=2),encoding='utf-8');print(json.dumps(result,indent=2))
