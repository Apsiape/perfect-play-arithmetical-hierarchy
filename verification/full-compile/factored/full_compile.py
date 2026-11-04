"""Full ten-label compiler: expand exact presentation, dry-count Boolean game.
Run with Python -I. It never creates question arrays or the game in dry mode.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict, Counter
from itertools import product
import json, math, time, sys, ctypes, gzip, hashlib
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
START=time.perf_counter()
GAMMA=['s','b','f','d','z0','z','h','H']
def phi(l,c,r,pulse):
    if c=='H':return 'H'
    if c=='s':return 'd'
    if c=='f':return 'z0' if pulse else 'd'
    if c=='z0':return 'z'
    if c=='z':return 'z'
    if c=='h':return 'H' if l=='#' else 'd'
    if c=='d':
        if r=='z0':return 'h'
        if r=='h':return 'd' if l=='#' else 'H'
        return 'd'
    if l=='s':return 'f'
    if l=='f' and not pulse:return 'f'
    return 'b'

def write_automaton_metadata(lookup):
    data={'description':'Explicit eight-symbol scan automaton for e=0; halt unless clock order is 2','input_e':0,'alphabet':GAMMA,'initial':['s','b'],'transition_table':lookup}
    (OUT/'automaton.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8',newline='\n')

if '--automaton-only' in sys.argv:
    write_automaton_metadata([[l,c,r,pulse,phi(l,c,r,pulse)] for l,c,r,pulse in product(['#']+GAMMA,GAMMA,GAMMA,(0,1))])
    print('Regenerated automaton.json from the producer transition function.')
    sys.exit(0)


_memory=__import__('runpy').run_path(str(Path(__file__).resolve().parent.parent/'memory.py'))
_memory['install_cap']()
def peak():
    n=_memory['peak']();assert n<7*1024**3;return n
params=['e'+str(i) for i in range(17)]+[a+str(g) for g in range(1,5) for a in ('ZI','IX')]
atoms=[]; refl=set()
def atom(name,reflection=False):
    i=len(atoms)+1;atoms.append(name)
    if reflection:refl.add(i)
    return {(i,):F(1)}
def inv(t):return t if abs(t) in refl else -t
def reduce_word(w):
    s=[]
    for t in w:
        if s and s[-1]==inv(t):s.pop()
        else:s.append(t)
    return tuple(s)
def add(*ps):
    d=defaultdict(F)
    for p,c in ps:
        for w,v in p.items():d[w]+=v*c
    return {w:v for w,v in d.items() if v}
def mul(*ps):
    p={():F(1)}
    for q in ps:
        d=defaultdict(F)
        for u,a in p.items():
            for v,b in q.items():d[reduce_word(u+v)]+=a*b
        p={w:v for w,v in d.items() if v}
    return p
def adj(p):return {reduce_word(tuple(inv(t) for t in w[::-1])):v for w,v in p.items()}
one={():F(1)}
E={p:add((one,F(1,2)),(atom('s_'+p,True),F(1,2))) for p in params}
e=[E['e'+str(i)] for i in range(17)]
corner=[e[0],e[1],e[5],e[9],e[13]]
axes={(g,a):atom(a+str(g)) for g in range(1,5) for a in ('x','z')}
labels={'root':'projection','Ux':'unitary','Uy':'unitary','Px':'projection','Py':'projection','W':'unitary','C':'positive','Z':'unitary','J':'unitary','K':'unitary'}
U={(r,n):atom('u'+str(r)+'_'+n) for r in range(5) for n in labels}
V={(g,n):atom('v'+str(g)+'_'+n) for g in range(1,5) for n in labels}

source={n:atom('source_'+n) for n in ['ret']+GAMMA}
tin=[atom('T_'+s) for s in ('plus','minus')]
a={ab:add((atom('a'+ab+'_plus'),F(1,2)),(atom('a'+ab+'_minus'),F(1,2))) for ab in ('00','01','10','11')}
def decode(r,n):
    u=U[r,n];c=corner[r];typ=labels[n]
    if typ=='unitary':return mul(c,u)
    if typ=='projection':return mul(c,add((one,F(1,2)),(u,F(1,2))))
    return mul(c,add((one,F(1,2)),(u,F(1,4)),(adj(u),F(1,4))))
D={(r,n):decode(r,n) for r in range(5) for n in labels}
P={n:mul(e[0],add((one,F(1,2)),(u,F(1,2)))) for n,u in source.items()}
T=mul(e[0],add(*[(u,F(1,2)) for u in tin]))
words={()}; app=[]; hist=Counter(); detail=[]
f=gzip.open(OUT/'application_polynomials.jsonl.gz','wt',encoding='utf-8',newline='\n')
def dim_terms(terms):
    if not terms:return 1,4,2
    den=math.lcm(*(v.denominator for v in terms.values()))
    ints={n:int(v*den) for n,v in terms.items()}
    c0=2*ints.get('I',0)+sum(v for n,v in ints.items() if n!='I')
    length=2+abs(c0)+sum(abs(v) for n,v in ints.items() if n!='I')
    assert length%2==0
    d=4
    while d<length:d*=4
    return den,d,length

def emit(name,p):
    # Keep nonzero rows only. Tautologies have no equation to enforce.
    if not p:return
    for w in p:
        for j in range(1,len(w)+1):words.add(w[:j])
    s=sum(p.values(),F(0));terms={('G',w):2*c for w,c in p.items()}
    if s:terms['F1']=-s;terms['F2']=-s
    den,d,l=dim_terms(terms);hist[d]+=1
    rec={'name':name,'L':den,'d':d,'slots_unpadded':l,'monomials':len(p)}
    app.append(rec)
    f.write(json.dumps({'name':name,'terms':[[list(w),str(c)] for w,c in sorted(p.items())]},separators=(',',':'))+'\n')
    if name.startswith('update_'):print(json.dumps(rec),flush=True)
    peak()
# The frame cover, axis definitions and copies.
emit('cover',add(*[(p,1) for p in e],(one,-1)))
for g in range(1,5):
    M=add(*[(e[j],1) for j in range(1+4*(g-1),5+4*(g-1))])
    for ax,ev in [('x','ZI'),('z','IX')]:
        emit('axis_'+ax+str(g),add((axes[g,ax],1),(one,-1),(M,2),(E[ev+str(g)],-2)))
for r in range(5):
    for n in labels:
        emit('support_u'+str(r)+'_'+n,mul(add((U[r,n],1),(one,-1)),add((one,1),(corner[r],-1))))
        if labels[n]=='projection':emit('involution_u'+str(r)+'_'+n,add((mul(U[r,n],U[r,n]),1),(one,-1)))
for g in range(1,5):
    M=add(*[(e[j],1) for j in range(1+4*(g-1),5+4*(g-1))])
    for n in labels:
        parts=[(V[g,n],1),(one,-1),(corner[g-1],1),(M,1),(mul(corner[g-1],U[g-1,n]),-1)]
        for aa,bb in product((0,1),repeat=2):
            x=axes[g,'x'] if aa else one;z=axes[g,'z'] if bb else one
            parts.append((mul(x,z,corner[g],U[g,n],adj(z),adj(x)),-1))
        emit('block_'+str(g)+'_'+n,add(*parts))
for n,u in source.items():
    emit('support_source_'+n,mul(add((u,1),(one,-1)),add((one,1),(e[0],-1))))
    emit('involution_source_'+n,add((mul(u,u),1),(one,-1)))
for i,u in enumerate(tin):emit('support_T'+str(i),mul(add((u,1),(one,-1)),add((one,1),(e[0],-1))))
for ab in a:emit('support_a'+ab,add((a[ab],1),(mul(e[13],a[ab],e[0]),-1)))
for ab in a:
    for cd in a:emit('fock_'+ab+'_'+cd,add((mul(adj(a[ab]),a[cd]),1),*(([(e[0],-1)]) if ab==cd else [])))
emit('range',add(*[(mul(x,adj(x)),1) for x in a.values()],(e[13],-1),(D[4,'root'],1)))
# Endpoint recursions: all typed copies use corner identities.
for ab,aa in a.items():
    av,bv=map(int,ab)
    for label,bit,pos in [('Ux',av,0),('Uy',bv,1)]:
        target=list(ab);target[pos]='0' if bit else '1';target=''.join(target)
        rhs=mul(a[target],D[0,label]) if bit else a[target]
        emit(label+'_'+ab,add((mul(D[4,label],aa),1),(rhs,-1)))
    for label,bit in [('Px',av),('Py',bv)]:
        emit(label+'_'+ab,add((mul(D[4,label],aa),1),*(([(mul(aa,D[0,label]),-1)]) if not bit else [])))
    for n in ('J','K','Z'):emit('commute_'+n+'_'+ab,add((mul(D[4,n],aa),1),(mul(aa,D[0,n]),-1)))
    rhs=mul(aa,D[0,'Z'] if bv else e[0],D[0,'W'],D[0,'W'])
    emit('clock_W_'+ab,add((mul(D[4,'W'],aa),1),(rhs,-1)))
    emit('counter_C_'+ab,add((mul(D[4,'C'],aa),1),(mul(aa,D[0,'C'],D[0,'C']),-F(1,2**bv))))
for n in ('Ux','Uy','Px','Py','W','C'):emit('root_'+n,add((mul(D[0,n],D[0,'root']),1),(D[0,'root'],-1)))
emit('weyl',add((mul(D[0,'J'],D[0,'K']),1),(mul(D[0,'Z'],D[0,'K'],D[0,'J']),-1)))
for n in ('J','K','Ux','Uy','Px','Py','W','C'):emit('Z_'+n,add((mul(D[0,'Z'],D[0,n]),1),(mul(D[0,n],D[0,'Z']),-1)))
for n,p in list(P.items())+[('T',T)]:emit('Z_source_'+n,add((mul(D[0,'Z'],p),1),(mul(p,D[0,'Z']),-1)))
emit('reader_return',mul(add((D[0,'W'],1),(e[0],-1)),P['ret']))
emit('reader_inverse',add((mul(T,add((D[0,'W'],1),(e[0],-1))),1),(mul(D[0,'C'],add((e[0],1),(P['ret'],-1))),-F(1,2))))
emit('PVM',add(*[(P[c],1) for c in GAMMA],(e[0],-1)))
px,py=D[0,'Px'],D[0,'Py'];ux,uy=D[0,'Ux'],D[0,'Uy']
emit('initial_s',mul(add((P['s'],1),(e[0],-1)),px,py))
emit('initial_b',mul(add((P['b'],1),(e[0],-1)),add((e[0],1),(px,-1)),py))
emit('no_halt',P['H'])
lastx=mul(adj(ux),px,ux);lasty=mul(adj(uy),py,uy)
# Replace only the expanded tableau equations by bounded circuit gates.
gate_count=0
cache={}
def gate(p):
    global gate_count
    gate_count+=1
    out=add((atom('gate'+str(gate_count)+'p'),F(1,2)),(atom('gate'+str(gate_count)+'m'),F(1,2)))
    emit('gate_'+str(gate_count),add((out,1),(p,-1)))
    return out
def times(*args):
    result=args[0]
    for right in args[1:]:
        key=(tuple(sorted(result.items())),tuple(sorted(right.items())))
        if key not in cache:cache[key]=gate(mul(result,right))
        result=cache[key]
    return result
def plus_gate(items):
    items=list(items)
    if not items:return {}
    while len(items)>1:
        items=[gate(add((items[i],1),(items[i+1],1))) if i+1<len(items) else items[i] for i in range(0,len(items),2)]
    return items[0]
lastx=times(adj(ux),px,ux);lasty=times(adj(uy),py,uy)
notx=gate(add((e[0],1),(px,-1)));notlastx=gate(add((e[0],1),(lastx,-1)));notlasty=gate(add((e[0],1),(lasty,-1)))
L={'#':px,**{c:times(ux,P[c],adj(ux),notx) for c in GAMMA}}
N={c:times(adj(ux),P[c],ux,notlastx) for c in GAMMA}
N['b']=gate(add((N['b'],1),(lastx,1)))
ret=[gate(add((e[0],1),(P['ret'],-1))),P['ret']]
lookup=[];updates={c:[] for c in GAMMA}
# Share both halves of a local pattern before combining them.
left={(l,c):times(L[l],P[c]) for l in ['#']+GAMMA for c in GAMMA}
right={(r,p):times(N[r],ret[p]) for r in GAMMA for p in (0,1)}
for l,c,r,pulse in product(['#']+GAMMA,GAMMA,GAMMA,(0,1)):
    dest=phi(l,c,r,pulse);lookup.append([l,c,r,pulse,dest])
    updates[dest].append(times(left[l,c],right[r,pulse]))
write_automaton_metadata(lookup)
for c in GAMMA:
    emit('update_'+c,mul(add((times(adj(uy),P[c],uy),1),(plus_gate(updates[c]),-1)),notlasty))
f.close()
for i in range(1,len(atoms)+1):
    words.add((i,))
    if i not in refl:words.add((-i,))
# Word list is a compact common input to the independent structural compiler.
with gzip.open(OUT/'words.jsonl.gz','wt',encoding='utf-8',newline='\n') as f:
    for w in sorted(words,key=lambda w:(len(w),w)):f.write(json.dumps(w,separators=(',',':'))+'\n')
W=len(words);long=sum(len(w)>1 for w in words);inverse=len(atoms)-len(refl)
triangles=1+2*(W-1)+long+inverse
variables=3+12*W+triangles+19*len(params)+4
# Structural row histograms generated by applying exactly the same slot rule.
def push(terms,mult):hist[dim_terms({k:F(v) for k,v in terms.items()}).__getitem__(1)]+=mult
push({'F1':1,'F2':1,'F3':1,'I':-1},1)
push({'G':1,'KG':1,'F1':-1,'F2':-1},6*W)
push({'H':5,'F1':-2,'F2':1,'G':-4},3*W)
push({'D':3,'G1':-2,'G2':-2,'G3':-2,'I':1},triangles)
# 3 EF partitions, 2 parameter sums, and 4 joint rows per frame edge.
for terms,mult in [({'E':1,'N':1,'F':-1},3),({'E1':1,'E2':1,'E3':1,'p':-1},1),({'N1':1,'N2':1,'N3':1,'p':1,'I':-1},1),({'B11':1,'B10':1,'E1':-1,'E2':-1},3),({'B00':1,'B01':1,'N1':-1,'N2':-1},3),({'B11':1,'B01':1,'G':-1},3),({'G':1,'B11':-1,'B00':-1},3)]:push(terms,len(params)*mult)
push({'act':1,'prev':-1,'m0':-1,'m1':-1,'m2':-1,'m3':-1},4)
maxd=max(hist);n=maxd.bit_length()-1
cross=4*(n*(n-1)//2-n//2)
pair=sum(d-1 for d in hist)
columns=sum(d*count for d,count in hist.items())
old=variables+85
Q=old+15*(n//2)+cross+2*n*variables+2+pair+columns
answer_entries_old=1+2*variables+20*6+64*12
# Both parties have same arities. Pair contexts and global/row outcomes dominate.
answer_entries=answer_entries_old+42*(n//2)+4*cross+8*n*variables+2*maxd+sum(d*(d-1) for d in hist)+sum((7*d-6)*count for d,count in hist.items())
rows=sum(hist.values())
assert rows==1+9*W+triangles+17*len(params)+4+len(app)
res={'atoms':len(atoms),'reflection_parameters':len(params),'transported_labels':10,'words':W,'long_words':long,'inverse_triangles':inverse,'triangles':triangles,'projection_variables':variables,'projection_rows':rows,'application_rows':len(app),'old_questions':old,'questions_per_party':Q,'max_answers':maxd,'scalar_qubits':n,'row_dimensions':dict(sorted(hist.items())),'question_kinds':{'old':old,'scalar_cells_and_contexts':15*(n//2),'cross_axes':cross,'commute_old':2*n*variables,'globals':2,'scalar_pairs':pair,'columns_and_joints':columns},'answer_entries_per_party':answer_entries,'uint64_answer_payload_bytes_two_parties':16*answer_entries,'fits_question_limit':Q<=10**7,'full_game_compiled':False,'tableau_gate_count':gate_count,'app_details':app,'elapsed_seconds':time.perf_counter()-START,'peak_working_set_bytes':peak()}
(OUT/'counts_primary.json').write_text(json.dumps(res,indent=2),encoding='utf-8')
(OUT/'symbols.json').write_text(json.dumps({'atoms':atoms,'reflections':sorted(refl),'parameters':params,'labels':labels},indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in res.items() if k!='app_details'},indent=2),flush=True)

