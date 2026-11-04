"""Independent structural census: SQLite prefix set; integer coefficient vectors.
Does not import the producer or read its word list or counts to obtain its result.
"""
from pathlib import Path
import sqlite3, json, gzip, struct, math, time, ctypes, sys
from fractions import Fraction
from collections import Counter
sys.dont_write_bytecode=True
O=Path(__file__).resolve().parent;start=time.perf_counter()
_memory=__import__('runpy').run_path(str(Path(__file__).resolve().parent.parent/'memory.py'))
_memory['install_cap']()
sym=json.loads((O/'symbols.json').read_text());ref=set(sym['reflections'])
db=sqlite3.connect(O/'independent_prefixes_verified.sqlite');db.execute('PRAGMA cache_size=-65536');db.execute('CREATE TABLE IF NOT EXISTS words (w BLOB PRIMARY KEY,n INTEGER) WITHOUT ROWID')
def ins(w):
    if '--reuse-prefixes' in sys.argv:return
    db.execute('INSERT OR IGNORE INTO words VALUES (?,?)',(struct.pack('<'+'h'*len(w),*w),len(w)))
ins(())
for t in range(1,len(sym['atoms'])+1):
    ins((t,))
    if t not in ref:ins((-t,))
def shape(coeff):
    # coeff[0] is scalar identity, all following entries name projections.
    den=1
    for c in coeff:den=den*c.denominator//math.gcd(den,c.denominator)
    ints=[c.numerator*(den//c.denominator) for c in coeff]
    signed=[2*ints[0]+sum(ints[1:])]+ints[1:]
    need=sum(abs(c) for c in signed)+2
    size=1
    while size<need:size<<=2
    return den,size
hist=Counter();apps=[]
with gzip.open(O/'application_polynomials.jsonl.gz','rt',encoding='utf-8') as f:
    for line in f:
        row=json.loads(line);coeff=[];s=Fraction(0)
        for word,value in row['terms']:
            for x,y in zip(word,word[1:]):assert y!=(x if abs(x) in ref else -x)
            for end in range(1,len(word)+1):ins(word[:end])
            v=Fraction(value);s+=v;coeff.append(2*v)
        L,d=shape([Fraction(0),*coeff,-s,-s]);hist[d]+=1
        apps.append({'name':row['name'],'L':L,'d':d,'monomials':len(coeff)})
        db.commit()
W=db.execute('SELECT COUNT(*) FROM words').fetchone()[0]
long=db.execute('SELECT COUNT(*) FROM words WHERE n>1').fetchone()[0]
# Enumerate the structural row families independently as integer vectors.
def rows(vector,repetitions):
    _,d=shape([Fraction(x) for x in vector]);hist[d]+=repetitions
rows([-1,1,1,1],1)
rows([0,1,1,-1,-1],W*6)
rows([0,5,-2,1,-4],W*3)
T=1+(W-1)*2+long+len(sym['atoms'])-len(ref)
rows([1,3,-2,-2,-2],T)
for vector,reps in [([0,1,1,-1],3),([0,1,1,1,-1],1),([-1,1,1,1,1],1),([0,1,1,-1,-1],6),([0,1,1,-1],6)]:rows(vector,25*reps)
rows([0,1,-1,-1,-1,-1,-1],4)
V=3+W*3*4+T+25*(1+3*2+3*4)+4
D=max(hist);r=(D.bit_length()-1)//2;n=2*r
categories={'old':V+1+4*(5+16),'scalar_cells_and_contexts':r*(9+6),'cross_axes':(r*(r-1)//2)*16,'commute_old':V*n*2,'globals':2,'scalar_pairs':sum(d-1 for d in hist),'columns_and_joints':sum(count*(1+d-1) for d,count in hist.items())}
Q=sum(categories.values())
answer_entries=2*V+1+4*5*6+4*16*12+r*(9*2+6*4)+4*categories['cross_axes']+4*categories['commute_old']+2*D+sum((d-1)*d for d in hist)+sum(c*(d+6*(d-1)) for d,c in hist.items())
# Validate the chosen automaton by a separate state-machine simulator.
ca=json.loads((O/'automaton.json').read_text());lookup={tuple(x[:4]):x[4] for x in ca['transition_table']}
assert len(lookup)==2*(len(ca['alphabet'])+1)*len(ca['alphabet'])**2
for pulse in (0,1):assert lookup['b','b','b',pulse]=='b'
sims=[]
for q in range(1,9):
    cells=['s']+['b']*63;first_mark=None;halt=None
    for y in range(24):
        cells=[lookup[cells[x-1] if x else '#',cells[x],cells[x+1] if x<63 else 'b',int(y%q==0)] for x in range(64)]
        assert all(c=='b' for c in cells[y+2:])
        if first_mark is None and 'z0' in cells:first_mark=[cells.index('z0'),y+1]
        if 'H' in cells and halt is None:halt=y+1
    assert first_mark==[q,q+1]
    assert (halt is None)==(q==2)
    sims.append({'q':q,'mark':first_mark,'halt_time':halt})
res={'words':W,'long_words':long,'triangles':T,'projection_variables':V,'projection_rows':sum(hist.values()),'application_rows':len(apps),'old_questions':categories['old'],'questions_per_party':Q,'max_answers':D,'scalar_qubits':n,'row_dimensions':dict(sorted(hist.items())),'question_kinds':categories,'answer_entries_per_party':answer_entries,'uint64_answer_payload_bytes_two_parties':16*answer_entries,'automaton_simulations':sims,'elapsed_seconds':time.perf_counter()-start,'peak_working_set_bytes':_memory['peak']()}
res=json.loads(json.dumps(res))
primary=json.loads((O/'counts_primary.json').read_text())
for k in res:
    if k in primary and k not in ('elapsed_seconds','peak_working_set_bytes'):assert res[k]==primary[k],(k,res[k],primary[k])
for a,b in zip(apps,primary['app_details']):
    for k in a:assert a[k]==b[k],(a,b)
res['all_shared_counts_match']=True
(O/'counts_independent.json').write_text(json.dumps(res,indent=2),encoding='utf-8')
print(json.dumps(res,indent=2));db.close()

