from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict,Counter
import json,math,itertools,hashlib
OUT=Path(__file__).resolve().parent
CA_SPECS={}

class P(dict):
    def __init__(self,x=0):
        if isinstance(x,dict): super().__init__({w:F(v) for w,v in x.items() if v})
        else: super().__init__({():F(x)} if x else {})
        self.ast=getattr(x,'ast',['expanded']) if isinstance(x,dict) else ['scalar',str(F(x))]
    def __add__(self,b):
        b=P(b); d=dict(self)
        for w,v in b.items():d[w]=d.get(w,F(0))+v
        z=P(d);z.ast=['add',self.ast,b.ast];return z
    __radd__=__add__
    def __neg__(self):
        z=P({w:-v for w,v in self.items()});z.ast=['neg',self.ast];return z
    def __sub__(self,b):return self+-P(b)
    def __rsub__(self,b):return P(b)+-self
    def __mul__(self,b):
        b=P(b); d=defaultdict(F)
        for w,v in self.items():
            for z,c in b.items():d[reduce(w+z)]+=v*c
        z=P(d);z.ast=['mul',self.ast,b.ast];return z
    __rmul__=__mul__
    def __truediv__(self,c):return self*F(1,c)
    def star(self):
        z=P({tuple(-t for t in w[::-1]):v for w,v in self.items()});z.ast=['star',self.ast];return z
    def power(self,n):
        z=P(1)
        for _ in range(n):z=z*self
        return z

def reduce(w):
    out=[]
    for a in w:
        if out and out[-1]==-a:out.pop()
        else:out.append(a)
    return tuple(out)

class Input:
    def __init__(self,name):
        self.name=name;self.names=[];self.ids={};self.params={};self.eqs=[];self.typed={};self.transport=[]
    def u(self,name):
        if name not in self.ids:self.ids[name]=len(self.names)+1;self.names.append(name)
        return P({(self.ids[name],):F(1)})
    def par(self,name):
        self.params[name]=self.u('s_'+name)
        z=(1+self.params[name])/2;z.ast=['corner',name];return z
    def eq(self,name,a,b=0,kind='structural'):
        self.eqs.append((name,P(a)-P(b),kind))
    def label(self,name,typ,scope,copy=True):
        us=[self.u(name+'_A'+s) for s in (('_plus','_minus') if typ=='contraction' else ('',))]
        vs=[self.u(name+'_E'+s) for s in (('_plus','_minus') if typ=='contraction' else ('',))] if copy else []
        for k,u in enumerate(us):
            self.eq(name+f'_supportA{k}',(u-1)*(1-scope))
            if copy:self.outer_transport(name+str(k),u,vs[k])
        if typ=='projection':self.eq(name+'_reflection',us[0]*us[0],1)
        def dec(U,c):
            if typ=='unitary':return c*U[0]
            if typ=='projection':return c*(1+U[0])/2
            if typ=='positive':return c*(2+U[0]+U[0].star())/4
            return c*(U[0]+U[1])/2
        a=dec(us,scope);a.ast=['label',name,'A']
        if copy:
            # The outer copies are supported in the image of scope by transport.
            if scope==self.A:c=self.E
            elif scope==self.f:c=self.fp
            else:raise ValueError('unsupported scope')
            b=dec(vs,c);b.ast=['label',name,'E']
        else:b=None
        self.typed[name]={'type':typ,'scope':'A' if scope==self.A else 'f','source':a,'target':b}
        return a,b
    def outer_transport(self,name,u,v):
        self.eq(name+'_supportE',(v-1)*(1-self.E))
        block=1-self.I+self.A*u
        for a,b in itertools.product(range(2),repeat=2):
            R=self.xo.power(a)*self.zo.power(b)
            block+=R*self.E*v*R.star()
        V=self.u('block_'+name)
        self.eq(name+'_outerblock',V,block)
        self.transport.append({'name':name,'unitaryA':next(iter(u))[0],'unitaryE':next(iter(v))[0],'block':next(iter(V))[0]})
    def scaffold(self):
        self.f=self.par('f'); inn=[self.par('m'+str(i)) for i in range(4)]
        self.e=inn[0]; self.A=self.par('activity'); self.I=P(1)
        outer=[self.par('E'+str(i)) for i in range(4)];self.E=outer[0]
        self.eq('inner_activity',self.A,self.f+sum(inn,P()))
        self.eq('outer_cover',self.A+sum(outer,P()),1)
        self.xi=self.u('xi');self.zi=self.u('zi');self.xo=self.u('xo');self.zo=self.u('zo')
        for name,u,M in [('xi',self.xi,sum(inn,P())),('zi',self.zi,sum(inn,P())),('xo',self.xo,sum(outer,P())),('zo',self.zo,sum(outer,P()))]:
            event=self.par('positive_'+name);self.eq('axis_'+name,u,1-2*M+2*event)
        # Source projections f and e must be carried by the same outer bridge.
        copies=[]
        for name,p in [('flag',self.f),('selected',self.e)]:
            u=1-2*self.A+2*p;v=self.u(name+'_E')
            # Here u is a polynomial reflection on A, not a formal token.
            self.eq(name+'_E_support',(v-1)*(1-self.E))
            V=self.u('block_'+name)
            block=self.A*u
            for a,b in itertools.product(range(2),repeat=2):
                R=self.xo.power(a)*self.zo.power(b);block+=R*self.E*v*R.star()
            self.eq(name+'_outerblock',V,block)
            self.transport.append({'name':name,'source_polynomial':encode(u),'unitaryE':next(iter(v))[0],'block':next(iter(V))[0]})
            copies.append(self.E*(1+v)/2)
        self.fp,self.ep=copies
        self.fp.ast=['corner','fp'];self.ep.ast=['corner','ep']
        tu,tv=self.u('t_plus'),self.u('t_minus');self.t=(tu+tv)/2;self.t.ast=['transport']
        self.eq('t_support',self.t,self.fp*self.t*self.e)
        self.eq('t_initial',self.t.star()*self.t,self.e)
        self.eq('t_final',self.t*self.t.star(),self.fp)
        self.mod={}
    def modular(self,name):
        a,ap=self.label('a_'+name,'contraction',self.A)
        a.ast=['modular',name,'A'];ap.ast=['modular',name,'E']
        self.eq(name+'_a_support',a,self.e*a*self.f)
        self.mod[name]=(a,ap)
    def root(self,name,typ):return self.label(name,typ,self.f)
    def app(self,name,a,b=0):self.eq(name,a,b,'application')
    def endpoint(self,name,L,i,j,R):
        self.app(name,L[1]*self.t*self.mod[i][0],self.t*self.mod[j][0]*R[0])
    def quad(self,name,i,j,k,l,adj=False):
        a,ap=self.mod[i];b,bp=self.mod[j];c,cp=self.mod[k];d,dp=self.mod[l]
        if adj:self.app(name,ap.star()*bp,self.t*c*d.star()*self.t.star())
        else:self.app(name,ap*self.t*b,cp*self.t*d)
    def source_inner(self,name,i,j,rhs):self.app(name,self.mod[i][0].star()*self.mod[j][0],rhs)
    def range(self,name,terms,rhs):
        self.app(name,sum((self.t*self.mod[i][0]*self.mod[j][0].star()*self.t.star()*c for i,j,c in terms),P()),rhs)

def encode(p):return [{'word':list(w),'coefficient':str(v)} for w,v in sorted(p.items())]
def comm(p,a,b,name):p.app(name,a*b,b*a)

def checker_register(p,prefix=''):
    S,T=prefix+'S',prefix+'T';p.modular(S);p.modular(T)
    px=p.root(prefix+'Px','projection');pt=p.root(prefix+'Pt','projection')
    cx=p.root(prefix+'Cx','positive');ct=p.root(prefix+'Ct','positive')
    p.source_inner(prefix+'S_isometry',S,S,p.f);p.source_inner(prefix+'T_isometry',T,T,p.f)
    p.quad(prefix+'ST',S,T,T,S);p.quad(prefix+'SstarT',S,T,T,S,True)
    p.range(prefix+'S_boundary',[(S,S,1)],p.fp-px[1]);p.range(prefix+'T_boundary',[(T,T,1)],p.fp-pt[1])
    comm(p,cx[0],ct[0],prefix+'counter_commutation')
    p.app(prefix+'Cx_boundary',cx[0]*px[0],px[0]);p.app(prefix+'Ct_boundary',ct[0]*pt[0],pt[0])
    p.endpoint(prefix+'CxS',cx,S,S,(cx[0]/2,cx[1]/2));p.endpoint(prefix+'CxT',cx,T,T,cx)
    p.endpoint(prefix+'CtS',ct,S,S,ct);p.endpoint(prefix+'CtT',ct,T,T,(ct[0]/2,ct[1]/2))
    return S,T,px,pt,cx,ct

def tableau(p,register,tracks):
    # A literal radius-one identity automaton. It checks the tableau compiler;
    # it is not a substitute for a supplied total verification program.
    S,T,px,pt,cx,ct=register
    spec=CA_SPECS.get(p.name)
    alphabet=list(range(spec['states'])) if spec else list(itertools.product((0,1),repeat=len(tracks)))
    if spec:
        n=len(alphabet)
        assert len(spec['interior'])==n**3 and len(spec['boundary'])==n**2
        assert all(0<=d<n for d in spec['interior']+spec['boundary'])
        assert len(spec['initial_map'])==2**(len(tracks)+1)
        assert all(0<=d<n for d in spec['initial_map'])
    Pm=[];Lm=[];Rm=[];Nm=[]
    for j,_ in enumerate(alphabet):
        Pm.append(p.root('P'+str(j),'projection'));Lm.append(p.root('L'+str(j),'projection'))
        Rm.append(p.root('R'+str(j),'projection'));Nm.append(p.root('N'+str(j),'projection'))
    for tag,fam in [('P',Pm),('L',Lm),('R',Rm),('N',Nm)]:
        p.app(tag+'_partition',sum((v[0] for v in fam),P()),p.f)
        for j,v in enumerate(fam):
            for c,cn in [(cx,'Cx'),(ct,'Ct')]+[( (p.typed[z]['source'],p.typed[z]['target']),z) for z in ['M','Depth','Guard'] if z in p.typed]:comm(p,v[0],c[0],tag+str(j)+'_'+cn)
    for j,bits in enumerate(alphabet):
        p.endpoint('left_'+str(j),Lm[j],S,S,Pm[j]);p.endpoint('right_'+str(j),Pm[j],S,S,Rm[j])
        p.endpoint('next_'+str(j),Pm[j],T,T,Nm[j])
        if spec:
            interior=sum((Lm[a][0]*Pm[b][0]*Rm[c][0] for a,b,c in itertools.product(alphabet,repeat=3) if spec['interior'][(a*n+b)*n+c]==j),P())
            boundary=sum((Pm[b][0]*Rm[c][0] for b,c in itertools.product(alphabet,repeat=2) if spec['boundary'][b*n+c]==j),P())
            p.app('update_'+str(j),Nm[j][0],(p.f-px[0])*interior+px[0]*boundary)
            init=P()
            for h,bitrow in enumerate(itertools.product((0,1),repeat=len(tracks)+1)):
                if spec['initial_map'][h]!=j:continue
                term=p.f
                for bit,track in zip(bitrow,tracks+[px]):term=term*(track[0] if bit else p.f-track[0])
                init+=term
        else:
            p.app('update_'+str(j),Nm[j][0],Pm[j][0])
            init=p.f
            for bit,track in zip(bits,tracks):init=init*(track[0] if bit else p.f-track[0])
        p.app('initial_'+str(j),pt[0]*Pm[j][0],pt[0]*init)
    if spec:
        for j in spec.get('reject',[]):p.app('reject_'+str(j),Pm[j][0])
        return {'states':n,'specification':spec,'purpose':'supplied verification automaton; no claim that its computation never rejects'}
    return {'alphabet':[list(x) for x in alphabet],'transition':'identity','purpose':'concrete structural validation instance; no rejecting state','states':len(alphabet)}

def program_tableau(p,register,program,tracks):
    S,T,px,pt,cx,ct=register
    uniform=program.startswith('uniform-')
    states=['none','boot','scan1','scan2','scanbig','move1','move2','movebig','accept','reject','wait'] if uniform else ['none','boot','scan','move','accept','reject']
    fam={}
    for tag in ['P','L','R','N']:
        fam[tag]=[p.root(tag+str(j),'projection') for j in range(len(states))]
        p.app(tag+'_partition',sum((z[0] for z in fam[tag]),P()),p.f)
        for j,z in enumerate(fam[tag]):
            for cn,c in [('Cx',cx),('Ct',ct)]+[(name,(p.typed[name]['source'],p.typed[name]['target'])) for name in ['M','Depth','Guard'] if name in p.typed]:
                comm(p,z[0],c[0],tag+str(j)+'_'+cn)
    for j in range(len(states)):
        p.endpoint('left_'+str(j),fam['L'][j],S,S,fam['P'][j])
        p.endpoint('right_'+str(j),fam['P'][j],S,S,fam['R'][j])
        p.endpoint('next_'+str(j),fam['P'][j],T,T,fam['N'][j])
        init=px[0] if states[j]=='boot' else p.f-px[0] if states[j]=='none' else P()
        p.app('initial_'+str(j),pt[0]*fam['P'][j][0],pt[0]*init)
    pp={name:fam['P'][j][0] for j,name in enumerate(states)}
    ll={name:fam['L'][j][0] for j,name in enumerate(states)}
    out={name:P() for name in states}
    if uniform:
        E=tracks[0][0]
        out['move1']=pp['boot']
        out['move2']=(p.f-E)*pp['scan1']
        out['movebig']=(p.f-E)*(pp['scan2']+pp['scanbig'])
        for a in ['1','2','big']:out['scan'+a]=(p.f-px[0])*ll['move'+a]*pp['none']
        out['accept']=pp['accept']+(E*pp['scan2'] if program=='uniform-yes' else P())
        out['wait']=E*pp['scan2'] if program=='uniform-lookup' else P()
        out['reject']=pp['reject']+E*(pp['scan1']+pp['scanbig']+(pp['scan2'] if program=='uniform-no' else P()))+pp['wait']
    else:
        EM,EL,D=[z[0] for z in tracks]
        out['scan']=pp['boot']+(p.f-px[0])*ll['move']*pp['none']
        if program=='comb-constant':
            correct=D*EL+(p.f-D)*(p.f-EL)
            out['accept']=pp['accept']+correct*pp['scan']
            out['reject']=pp['reject']+(p.f-correct)*pp['scan']
        else:
            trigger=EM+EL-EM*EL;truth=EL*(p.f-EM)
            correct=D*truth+(p.f-D)*(trigger-truth)
            out['move']=(p.f-EM)*(p.f-EL)*pp['scan']
            out['accept']=pp['accept']+correct*pp['scan']
            out['reject']=pp['reject']+(trigger-correct)*pp['scan']
    out['none']=p.f-sum((z for n,z in out.items() if n!='none'),P())
    for j,name in enumerate(states):p.app('update_'+str(j),fam['N'][j][0],out[name])
    p.app('reject_'+str(states.index('reject')),pp['reject'])
    return {'program':program,'states':states,'transition':'factored deterministic one-sided head scan','initial':'boot at x=0; none elsewhere','both_branches':'correct and incorrect decision outcomes; marker and nonmarker motion'}

def uniform(program=None):
    p=Input('quarter-plane');p.scaffold();r=checker_register(p);S,T,px,pt,cx,ct=r
    Z=p.root('Z','unitary');J=p.root('J','unitary');K=p.root('K','unitary');W=p.root('W','unitary')
    E=p.root('Return','projection');D=p.root('Reader','contraction')
    p.app('Weyl',J[0]*K[0],Z[0]*K[0]*J[0]);comm(p,Z[0],J[0],'ZJ');comm(p,Z[0],K[0],'ZK')
    for tag,L in [('Z',Z),('J',J),('K',K)]:
        p.endpoint(tag+'_S',L,S,S,L);p.endpoint(tag+'_T',L,T,T,L)
    p.endpoint('WS',W,S,S,(Z[0]*W[0],Z[1]*W[1]));p.endpoint('WT',W,T,T,W)
    p.app('W_boundary',W[0]*px[0],px[0]);p.app('return_support',(W[0]-p.f)*E[0])
    p.app('reader',D[0]*(W[0]-p.f),cx[0]*(p.f-E[0])/2)
    for tag,L in [('Z',Z),('J',J),('K',K),('W',W),('Return',E),('Reader',D)]:
        for cn,c in [('Cx',cx),('Ct',ct)]:comm(p,L[0],c[0],tag+'_'+cn)
    auto=program_tableau(p,r,program,[E]) if program else tableau(p,r,[E])
    return p,{'automaton':auto,'instance_id':program or 'quarter-plane','canonical_period':2,'predicate':{'uniform-no':'R(n,s)=false','uniform-yes':'R(n,s)=(n==0)','uniform-lookup':'R(n,s)=(n==0 and s==0)'}.get(program,'identity validation')}

def comb(program=None):
    p=Input('comb');p.scaffold();r=checker_register(p,'check_');S,T,px,pt,cx,ct=r
    for name in ['A','B0','B1']:p.modular(name)
    Q=p.root('Q','projection');P0=p.root('Root','projection');D=p.root('Guard','projection')
    M=p.root('M','positive');L=p.root('Depth','positive')
    p.app('Root_under_Q',P0[0]*Q[0],P0[0])
    p.source_inner('A_initial','A','A',Q[0]);p.range('A_final',[('A','A',1)],Q[1]-P0[1])
    for i,j in itertools.product(range(2),repeat=2):p.source_inner('B_inner_'+str(i)+str(j),'B'+str(i),'B'+str(j),D[0] if i==j else 0)
    p.range('B_cover',[('B0','B0',1),('B1','B1',1)],p.fp-Q[1])
    p.app('M_root',M[0]*P0[0],P0[0]/2);p.endpoint('MA',M,'A','A',(M[0]/2,M[1]/2))
    p.app('L_spine',L[0]*Q[0],Q[0])
    for i in range(2):
        p.endpoint('MB'+str(i),M,'B'+str(i),'B'+str(i),M)
        p.endpoint('LB'+str(i),L,'B'+str(i),'B'+str(i),(L[0]/2,L[1]/2))
    comm(p,M[0],L[0],'ML')
    for n,v in [('Q',Q),('Root',P0),('Guard',D)]:
        for cn,c in [('M',M),('L',L)]:comm(p,v[0],c[0],n+'_'+cn)
    # Complete tensor independence: both ordinary and double commutation.
    for j in ['A','B0','B1']:
        for c in [S,T]:p.quad('independent_'+j+c,j,c,c,j);p.quad('double_'+j+c,j,c,c,j,True)
    for n,v in [('Q',Q),('Root',P0),('Guard',D),('M',M),('L',L)]:
        for c in [S,T]:p.endpoint(n+'_'+c,v,c,c,v)
    em=p.root('EqualM','projection');el=p.root('EqualL','projection')
    fm=p.root('InverseM','contraction');fl=p.root('InverseL','contraction')
    for tag,c,e,iv in [('M',M,em,fm),('L',L,el,fl)]:
        p.app(tag+'_equality',(c[0]-cx[0])*e[0]);p.app(tag+'_separation',iv[0]*(c[0]-cx[0]),c[0]*cx[0]*(p.f-e[0])/2)
    auto=program_tableau(p,r,program,[em,el,D]) if program else tableau(p,r,[em,el,D])
    return p,{'automaton':auto,'instance_id':program or 'comb','canonical_bush_depth':'1' if program=='comb-constant' else 'm' if program=='comb-linear' else '0','critical_index':'1/2' if program=='comb-linear' else '0'}

def compile_presentation(spec):
    """General common-half-ratio degree-two compiler.
    spec: labels {name:type}, modular [names], relations [{name,terms:
    [{coefficient:rational-string,word:[tokens]}]}]. A token ends in *
    for an adjoint. Labels and modular names are disjoint.
    """
    original_spec=spec;renaming={}
    raw_labels=spec.get('labels',{});raw_modular=spec.get('modular',[])
    assert all(name and not name.endswith('*') for name in list(raw_labels)+list(raw_modular))
    unsafe=set(raw_labels)&({'flag','selected'}|{'a_'+name for name in raw_modular})
    if unsafe or any(name.startswith('derived_') for name in raw_labels):
        renaming={name:'input_label_'+str(i) for i,name in enumerate(raw_labels)}
        renaming.update({name:'input_mod_'+str(i) for i,name in enumerate(raw_modular)})
        spec=json.loads(json.dumps(spec))
        spec['labels']={renaming[name]:typ for name,typ in raw_labels.items()}
        spec['modular']=[renaming[name] for name in raw_modular]
        for relation in spec.get('relations',[]):
            for term in relation['terms']:
                term['word']=[renaming[z[:-1]]+'*' if z.endswith('*') else renaming[z] for z in term['word']]
    assert spec.get('ratio','1/2')=='1/2'
    p=Input(spec.get('name','parametric-instance'));p.scaffold()
    labels=spec.get('labels',{});modular=spec.get('modular',[])
    assert not(set(labels)&set(modular))
    for name,typ in labels.items():p.root(name,typ)
    for name in modular:p.modular(name)
    derived=0;aux_definitions={}
    def token(z):return (z[:-1],True) if z.endswith('*') else (z,False)
    def coeffword(tokens,target=False):
        out=p.fp if target else p.f
        for z in tokens:
            name,adj=token(z);assert name in labels
            v=p.typed[name]['target' if target else 'source'];out=out*(v.star() if adj else v)
        return out
    def aux(expr):
        nonlocal derived
        name='derived_'+str(derived);derived+=1
        a,b=p.label(name,'contraction',p.A);p.eq(name+'_definition',a,expr);aux_definitions[name]=expr.ast
        return b
    for rid,rel in enumerate(spec.get('relations',[])):
        groups=defaultdict(list)
        for term in rel['terms']:
            tokens=list(term['word']);mods=[token(z) for z in tokens if token(z)[0] in modular]
            assert len(mods)<=2
            degree=sum(-1 if adj else 1 for _,adj in mods)
            if degree<0:tokens=[z[:-1] if z.endswith('*') else z+'*' for z in tokens[::-1]]
            groups[degree].append((F(term['coefficient']),tokens))
        for original_degree,terms in groups.items():
            total=P()
            for c,tokens in terms:
                positions=[i for i,z in enumerate(tokens) if token(z)[0] in modular]
                if not positions:lift=coeffword(tokens,True)
                elif len(positions)==1:
                    k=positions[0];name,adj=token(tokens[k]);assert not adj
                    lift=coeffword(tokens[:k],True)*p.t*p.mod[name][0]*coeffword(tokens[k+1:])
                else:
                    j,k=positions;ni,ai=token(tokens[j]);nj,aj=token(tokens[k])
                    B,C,D=tokens[:j],tokens[j+1:k],tokens[k+1:]
                    a,ap=p.mod[ni];b,bp=p.mod[nj]
                    if not ai and not aj:
                        HB=aux(p.t.star()*coeffword(B,True)*p.t)
                        lift=HB*ap*coeffword(C,True)*p.t*b*coeffword(D)
                    elif not ai and aj:
                        lift=coeffword(B,True)*p.t*a*coeffword(C)*b.star()*p.t.star()*coeffword(D,True)
                    elif ai and not aj:
                        lift=aux(coeffword(B)*a.star()*p.t.star()*coeffword(C,True)*p.t*b*coeffword(D))
                    else:raise AssertionError('negative degree was not adjointed')
                total+=c*lift
            p.app(rel.get('name','relation_'+str(rid))+'_degree_'+str(original_degree),total)
    return p,{'presentation':spec,'original_presentation':original_spec,'symbol_renaming':renaming,'derived_definitions':derived,'derived_coefficients':aux_definitions,'scope':'parametric degree-two input, common ratio 1/2; no model claim'}

class Rows:
    def __init__(self,p):
        self.p=p;self.rows=[];self.proj={'F1','F2','F3'}
        words={()}
        for _,poly,_ in p.eqs:
            for w in poly:
                for n in range(len(w)+1):words.add(w[:n])
        for j in range(1,len(p.names)+1):words.add((j,));words.add((-j,))
        self.words=sorted(words,key=lambda w:(len(w),w));self.wid={w:i for i,w in enumerate(self.words)}
        self.add('frame',{'F1':1,'F2':1,'F3':1,'I':-1},'frame')
        for w in self.words:
            k=self.wid[w]
            for ij in ['12','13','23']:
                i,j=ij;g=f'G{ij}_{k}';h=f'H{ij}_{k}';kg=f'KG{ij}_{k}';kh=f'KH{ij}_{k}'
                self.add('graphG_'+ij+'_'+str(k),{g:1,kg:1,'F'+i:-1,'F'+j:-1},'graph')
                self.add('graphH_'+ij+'_'+str(k),{h:1,kh:1,'F'+i:-1,'F'+j:-1},'graph')
                self.add('graphTilt_'+ij+'_'+str(k),{h:5,'F'+i:-2,'F'+j:1,g:-4},'graph')
        self.triangle((),(),(),'reference')
        for w in self.words:
            if not w:continue
            self.triangle(w,(),w,'placement_left');self.triangle((),w,w,'placement_right')
            if len(w)>1:self.triangle(w[:-1],w[-1:],w,'product')
        for j in range(1,len(p.names)+1):self.triangle((j,),(-j,),(),'inverse')
        for name,s in p.params.items():self.bind(name,next(iter(s)))
        for name,poly,kind in p.eqs:
            terms=defaultdict(F)
            for w,c in poly.items():terms['G12_'+str(self.wid[w])]+=2*c
            total=sum(poly.values(),F());terms['F1']-=total;terms['F2']-=total
            self.add('polynomial_'+name,terms,kind,polynomial=name)
    def add(self,name,terms,kind,**meta):
        terms={k:str(F(v)) for k,v in sorted(terms.items()) if v}
        self.proj.update(set(terms)-{'I'});self.rows.append(dict(name=name,terms=terms,kind=kind,**meta))
    def triangle(self,u,v,w,kind):
        self.add('triangle_'+str(len(self.rows)),{'D'+str(len(self.rows)):3,'G12_'+str(self.wid[u]):-2,'G23_'+str(self.wid[v]):-2,'G13_'+str(self.wid[w]):-2,'I':1},kind,words=[list(u),list(v),list(w)])
    def bind(self,name,w):
        for i in '123':self.add(name+'_split'+i,{name+'_p'+i:1,name+'_n'+i:1,'F'+i:-1},'binding')
        self.add(name+'_psum',{name+'_p'+i:1 for i in '123'}|{name:-1},'binding')
        self.add(name+'_nsum',{name+'_n'+i:1 for i in '123'}|{'I':-1,name:1},'binding')
        for ij in ['12','13','23']:
            i,j=ij;b={ab:name+'_'+ij+'_'+ab for ab in ['11','10','01','00']}
            self.add(name+'_joint1_'+ij,{b['11']:1,b['10']:1,name+'_p'+i:-1,name+'_p'+j:-1},'binding')
            self.add(name+'_joint0_'+ij,{b['00']:1,b['01']:1,name+'_n'+i:-1,name+'_n'+j:-1},'binding')
            self.add(name+'_jointG_'+ij,{b['11']:1,b['01']:1,'G'+ij+'_0':-1},'binding')
            self.add(name+'_reflection_'+ij,{'G'+ij+'_'+str(self.wid[w]):1,b['11']:-1,b['00']:-1},'binding')
    def export(self,meta):
        plans=[]
        for row in self.rows:
            al={k:F(v) for k,v in row['terms'].items()};den=math.lcm(*(v.denominator for v in al.values())) if al else 1
            c0=2*den*al.get('I',0)+sum(den*v for k,v in al.items() if k!='I')
            n=2+abs(int(c0))+sum(abs(int(den*v)) for k,v in al.items() if k!='I');d=4
            while d<n:d*=4
            assert n%2==0
            plans.append({'row':row['name'],'denominator':den,'dimension':d,'slot_count_before_padding':n})
        return {'format':'nested-rational-core-v2','name':self.p.name,'metadata':meta,'generators':self.p.names,'typed_labels':{n:z['type'] for n,z in self.p.typed.items()},'typed_scopes':{n:z['scope'] for n,z in self.p.typed.items()},'parameters':list(self.p.params),'words':[list(w) for w in self.words],'polynomials':[{'name':n,'terms':encode(poly),'kind':k,**({'semantic_ast':poly.ast} if k=='application' else {})} for n,poly,k in self.p.eqs],'projections':sorted(self.proj),'rows':self.rows,'transport_refinements':self.p.transport,'row_plans':plans,'counts':{'unitary_generators':len(self.p.names),'words':len(self.words),'polynomials':len(self.p.eqs),'projections':len(self.proj),'rational_rows':len(self.rows),'row_kinds':dict(Counter(r['kind'] for r in self.rows)),'row_dimensions':dict(Counter(x['dimension'] for x in plans))}}

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--uniform-ca',type=Path);parser.add_argument('--comb-ca',type=Path)
    parser.add_argument('--presentation',type=Path);parser.add_argument('--output-stem',default='presentation');parser.add_argument('--schemas-only',action='store_true')
    args=parser.parse_args()
    for key,path in [('quarter-plane',args.uniform_ca),('comb',args.comb_ca)]:
        if path:CA_SPECS[key]=json.loads(path.read_text(encoding='utf-8-sig'))
    if args.presentation:
        assert __import__('re').fullmatch(r'[A-Za-z0-9_-]+',args.output_stem)
        p,meta=compile_presentation(json.loads(args.presentation.read_text(encoding='utf-8-sig')))
        core=Rows(p).export(meta);(OUT/(args.output_stem+'-core.json')).write_text(json.dumps(core,separators=(',',':')),encoding='utf-8')
        import psutil
        peak=__import__('runpy').run_path(str(Path(__file__).resolve().parent/'memory.py'))['peak_bytes']();assert peak<1500000000
        (OUT/(args.output_stem+'-generation.json')).write_text(json.dumps({'counts':core['counts'],'peak_working_set_bytes':peak,'derived_definitions':meta['derived_definitions']},indent=2),encoding='utf-8')
        print(json.dumps(core['counts']|{'peak_working_set_bytes':peak},indent=2));raise SystemExit(0)
    if args.uniform_ca or args.comb_ca:
        for family,fun,arg in [('custom-uniform',uniform,args.uniform_ca),('custom-comb',comb,args.comb_ca)]:
            if not arg:continue
            p,meta=fun();core=Rows(p).export(meta)
            (OUT/(family+'-core.json')).write_text(json.dumps(core,separators=(',',':')),encoding='utf-8')
            print(family,core['counts'])
        raise SystemExit(0)
    counts={}
    schemas={'format':'nested-compiler-schemas-v1','parameters':{'s':'number of modular generators','c':'number of unitary encodings of transported root labels and derived coefficients','r':'number of transported projection labels','d':'number of derived coefficient definitions','p_app':'number of translated application equations','a':'number of frame-bound parameter projections, 14 here','w':'cardinality of the reduced-word prefix closure, including identity and all signed generator tokens'},'formulas':{'g':'24+6*s+3*c','p_structural':'13+7*s+3*c+r+d','p':'p_structural+p_app','rational_rows':'12*w-g+p+17*a-1','projection_variables':'15*w+1-g+19*a','word_count':'1+2*g+sum_{k>=2} number_of_distinct_reduced_prefixes_of_length_k','outer_transported_encodings':'2+c+2*s','inner_refinements_per_party':'6','outer_refinements_per_party':'8+c+2*s'},'word_schema':['expand each typed polynomial in the formal unitary encodings','cancel adjacent inverse tokens','include every proper prefix, identity, and signed singleton token'],'row_schemas':{'frame':'F1+F2+F3=I','graph_complement':'G_ij(w)+KG_ij(w)=Fi+Fj','tilted_complement':'H_ij(w)+KH_ij(w)=Fi+Fj','graph_tilt':'5H_ij(w)+Fi+Fj=3Fi+4G_ij(w)','triangle':'3D(u,v,w)=2(G12(u)+G23(v)+G13(w))-I, w=uv','placement':'(w,1,w) and (1,w,w)','prefix_product':'(prefix,last_token,word)','inverse':'(u,u_inverse,1)','parameter_binding':'17 rows per parameter; see Rows.bind and equations in note','polynomial':'2 sum q_w G12(w) - (sum q_w)(F1+F2)=0','outer_block':'B_k=A U_k+sum R_ab E V_k R_ab*','source_support':'(U-I)(I-scope)=0','lift_support':'a_i=e a_i f','corner_unitary':['t=f_prime t e','t* t=e','t t*=f_prime']},'scope':'Templates are emitted once. Full verifier families are parametric; concrete lists below are validation instances.'}
    (OUT/'compiler-schemas.json').write_text(json.dumps(schemas,indent=2),encoding='utf-8')
    if args.schemas_only:print('Emitted parametric schemas');raise SystemExit(0)
    for instance,fun in [('uniform-no',uniform),('uniform-yes',uniform),('uniform-lookup',uniform),('comb-constant',comb),('comb-linear',comb)]:
        p,meta=fun(instance);core=Rows(p).export(meta);file=OUT/(instance+'-core.json')
        file.write_text(json.dumps(core,separators=(',',':')),encoding='utf-8')
        c=sum(2 if z['type']=='contraction' else 1 for n,z in p.typed.items() if not n.startswith('a_'))
        r=sum(z['type']=='projection' for n,z in p.typed.items() if not n.startswith('a_'));sm=len(p.mod)
        assert len(p.names)==24+6*sm+3*c
        assert sum(k=='structural' for _,_,k in p.eqs)==13+7*sm+3*c+r
        w=len(core['words']);g=len(p.names);np=len(p.eqs);a=len(p.params)
        assert len(core['rows'])==12*w-g+np+17*a-1
        assert len(core['projections'])==15*w+1-g+19*a
        counts[instance]=core['counts']|{'size_parameters':{'s':sm,'c':c,'r':r,'a':a,'p_app':sum(k=='application' for _,_,k in p.eqs)},'sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'bytes':file.stat().st_size}
        print(instance,core['counts'],flush=True)
        del core
    (OUT/'compiler-counts.json').write_text(json.dumps(counts,indent=2),encoding='utf-8')

    if __name__=='__main__':
        import psutil
        peak=__import__('runpy').run_path(str(Path(__file__).resolve().parent/'memory.py'))['peak_bytes']();assert peak<1500000000
        (OUT/'generation-memory.json').write_text(json.dumps({'peak_working_set_bytes':peak}),encoding='utf-8')
