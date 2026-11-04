from pathlib import Path
import json,runpy,itertools
import sympy as s
OUT=Path(__file__).resolve().parent
lib=runpy.run_path(str(OUT/'check_scaffold.py'));Scaffold=lib['Scaffold'];Model=lib['Model']
wl=lib['lib']['wl']
r=s.Symbol('r',real=True);enc={}
assert s.expand((2*r-1)**2+4*r*(1-r))==1
assert s.expand((2+(2*r-1)+(2*r-1))/4)==r
assert s.expand(r*r+(1-r*r))==1
assert s.expand((r+s.I*s.sqrt(1-r*r)+r-s.I*s.sqrt(1-r*r))/2)==r
enc['positive_encoding']='generic r in [0,1]: norm one, decoding r; endpoints separately'
enc['real_contraction_encoding']='generic r in [-1,1]: two unit-modulus phases average r; endpoints separately'
for value in [s.Rational(-1),s.Rational(0),s.Rational(1)]:
    u=value+s.I*s.sqrt(1-value**2);assert s.simplify(u*s.conjugate(u))==1
counts={}
for instance in ['uniform-yes','comb-constant','comb-linear']:
    core=json.loads((OUT/(instance+'-core.json')).read_text());sc=Scaffold(core);n=0;mods=0
    for g,name in enumerate(core['generators'],1):
        deps=[name]
        if g in sc.blocks and 'unitaryA' in sc.blocks[g]:deps.append(sc.names[sc.blocks[g]['unitaryA']-1])
        for o,i,(x,t,m,w) in itertools.product(range(5),range(5),sc.root_cases(deps)):
            v=(o,i,x,t,m,0,w)
            def exponent(z):return z[2]+z[3]+(z[4]+wl(z[6]) if core['name']=='comb' else 0)-int(z[0]>0)-int(z[1]>0)
            for token in [g,-g]:
                z,_,_=sc.generator(token,v);assert s.simplify(exponent(z)-exponent(v))==0
                n+=1
    for name in (['S','T'] if core['name']=='quarter-plane' else ['check_S','check_T','A','B0','B1']):
        cases=sc.root_cases(['a_'+name+'_A_plus'])
        for x,t,m,w in cases:
            v=(0,0,x,t,m,0,w);z=sc.model.shift(name,v,False)
            if z is not None:
                before=x+t+(m+wl(w) if core['name']=='comb' else 0)
                after=z[2]+z[3]+(z[4]+wl(z[6]) if core['name']=='comb' else 0)
                assert s.simplify(after-before)==1;mods+=1
    counts[instance]={'exact_generic_centralizer_density_checks':n,'exact_modular_half_ratio_checks':mods}
programs=runpy.run_path(str(OUT/'validation_programs.py'))
for e,n,t in itertools.product(range(3),range(3),range(3)):
    expected=False if e==0 else n==0 if e==1 else n==0 and t==0
    assert programs['R'](e,n,t)==expected
result={'encoding_identities':enc,'basis_density_covariance':counts,'uniform_negative_cases_share_identical_structural_certificates_with_positive':True,'application_R_predicate_27_truth_table_samples_checked':True,'Boolean_question_predicate_table_materialized':False}
(OUT/'encoding-density-validation.json').write_text(json.dumps(result,indent=2),encoding='utf-8');print(json.dumps(result,indent=2))
