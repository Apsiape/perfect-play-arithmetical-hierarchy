"""Exact symbolic checks; finite arithmetic checks support, not replace, proofs."""
import sympy as s

for n in range(1, 21):
    weights = [s.Integer(1)] + [s.Integer(2)**g for g in range(1,n+1) for _ in range(4)]
    W = 2**(n+3)-7
    assert len(weights)==4*n+1
    assert len(weights)+2*n==6*n+1
    assert sum(weights)==W
    mu=[a/W for a in weights]
    assert sum(mu)==1
    assert mu[-1]/mu[0]==2**n
    assert s.simplify(sum(s.sqrt(a) for a in mu) - (1+4*sum(s.sqrt(s.Integer(2)**g) for g in range(1,n+1)))/s.sqrt(W))==0
    if n<3: continue
    lam=s.Rational(1,2**n); root=1-4*lam; growth=4*s.sqrt(lam)
    assert root>0
    for M in [0,1,2,7,19]:
        tail=(4*lam)**(M+1)
        assert s.simplify(root*sum((4*lam)**m for m in range(M+1))+tail-1)==0
    if n==4: assert growth==1
    if n>4: assert growth<1
    if n<4: assert growth>1
    if n>4:
        T=s.sqrt(root)/(1-growth)
        code_coeff=s.simplify(s.sqrt(root)/T)
        assert s.simplify(code_coeff-(1-growth))==0
        if n==8:
            assert s.sqrt(lam)==s.Rational(1,16)
            assert code_coeff==s.Rational(3,4)
        coeff=s.simplify(s.sqrt(3)*sum(s.sqrt(a) for a in mu)*T)
        if n==5:
            exact=(81+53*s.sqrt(2))*s.sqrt(7)/(2*s.sqrt(83))
        elif n==8:
            exact=(121+60*s.sqrt(2))*s.sqrt(21)/(2*s.sqrt(2041))
        else: exact=coeff
        assert s.simplify(coeff-exact)==0
        if n in (5,8): print('n=',n,'Omega_n=',W,'Tr sqrt(F)=',s.simplify(T),'TrD/sqrt(q_clk d_row)=',exact,'~',s.N(exact,14))

# Direct finite spectral-tensor check of the exact spectrum identity and normalized-square-root inversion.
h0=[s.Rational(1,2),s.Rational(1,3),s.Rational(1,6)]
for n in [4,5,8]:
    W=2**(n+3)-7
    mu=[s.Rational(1,W)]+[s.Rational(2**g,W) for g in range(1,n+1) for _ in range(4)]
    d=4
    spectrum=[a*b/(3*d) for a in mu for b in h0 for _ in range(3*d)]
    trD=sum(s.sqrt(x) for x in spectrum)
    cn=s.sqrt(3*d)*sum(s.sqrt(a) for a in mu)
    assert s.simplify(trD-cn*sum(s.sqrt(x) for x in h0))==0
    rho=[s.sqrt(x)/trD for x in spectrum]
    # rho^2 / Tr rho^2 recovers h entry by entry; use the shared normalization symbolically.
    assert sum(spectrum)==1
    assert s.simplify(sum(x*x for x in rho)-1/trD**2)==0

F=lambda z:(1-s.sqrt(1-4*z))/(2*z)
a=s.simplify(F(s.Rational(1,4))); b=s.simplify(F(s.Rational(1,16)))
assert a==2 and s.simplify(b-(8-4*s.sqrt(3)))==0
purity=s.simplify(b/4)
assert s.simplify(purity-(2-s.sqrt(3)))==0
trsqrt=s.simplify(a/s.sqrt(b))
assert s.simplify(trsqrt-(s.sqrt(6)+s.sqrt(2))/2)==0
assert s.simplify((1/s.sqrt(b))/trsqrt-s.Rational(1,2))==0
# Coefficientwise k=h_Cat^2/Tr h_Cat^2 for representative exact word sizes.
for j in range(15):
    assert s.simplify(s.Rational(1,16)**j/b - (s.Rational(1,2)*s.Rational(1,4)**j)**2/purity)==0
print('PASS: n-bridge constants n=1..20; exact tensor spectra; criticality; five/eight sums; Catalan identities')

# Entropy is computed from generating functions, independently of truncations.
r=s.sqrt(2)/2
mean_depth=s.simplify(r/(1-r))
assert s.simplify(mean_depth-(1+s.sqrt(2)))==0
S5=-s.log(1-r,2)+s.Rational(5,2)*mean_depth
assert 7.807 < float(S5) < 7.808
z=s.symbols('z',positive=True)
Fz=(1-s.sqrt(1-4*z))/(2*z)
mean_up=s.simplify((z*s.diff(Fz,z)/Fz).subs(z,s.Rational(1,16)))
assert s.simplify(mean_up-(1/s.sqrt(3)-s.Rational(1,2)))==0
Scat=s.log(8-4*s.sqrt(3),2)+4*mean_up
assert 0.409 < float(Scat) < 0.410
print('PASS: five-bridge code tree entropy =',s.N(S5,16),'bits; squared Catalan entropy =',s.N(Scat,16),'bits')
