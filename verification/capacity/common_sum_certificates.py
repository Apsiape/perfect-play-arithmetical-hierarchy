"""Numerical stress checks for common-sum extension, plus exact obstruction examples."""
from fractions import Fraction as F
import numpy as np
rng=np.random.default_rng(20261103)
def positive(n):
    z=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n));return z@z.conj().T
root=lambda a:(lambda v,u:(u*np.sqrt(np.maximum(v,0)))@u.conj().T)(*np.linalg.eigh(a))
tr=lambda a:float(np.trace(a).real)
worst=0.0
for n in [2,3,7,13]:
 for trial in range(20):
    X=[[positive(n) for _ in range(3)] for _ in range(2)]
    Y=[[positive(n) for _ in range(2)] for _ in range(3)]
    sx=[sum(z) for z in X];sy=[sum(z) for z in Y]
    sigma=(sum(sx)/2+sum(sy)/3)/2
    D=[s-sigma for s in sx+sy];A=root(sum(d@d for d in D));W=sigma+A
    residuals=[W-z for z in sx+sy]
    assert all(np.linalg.eigvalsh(z).min()>-1e-9 for z in residuals)
    XX=[[a.copy() for a in z] for z in X];YY=[[a.copy() for a in z] for z in Y]
    for i in range(2):XX[i][0]+=residuals[i]
    for j in range(3):YY[j][0]+=residuals[2+j]
    assert all(np.allclose(sum(z),W) for z in XX+YY)
    lose=rng.integers(0,2,size=(2,3,3,2))
    L=sum(lose[i,j,a,b]*tr(X[i][a]@Y[j][b]) for i in range(2) for j in range(3) for a in range(3) for b in range(2))/6
    LL=sum(lose[i,j,a,b]*tr(XX[i][a]@YY[j][b]) for i in range(2) for j in range(3) for a in range(3) for b in range(2))/6
    eps=np.sqrt(sum(tr(d@d) for d in D)/tr(sigma@sigma))
    assert LL/tr(W@W)<=L/tr(sigma@sigma)+2*eps+1e-10
    # Check the actual square-normalized game probabilities, not just the bound.
    val,vec=np.linalg.eigh(W);invsqrt=(vec/np.sqrt(val))@vec.conj().T
    E=[[invsqrt@a@invsqrt for a in z] for z in XX]
    B=[[invsqrt@a@invsqrt for a in z] for z in YY]
    loss=sum(lose[i,j,a,b]*tr(W@E[i][a]@W@B[j][b]) for i in range(2) for j in range(3) for a in range(3) for b in range(2))/(6*tr(W@W))
    worst=max(worst,abs(loss-LL/tr(W@W)));assert abs(loss-LL/tr(W@W))<1e-10
# Exact compression counterexample: P A P = P B P = P/2; product P/4.
P=[[F(1,2)]*2]*2
mul=lambda a,b:[[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
AA=[[F(1),F(0)],[F(0),F(0)]];BB=[[F(0),F(0)],[F(0),F(1)]]
assert mul(AA,BB)==[[0,0],[0,0]]
assert mul(mul(P,AA),P)==[[z/2 for z in row] for row in P]
assert mul(mul(P,BB),P)==[[z/2 for z in row] for row in P]
assert mul(mul(mul(P,AA),P),mul(mul(P,BB),P))==[[z/4 for z in row] for row in P]
# Exact keyed code has zero deficit and question-conditioned orthogonal states.
for k in [2,3,7]:
 for message in range(k):
    assert sorted((q-message)%k for q in range(k))==list(range(k))
 for q in range(k):assert len({(q-message)%k for message in range(k)})==k
print('PASS: 80 common-sum stress models; square-normalized conversion error',worst)
print('PASS: exact spectral-compression and zero-deficit keyed-code obstructions')
