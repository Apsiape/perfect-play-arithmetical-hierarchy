"""Exact checks of the finite-entropy YES model of the II-ONLY return (Section 7),
factor by factor, with exact rational arithmetic on sparse matrices.

Selector factor: 16-ary words of length <= n, S_i prepends i (vanishes at depth n),
C_sel = 2^{-|v|}, h_sel = 16^{-|v|}/(n+1).
Fock factor: 4-ary words truncated at depth M (relations checked where the truncation
is exact), h_F = (3/4) 16^{-|w|}.
Joint diagonal labels: C_ctr = 2^{-y}, P_ret = 1{y = l+1}, T_inv from (34).
"""
from fractions import Fraction as Fr
from itertools import product
import math, sys

def words(alpha, maxlen):
    out = [()]
    layer = [()]
    for _ in range(maxlen):
        layer = [(a,) + w for w in layer for a in range(alpha)]  # prepend
        out += layer
    return out

# ---------- sparse helpers: dict {(r,c): Fraction} ----------
def mul(A, B):
    Bc = {}
    for (r, c), v in B.items():
        Bc.setdefault(r, []).append((c, v))
    out = {}
    for (r, k), v in A.items():
        for (c, w) in Bc.get(k, []):
            out[(r, c)] = out.get((r, c), 0) + v * w
    return {k: v for k, v in out.items() if v != 0}

def adj(A):
    return {(c, r): v for (r, c), v in A.items()}  # real matrices

def add(A, B, s=1):
    out = dict(A)
    for k, v in B.items():
        out[k] = out.get(k, 0) + s * v
    return {k: v for k, v in out.items() if v != 0}

def scal(A, s):
    return {k: s * v for k, v in A.items() if s * v != 0}

def diag(vals):
    return {(i, i): Fr(v) for i, v in enumerate(vals) if v != 0}

def eq(A, B, rows=None):
    D = add(A, B, -1)
    if rows is not None:
        D = {k: v for k, v in D.items() if k[0] in rows and k[1] in rows}
    return len(D) == 0

fails = []
def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        fails.append(name)

# ---------- selector ----------
for n in [0, 1, 2]:
    W = words(16, n)
    idx = {w: k for k, w in enumerate(W)}
    N = len(W)
    S = []
    for i in range(16):
        Si = {}
        for w in W:
            if len(w) < n:
                Si[(idx[(i,) + w], idx[w])] = Fr(1)
        S.append(Si)
    I = diag([1] * N)
    P = diag([1 if len(w) == n else 0 for w in W])
    Q = diag([1 if len(w) == 0 else 0 for w in W])
    C = diag([Fr(1, 2 ** len(w)) for w in W])
    h = diag([Fr(1, 16 ** len(w)) / (n + 1) for w in W])
    hinv = diag([Fr(16 ** len(w)) * (n + 1) for w in W])
    ok_gram = all(eq(mul(adj(S[i]), S[j]), add(I, P, -1) if i == j else {}) for i in range(16) for j in range(16))
    check(f"sel n={n}: S_i^*S_j = delta(I-P)", ok_gram)
    rng = {}
    for i in range(16):
        rng = add(rng, mul(S[i], adj(S[i])))
    check(f"sel n={n}: sum S_iS_i^* = I-Q", eq(rng, add(I, Q, -1)))
    check(f"sel n={n}: C Q = Q", eq(mul(C, Q), Q))
    check(f"sel n={n}: C S_i = (1/2) S_i C", all(eq(mul(C, S[i]), scal(mul(S[i], C), Fr(1, 2))) for i in range(16)))
    check(f"sel n={n}: [C,P]=0", eq(mul(C, P), mul(P, C)))
    check(f"sel n={n}: h S_i h^-1 = S_i/16 (modular ratio 1/16)", all(eq(mul(mul(h, S[i]), hinv), scal(S[i], Fr(1, 16))) for i in range(16)))
    trh = sum(v for (r, c), v in h.items() if r == c)
    check(f"sel n={n}: Tr h_sel = 1", trh == 1)
    phiP = sum(v for (r, c), v in mul(h, P).items() if r == c)
    phiQ = sum(v for (r, c), v in mul(h, Q).items() if r == c)
    check(f"sel n={n}: phi(P) = phi(Q) = 1/(n+1)", phiP == phiQ == Fr(1, n + 1))
    # E_j = Phi^j(Q)
    X = Q
    okE = True
    for j in range(n + 1):
        Ej = diag([1 if len(w) == j else 0 for w in W])
        okE &= eq(X, Ej)
        Y = {}
        for i in range(16):
            Y = add(Y, mul(mul(S[i], X), adj(S[i])))
        X = Y
    okE &= (len(X) == 0)
    check(f"sel n={n}: E_j = Phi^j(Q), Phi^(n+1)(I)... = 0", okE)
    # entropy exact formula
    ent = -sum(float(v) * math.log2(float(v)) for (r, c), v in h.items())
    check(f"sel n={n}: S(h_sel) = log2(n+1)+2n  ({ent:.12f})", abs(ent - (math.log2(n + 1) + 2 * n)) < 1e-9)

# n = 7 entropy via counts (not building matrices)
n = 7
ent = sum((16 ** l) * (Fr(1, 16 ** l) / (n + 1)) * (math.log2(n + 1) + 4 * l) for l in range(n + 1))
check(f"sel n=7 entropy = 17 ({float(ent)})", abs(float(ent) - 17.0) < 1e-12)

# ---------- Fock factor (truncated at depth M) ----------
M = 4
W = words(4, M)  # letters alpha = 2a+b encode (a,b)
idx = {w: k for k, w in enumerate(W)}
N = len(W)
def ab(al):
    return al >> 1, al & 1
def xy(w):
    # first letter = least significant bit
    x = sum(ab(al)[0] << j for j, al in enumerate(w))
    y = sum(ab(al)[1] << j for j, al in enumerate(w))
    return x, y
A = []
for al in range(4):
    Aa = {}
    for w in W:
        if len(w) < M:
            Aa[(idx[(al,) + w], idx[w])] = Fr(1)
    A.append(Aa)
inner = {idx[w] for w in W if len(w) < M}
I = diag([1] * N)
Pc = diag([1 if len(w) == 0 else 0 for w in W])
hF = diag([Fr(3, 4) / 16 ** len(w) for w in W])
hFinv = diag([Fr(4, 3) * 16 ** len(w) for w in W])
check("Fock: A^*_a A_b = delta I (on depth < M)", all(eq(mul(adj(A[a]), A[b]), I if a == b else {}, rows=inner) for a in range(4) for b in range(4)))
rng = {}
for a in range(4):
    rng = add(rng, mul(A[a], adj(A[a])))
check("Fock: sum A A^* = I - P_root (exact on truncation)", eq(rng, add(I, Pc, -1)))
check("Fock: h_F A h_F^-1 = A/16", all(eq(mul(mul(hF, A[a]), hFinv), scal(A[a], Fr(1, 16))) for a in range(4)))
# coordinates: U_x, U_y cyclic increments at fixed depth; P_x, P_y; counter
def perm_matrix(f):
    return {(idx[f(w)], idx[w]): Fr(1) for w in W}
def inc(w, coord):
    m = len(w)
    if m == 0:
        return w
    x, y = xy(w)
    if coord == 0:
        x = (x + 1) % (2 ** m)
    else:
        y = (y + 1) % (2 ** m)
    return tuple(((x >> j) & 1) * 2 + ((y >> j) & 1) for j in range(m))
Ux = perm_matrix(lambda w: inc(w, 0))
Uy = perm_matrix(lambda w: inc(w, 1))
Px = diag([1 if xy(w)[0] == 0 else 0 for w in W])
Py = diag([1 if xy(w)[1] == 0 else 0 for w in W])
Cc = diag([Fr(1, 2 ** xy(w)[1]) for w in W])
def L(a, b):
    return 2 * a + b
ok = True
for b in range(2):
    ok &= eq(mul(mul(Ux, A[L(0, b)]), diag([1 if len(w) < M else 0 for w in W])), A[L(1, b)])
    ok &= eq(mul(mul(Ux, A[L(1, b)]), diag([1 if len(w) < M else 0 for w in W])), mul(A[L(0, b)], Ux))
for a in range(2):
    ok &= eq(mul(mul(Uy, A[L(a, 0)]), diag([1 if len(w) < M else 0 for w in W])), A[L(a, 1)])
    ok &= eq(mul(mul(Uy, A[L(a, 1)]), diag([1 if len(w) < M else 0 for w in W])), mul(A[L(a, 0)], Uy))
ok &= eq(mul(Ux, Pc), Pc) and eq(mul(Uy, Pc), Pc)
check("Fock: U_x,U_y recursions (7)", ok)
ok = True
for b in range(2):
    ok &= eq(mul(Px, A[L(0, b)]), mul(A[L(0, b)], Px)) and eq(mul(Px, A[L(1, b)]), {})
for a in range(2):
    ok &= eq(mul(Py, A[L(a, 0)]), mul(A[L(a, 0)], Py)) and eq(mul(Py, A[L(a, 1)]), {})
ok &= eq(mul(Px, Pc), Pc) and eq(mul(Py, Pc), Pc)
check("Fock: P_x,P_y recursions (7)", ok)
ok = eq(mul(Cc, Pc), Pc)
for a in range(2):
    for b in range(2):
        ok &= eq(mul(Cc, A[L(a, b)]), scal(mul(A[L(a, b)], mul(Cc, Cc)), Fr(1, 2 ** b)))
check("Fock: counter C_ctr A_ab = 2^-b A_ab C_ctr^2, C_ctr P_root = P_root (8)", ok)
check("Fock: coordinate labels commute with h_F (centralizer)", all(eq(mul(X, hF), mul(hF, X)) for X in [Ux, Uy, Px, Py, Cc, Pc]))
ent = sum((4 ** m) * (Fr(3, 4) / 16 ** m) * (math.log2(4 / 3) + 4 * m) for m in range(200))
check(f"Fock entropy log2(4/3)+4/3 ({float(ent):.12f})", abs(float(ent) - (math.log2(4 / 3) + 4 / 3)) < 1e-12)
check("Fock: phi(P_root) = 3/4", Fr(3, 4) == hF[(idx[()], idx[()])])

# ---------- equality reader (joint diagonal labels) exact ----------
maxv = 0
ok = True
for l in range(0, 70):
    for y in range(0, 140):
        Cc_, Cs_ = Fr(1, 2 ** y), Fr(1, 2 ** l)
        D = 2 * Cc_ - Cs_
        Pr = 1 if y == l + 1 else 0
        ok &= ((D == 0) == (Pr == 1))
        T = Fr(0) if y == l + 1 else Fr(1, 8 * (2 ** (l + 1) - 2 ** y))
        ok &= (D * Pr == 0)
        ok &= (T * D == Fr(1, 8) * Cc_ * Cs_ * (1 - Pr))
        maxv = max(maxv, abs(T))
check(f"reader (9)-(10) exact on l<70,y<140; P_ret = 1{{y=l+1}}; max|T_inv| = {maxv}", ok and maxv == Fr(1, 8))
neg = any(Fr(1, 8 * (2 ** (l + 1) - 2 ** y)) < 0 for l in range(5) for y in range(8) if y != l + 1)
check("T_inv takes negative values (cannot be typed positive)", neg)
check("no time-zero pulse: 2*1 - 2^-l != 0 for all l", all(2 - Fr(1, 2 ** l) != 0 for l in range(100)))

# ---------- scaffold ----------
Z = 1 + 4 * sum(2 ** g for g in range(1, 5))
check(f"scaffold Z_4 = 121 (got {Z}); e4/e0 ratio 16 cancels 1/16", Z == 121)

print("\nFAILURES:", fails if fails else "none")
sys.exit(1 if fails else 0)
