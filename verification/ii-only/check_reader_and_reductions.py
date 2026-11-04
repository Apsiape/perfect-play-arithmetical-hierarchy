"""(a) Equality-reader lemma (30)-(31) on random NONcommuting finite-dimensional data,
plus the counterexample showing injectivity of Y is load-bearing.
(b) Front-layer cellular automaton of the Sigma2 tableau with a single pulse at q=n+1.
(c) Boolean coordinate table (45)-(48).
(d) Three-star reduction for 'exactly one finite component'.
"""
import numpy as np, itertools, sys
rng = np.random.default_rng(20261103)
fails = []
def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name); 
    if not ok: fails.append(name)

def rand_herm(d):
    G = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    return (G + G.conj().T) / 2

def solvable(D, B, tol=1e-9):
    # exists T with T D = B  iff  B vanishes on ker D  (finite dim)
    w, V = np.linalg.eigh(D)
    K = V[:, np.abs(w) < tol]
    return np.linalg.norm(B @ K) < 1e-7

# (a) equality reader
ok_full, ok_proper = True, True
for trial in range(300):
    d = rng.integers(4, 9); k = rng.integers(1, d)
    U, _ = np.linalg.qr(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))
    Kb = U[:, :k]; Kp = Kb @ Kb.conj().T
    # D self-adjoint with kernel exactly K
    Dw = np.concatenate([np.zeros(k), rng.uniform(0.5, 2, d - k) * rng.choice([-1, 1], d - k)])
    D = U @ np.diag(Dw) @ U.conj().T
    G = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    Y = G @ G.conj().T + 0.1 * np.eye(d)          # positive, injective, generic: does not commute with D
    X = (D + Y) / 2                                 # so 2X - Y = D, X self-adjoint
    kappa = 1 / 8
    # R = K solvable
    ok_full &= solvable(D, kappa * X @ Y @ (np.eye(d) - Kp))
    # every proper subprojection R < K (random) is NOT solvable
    if k >= 1:
        r = rng.integers(0, k)
        Rb = Kb @ np.linalg.qr(rng.standard_normal((k, k)) + 1j * rng.standard_normal((k, k)))[0][:, :r]
        R = Rb @ Rb.conj().T
        ok_proper &= (np.linalg.norm(D @ R) < 1e-9) and not solvable(D, kappa * X @ Y @ (np.eye(d) - R))
check("reader: R = proj ker(2X-Y) satisfies (30) (300 random noncommuting cases)", ok_full)
check("reader: every proper R < ker(2X-Y) violates (30) (300 random cases)", ok_proper)
# injectivity is load-bearing
d = 3
Y = np.diag([0.0, 1.0, 2.0]); X = np.diag([0.0, 0.5, 0.3])   # 2X-Y = diag(0,0,-1.4); ker = span(e0,e1)
D = 2 * X - Y
R = np.diag([0.0, 1.0, 0.0])                                  # proper: drops e0 where X=Y=0
check("reader: without injectivity of Y a proper R passes (so (24) ker C_sel=0 is needed)",
      np.linalg.norm(D @ R) < 1e-12 and solvable(D, X @ Y @ (np.eye(3) - R) / 8))

# (b) front layer, single pulse at q = n+1
def front(pulse, T, width):
    row = ['s'] + ['b'] * (width - 1)
    rows = [row]
    for y in range(T):
        eps = pulse(y)
        new = []
        for x in range(width):
            l = row[x - 1] if x > 0 else '#'
            c = row[x]
            if c == 's': nc = 'b'
            elif c == 'f': nc = 'z' if eps else 'b'
            elif c == 'b' and l == 's': nc = 'f'
            elif c == 'b' and l == 'f': nc = 'f' if eps == 0 else 'b'
            elif c == 'z': nc = 'z'
            elif c == 'H': nc = 'H'
            else: nc = 'b'
            new.append(nc)
        row = new; rows.append(row)
    return rows
ok = True
for n in range(0, 12):
    q = n + 1
    rows = front(lambda y: 1 if y == q else 0, 3 * q + 5, 4 * q + 8)
    zs = [(x, y) for y, r in enumerate(rows) for x, c in enumerate(r) if c == 'z']
    first = min(zs, key=lambda t: t[1])
    fs_after = [(x, y) for y, r in enumerate(rows) for x, c in enumerate(r) if c == 'f' and y > q + 1]
    ok &= (first == (q, q + 1)) and all(x == q for x, _ in zs) and not fs_after
check("front: single pulse at y=n+1 freezes mark at (x,y)=(n+1,n+2), front never restarts (n<12)", ok)
# Multiple pulses (Sigma2) vs single pulse: same frozen coordinate when first pulse coincides
rows1 = front(lambda y: 1 if y > 0 and y % 5 == 0 else 0, 30, 40)
rows2 = front(lambda y: 1 if y == 5 else 0, 30, 40)
check("front: later pulses ignored (Sigma2 periodic vs single pulse give identical tableau)", rows1 == rows2)

# (c) Boolean coordinates
langs = ['E', 'I', 'J', 'U', 'C']
def AND(g, h): return {L: g[L] and h[L] for L in langs}
def OR(g, h): return {L: g[L] or h[L] for L in langs}
T_star = dict(E=0, I=0, J=1, U=1, C=1)
Q_star = dict(E=0, I=0, J=0, U=0, C=1)
ok = True
for Ae, Af, Ce, Cf in itertools.product([0, 1], repeat=4):
    Fe = dict(E=Ae, I=Ae, J=0, U=Ae, C=Ce if not Ae else 1)
    Ff = dict(E=Af, I=Af, J=0, U=Af, C=Cf if not Af else 1)
    Lam = AND(Fe, OR(T_star, Ff))
    target = Ae and not Af
    ok &= (bool(Lam['U'] and not Lam['I']) == bool(target))
    ok &= (bool(Lam['U'] and not Lam['E']) == bool(target))
    ok &= (bool(Lam['U'] and not (Lam['I'] or Lam['J'])) == bool(target))
    Fe2, Ff2 = OR(Fe, Q_star), OR(Ff, Q_star)
    Lam2 = AND(Fe2, OR(T_star, Ff2))
    ok &= all(Lam2[L] == Lam[L] for L in ['E', 'I', 'J', 'U']) and Lam2['C'] == 1 and Lam2['J'] == 0
check("Boolean: (45)-(46) coordinates and (47)-(48) padding, all 16 profiles", ok)

# (d) three stars
def build(Wa_growth, Wb_growth, S):
    # vertices: centers 0,1,2; leaves x_s=3s+3, y_s=3s+4, z_s=3s+5
    comp = {0: [0], 1: [1], 2: [2]}
    for s in range(S):
        a, b = Wa_growth(s), Wb_growth(s)
        comp[0 if a else 2].append(3 * s + 3)
        comp[1 if (a or b) else 2].append(3 * s + 4)
        comp[2].append(3 * s + 5)
    return comp
def eventually_finite_size(growth, S1, S2):
    return sum(map(growth, range(S1))) == sum(map(growth, range(S2)))
ok = True
cases = {'fin': lambda s: s in (1, 4, 9), 'inf': lambda s: s % 3 == 0, 'empty': lambda s: False}
for na, ga in cases.items():
    for nb, gb in cases.items():
        c1, c2 = build(ga, gb, 300), build(ga, gb, 600)
        finite = [k for k in range(3) if len(c1[k]) == len(c2[k])]
        exactly_one = (len(finite) == 1)
        ok &= exactly_one == (na != 'inf' and nb == 'inf')
check("three stars: exactly one finite component iff W_a finite and W_b infinite", ok)

print("\nFAILURES:", fails if fails else "none")
sys.exit(1 if fails else 0)
