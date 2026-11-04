"""Exact / numerical checks of the spectral formulas in the Renyi-ladder return.

(9)  weighted Fock: Tr h^a = (1-b l)^a/(1-b l^a) * Tr s^a
(28) quarter plane: Tr rho^a = 4^-a q^(1-a) (1-2^-a)^-2, S = 4 + log2 q
(31)-(32) k_m construction: k_m <= m^2, |k/(m+k) - u_m| < 1/m
(33)-(37) comb: 1 <= Z <= 7, entropy formula and bound 106 + log2 7, moment test
(44) |uv/(2(u-v))| <= 1 for distinct dyadic u,v <= 1
(1),(3) tail bounds; (55)-(56) dimension bound on bare trees
R6 counterexamples
"""
import math
from fractions import Fraction as Fr
import random

ok_all = True
def check(name, cond):
    global ok_all
    ok_all &= bool(cond)
    print(("PASS " if cond else "FAIL ") + name)

# ---------- (9)
for b, n in [(4, 3), (4, 4), (4, 5), (2, 2), (3, 2), (7, 3)]:
    lam = 2.0 ** (-n)
    if b * lam >= 1:
        continue
    for a in [0.3, 0.5, 0.7, 0.9]:
        if b * lam ** a >= 1:
            continue
        direct = sum(math.exp(m * math.log(b) + a * (math.log(1 - b * lam) + m * math.log(lam))) for m in range(0, 4000))
        formula = (1 - b * lam) ** a / (1 - b * lam ** a)
        check(f"(9) b={b} n={n} a={a}: {direct:.10f} vs {formula:.10f}", abs(direct - formula) < 1e-9 * formula)
# critical index log2(b)/n and divergence at it
check("(9) four bridges: 4*(1/16)^(1/2) == 1 (half-moment diverges)", abs(4 * (1 / 16) ** 0.5 - 1) < 1e-15)
check("(9) five bridges: 4*(1/32)^(1/2) < 1", 4 * (1 / 32) ** 0.5 < 1)

# ---------- (28)
for q in [2, 3, 5, 8, 13]:
    for a in [0.05, 0.3, 0.5, 1.0, 1.7]:
        tau = [2.0 ** (-j - 1) for j in range(6000)]
        ta = sum(t ** a for t in tau)
        direct = ta * ta * q * (1.0 / q) ** a
        formula = 4 ** (-a) * q ** (1 - a) * (1 - 2 ** (-a)) ** (-2)
        check(f"(28) q={q} a={a}", abs(direct - formula) < 1e-9 * formula)
    S = 2 * sum(2.0 ** (-j - 1) * (j + 1) for j in range(1000)) + math.log2(q)
    check(f"(28) S = 4 + log2 q at q={q}: {S:.12f}", abs(S - (4 + math.log2(q))) < 1e-9)

# ---------- (31)-(32)
random.seed(1)
bad = 0
for trial in range(2000):
    m = random.randint(1, 400)
    a_m = Fr(random.randint(-50, 150), random.randint(1, 100))
    u = min(max(a_m, Fr(0)), Fr(m, m + 1))
    k = math.floor(m * u / (1 - u))
    s = Fr(k, m + k)
    if not (0 <= k <= m * m and abs(s - u) < Fr(1, m)):
        bad += 1
check(f"(31)-(32) 0<=k_m<=m^2 and |s_m-u_m|<1/m on 2000 random (m,a_m): bad={bad}", bad == 0)

# ---------- (33)-(37)
def sums(p):
    return sum(Fr(m ** p, 2 ** m) for m in range(1, 400))
S1, S2, S3, S4 = [float(sums(p)) for p in (1, 2, 3, 4)]
print("sum m/2^m, m^2/2^m, m^3/2^m, m^4/2^m =", S1, S2, S3, S4)
Zmax = S2 + 1.0
check(f"(33) Z <= sum (m^2+1)2^-m = {Zmax}", abs(Zmax - 7) < 1e-12)
ent_bound = S3 + S1 + (S4 + S2) / 2
check(f"(37) entropy sum bound = {ent_bound} (claimed 106)", abs(ent_bound - 106) < 1e-9)

def comb_stats(k, M, alpha):
    Z = sum((k(m) + 1) * 2.0 ** (-m) for m in range(1, M))
    # entropy formula vs direct
    S_formula = math.log2(Z) + (1 / Z) * sum(2.0 ** (-m) * ((k(m) + 1) * m + k(m) * (k(m) + 1) / 2) for m in range(1, M))
    S_direct = 0.0
    for m in range(1, M):
        for l in range(0, k(m) + 1):
            p = 2.0 ** (-(m + l)) / Z
            S_direct += (2 ** l) * p * (-math.log2(p))
    # moment partial sums: terms of (35)
    terms = [2.0 ** ((1 - alpha) * k(m) - alpha * m) for m in range(1, M)]
    return Z, S_formula, S_direct, terms

for name, k in [("k=m^2", lambda m: m * m), ("k=0", lambda m: 0), ("k=floor(m/2)", lambda m: m // 2)]:
    Z, Sf, Sd, _ = comb_stats(k, 25, 0.5)
    check(f"(37) comb {name}: Z={Z:.6f} in [1,7], S formula {Sf:.9f} = direct {Sd:.9f} <= {106 + math.log2(7):.4f}",
          1 - 2.0 ** -20 <= Z <= 7 + 1e-12 and abs(Sf - Sd) < 1e-6 and Sf <= 106 + math.log2(7))

# alpha_c = limsup k/(m+k): oscillating sequence with limsup r = 0.6, liminf 0.2
def ksel(m):
    u = 0.6 if m % 3 == 0 else 0.2
    u = min(u, m / (m + 1))
    return math.floor(m * u / (1 - u))
for alpha, expect in [(0.55, "diverge"), (0.65, "converge")]:
    terms = [2.0 ** ((1 - alpha) * ksel(m) - alpha * m) for m in range(1, 300)]
    tail = terms[-30:]
    grows = max(tail) > 1e3
    decays = max(tail) < 1e-3
    check(f"(36) oscillating r=0.6: alpha={alpha} -> {expect} (tail max {max(tail):.3e})",
          (expect == "diverge" and grows) or (expect == "converge" and decays))

# (35) equivalence: inner sum comparable to last term
for alpha in [0.1, 0.5, 0.9]:
    for kk in [0, 1, 5, 40]:
        inner = sum(2.0 ** ((1 - alpha) * l) for l in range(kk + 1))
        last = 2.0 ** ((1 - alpha) * kk)
        c = 1 / (1 - 2 ** (-(1 - alpha)))
        check(f"(35) inner sum within [last, last*{c:.3f}] alpha={alpha} k={kk}", last - 1e-12 <= inner <= last * c + 1e-9)

# ---------- (44)
worst = 0.0
for a_ in range(0, 60):
    for b_ in range(0, 60):
        if a_ == b_:
            continue
        u, v = 2.0 ** (-a_), 2.0 ** (-b_)
        worst = max(worst, abs(u * v / (2 * (u - v))))
check(f"(44) max |uv/(2(u-v))| over distinct dyadics <=1: {worst}", worst <= 1)

# ---------- (1) and (3) tail bounds on adversarial sorted vectors
random.seed(2)
viol = 0
for trial in range(300):
    alpha = random.choice([0.2, 0.5, 0.8])
    N = random.randint(5, 3000)
    s = random.uniform(1.01, 6)
    p = [i ** (-s) for i in range(1, N + 1)]
    Zs = sum(p); p = [x / Zs for x in p]
    K = sum(x ** alpha for x in p)
    H = -sum(x * math.log2(x) for x in p)
    for D in [1, 2, 5, 10, 50, 200]:
        if D >= N:
            continue
        tD = sum(p[D:])
        if tD > K ** (1 / alpha) * (D + 1) ** (-(1 - alpha) / alpha) + 1e-12:
            viol += 1
        if tD > H / math.log2(D + 1) + 1e-12:
            viol += 1
check(f"(1),(3) tail bounds on 300 random power-law spectra: violations={viol}", viol == 0)
# flat states: uniform I_N/N has tail 1 - D/N (no trace-one control)
check("trace-one gives no tail control: tail of I_N/N beyond D=10 at N=10^6 is ~1", 1 - 10 / 1e6 > 0.99)

# ---------- (55)-(56) on a bare tree, r = log2(b)/n
for b, n, alpha in [(4, 4, 0.6), (4, 5, 0.5), (2, 3, 0.4)]:
    lam = 2.0 ** (-n)
    r = math.log2(b) / n
    if alpha <= r:
        continue
    K = (1 - b * lam) ** alpha / (1 - b * lam ** alpha)
    # sorted spectrum truncation tail at dimension D
    spec = []
    for m in range(0, 30):
        spec += [(1 - b * lam) * lam ** m] * (b ** m) if b ** m < 2_000_000 else []
        if len(spec) > 3_000_000:
            break
    for eps in [1e-2, 1e-3, 1e-4]:
        D = math.ceil(K ** (1 / (1 - alpha)) * eps ** (-alpha / (1 - alpha)))
        tail = 1 - sum(spec[:D]) if D < len(spec) else 0.0
        check(f"(56) b={b} n={n} alpha={alpha} eps={eps}: D={D}, tail={tail:.3e} <= eps", tail <= eps * (1 + 1e-9))

# ---------- R6 counterexamples (analytic tails, sanity numerics)
# p_j ~ 1/(j^2 (log j)^4): sqrt summable, normalized sqrt has infinite entropy
def partial(fn, J):
    return sum(fn(j) for j in range(3, J))
for J in [10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6]:
    sq = partial(lambda j: 1 / (j * math.log(j) ** 2), J)
    ent = partial(lambda j: (math.log(j) + 2 * math.log(math.log(j))) / (j * math.log(j) ** 2), J)
    print(f"R6a J={J:>8}: sum sqrt p_j = {sq:.5f} (converges like 1/log J), entropy partial ~ {ent:.4f} (grows like log log J)")
# p_j ~ j^-s with max(1,2/beta) < s <= 2: beta/2 moment finite, half-moment infinite
beta, s = 1.5, 1.8
print(f"R6b beta={beta}, s={s}: s*beta/2={s*beta/2:.3f} > 1 (beta/2-moment finite); s/2={s/2:.2f} <= 1 (half-moment diverges)")
check("R6b parameter window nonempty for beta in (1,2]", all(max(1, 2 / bb) < 2 for bb in [1.01, 1.5, 2.0]))

print("ALL PASS" if ok_all else "SOME FAIL")

assert ok_all, 'spectral check failed'
