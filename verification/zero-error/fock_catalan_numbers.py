"""Exact numbers for Part B items 8-9 (sympy)."""
import sympy as sp
m, n = sp.symbols('m n', integer=True, nonnegative=True)

print('--- Fock tree, n calibrated ratio-2 bridges, modular ratio lam = 2^-n ---')
for nb in [4, 5, 6, 8]:
    lam = sp.Rational(1, 2**nb)
    root = 1 - 4*lam                     # Tr(h P_o) = 1 - 4 lam
    ratio = 4*sp.sqrt(lam)               # per-depth growth of the amplitude sum
    if ratio >= 1:
        trsqrt = sp.oo
    else:
        trsqrt = sp.sqrt(root) / (1 - ratio)
    cover = 2**(nb+3) - 7                # 1 + 4(2+...+2^n)
    mu = [sp.Integer(1)] + [sp.Integer(2)**g for g in range(1, nb+1) for _ in range(4)]
    assert sum(mu) == cover
    sqrtmu = sp.nsimplify(sum(sp.sqrt(x) for x in mu)) / sp.sqrt(cover)
    print(f'n={nb}: lam=1/{2**nb}, Tr(hP_o)={root}, amplitude growth 4*sqrt(lam)={sp.nsimplify(ratio)}, '
          f'Tr sqrt(h_F)={sp.simplify(trsqrt)} ~ {sp.N(trsqrt, 8) if trsqrt != sp.oo else "inf"}; '
          f'Omega_n={cover}; sum sqrt(mu)={sp.N(sqrtmu, 8)}')
    if trsqrt != sp.oo:
        q, d = sp.symbols('q d_max', positive=True)
        TrD = sqrtmu * trsqrt * sp.sqrt(q) * sp.sqrt(3) * sp.sqrt(d)
        print(f'     YES-witness amplitude sum Tr D = {sp.N(sqrtmu*trsqrt*sp.sqrt(3), 8)} * sqrt(q_clk * d_row)')
        # code marginal = D/Tr D: on the Fock factor sqrt(h_F)/Tr sqrt(h_F)  ~ ratio sqrt(lam)
        print(f'     code marginal Fock factor has ratio sqrt(lam) = 1/{sp.sqrt(2**nb)} per letter; '
              f'its depth masses (4 sqrt lam)^m = ({sp.nsimplify(ratio)})^m')

print('--- truncated check: partial sums of Tr sqrt(h_F) at ratio 1/16 (diverges linearly) ---')
for M in [10, 100, 1000]:
    s = sp.sqrt(sp.Rational(3, 4)) * sum(4**j * sp.Rational(1, 4**j) for j in range(M+1))
    print(M, sp.N(s, 8))

print('--- Catalan, squared ratio: hA = Ah/4 -> kA = Ak/16 ---')
C = lambda z: (1 - sp.sqrt(1 - 4*z)) / (2*z)
s4 = sp.simplify(C(sp.Rational(1, 4)))
s16 = sp.simplify(C(sp.Rational(1, 16)))
print('sum Cat_n 4^-n =', s4, '; sum Cat_n 16^-n =', s16, '=', sp.nsimplify(8 - 4*sp.sqrt(3)), sp.simplify(s16 - (8-4*sp.sqrt(3))))
TrhCat2 = sp.simplify(sp.Rational(1, 4) * s16)
print('Tr h_Cat^2 =', TrhCat2, ' (claim 2 - sqrt3):', sp.simplify(TrhCat2 - (2 - sp.sqrt(3))) == 0)
# k_w = h_Cat_w^2 / Tr h_Cat^2 = (1/4) 16^-n / (2 - sqrt3) = 16^-n / (8 - 4 sqrt3)
kcoef = sp.simplify(sp.Rational(1, 4) / TrhCat2)
print('k_w = 16^-n *', kcoef, ' = 16^-n/(8-4sqrt3)?', sp.simplify(kcoef - 1/(8-4*sp.sqrt(3))) == 0)
Trsqrtk = sp.simplify(sp.sqrt(kcoef) * s4)
print('Tr sqrt(k) = sum_n Cat_n 4^-n sqrt(kcoef) =', sp.nsimplify(Trsqrtk), '~', sp.N(Trsqrtk, 10),
      ' (sqrt6+sqrt2)/2 =', sp.N((sp.sqrt(6)+sp.sqrt(2))/2, 10))
# code marginal = sqrt(k)/Tr sqrt(k) = 4^-n sqrt(kcoef)/Trsqrtk
cm = sp.simplify(sp.sqrt(kcoef) / Trsqrtk)
print('code marginal coefficient (should be 1/2, i.e. h_Cat):', cm)
# entropies: S(h_Cat) = infinite, S(k) finite
import mpmath as mp
mp.mp.dps = 30
def cat(j): return mp.binomial(2*j, j) / (j + 1)
def S_partial(coef, base, N):
    tot = mp.mpf(0)
    for j in range(N):
        p = coef * mp.mpf(base)**(-j)
        tot += cat(j) * (-p * mp.log(p, 2))
    return tot
kc = mp.mpf(1) / (8 - 4*mp.sqrt(3))
for N in [100, 1000, 4000]:
    print(f'N={N}: partial S(h_Cat) = {mp.nstr(S_partial(mp.mpf(1)/2, 4, N), 10)}   partial S(k) = {mp.nstr(S_partial(kc, 16, N), 15)}')
