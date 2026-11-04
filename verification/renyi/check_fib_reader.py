"""Check the Fibonacci period reader of Section 5 (uniform family).

Claims tested:
  (a) |z^x - 1| >= 8/(9x) at every nonreturn x (q does not divide x), where
      q = F_{n+3}, z = exp(2 pi i F_{n+2}/F_{n+3}).
  (b) ||D_x|| <= 9/32 where D_x = 2^{-x-1}/(z^x-1) (0 at returns).
  (c) the two stated ingredients: ||x theta|| > 1/(3x) (theta=(sqrt5-1)/2)
      and |theta - a/q| < q^{-2}; and which x-range they cover by themselves.
Exact integer residues are used for (a); periodicity in x reduces to 1<=x<q
(for x>q the residue r=x mod q has 8/(9x) < 8/(9r)).
"""
import math
import numpy as np

def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a

theta = (math.sqrt(5) - 1) / 2
worst_overall = float("inf")
maxD_overall = 0.0
print("n  q        worst ratio |z^x-1|/(8/(9x))   argmin x   max|D_x|   crude-range-ok(x<=q/3)")
for n in range(0, 31):
    q = fib(n + 3)
    a = fib(n + 2)
    x = np.arange(1, q, dtype=np.int64)
    r = (x * a) % q
    d = np.minimum(r, q - r).astype(np.float64) / q
    dist = 2 * np.sin(np.pi * d)
    ratio = dist * 9 * x / 8.0
    i = int(np.argmin(ratio))
    worst = float(ratio[i])
    worst_overall = min(worst_overall, worst)
    # D_x for x up to 200 (beyond, 2^{-x} kills it); include x>=q via residues
    xs = np.arange(1, 400, dtype=np.int64)
    rr = (xs * a) % q
    nonret = rr != 0
    dd = np.minimum(rr, q - rr).astype(np.float64) / q
    zz = 2 * np.sin(np.pi * dd)
    Dx = np.where(nonret, 2.0 ** (-xs - 1) / np.where(nonret, zz, 1.0), 0.0)
    maxD = float(Dx.max())
    maxD_overall = max(maxD_overall, maxD)
    # crude route: 1/(3x) - x/q^2 >= 2/(9x)  <=> x <= q/3
    crude_ok = bool(np.all((1 / (3 * x) - x / q**2 >= 2 / (9 * x)) | (x > q / 3)))
    print(f"{n:2d} {q:8d}  {worst:10.4f}   {int(x[i]):8d}   {maxD:.5f}   {crude_ok}")
print("worst ratio overall (must be >=1):", worst_overall)
print("max |D_x| overall (claim <= 9/32 = 0.28125):", maxD_overall)

# ingredient: ||x theta|| > 1/(3x), x up to 2e6 (float64 adequate: error ~1e-10)
X = np.arange(1, 2_000_001, dtype=np.float64)
fr = X * theta
dist = np.abs(fr - np.round(fr))
print("min x*||x theta|| for x<=2e6:", float((X * dist).min()), "(claim > 1/3)")
# Fibonacci approximation |theta - a/q| < 1/q^2
ok = all(abs(theta - fib(n + 2) / fib(n + 3)) < 1 / fib(n + 3) ** 2 for n in range(0, 30))
print("|theta - F_{n+2}/F_{n+3}| < q^-2 for n<30:", ok)
# where the stated two ingredients alone fail: x in (q/3, q): need the trivial bound ||xa/q|| >= 1/q
# 4/q >= 8/(9x) iff x >= 2q/9, which covers x > q/3.
print("trivial-residue bound covers x >= 2q/9 (so all x > q/3): ", 2/9 < 1/3)
