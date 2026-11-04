"""Finite-dimensional algebraic test of the nested-bridge identities (12)-(18).

Model: corners f, e, f', e' each ~ C^N, with root density rho = diag(2^-k) (multiplicity d_k)
on f, density 2*U rho U^* on e, 2*V rho V^* on f', 4*W(U rho U^*)W^* on e'.
Calibrated transports: w0 = V (f->f'), w1 = W (e->e'), both satisfy h w = 2 w h.
Centralizer data: t = V T U^* (T block-unitary commuting with rho), a_i = U A_i with
2 rho A_i = A_i rho (A_i maps block k to block k+1), labels L,R commuting with rho.
We check, as exact matrix identities (to float precision):
  (14) rho X = X rho / 2, X_i = w0^* t a_i
  (15) X_i^* X_j = a_i^* a_j;  w0 X_i X_j^* w0^* = t a_i a_j^* t^*;  X_i X_j = l (a_i' t a_j), l = w0^* t w1^*
       with the SAME l for every pair, and l^* l = identity on e'
  (16)-(18) as norm equalities (so each "iff" holds quantitatively):
       ||X_i X_j - X_j X_i|| = ||a_i' t a_j - a_j' t a_i||
       ||X_i^* X_j - X_j X_i^*|| = ||a_i'^* a_j' - t a_j a_i^* t^*||
       ||L X_i - X_i R|| = ||L' t a_i - t a_i R||,  L' = w0 L w0^*
  every centralizer variable commutes with the corresponding densities.
"""
import numpy as np

rng = np.random.default_rng(7)
mult = [3, 2, 4, 3, 2, 3]                 # multiplicities d_k of eigenvalue 2^-k
N = sum(mult)
offs = np.cumsum([0] + mult)
rho = np.diag(np.concatenate([np.full(d, 2.0 ** -k) for k, d in enumerate(mult)]))

def haar(n):
    z = (rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))) / np.sqrt(2)
    q, r = np.linalg.qr(z)
    return q * (np.diag(r) / np.abs(np.diag(r)))

def block_unitary():
    T = np.zeros((N, N), complex)
    for k, d in enumerate(mult):
        T[offs[k]:offs[k + 1], offs[k]:offs[k + 1]] = haar(d)
    return T

def block_label():
    Lb = np.zeros((N, N), complex)
    for k, d in enumerate(mult):
        g = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        Lb[offs[k]:offs[k + 1], offs[k]:offs[k + 1]] = g / np.linalg.norm(g, 2)
    return Lb

def creation():
    A = np.zeros((N, N), complex)
    for k in range(len(mult) - 1):
        g = rng.normal(size=(mult[k + 1], mult[k])) + 1j * rng.normal(size=(mult[k + 1], mult[k]))
        A[offs[k + 1]:offs[k + 2], offs[k]:offs[k + 1]] = g / np.linalg.norm(g, 2)
    return A

U, V, W = haar(N), haar(N), haar(N)
h_f = rho
h_e = 2 * U @ rho @ U.conj().T
h_fp = 2 * V @ rho @ V.conj().T
h_ep = 4 * W @ (U @ rho @ U.conj().T) @ W.conj().T
w0, w1 = V, W
T = block_unitary()
t = V @ T @ U.conj().T
As = [creation() for _ in range(4)]
a = [U @ Ai for Ai in As]
H = lambda M: M.conj().T
nrm = lambda M: np.linalg.norm(M, 2)

res = {}
res["h w0 = 2 w0 h"] = nrm(h_fp @ w0 - 2 * w0 @ h_f)
res["h w1 = 2 w1 h"] = nrm(h_ep @ w1 - 2 * w1 @ h_e)
res["t centralizer"] = nrm(h_fp @ t - t @ h_e)
res["a_i centralizer"] = max(nrm(h_e @ ai - ai @ h_f) for ai in a)
X = [H(w0) @ t @ ai for ai in a]
ap = [w1 @ ai @ H(w0) for ai in a]           # transported copies a_i' : f' -> e'
res["a_i' centralizer"] = max(nrm(h_ep @ x - x @ h_fp) for x in ap)
res["(14) rho X = X rho/2"] = max(nrm(rho @ x - 0.5 * x @ rho) for x in X)
ell = H(w0) @ t @ H(w1)
res["l^* l = I_{e'}"] = nrm(H(ell) @ ell - np.eye(N))
res["h l = l h /4"] = nrm(h_f @ ell - 0.25 * ell @ h_ep)
m15a = m15b = m15c = 0.0
m16 = m17 = 0.0
for i in range(4):
    for j in range(4):
        m15a = max(m15a, nrm(H(X[i]) @ X[j] - H(a[i]) @ a[j]))
        m15b = max(m15b, nrm(w0 @ X[i] @ H(X[j]) @ H(w0) - t @ a[i] @ H(a[j]) @ H(t)))
        m15c = max(m15c, nrm(X[i] @ X[j] - ell @ (ap[i] @ t @ a[j])))
        lhs = nrm(X[i] @ X[j] - X[j] @ X[i]); rhs = nrm(ap[i] @ t @ a[j] - ap[j] @ t @ a[i])
        m16 = max(m16, abs(lhs - rhs))
        lhs = nrm(H(X[i]) @ X[j] - X[j] @ H(X[i])); rhs = nrm(H(ap[i]) @ ap[j] - t @ a[j] @ H(a[i]) @ H(t))
        m17 = max(m17, abs(lhs - rhs))
res["(15a) X_i^*X_j = a_i^*a_j"] = m15a
res["(15b) w0 X_i X_j^* w0^* = t a_i a_j^* t^*"] = m15b
res["(15c) X_iX_j = l(a_i' t a_j), same l all pairs"] = m15c
res["(16) norm equality"] = m16
res["(17) norm equality"] = m17
m18 = 0.0
for _ in range(10):
    L, R = block_label(), block_label()
    Lp = w0 @ L @ H(w0)
    for i in range(4):
        m18 = max(m18, abs(nrm(L @ X[i] - X[i] @ R) - nrm(Lp @ t @ a[i] - t @ a[i] @ R)))
res["(18) norm equality"] = m18
# a nontrivial commutator really occurs (so (16) is not vacuous) and a commuting pair passes
res["sanity: random X's do not commute (should be >0)"] = -nrm(X[0] @ X[1] - X[1] @ X[0])
A_c = creation()
A_d = 0.5 * A_c                               # commuting pair: X = T A_c, T A_d
a_c, a_d = U @ A_c, U @ A_d
Xc, Xd = H(w0) @ t @ a_c, H(w0) @ t @ a_d
res["commuting pair: ||XcXd-XdXc|| and its translation"] = nrm(Xc @ Xd - Xd @ Xc) + nrm(
    (w1 @ a_c @ H(w0)) @ t @ a_d - (w1 @ a_d @ H(w0)) @ t @ a_c)
# completeness: a = |e><f| (x) X commutes with diag(rho, 2 rho)
Xr = X[0]
h_sc = np.block([[rho, np.zeros((N, N))], [np.zeros((N, N)), 2 * rho]])
a_sc = np.block([[np.zeros((N, N)), np.zeros((N, N))], [Xr, np.zeros((N, N))]])
res["completeness: [h_sc, |e><f| (x) X] = 0"] = nrm(h_sc @ a_sc - a_sc @ h_sc)

ok = True
for k, v in res.items():
    if k.startswith("sanity"):
        good = v < -1e-3
        print(f"{'PASS' if good else 'FAIL'} {k}: {-v:.3e}")
    else:
        good = v < 1e-10
        print(f"{'PASS' if good else 'FAIL'} {k}: {v:.3e}")
    ok &= good
print("ALL PASS" if ok else "SOME FAIL")
