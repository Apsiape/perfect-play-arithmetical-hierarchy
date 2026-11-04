"""Section 3 (saturation cancellation, slicing), item 7 (theta vector bound with Naimark), Section 8 (identity).
H = Mancinska game graph of the Mermin-Peres magic square (24 vertices, k = 6 cliques).
Build a NON-product, NON-maximally-mixed, randomly rotated saturating code for H^{strong 2} (36 messages):
  - adaptive T-family: coordinate-2 effects conjugated by a unitary depending on the coordinate-1 clique,
  - direct sum of two such families with weights p, 1-p (receiver state not maximally mixed),
  - Latin-square shared register on coordinate 1, so P_{i,z} is not clique-aligned,
  - global random unitary on Bob's space.
Then verify (5),(6),(7), the slicing code, negative controls, theta vectors, and the entropy identity.
"""
import itertools, math
import numpy as np
import networkx as nx

rng = np.random.default_rng(20261103)
TOL = 1e-9
I2 = np.eye(2); X = np.array([[0, 1], [1, 0]], complex); Z = np.diag([1, -1]).astype(complex); Y = np.array([[0, -1j], [1j, 0]])
kr = np.kron
O = [[kr(I2, Z), kr(Z, I2), kr(Z, Z)],
     [kr(X, I2), kr(I2, X), kr(X, X)],
     [-kr(X, Z), -kr(Z, X), kr(Y, Y)]]
I4 = np.eye(4)
rowsign = [int(round(np.real((O[r][0] @ O[r][1] @ O[r][2])[0, 0]))) for r in range(3)]
colsign = [int(round(np.real((O[0][c] @ O[1][c] @ O[2][c])[0, 0]))) for c in range(3)]
for r in range(3): assert np.allclose(O[r][0] @ O[r][1] @ O[r][2], rowsign[r] * I4)
for c in range(3): assert np.allclose(O[0][c] @ O[1][c] @ O[2][c], colsign[c] * I4)
print('row signs', rowsign, 'col signs', colsign)

# vertices of H, cliques 0..2 Alice rows, 3..5 Bob columns
verts, clique, eff = [], [], []
for r in range(3):
    for a in itertools.product([1, -1], repeat=3):
        if np.prod(a) != rowsign[r]: continue
        E = I4.copy().astype(complex)
        for c in range(3): E = E @ (I4 + a[c] * O[r][c]) / 2
        verts.append(('L', r, a)); clique.append(r); eff.append(E)
for c in range(3):
    for b in itertools.product([1, -1], repeat=3):
        if np.prod(b) != colsign[c]: continue
        F = I4.copy().astype(complex)
        for r in range(3): F = F @ (I4 + b[r] * O[r][c]) / 2   # Bob effect stored in transposed form
        verts.append(('R', c, b)); clique.append(3 + c); eff.append(F)
nv = len(verts); k = 6
def adj(x, y):
    vx, vy = verts[x], verts[y]
    if x == y: return False
    if clique[x] == clique[y]: return True
    if vx[0] == vy[0]: return False
    if vx[0] == 'R': vx, vy = vy, vx
    r, a = vx[1], vx[2]; c, b = vy[1], vy[2]
    return a[c] != b[r]          # losing
ADJ = np.array([[adj(x, y) for y in range(nv)] for x in range(nv)])
CONF = ADJ | np.eye(nv, dtype=bool)
print('H: vertices', nv, 'edges', ADJ.sum() // 2, 'cliques', k)
# one-shot T-family with rho0 = I/4: (6),(7)
T1 = [E / 4 for E in eff]
for z in range(k):
    assert np.allclose(sum(T1[x] for x in range(nv) if clique[x] == z), I4 / 4)
bad = max(abs(np.trace(T1[x] @ T1[y])) for x in range(nv) for y in range(nv) if ADJ[x, y] and clique[x] != clique[y])
print('one-shot T-family: (6) ok, max |Tr T_x T_y| over cross-clique edges =', bad)

def haar(d):
    A = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); Q, R = np.linalg.qr(A)
    return Q * (np.diag(R) / abs(np.diag(R)))

# two-fold inputs
V2 = [(x1, x2) for x1 in range(nv) for x2 in range(nv)]
cl2 = [clique[x1] * k + clique[x2] for (x1, x2) in V2]
def conf2(w, w2):
    return CONF[w[0], w2[0]] and CONF[w[1], w2[1]]
# factor vectors: T-family rank-1 per block. Build adaptive families A and B.
def factor(E):  # rank-1 projector E -> unit vector
    vals, vecs = np.linalg.eigh(E); return vecs[:, -1] * math.sqrt(max(vals[-1], 0))
f1 = [factor(T1[x]) for x in range(nv)]     # T1[x] = f f^*
for x in range(nv): assert np.allclose(np.outer(f1[x], f1[x].conj()), T1[x])
Vs_A = [haar(4) for _ in range(k)]; Vs_B = [haar(4) for _ in range(k)]; W = haar(16)
p = 0.3
dimT = 32
def Tfactor(w):
    x1, x2 = w
    a = np.kron(f1[x1], Vs_A[clique[x1]] @ f1[x2])
    b = W @ np.kron(f1[x1], Vs_B[clique[x1]] @ f1[x2])
    return np.stack([np.concatenate([math.sqrt(p) * a, np.zeros(16)]), np.concatenate([np.zeros(16), math.sqrt(1 - p) * b])], axis=1)
TF = [Tfactor(w) for w in V2]
rhoT = np.diag([p / 16] * 16 + [(1 - p) / 16] * 16).astype(complex)
# Latin register on coordinate 1
perm = rng.permutation(6); sig = rng.permutation(6); tau = rng.permutation(6)
L = lambda i1, z1: perm[(sig[i1] + tau[z1]) % 6]
D = dimT * 6
Ug = haar(D)
rho = Ug @ np.kron(rhoT, np.eye(6) / 6) @ Ug.conj().T
msgs = [(i1, i2) for i1 in range(6) for i2 in range(6)]
def beta_factor(i, widx):
    i1, i2 = i; x1, x2 = V2[widx]; z1, z2 = clique[x1], clique[x2]
    if z2 != i2: return None
    e = np.zeros(6); e[L(i1, z1)] = 1 / math.sqrt(6)
    return Ug @ np.kron(TF[widx], e[:, None])
BF = {(mi, w): beta_factor(m, w) for mi, m in enumerate(msgs) for w in range(len(V2))}
BF = {key: v for key, v in BF.items() if v is not None}
op = lambda Fm: Fm @ Fm.conj().T
ok = True
# (a) each message sums to rho
err_a = max(np.abs(sum(op(BF[(mi, w)]) for w in range(len(V2)) if (mi, w) in BF) - rho).max() for mi in range(36))
print('(a) code: max |sum_w beta^i_w - rho| =', err_a); ok &= err_a < 1e-10
# (b) zero error on H^{strong 2}: Tr(beta^i_w beta^j_w') = 0 for i != j, w ~ w'
used = {mi: [w for w in range(len(V2)) if (mi, w) in BF] for mi in range(36)}
Cmat = np.zeros((len(V2), len(V2)), dtype=bool)
CONF2 = np.kron(CONF, CONF)  # index (x1,x2) -> x1*nv+x2 matches V2 ordering
worst = 0.0
for mi in range(36):
    Fi = np.concatenate([BF[(mi, w)] for w in used[mi]], axis=1)
    for mj in range(36):
        if mj == mi: continue
        Fj = np.concatenate([BF[(mj, w)] for w in used[mj]], axis=1)
        G = np.abs(Fi.conj().T @ Fj) ** 2
        r = BF[(mi, used[mi][0])].shape[1]
        Gs = G.reshape(len(used[mi]), r, len(used[mj]), r).sum(axis=(1, 3))
        mask = CONF2[np.ix_(used[mi], used[mj])]
        worst = max(worst, (Gs * mask).max())
print('(b) code zero-error: max Tr(beta^i_w beta^j_w\') over i!=j, w~w\' =', worst); ok &= worst < 1e-10

# (c) equality conditions (5), computed on the fly (memory)
def supp(M):
    vals, vecs = np.linalg.eigh((M + M.conj().T) / 2); V = vecs[:, vals > 1e-10]; return V @ V.conj().T
def sigma_of(mi, z):
    terms = [BF[(mi, w)] for w in used[mi] if cl2[w] == z]
    if not terms: return np.zeros((D, D), complex)
    Fm = np.concatenate(terms, axis=1); return Fm @ Fm.conj().T
e1 = 0.0; colsum = [np.zeros((D, D), complex) for _ in range(36)]; ranks = set(); e3 = 0.0
for mi in range(36):
    rowsum = np.zeros((D, D), complex)
    for z in range(36):
        S_ = sigma_of(mi, z); P_ = supp(S_)
        e1 = max(e1, np.abs(rho @ P_ - S_).max(), np.abs(P_ @ rho - S_).max())
        colsum[z] += P_; rowsum += P_; ranks.add(int(round(np.trace(P_).real)))
    e3 = max(e3, np.abs(rowsum - np.eye(D)).max())
e2 = max(np.abs(cs - np.eye(D)).max() for cs in colsum)
del colsum
print(f'(c) (5): |rho P - sigma|={e1:.2e}, |sum_i P - I|={e2:.2e}, |sum_z P - I|={e3:.2e}; ranks of P_(i,z) = {sorted(ranks)}')
ok &= max(e1, e2, e3) < 1e-8
# (d) gamma, (6), (7)
gf = []
for w in range(len(V2)):
    Fw = np.concatenate([BF[(mi, w)] for mi in range(36) if (mi, w) in BF], axis=1)
    U_, s_, _ = np.linalg.svd(Fw, full_matrices=False); keep = s_ > 1e-12; gf.append(U_[:, keep] * s_[keep])
gamma_op = lambda w: gf[w] @ gf[w].conj().T
def gsum(ws):
    Fm = np.concatenate([gf[w] for w in ws], axis=1); return Fm @ Fm.conj().T
e6 = max(np.abs(gsum([w for w in range(len(V2)) if cl2[w] == z]) - rho).max() for z in range(36))
e7 = 0.0
for w in range(len(V2)):
    for w2 in range(len(V2)):
        if cl2[w] != cl2[w2] and CONF2[w, w2]:
            e7 = max(e7, (np.abs(gf[w].conj().T @ gf[w2]) ** 2).sum())
print(f'(d) (6): max|sum_C gamma - rho| = {e6:.2e}; (7): max Tr(gamma_w gamma_w\') = {e7:.2e}')
ok &= e6 < 1e-10 and e7 < 1e-10

# (e) slicing: coordinate 1 with z2 fixed, and coordinate 2 with z1 fixed
def check_oneshot(bt, label):
    # bt[z][v] = operator for v in clique z
    s = max(np.abs(sum(bt[z][v] for v in bt[z]) - rho).max() for z in range(k))
    e = 0.0
    for z in range(k):
        for z2 in range(k):
            if z == z2: continue
            for v in bt[z]:
                for v2 in bt[z2]:
                    if ADJ[v, v2]:
                        e = max(e, abs((bt[z][v] * bt[z2][v2].T).sum()))
    print(f'(e) {label}: max|sum_v beta~ - rho| = {s:.2e}; max zero-error violation = {e:.2e}')
    return s, e
sliced_codes = []
for fixed in range(k):
    bt1 = {z: {} for z in range(k)}; bt2 = {z: {} for z in range(k)}
    for z in range(k):
        for v in range(nv):
            if clique[v] != z: continue
            bt1[z][v] = gsum([v * nv + v2 for v2 in range(nv) if clique[v2] == fixed])
            bt2[z][v] = gsum([v1 * nv + v for v1 in range(nv) if clique[v1] == fixed])
    s1, e1_ = check_oneshot(bt1, f'slice coord1 | z2={fixed}')
    s2, e2_ = check_oneshot(bt2, f'slice coord2 | z1={fixed}')
    ok &= max(s1, e1_, s2, e2_) < 1e-10

# negative control 1: drop one message (non-saturating, 35 messages): common state lost in (6)
drop = 7
def gsum35(ws):
    Fm = np.concatenate([BF[(mi, w)] for w in ws for mi in range(36) if mi != drop and (mi, w) in BF], axis=1); return Fm @ Fm.conj().T
e6n = max(np.abs(gsum35([w for w in range(len(V2)) if cl2[w] == z]) - rho).max() for z in range(36))
print(f'NEG1 35-message subcode: max_z |sum_C gamma - rho| = {e6n:.3e} (nonzero => common state lost)')
# negative control 2: slicing with per-message (not message-summed) operators violates sum-to-rho
bt_bad = {z: {v: sum(op(BF[(0, v * nv + v2)]) for v2 in range(nv) if clique[v2] == 0 and (0, v * nv + v2) in BF) for v in range(nv) if clique[v] == z} for z in range(k)}
sbad = max(np.abs(sum(bt_bad[z][v] for v in bt_bad[z]) - rho).max() for z in range(k))
print(f'NEG2 per-message slice: max|sum - rho| = {sbad:.3e} (nonzero => message-summing is essential)')

# (f) theta vector bound (item 7): Naimark + w_x = sum_i P^i_x psi, on the first sliced one-shot code
def theta_vectors(msg_ops, nin, ADJm, rho):
    """msg_ops[i][x] = R_{i,x}. Pure resource |sqrt rho>> (Bob x Alice), Alice effects G^T, G = rho^-1/2 R rho^-1/2.
    Naimark: isometry Viso_i phi = sum_x sqrt(G^T_x) phi (x) |x>, completed to a unitary; P^i_x = U^* (I (x) |x><x|) U.
    w_x = sum_i (I (x) P^i_x) psi'.  Check w_x orthogonal on edges and sum_x |<psi',w_x>|^2/|w_x|^2 = m."""
    d = rho.shape[0]
    vals, vecs = np.linalg.eigh(rho); rih = vecs @ np.diag(vals ** -0.5) @ vecs.conj().T; rh = vecs @ np.diag(vals ** 0.5) @ vecs.conj().T
    dn = d * nin
    Psi_e = np.zeros((d, dn), complex); Psi_e[:, 0::nin] = rh      # psi (x) |0>_ancilla, rows Bob, cols (a, x)
    wx = np.zeros((nin, d, dn), complex)
    for i, ops in enumerate(msg_ops):
        Ga = [(rih @ ops[x] @ rih).T if x in ops else np.zeros((d, d), complex) for x in range(nin)]
        Viso = np.zeros((dn, d), complex)
        for x in range(nin):
            ev, evec = np.linalg.eigh((Ga[x] + Ga[x].conj().T) / 2); ev = np.clip(ev, 0, None)
            Viso[x::nin, :] = evec @ np.diag(np.sqrt(ev)) @ evec.conj().T
        assert np.allclose(Viso.conj().T @ Viso, np.eye(d), atol=1e-8)
        Q, _ = np.linalg.qr(np.concatenate([Viso, rng.normal(size=(dn, dn - d)) + 1j * rng.normal(size=(dn, dn - d))], axis=1))
        Ufull = np.concatenate([Viso, Q[:, d:]], axis=1)
        Jcols = [a * nin for a in range(d)]; rest = [c for c in range(dn) if c not in set(Jcols)]
        Uperm = np.zeros_like(Ufull); Uperm[:, Jcols + rest] = Ufull      # Uperm (e_a (x) |0>) = Viso e_a
        assert np.allclose(Uperm.conj().T @ Uperm, np.eye(dn), atol=1e-8)
        A1 = Psi_e @ Uperm.T                                                # (I (x) U) psi' as a d x dn matrix
        Uc = Uperm.conj()
        for x in range(nin):
            idx = np.arange(x, dn, nin)
            wx[x] += A1[:, idx] @ Uc[idx, :]                                # (I (x) U^* P_x U) psi'
    wv = wx.reshape(nin, -1); pv = Psi_e.reshape(-1)
    nrm = np.linalg.norm(wv, axis=1); ov = wv.conj() @ pv
    S = sum(abs(ov[x]) ** 2 / nrm[x] ** 2 for x in range(nin) if nrm[x] > 1e-12)
    G = wv.conj() @ wv.T
    orth = max((abs(G[x, y]) for x in range(nin) for y in range(nin) if ADJm[x, y]), default=0.0)
    return S, orth
# one-shot sliced code on H (6 messages), receiver state rho (dim 192) -- too big for Naimark loops; use a compressed copy:
# compress to support blocks is not needed: build a fresh one-shot code with a non-ME state of small dimension instead.
q = 0.25
rho_s = np.diag([q / 4] * 4 + [(1 - q) / 4] * 4).astype(complex)
Wb = haar(4); Us = haar(8)
def Ts(x):
    return np.kron(np.diag([1, 0]), T1[x]) * q * 4 / 4 * 1 + np.kron(np.diag([0, 1]), Wb @ T1[x] @ Wb.conj().T) * (1 - q)
for z in range(k):
    assert np.allclose(sum(Ts(x) for x in range(nv) if clique[x] == z), rho_s)
# Latin register so each message uses all cliques
Lr = lambda i, z: (i + 5 * z + 1) % 6   # Latin square on Z_6
assert all(len({Lr(i, z) for i in range(6)}) == 6 for z in range(6)) and all(len({Lr(i, z) for z in range(6)}) == 6 for i in range(6))
rho_l = np.kron(Us @ rho_s @ Us.conj().T, np.eye(6) / 6)
msg_ops = []
for i in range(6):
    ops = {}
    for x in range(nv):
        e = np.zeros((6, 6)); e[Lr(i, clique[x]), Lr(i, clique[x])] = 1 / 6
        ops[x] = np.kron(Us @ Ts(x) @ Us.conj().T, e)
    msg_ops.append(ops)
# sanity: code conditions
assert max(np.abs(sum(msg_ops[i].values()) - rho_l).max() for i in range(6)) < 1e-10
zev = max(abs(np.trace(msg_ops[i][x] @ msg_ops[j][y])) for i in range(6) for j in range(6) if i != j for x in range(nv) for y in range(nv) if CONF[x, y])
print('(f) one-shot Latin code on H (48-dim non-ME receiver, messages use all cliques): zero-error violation', zev)
S, orth = theta_vectors(msg_ops, nv, ADJ, rho_l)
print(f'(f) theta vectors: sum |<psi,w_x>|^2/|w_x|^2 = {S:.10f} (m=6); max |<w_x,w_y>| over edges = {orth:.2e}')
ok &= abs(S - 6) < 1e-8 and orth < 1e-8 and zev < 1e-10
try:
    import cvxpy as cp
    Bv = cp.Variable((nv, nv), symmetric=True)
    cons = [Bv >> 0, cp.trace(Bv) == 1] + [Bv[x, y] == 0 for x in range(nv) for y in range(x + 1, nv) if ADJ[x, y]]
    pr = cp.Problem(cp.Maximize(cp.sum(Bv)), cons); pr.solve(solver=cp.CLARABEL)
    print(f'(f) theta(H_magic) by SDP = {pr.value:.6f}; classical alpha(H) =', nx.max_weight_clique(nx.complement(nx.from_numpy_array(ADJ.astype(int))), weight=None)[1])
except Exception as ex:
    print('SDP skipped', ex)

# (g) entropy identity (22)/(23) on a 20-message subcode and the full 36-message code of H^{strong 2}
def S_vn(M):
    v = np.linalg.eigvalsh((M + M.conj().T) / 2); v = v[v > 1e-14]; return float(-(v * np.log2(v)).sum())
def H_cl(pv):
    pv = np.asarray([x for x in pv if x > 1e-15]); return float(-(pv * np.log2(pv)).sum())
for msub in [36, 20, 9]:
    sub = sorted(rng.choice(36, size=msub, replace=False)) if msub < 36 else list(range(36))
    m = len(sub)
    pq = np.zeros(36); rq = [np.zeros((D, D), complex) for _ in range(36)]
    HQMB = 0.0; pairs = []
    for mi in sub:
        for z in range(36):
            s = sigma_of(mi, z); t = np.trace(s).real
            if t < 1e-14: continue
            pq[z] += t / m; rq[z] += s / m; pairs.append(t / m)
            HQMB += (t / m) * S_vn(s / t)
    HQMB += H_cl(pairs)                           # H(QMB) for cq state
    HMB = math.log2(m) + S_vn(rho)
    H_Q_given_MB = HQMB - HMB
    IQB = S_vn(rho) - sum(pq[z] * S_vn(rq[z] / pq[z]) for z in range(36) if pq[z] > 1e-14)
    Dpu = 2 * math.log2(k) - H_cl(pq)
    lhs = 2 * math.log2(k) - math.log2(m)
    rhs = Dpu + IQB + H_Q_given_MB
    # Pinsker check: ||Omega_QB - u (x) rho||_1
    tn = sum(np.abs(np.linalg.eigvalsh(rq[z] - rho / 36)).sum() for z in range(36))
    print(f'(g) m={m}: n*delta={lhs:.10f}; D(p_Q||u)={Dpu:.6f} I(Q:B)={IQB:.6f} H(Q|MB)={H_Q_given_MB:.6f}; sum={rhs:.10f}; '
          f'||Omega-u(x)rho||_1={tn:.4f} <= sqrt(2ln2 n delta)={math.sqrt(2*math.log(2)*lhs):.4f}')
    ok &= abs(lhs - rhs) < 1e-8 and tn <= math.sqrt(2 * math.log(2) * lhs) + 1e-8 and H_Q_given_MB > -1e-9
# even parity & rho vs rho^2
n = 6; ev = [s for s in itertools.product([0, 1], repeat=n) if sum(s) % 2 == 0]
Dp = n - math.log2(len(ev))
print('(g) even parity n=6: D(p||u) =', Dp, '; H(Q_j|Q_-j)=0 since parity fixes Q_j')
for eps, d in [(0.01, 10), (0.01, 10**4), (0.01, 10**8)]:
    w2 = eps ** 2 / (eps ** 2 + (1 - eps) ** 2 / d)
    print(f'(g) rho-vs-rho^2: eps={eps}, d={d}: rho-weight {eps}, rho^2-weight {w2:.6f}')
print('ALL OK' if ok else 'FAILURE')

assert ok, "capacity slicing or rate identity check failed"
