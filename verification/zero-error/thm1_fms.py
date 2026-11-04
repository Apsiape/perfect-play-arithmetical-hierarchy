"""Exact-ish (float64, tol 1e-12) check of Theorem 1 on the flagged magic square (FMS)
and on the plain Mermin-Peres magic square.

Theorem 1 (claim): channel N_Gamma(G) with confusability graph Gamma(G); k = |U|+|V|.
  ZE_qs(N_Gamma(G), k)  <=>  G has a perfect pure strategy with Tr D < infinity.
Forward map: rho = D/Tr D, R_{c,(c,a)} = D^1/2 E_{c,a} D^1/2 / Tr D.
Reverse map: B_{i,c} = sum_a R_{i,(c,a)} = rho P_{i,c};  M_{c,a} = sum_i R_{i,(c,a)};
             E_{c,a} = rho^-1/2 M_{c,a} rho^-1/2; strategy D_G = rho/||rho||_2.
Conventions: Bob's effects are stored in 'Alice-side' form G, actual Bob effect = G^T.
For coefficient matrix D (real diagonal), p(E,F=G^T) = Tr(D E D G); zero iff E D G = 0.
"""
import itertools, sys
import numpy as np
import networkx as nx

TOL = 1e-11
I2 = np.eye(2); X = np.array([[0, 1], [1, 0]], float); Z = np.diag([1., -1.])
Y = np.array([[0, -1j], [1j, 0]])
def kron(*a):
    out = np.array([[1.0]])
    for m in a:
        out = np.kron(out, m)
    return out

# magic square cells (rows i, cols j), canonical realization
SQ = [[kron(X, I2), kron(I2, X), kron(X, X)],
      [kron(I2, Z), kron(Z, I2), kron(Z, Z)],
      [kron(X, Z), kron(Z, X), kron(Y, Y)]]
for i in range(3):
    assert np.allclose(SQ[i][0] @ SQ[i][1] @ SQ[i][2], np.eye(4))
colsign = [1, 1, -1]
for j in range(3):
    assert np.allclose(SQ[0][j] @ SQ[1][j] @ SQ[2][j], colsign[j] * np.eye(4))

def triples(prod):
    return [t for t in itertools.product([1, -1], repeat=3) if t[0] * t[1] * t[2] == prod]

def joint_proj(obs, t):
    P = np.eye(obs[0].shape[0], dtype=complex)
    for O, s in zip(obs, t):
        P = P @ (np.eye(O.shape[0]) + s * O) / 2
    return P

def embed_magic(P4):
    """5-dim space: index 0 = flag f, 1..4 = magic C^4."""
    P = np.zeros((5, 5), complex); P[1:, 1:] = P4; return P

def build_fms():
    flag = np.zeros((5, 5), complex); flag[0, 0] = 1
    # Alice questions: R0,R1,R2 (answers f + 4 even triples), T0,T1
    # Bob questions: C0,C1,C2 (answers f + 4 triples of product colsign), B0,B1
    A_q, B_q = {}, {}
    for i in range(3):
        ans = {('f',): flag}
        for t in triples(1):
            ans[t] = embed_magic(joint_proj(SQ[i], t))
        A_q['R%d' % i] = ans
    for j in range(3):
        ans = {('f',): flag}
        col = [SQ[0][j], SQ[1][j], SQ[2][j]]
        for t in triples(colsign[j]):
            # Bob's actual effect is the transpose of the Alice-side projector; store Alice-side
            ans[t] = embed_magic(joint_proj(col, t))
        B_q['C%d' % j] = ans
    # column-zero vectors c_0=(+++), c_1=(+--); row-zero r_0=(+++), r_1=(+--)
    col0 = [SQ[0][0], SQ[1][0], SQ[2][0]]
    row0 = SQ[0]
    def vec_of(P):
        w, v = np.linalg.eigh(P); return v[:, np.argmax(w)]
    c = {t: vec_of(embed_magic(joint_proj(col0, t))) for t in triples(1)}
    r = {t: vec_of(embed_magic(joint_proj(row0, t))) for t in triples(1)}
    cx = [(1, 1, 1), (1, -1, -1)]
    ry = [(1, 1, 1), (1, -1, -1)]
    # fix phases so that <c_x, r_y> = (-1)^{xy}/sqrt2 and vectors real
    for d in (c, r):
        for t in d:
            v = d[t]; k = np.argmax(abs(v)); d[t] = v * np.conj(v[k]) / abs(v[k])
    # choose sign of r_1 so <c_1,r_1> = -1/sqrt2 and <c_0,r_y> = +1/sqrt2
    for y in range(2):
        if np.real(np.vdot(c[cx[0]], r[ry[y]])) < 0:
            r[ry[y]] = -r[ry[y]]
    if np.real(np.vdot(c[cx[1]], r[ry[0]])) < 0:
        c[cx[1]] = -c[cx[1]]
    for x in range(2):
        for y in range(2):
            assert abs(np.vdot(c[cx[x]], r[ry[y]]) - (-1) ** (x * y) / np.sqrt(2)) < 1e-12, (x, y)
    f = np.zeros(5, complex); f[0] = 1
    for x in range(2):
        ans = {}
        Xx = np.outer(f, c[cx[x]].conj()) + np.outer(c[cx[x]], f.conj())
        S = np.outer(f, f.conj()) + np.outer(c[cx[x]], c[cx[x]].conj())
        ans[('+',)] = (S + Xx) / 2; ans[('-',)] = (S - Xx) / 2
        for t in triples(1):
            if t != cx[x]:
                ans[t] = np.outer(c[t], c[t].conj())
        A_q['T%d' % x] = ans
    for y in range(2):
        ans = {}
        Yy = np.outer(f, r[ry[y]].conj()) + np.outer(r[ry[y]], f.conj())
        S = np.outer(f, f.conj()) + np.outer(r[ry[y]], r[ry[y]].conj())
        ans[('+',)] = (S + Yy) / 2; ans[('-',)] = (S - Yy) / 2
        for t in triples(1):
            if t != ry[y]:
                ans[t] = np.outer(r[t], r[t].conj())
        B_q['B%d' % y] = ans
    # the c- and r- vectors are real, so the Alice-side form of Bob's T/B effects equals its transpose
    # predicate
    def V(u, a, v, b):
        if u[0] == 'R' and v[0] == 'C':
            i, j = int(u[1]), int(v[1])
            if (a == ('f',)) != (b == ('f',)):
                return 0
            if a == ('f',):
                return 1
            return int(a[j] == b[i])
        if u[0] == 'T' and v == 'C0':
            x = int(u[1])
            if a in [('+',), ('-',)]:
                return int(b == ('f',) or b == cx[x])
            return int(a == b)
        if u == 'R0' and v[0] == 'B':
            y = int(v[1])
            if b in [('+',), ('-',)]:
                return int(a == ('f',) or a == ry[y])
            return int(a == b)
        if u[0] == 'T' and v[0] == 'B':
            x, y = int(u[1]), int(v[1])
            if a in [('+',), ('-',)] and b in [('+',), ('-',)]:
                sa = 1 if a == ('+',) else -1; sb = 1 if b == ('+',) else -1
                return int(sa * sb == (-1) ** (x * y))
            return 1
        return 1
    D = np.diag([1 / 3] + [np.sqrt(2) / 3] * 4).astype(complex)
    return A_q, B_q, V, D

def build_ms():
    A_q, B_q = {}, {}
    for i in range(3):
        A_q['R%d' % i] = {t: joint_proj(SQ[i], t) for t in triples(1)}
    for j in range(3):
        col = [SQ[0][j], SQ[1][j], SQ[2][j]]
        B_q['C%d' % j] = {t: joint_proj(col, t) for t in triples(colsign[j])}
    def V(u, a, v, b):
        i, j = int(u[1]), int(v[1]); return int(a[j] == b[i])
    D = np.eye(4, dtype=complex) / 2
    return A_q, B_q, V, D

def psd_check(M):
    return np.min(np.linalg.eigvalsh((M + M.conj().T) / 2)) > -TOL

def verify_strategy(A_q, B_q, V, D):
    worst = 0
    for u, Ea in A_q.items():
        assert np.allclose(sum(Ea.values()), np.eye(D.shape[0])), u
    for v, Gb in B_q.items():
        assert np.allclose(sum(Gb.values()), np.eye(D.shape[0])), v
    for u, Ea in A_q.items():
        for v, Gb in B_q.items():
            for a, E in Ea.items():
                for b, G in Gb.items():
                    if not V(u, a, v, b):
                        p = np.real(np.trace(D.conj().T @ E @ D @ G))
                        worst = max(worst, abs(p), np.max(abs(E @ D @ G)))
    return worst

def game_graph(A_q, B_q, V):
    verts = [('L', u, a) for u in A_q for a in A_q[u]] + [('R', v, b) for v in B_q for b in B_q[v]]
    Gr = nx.Graph(); Gr.add_nodes_from(verts)
    for x, y in itertools.combinations(verts, 2):
        if x[0] == y[0] and x[1] == y[1]:
            Gr.add_edge(x, y)
        elif x[0] == 'L' and y[0] == 'R' and not V(x[1], x[2], y[1], y[2]):
            Gr.add_edge(x, y)
        elif x[0] == 'R' and y[0] == 'L' and not V(y[1], y[2], x[1], x[2]):
            Gr.add_edge(x, y)
    return Gr

def sqrtm_psd(M):
    w, v = np.linalg.eigh((M + M.conj().T) / 2); w = np.clip(w, 0, None)
    return (v * np.sqrt(w)) @ v.conj().T

def forward_code(A_q, B_q, D):
    """messages = tagged questions; R[i][x]"""
    Dh = sqrtm_psd(D); trD = np.real(np.trace(D))
    cliques = [('L', u) for u in A_q] + [('R', v) for v in B_q]
    R = {}
    for i in cliques:
        R[i] = {}
        ops = A_q[i[1]] if i[0] == 'L' else B_q[i[1]]
        for a, E in ops.items():
            R[i][(i[0], i[1], a)] = Dh @ E @ Dh / trD
    rho = D / trD
    return cliques, R, rho

def verify_code(Gr, R, rho, msgs):
    dim = rho.shape[0]; worst_sum = 0; worst_orth = 0
    for i in msgs:
        S = sum(R[i].values()); worst_sum = max(worst_sum, np.max(abs(S - rho)))
        for M in R[i].values():
            assert psd_check(M)
    verts = list(Gr.nodes)
    for i, j in itertools.permutations(msgs, 2):
        for x, Mx in R[i].items():
            for xp, Mxp in R[j].items():
                if x == xp or Gr.has_edge(x, xp):
                    worst_orth = max(worst_orth, np.max(abs(Mx @ Mxp)))
    return worst_sum, worst_orth

def supp_proj(M, tol=1e-10):
    w, v = np.linalg.eigh((M + M.conj().T) / 2); v = v[:, w > tol]; return v @ v.conj().T

def reverse(Gr, R, rho, msgs, cliques, ops_index):
    """returns diagnostics and the reconstructed strategy"""
    out = {}
    B = {(i, c): sum((M for x, M in R[i].items() if (x[0], x[1]) == c), np.zeros_like(rho)) for i in msgs for c in cliques}
    tot = sum(np.real(np.trace(Bm)) for Bm in B.values())
    out['sum_Tr_B'] = tot
    P = {key: supp_proj(Bm) for key, Bm in B.items()}
    out['max|B - rho P|'] = max(np.max(abs(B[key] - rho @ P[key])) for key in B)
    out['max|[P,rho]|'] = max(np.max(abs(P[key] @ rho - rho @ P[key])) for key in B)
    # rows (fixed i) and columns (fixed c) orthogonal and summing to identity on supp rho
    sp = supp_proj(rho)
    out['rows sum-to-I err'] = max(np.max(abs(sum(P[(i, c)] for c in cliques) - sp)) for i in msgs)
    out['cols sum-to-I err'] = max(np.max(abs(sum(P[(i, c)] for i in msgs) - sp)) for c in cliques)
    out['row orth err'] = max(np.max(abs(P[(i, c)] @ P[(i, cp)])) for i in msgs for c in cliques for cp in cliques if c != cp)
    out['col orth err'] = max(np.max(abs(P[(i, c)] @ P[(j, c)])) for c in cliques for i in msgs for j in msgs if i != j)
    # aggregated M
    Mca = {}
    for c in cliques:
        for a in ops_index[c]:
            x = (c[0], c[1], a)
            Mca[x] = sum((R[i][x] for i in msgs if x in R[i]), np.zeros_like(rho))
    w, v = np.linalg.eigh(rho)
    assert np.min(w) > 1e-12, 'test uses faithful rho'
    rmh = (v / np.sqrt(w)) @ v.conj().T
    E = {x: rmh @ Mx @ rmh for x, Mx in Mca.items()}
    for x in E:
        assert psd_check(E[x])
    for c in cliques:
        Ssum = sum(E[(c[0], c[1], a)] for a in ops_index[c])
        assert np.allclose(Ssum, np.eye(rho.shape[0]), atol=1e-9)
    DG = rho / np.linalg.norm(rho, 'fro')
    worst = 0
    for x in E:
        for y in E:
            if x[0] == 'L' and y[0] == 'R' and Gr.has_edge(x, y):
                worst = max(worst, np.max(abs(E[x] @ DG @ E[y])), abs(np.trace(DG @ E[x] @ DG @ E[y])))
    out['reconstructed losing max'] = worst
    out['Tr D_G'] = np.real(np.trace(DG))
    return out, E, DG

def run(name, builder):
    print('=' * 70); print(name)
    A_q, B_q, V, D = builder()
    print('dim', D.shape[0], '|U|,|V| =', len(A_q), len(B_q), ' Schmidt amplitudes', np.round(np.real(np.diag(D)), 6))
    w = verify_strategy(A_q, B_q, V, D)
    assert w < 1e-9, ('perfect strategy residual', w)
    print('perfect strategy: max losing sandwich/prob =', w)
    Gr = game_graph(A_q, B_q, V)
    k = len(A_q) + len(B_q)
    print('Gamma: %d vertices, %d edges, k = %d' % (Gr.number_of_nodes(), Gr.number_of_edges(), k))
    comp = nx.complement(Gr)
    alpha = max(len(cq) for cq in nx.find_cliques(comp))
    print('classical independence number alpha(Gamma) =', alpha, '(classical one-shot zero-error number)')
    cliques, R, rho = forward_code(A_q, B_q, D)
    ws, wo = verify_code(Gr, R, rho, cliques)
    assert max(ws, wo) < 1e-9, ('forward code', ws, wo)
    print('forward code: max|sum_x R_ix - rho| =', ws, ' max|R_ix R_jx\'| over i!=j, x~x\' =', wo)
    print('Tr D =', np.real(np.trace(D)), ' code marginal rho eigenvalues', np.round(np.linalg.eigvalsh(rho), 6))
    ops_index = {('L', u): list(A_q[u]) for u in A_q}; ops_index.update({('R', v): list(B_q[v]) for v in B_q})
    out, E, DG = reverse(Gr, R, rho, cliques, cliques, ops_index)
    assert all(val < 1e-8 for key, val in out.items() if key not in ['sum_Tr_B', 'Tr D_G']), out
    assert np.max(abs(DG @ DG - D @ D)) < 1e-9
    for kk, vv in out.items():
        print('  reverse:', kk, '=', vv)
    # marginal of reconstructed strategy equals original marginal
    print('  reconstructed marginal D_G^2 vs original D^2: max diff', np.max(abs(DG @ DG - D @ D)))
    # scrambled code: ancilla C^2 with a non-classical magic unitary built from noncommuting p,q
    n = 2
    th = 0.7
    p = np.array([[1, 0], [0, 0]], complex)
    vq = np.array([np.cos(th), np.sin(th)], complex); q = np.outer(vq, vq)
    kk = len(cliques)
    Q = [[np.zeros((n, n), complex) for _ in range(kk)] for _ in range(kk)]
    # block 0,1 uses p ; block 2,3 uses q ; rest identity permutation
    Q[0][0] = p; Q[0][1] = np.eye(n) - p; Q[1][0] = np.eye(n) - p; Q[1][1] = p
    Q[2][2] = q; Q[2][3] = np.eye(n) - q; Q[3][2] = np.eye(n) - q; Q[3][3] = q
    for t in range(4, kk):
        Q[t][t] = np.eye(n, dtype=complex)
    assert np.max(abs(p @ q - q @ p)) > 0.1
    msgs = list(range(kk))
    R2 = {}
    rho2 = np.kron(rho, np.eye(n) / n)
    for i in msgs:
        R2[i] = {}
        for ci, c in enumerate(cliques):
            if np.max(abs(Q[i][ci])) == 0:
                continue
            for x, Mx in R[c].items():
                R2[i][x] = np.kron(Mx, Q[i][ci] / n)
    ws, wo = verify_code(Gr, R2, rho2, msgs)
    assert max(ws, wo) < 1e-9, ('scrambled code', ws, wo)
    print('scrambled code (noncommutative magic unitary on ancilla): sum err', ws, ' orth err', wo)
    out2, E2, DG2 = reverse(Gr, R2, rho2, msgs, cliques, ops_index)
    assert all(val < 1e-8 for key, val in out2.items() if key not in ['sum_Tr_B', 'Tr D_G']), out2
    for kk2, vv in out2.items():
        print('  reverse(scrambled):', kk2, '=', vv)
    return dict(alpha=alpha, k=k)

if __name__ == '__main__':
    r1 = run('Mermin-Peres magic square', build_ms)
    r2 = run('Flagged magic square (Mancinska FMS, unconditional instance)', build_fms)

    assert r1 == dict(alpha=5, k=6), r1
    assert r2 == dict(alpha=9, k=10), r2
    print('PASS: both graph counts, forward maps, reverse maps and scrambled maps')
