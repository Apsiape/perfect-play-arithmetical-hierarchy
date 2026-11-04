"""Section 1 + Section 2 checks.
S1: strong product of a game graph vs OR / AND repetition game graphs (CHSH, n=2).
S2: G_t = anchored always-reject game; Gamma = K_{t,1} + 2K_1, k=t+3;
    exact alpha(Gamma^{strong n}) == (k-1)^n, clique cover k-1, theta(Gamma)=k-1,
    Bernoulli density, exponent (3).
"""
import itertools, math, sys
import networkx as nx
import numpy as np
import cvxpy as cp

def game_graph(U, V, A, B, lose, supp):
    """Mancinska/our-paper game graph. lose(u,v,a,b) True if losing; supp(u,v) positive prob."""
    G = nx.Graph()
    for u in U:
        for a in A[u]:
            G.add_node(('L', u, a))
    for v in V:
        for b in B[v]:
            G.add_node(('R', v, b))
    for u in U:
        for a, a2 in itertools.combinations(A[u], 2):
            G.add_edge(('L', u, a), ('L', u, a2))
    for v in V:
        for b, b2 in itertools.combinations(B[v], 2):
            G.add_edge(('R', v, b), ('R', v, b2))
    for u in U:
        for v in V:
            if not supp(u, v):
                continue
            for a in A[u]:
                for b in B[v]:
                    if lose(u, v, a, b):
                        G.add_edge(('L', u, a), ('R', v, b))
    return G

def conf(G, x, y):
    return x == y or G.has_edge(x, y)

def strong_power(G, n):
    H = nx.Graph()
    nodes = list(G.nodes())
    verts = list(itertools.product(nodes, repeat=n))
    H.add_nodes_from(verts)
    for x, y in itertools.combinations(verts, 2):
        if all(conf(G, a, b) for a, b in zip(x, y)):
            H.add_edge(x, y)
    return H

def alpha(G):
    C = nx.complement(G)
    c, w = nx.max_weight_clique(C, weight=None)
    return w

def theta(G):
    nodes = list(G.nodes()); idx = {v: i for i, v in enumerate(nodes)}; N = len(nodes)
    B = cp.Variable((N, N), symmetric=True)
    cons = [B >> 0, cp.trace(B) == 1]
    for x, y in G.edges():
        cons.append(B[idx[x], idx[y]] == 0)
    prob = cp.Problem(cp.Maximize(cp.sum(B)), cons)
    prob.solve(solver=cp.CLARABEL)
    return prob.value

ok = True
# ---------------- S1: CHSH -----------------
U = [0, 1]; V = [0, 1]; A = {u: [0, 1] for u in U}; Bans = {v: [0, 1] for v in V}
lose = lambda u, v, a, b: (a ^ b) != (u & v)
G = game_graph(U, V, A, Bans, lose, lambda u, v: True)
H2 = strong_power(G, 2)
# induced subgraph on all-Alice / all-Bob strings
allA = [x for x in H2.nodes() if all(c[0] == 'L' for c in x)]
allB = [x for x in H2.nodes() if all(c[0] == 'R' for c in x)]
S = H2.subgraph(allA + allB)
# OR-repetition game graph: questions U^2, V^2, answers A^2, lose iff every coordinate loses
U2 = list(itertools.product(U, U)); V2 = list(itertools.product(V, V))
A2 = {u: list(itertools.product([0, 1], [0, 1])) for u in U2}
B2 = {v: list(itertools.product([0, 1], [0, 1])) for v in V2}
lose_or = lambda u, v, a, b: all(lose(u[j], v[j], a[j], b[j]) for j in range(2))
lose_and = lambda u, v, a, b: any(lose(u[j], v[j], a[j], b[j]) for j in range(2))
Gor = game_graph(U2, V2, A2, B2, lose_or, lambda u, v: True)
# relabel S nodes to OR-graph labels
def lab(x):
    side = x[0][0]
    q = tuple(c[1] for c in x); a = tuple(c[2] for c in x)
    return (side, q, a)
Srel = nx.relabel_nodes(S, {x: lab(x) for x in S.nodes()})
same_or = set(map(frozenset, Srel.edges())) == set(map(frozenset, Gor.edges())) and set(Srel.nodes()) == set(Gor.nodes())
print('S1 induced all-Alice/all-Bob subgraph == OR-repetition game graph:', same_or)
ok &= same_or
Gand = game_graph(U2, V2, A2, B2, lose_and, lambda u, v: True)
print('S1 AND graph cliques u^n+v^n =', len(U2) + len(V2), '; alpha(AND graph) =', alpha(Gand), '>= max(u^n,v^n) =', max(len(U2), len(V2)))
ok &= alpha(Gand) >= max(len(U2), len(V2))
# also check zero-probability pairs handled: a game with a zero-probability pair
supp0 = lambda u, v: not (u == 1 and v == 1)
G0 = game_graph(U, V, A, Bans, lose, supp0)
H0 = strong_power(G0, 2)
S0 = nx.relabel_nodes(H0.subgraph([x for x in H0.nodes() if all(c[0] == 'L' for c in x) or all(c[0] == 'R' for c in x)]), lab)
Gor0 = game_graph(U2, V2, A2, B2, lose_or, lambda u, v: all(supp0(u[j], v[j]) for j in range(2)))
same0 = set(map(frozenset, S0.edges())) == set(map(frozenset, Gor0.edges()))
print('S1 (with a zero-probability question pair) still OR graph under product distribution:', same0)
ok &= same0

# ---------------- S2: G_t -----------------
def Gt_graph(t):
    # Alice questions 1..t plus anchor 'aA'; Bob question 1 plus anchor 'aB'; one answer each
    Uq = list(range(1, t + 1)) + ['aA']; Vq = [1, 'aB']
    Aa = {u: [0] for u in Uq}; Bb = {v: [0] for v in Vq}
    # always-reject base predicate; accept whenever an anchor appears
    lose_t = lambda u, v, a, b: (u != 'aA' and v != 'aB')
    return game_graph(Uq, Vq, Aa, Bb, lose_t, lambda u, v: True), len(Uq) + len(Vq)

for t in [1, 2, 3, 4]:
    Gt, k = Gt_graph(t)
    star_ok = (Gt.number_of_edges() == t) and sum(1 for v in Gt.nodes() if Gt.degree(v) == 0) == 2
    a1 = alpha(Gt)
    # clique cover number = chromatic number of complement
    cc = min(len(set(c.values())) for c in [nx.coloring.greedy_color(nx.complement(Gt), strategy=s) for s in ['largest_first', 'DSATUR', 'independent_set']])
    th = theta(Gt)
    print(f'S2 t={t} k={k}: K_(t,1)+2K_1 {star_ok}; alpha={a1} (k-1={k-1}); clique cover<= {cc}; theta={th:.6f}')
    ok &= star_ok and a1 == k - 1 and cc == k - 1 and abs(th - (k - 1)) < 1e-5
    for n in [2, 3]:
        if (t + 3) ** n > 130:
            continue
        Hn = strong_power(Gt, n)
        an = alpha(Hn)
        print(f'   n={n}: alpha(Gamma^n) = {an}, (k-1)^n = {(k-1)**n}, k^n = {k**n}')
        ok &= an == (k - 1) ** n
# value of G_t: P(at least one anchor) = 3/4 independent of answers
print('S2 omega(G_t)=1-(1/2)^2 =', 1 - 0.25)
# Bernoulli: k=2n+2 gives (1-1/k)^n > 1/2
bern = all((1 - 1 / (2 * n + 2)) ** n > 0.5 for n in range(1, 2000))
print('S2 (1-1/(2n+2))^n > 1/2 for n<2000:', bern); ok &= bern
for k in [4, 10, 100, 1000, 10**5]:
    pt = math.log(3 / 4) / math.log(1 - 1 / k)
    print(f'S2 (3): k={k} p_t >= {pt:.5f}, p_t/k = {pt / k:.6f}  (ln(4/3)={math.log(4/3):.6f})')
print('ALL OK' if ok else 'FAILURE')
