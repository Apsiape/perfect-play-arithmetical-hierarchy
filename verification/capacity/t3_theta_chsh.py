"""Sanity: theta of the CHSH game graph (no perfect vector strategy) is < k = 4."""
import itertools, networkx as nx, cvxpy as cp
U=[0,1];V=[0,1]
G=nx.Graph()
for u in U:
    G.add_edge(('L',u,0),('L',u,1))
for v in V:
    G.add_edge(('R',v,0),('R',v,1))
for u in U:
    for v in V:
        for a in [0,1]:
            for b in [0,1]:
                if (a^b)!=(u&v): G.add_edge(('L',u,a),('R',v,b))
nodes=list(G.nodes()); ix={x:i for i,x in enumerate(nodes)}; N=len(nodes)
B=cp.Variable((N,N),symmetric=True)
cons=[B>>0,cp.trace(B)==1]+[B[ix[x],ix[y]]==0 for x,y in G.edges()]
pr=cp.Problem(cp.Maximize(cp.sum(B)),cons); pr.solve(solver=cp.CLARABEL)
print('theta(Gamma_CHSH) =', pr.value, '(k=4; 2+sqrt2 =', 2+2**0.5, ')')

assert pr.status == 'optimal' and abs(pr.value-(2+2**0.5)) < 1e-6
