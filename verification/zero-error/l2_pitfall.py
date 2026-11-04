"""Show the l1 normalization rho = D/Tr D is load-bearing: the naive code built from the
actual marginal rho_A = D^2 (R = D E D) violates zero-error orthogonality for the FMS game."""
import numpy as np, itertools
from thm1_fms import build_fms, game_graph, verify_code
A_q, B_q, V, D = build_fms()
Gr = game_graph(A_q, B_q, V)
cl = [('L', u) for u in A_q] + [('R', v) for v in B_q]
R = {}
for i in cl:
    ops = A_q[i[1]] if i[0] == 'L' else B_q[i[1]]
    R[i] = {(i[0], i[1], a): D @ E @ D for a, E in ops.items()}
rho = D @ D
ws, wo = verify_code(Gr, R, rho, cl)
print('naive code from rho_A = D^2: sum err', ws, ' max orthogonality violation', wo)

assert ws < 1e-9 and wo > 1e-4, (ws, wo)
print('PASS: naive marginal negative control fails orthogonality as required')
