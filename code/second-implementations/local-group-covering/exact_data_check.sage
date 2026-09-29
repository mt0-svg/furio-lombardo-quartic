# exact_data_check.sage: consistency of the exact inputs over K21 (no p-adic computation).
#  (1) Q1 Q3 - Q2^2 = c F for a constant c in K21;
#  (2) the export sextic f_k equals -delta_k det(M1 + 2 t M2 + t^2 M3) (Bruin's model of F_delta);
#  (3) the lifts x_i lie on D_delta, and the exported phi_i equal the phi(x_i) of exact_global_data.sage;
#  (4) the pullback matrices A of pullback_known_lifts.gp: shape, equality at x_a, x_b; c_1 of the export = first TINY terms.
# Run from code/second-implementations/local-group-covering: sage exact_data_check.sage
import time
load('exact_data.sage')
t0 = time.time()
X = s3_exact(); K = X['K']
print('K21 degree', K.degree(), '; data loaded in %.1fs' % (time.time() - t0))
R3 = X['R3']; x, y, z = R3.gens()
Q1, Q2, Q3 = X['Q']
G = Q1 * Q3 - Q2^2
c = G.monomial_coefficient(x^4) / X['Fq'].monomial_coefficient(x^4)
print('(1) Q1 Q3 - Q2^2 == c F:', G == c * X['Fq'], '; c nonzero:', c != 0)
def gram(q):
    a, b_, c_, d, e, f = q
    return matrix(K, [[a, b_/2, c_/2], [b_/2, d, e/2], [c_/2, e/2, f]])
M = [gram(q) for q in X['Qc']]
Rt = PolynomialRing(K, 't'); t = Rt.gen()
Mt = M[0].change_ring(Rt) + 2*t*M[1].change_ring(Rt) + t^2*M[2].change_ring(Rt)
detM = Mt.det()
for k in [0, 1]:
    dl = X['delta'][k]
    fB = -dl * detM
    fE = Rt(X['tw'][k]['f'])
    print('(2) k = %d: export f == -delta det(M_t): %s; degree %d' % (k, fE == fB, fE.degree()))
    if fE != fB:
        print('    ratio of leading coefficients', fE.leading_coefficient() / fB.leading_coefficient())
v5 = lambda P: vector(K, P)
for i, ph in sorted(X['PHI'].items()):
    k = ph['k']; dl = X['delta'][k]
    P = ph['x']
    qv = [q(P[0], P[1], P[2]) for q in X['Q']]
    onD = (qv[0] == dl * P[3]^2) and (qv[1] == dl * P[3] * P[4]) and (qv[2] == dl * P[4]^2)
    e = X['tw'][k]['phi'].get(i)
    same = None
    if e is not None:
        same = (e[0] == ph['U']) and (e[1] == ph['V'] or e[1] == [-t_ for t_ in ph['V']])
        sgn = 1 if e[1] == ph['V'] else -1
    print('(3) x_%d (k = %d): on D_delta %s; x_i =' % (i, k, onD), P[:3], '; export phi_%d equals refutM5_10 phi(x_%d): %s (sign %s)' % (i, i, same, sgn if same else None))
TI = s3_tiny(X)
for i in sorted(TI):
    A = TI[i]['A']; k = TI[i]['k']
    c1 = X['tw'][k]['c1'][i]
    print('(4) x_%d: A antidiagonal: %s; a12 = 0: %s, a21 = 0: %s; c1 == (w0_0, w1_0): %s; number of terms %d' %
          (i, A[0, 0] == 0 and A[1, 1] == 0, A[0, 1] == 0, A[1, 0] == 0, c1 == (TI[i]['w0'][0], TI[i]['w1'][0]), len(TI[i]['w0'])))
print('(4) A(x0) == A(x2):', TI[0]['A'] == TI[2]['A'], '; A(x1) == A(x3):', TI[1]['A'] == TI[3]['A'])
print('total %.1fs' % (time.time() - t0))
