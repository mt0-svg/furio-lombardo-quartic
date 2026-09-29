# rank_bound_q23.sage: Q_23-coordinates of the logs of phi(x_i) in Lie Res_{K21/Q} Jac(F_delta) (Q_23)
# = direct sum over the 13 places v of K_v^2 (dimension 42), and a rank lower bound for P_delta(K21).
# K_v = Q_23(r_v), r_v the root of K21 above v; x in K_v has coordinates c_j with x = sum_j c_j r_v^j (j < f_v),
# obtained from the traces Tr_{K/Q_23}(x r_v^i) (K the working field, K_v inside K), with a residual check.
# If the logs of phi(x_a), phi(x_b) (same twist) are Q_23-linearly independent, then phi(x_a), phi(x_b) are
# Z-independent in P_delta(K21) (log is a homomorphism killing only torsion on a finite index subgroup).
# Run from code/earlier-computations: sage rank_bound_q23.sage
import sys
import os
p = ZZ(os.environ.get("CHAB_P", "23"))   # the Chabauty prime (default 23; environment variable CHAB_P)
SUF = "" if p == 23 else "_p%d" % p
res = load("logs_q23" + SUF + ".sobj")
failures = []

def check(cond, msg):
    print(("PASS " if cond else "FAIL ") + msg); sys.stdout.flush()
    if not cond: failures.append(msg)

def qp_coords(x, r, fv):
    K = x.parent()
    if K.degree() == 1:
        assert fv == 1
        return [x]
    Qp_ = K.base_ring()
    tr = lambda z: z.trace()
    Mt = matrix(Qp_, fv, fv, [tr(r**(i + j)) for i in range(fv) for j in range(fv)])
    bt = vector(Qp_, [tr(x * r**i) for i in range(fv)])
    c = Mt.solve_right(bt)
    back = sum(K(c[j]) * r**j for j in range(fv))
    d = back - x
    if d != 0 and d.valuation() < min(x.precision_absolute(), 30) - 5:
        raise ValueError("qp_coords: x not in Q_p(r) (residual p^%d)" % d.valuation())
    return list(c)

places = sorted(set(d['place'] for d in res))
vec = {}
for i in range(4):
    v = []
    for pl in places:
        d = [e for e in res if e['place'] == pl and e['i'] == i][0]
        for kk in range(2):
            v += qp_coords(d['Lval'][kk], d['root'], d['fv'])
    vec[i] = v
    print("x%d: log vector of length %d, min valuation %d, min absolute precision %d" % (i, len(v), min(c.valuation() for c in v), min(c.precision_absolute() for c in v)))
check(all(len(vec[i]) == 42 for i in range(4)), "log vectors have dimension 42 = 2 [K21 : Q]")
Qp_ = Qp(p, prec=100)
for (a, b_, tw) in [(0, 2, 0), (1, 3, 1)]:
    Mab = matrix(Qp_, 2, 42, [Qp_(c) for c in vec[a]] + [Qp_(c) for c in vec[b_]])
    # 2x2 minors: independence certified by one minor of valuation below the working precision
    best = None
    for j1 in range(42):
        for j2 in range(j1 + 1, 42):
            mnr = Mab[0, j1] * Mab[1, j2] - Mab[0, j2] * Mab[1, j1]
            if mnr != 0 and (best is None or mnr.valuation() < best[0]):
                best = (mnr.valuation(), mnr.precision_absolute(), j1, j2)
    check(best is not None and best[0] < best[1], "twist delta%d: log phi(x%d), log phi(x%d) are Q_%d-independent (a 2x2 minor of valuation %s, known to p^%s): rank P_delta%d(K21) >= 2" % (tw, a, b_, p, best[0] if best else None, best[1] if best else None, tw))
save(vec, "rank_bound_q23" + SUF + ".sobj")
print("RESULT", "PASS" if not failures else "FAIL")
