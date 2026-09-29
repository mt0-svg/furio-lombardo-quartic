# completion_kv_eisenstein.sage: the completion K_v of K21 at pr = (2, prgen[2]) (e = 3, f = 1) as a Sage Eisenstein extension of Q_2,
# with a certified embedding K21 -> K_v, and certified square roots.
#
# Error model. A Sage p-adic element z with absolute precision n stands for the ball z + pi^n O_v. Sage propagates
# the precision of +, -, *, / by the ball rules (capped relative model), so a straight-line program returns balls
# that contain the exact results for all inputs in the input balls. Every other step (Hensel roots, square roots,
# series tails, branch decisions) is certified below by an explicit lemma, and its precision is set by hand.
#
# Field. E = characteristic polynomial of prgen[2] on the cubic factor g of K21 over Q_2 (only used to define the
# field; any Eisenstein E' = E mod 2^PREC defines the same ring O_v / 2^PREC). K_v = Q_2[pi]/(E).
# Embedding. R = a root of K21 found by Sage, lifted to the cap and certified by Hensel: v(K21(R)) > 2 v(K21'(R))
# gives a unique exact root r* with v(r* - R) >= v(K21(R)) - v(K21'(R)); r = R + O(pi^that). The map b -> r* is a
# field embedding K21 -> K_v; v(prgen2(r*)) = 1 is checked, so the closure of K21 is ramified of degree 3 over Q_2,
# hence equal to K_v, and pr lies in the prime of the induced valuation (pr is maximal), i.e. K_v is the completion
# at pr. K_v/Q_2 is a cubic totally ramified, tamely ramified, non-Galois extension (Q_2(mu_3) is unramified), so
# Aut(K_v/Q_2) = 1 and the embedding is unique.

def s3_setup(PREC, X):
    K21pol = X['K21pol']
    Q2 = Qp(2, PREC)
    fac = K21pol.change_ring(Q2).factor()
    degs = sorted(g.degree() for g, e in fac)
    assert degs == [3, 6, 12], degs
    g = [gg for gg, e in fac if gg.degree() == 3][0]
    g = g / g.leading_coefficient()
    Cm = companion_matrix(g, format='right')
    pgq = X['pg'].polynomial()
    Mpi = sum((Q2(pgq[i]) * Cm**i for i in range(pgq.degree() + 1)), matrix(Q2, 3, 3))
    E = Mpi.charpoly('y')
    # E with rational (dyadic) coefficients, checked Eisenstein
    Eq = PolynomialRing(QQ, 'y')([QQ(E[i].lift()) if not E[i].is_zero() else 0 for i in range(3)] + [1])
    assert all(Eq[i].valuation(2) >= 1 for i in range(3)) and Eq[0].valuation(2) == 1, 'E not Eisenstein'
    Kv = Q2.extension(Eq.change_ring(Q2), names='pi'); pi = Kv.gen()
    cap = Kv.precision_cap()
    rts = [rr for rr, m in K21pol.change_ring(Kv).roots() if pgq(rr).valuation() > 0]
    assert len(rts) == 1
    R = rts[0].lift_to_precision()
    fR = K21pol.change_ring(Kv)(R); dR = K21pol.derivative().change_ring(Kv)(R)
    v1 = vlb(fR); v2 = vex(dR)
    assert v1 > 2 * v2, 'Hensel certificate of the root of K21 fails'
    r = R.add_bigoh(v1 - v2)
    vpg = vex(pgq.change_ring(Kv)(r))
    assert vpg == 1, 'prgen2 is not a uniformizer'
    def emb(zK, prec=None):
        # z in K21 (Sage number field element) -> K_v by Horner at r
        lst = zK.polynomial().list()
        acc = Kv(0)
        for cf in reversed(lst):
            acc = acc * r + Kv(cf)
        if prec is not None:
            acc = acc.add_bigoh(prec)
        return acc
    info = dict(Eq=Eq, v_K21_R=v1, v_dK21_R=v2, r_prec=v1 - v2, v_pg_r=vpg,
                pg_minus_pi=vlb(pgq.change_ring(Kv)(r) - pi))
    return dict(PREC=PREC, Q2=Q2, Kv=Kv, pi=pi, r=r, emb=emb, cap=cap, info=info)

def pipow(K, n):
    pi = K.uniformizer(); n = ZZ(n)
    return pi**n if n >= 0 else 1 / pi**(-n)

def csqrt(a):
    # certified square root of the ball a in K_v (a certified nonzero). Returns r with r^2 in the ball and the
    # precision of r such that every exact element a* of the ball has a square root in r + O(pi^prec(r)), or None
    # when a is not a square (decided from a mod pi^(v(a) + 2e + 1), certified by the precision of a).
    # Lemma (Hensel): if v(r0^2 - a*) > 2 v(2 r0), there is a unique root r* of X^2 = a* with v(r* - r0) >=
    # v(r0^2 - a*) - v(2 r0). Here v(r0^2 - a*) >= vlb(r0^2 - a) computed with the ball a.
    K = a.parent(); pi = K.uniformizer(); e = K.absolute_e()
    va = ZZ(vex(a))
    if va % 2:
        return None
    eps = a / pipow(K, va)
    if eps.precision_relative() < 2 * e + 1:
        raise ValueError('square class undetermined at this precision')
    x0 = None
    for cs in cartesian_product([[0, 1]] * e):
        c = 1 + sum(cs[i - 1] * pi**i for i in range(1, e + 1))
        if (c * c - eps).valuation() >= 2 * e + 1:
            x0 = c; break
    if x0 is None:
        return None
    r0 = (x0 * pipow(K, va // 2)).lift_to_precision()
    for _ in range(24):
        r0 = ((r0 + a / r0) / 2).lift_to_precision()
    d = r0 * r0 - a
    vd = vlb(d); v2r = e + va // 2
    assert vd > 2 * v2r, 'square root certificate fails'
    return r0.add_bigoh(vd - v2r)
