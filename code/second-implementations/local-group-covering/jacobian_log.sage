# jacobian_log.sage: logarithms on A(K_v) = Jac(F_delta)(K_v) and coordinates, on top of genus2_log.sage.
# log D = log(N D)/N with N = 45045 * 2^j (jlog of genus2_log.sage); the tiny integral carries an explicit tail bound.
# A pair (U, V) given with Sage precision stands for a ball; the returned log is a ball that contains log D* for the
# genuine point D* in the input ball that the computation is about (the ring operations of the group law and of the
# tiny integral propagate the precision; the tail and the branch are certified in genus2_log.tiny).

ODD = 45045                   # odd part of NM = 180180 (the odd torsion multiplier)

def s3_log(f, D, T_goal, mu=8, m=ODD):
    r = jlog(f, D, m, T_goal, mu_target=mu)
    return r['logD'], r

def z2c(z, e=3):
    # z in K_v -> [(a_i, n_i)] with z = sum a_i pi^i, a_i in Q_2 known modulo 2^n_i (n_i = ceil((n - i)/e), n the
    # absolute precision of z); a_i returned as rationals
    n = z.precision_absolute()
    if n == Infinity:
        n = 10**6            # exact zero
    if z.is_zero():
        return [(QQ(0), ceil((n - i) / e)) for i in range(e)]
    p = z.polynomial()
    out = []
    for i in range(e):
        ai = p[i] if i <= p.degree() else 0
        ni = ceil((n - i) / e)
        out.append((QQ(ai.lift()) if ai != 0 else QQ(0), ni))
    return out

def vec6c(l):
    return z2c(l[0]) + z2c(l[1])

def torsion_T(X, S, k):
    # T = [f2, 0], f2 the monic quadratic factor of f over K21 (exact factorisation)
    K = X['K']; Rt = PolynomialRing(K, 't')
    fK = Rt(X['tw'][k]['f'])
    fa = [g for g, e in fK.factor() if g.degree() == 2]
    assert len(fa) == 1 and fK.degree() == 6
    g = fa[0] / fa[0].leading_coefficient()
    Kv = S['Kv']
    return ((S['emb'](g[0]), S['emb'](g[1])), (Kv(0), Kv(0)))
