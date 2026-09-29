# abel_prym.sage: points of C(Q_2) from the disc data, their lifts to D_delta(K_v), and Bruin's Abel-Prym map
# phi : D_delta -> Jac(F_delta) over K_v (arXiv math/0408069, Lemma phimap and Proposition Demb).
#
# Model (checked exactly over K21 by exact_data_check.sage):
#   C : Q1 Q3 - Q2^2 = c F,  D_delta : Q1 = delta r^2, Q2 = delta r s, Q3 = delta s^2 in P^4 (x, y, z, r, s),
#   F_delta : Y^2 = f(t) = -delta det(M1 + 2 t M2 + t^2 M3), M_i the Gram matrices of Q_i.
#   QD_i = diag(M_i, -delta E_i), E_1 = diag(1, 0), E_2 = [[0, 1/2], [1/2, 0]], E_3 = diag(0, 1).
# phi(P), P in D: T a tangent vector of D at P not proportional to P; a_i = T' QD_i T; the t-coordinates of the two
# points of phi(P) are the roots of U = t^2 + 2 (a2/a3) t + a1/a3 (Lemma phimap (iii)); at a root t0 the quadric
# QD_1 + 2 t0 QD_2 + t0^2 QD_3 = M_t0 (+) -delta (r + t0 s)^2 is a cone with vertex (0:0:0:t0:-1); projected to
# (x, y, z, w = r + t0 s) it is G = diag(M_t0, -delta) and contains the line <a, b> (images of P, T); the ruling of
# that line gives Y with Y^2 = det G = f(t0) by the invariant
#   Y = ((a'Gc)(b'Ge) - (b'Gc)(a'Ge)) / det[a b c e]    (any c, e with det != 0).
# Computed in the algebra B = K_v[theta]/(U) (class QA of genus2_log.sage), Y(theta) = V0 + V1 theta is the Mumford
# V of phi(P) = [U, V]. The tangent vector is built from the tangent of C (not from a kernel computation):
#   chart z = 1: v = (F_y, -F_x, 0); chart y = 1: v = (F_z, 0, -F_x); then with r != 0
#   r' = P3 M1 v / (delta r), s' = (2 P3 M2 v / delta - r' s) / r   (the linearised equations of D; the third one
#   follows from Q1 Q3 - Q2^2 = c F and dF(v) = 0), T = (v, r', s'). When r = 0 the roles of (Q1, r) and (Q3, s)
#   are exchanged.

def quad_roots(u0, u1):
    # replaces genus2_log.quad_roots: the square root of the discriminant is certified (csqrt)
    K = u0.parent(); pi = _set_field(K)
    d = u1 * u1 - 4 * u0
    s = csqrt(d)
    if s is not None:
        return 'split', (-u1 + s) / 2, (-u1 - s) / 2
    vd = d.valuation(); k = vd // 2
    d1 = d / pipow(K, 2 * k)
    if vd % 2:
        s0, s1, c, j = -d1, K(0), K(0), 0
    else:
        c = K(1)
        while True:
            e = d1 - c * c
            assert not e.is_zero()
            ve = e.valuation()
            if ve % 2 == 0 and ve < 2 * E2:
                c = c + pi**(ve // 2)
                continue
            assert ve <= 2 * E2
            j = (ve - 1) // 2 if ve % 2 else E2
            s1 = 2 * c / pi**j; s0 = (c * c - d1) / pi**(2 * j)
            break
    x1 = QA((-u1 + pipow(K, k) * c) / 2, pipow(K, k + j) / 2, s0, s1)
    return 'qa', x1, x1.conj()

def s3_gram(q):
    a, b_, c_, d, e, f = q
    return [[a, b_/2, c_/2], [b_/2, d, e/2], [c_/2, e/2, f]]

def _det(Mx):
    # Leibniz determinant over any commutative ring (entries may be QA)
    n = len(Mx)
    tot = None
    for p in Permutations(n):
        term = None
        for i in range(n):
            ent = Mx[i][p[i] - 1]
            term = ent if term is None else term * ent
        if p.signature() < 0:
            term = -term
        tot = term if tot is None else tot + term
    return tot

def _qf(u, Mx, w):
    # u' Mx w
    n = len(u)
    acc = None
    for i in range(n):
        for j in range(n):
            if Mx[i][j] is None:
                continue
            term = u[i] * Mx[i][j] * w[j]
            acc = term if acc is None else acc + term
    return acc

# F partial derivatives (exact rational polynomial)
_R3Q = PolynomialRing(QQ, 'x,y,z')
_FQ = _R3Q(FQ_STR)
_FD = [_FQ.derivative(g) for g in _R3Q.gens()]

class BruinKv:
    def __init__(self, S, X, k):
        self.S = S; self.k = k
        Kv = S['Kv']; emb = S['emb']
        self.Kv = Kv
        self.delta = emb(X['delta'][k])
        self.M = [[[emb(c) for c in row] for row in s3_gram(q)] for q in X['Qc']]
        self.f = [emb(c) for c in X['tw'][k]['f']]
        z = Kv(0); h = Kv(1) / 2; dl = self.delta
        E = [[[1, 0], [0, 0]], [[0, h], [h, 0]], [[0, 0], [0, 1]]]
        self.QD = []
        for i in range(3):
            Mx = [[z] * 5 for _ in range(5)]
            for a in range(3):
                for b_ in range(3):
                    Mx[a][b_] = self.M[i][a][b_]
            for a in range(2):
                for b_ in range(2):
                    Mx[3 + a][3 + b_] = -dl * Kv(E[i][a][b_])
            self.QD.append(Mx)

    def Qval(self, i, P3):
        return _qf(P3, self.M[i], P3)

    def lift(self, P3):
        # P3 = (x, y, z) over K_v on C; returns (r, s) with Q_i(P3) = delta (r^2, rs, s^2), or None if Q1/delta
        # (resp. Q3/delta when Q1 = 0) is not a square in K_v
        q = [self.Qval(i, P3) for i in range(3)]
        dl = self.delta
        if not q[0].is_zero():
            r = csqrt(q[0] / dl)
            if r is None:
                return None
            s = q[1] / (dl * r)
        else:
            s = csqrt(q[2] / dl)
            if s is None:
                return None
            r = q[1] / (dl * s)
        return (r, s)

    def ondD(self, P):
        return [_qf(P, self.QD[i], P) for i in range(3)]

    def tangent(self, P, chart):
        x, y, z = P[:3]
        dF = [g(x, y, z) for g in _FD]
        if chart == 1:          # z = 1
            v = [dF[1], -dF[0], 0 * x]
        elif chart == 2:        # y = 1
            v = [dF[2], 0 * x, -dF[0]]
        else:
            raise ValueError('chart')
        P3 = list(P[:3]); r, s = P[3], P[4]; dl = self.delta
        m1 = _qf(P3, self.M[0], v); m2 = _qf(P3, self.M[1], v); m3 = _qf(P3, self.M[2], v)
        if not r.is_zero():
            rd = m1 / (dl * r)
            sd = (2 * m2 / dl - rd * s) / r
        else:
            sd = m3 / (dl * s)
            rd = (2 * m2 / dl - sd * r) / s
        T = v + [rd, sd]
        J = [_qf(P, self.QD[i], T) for i in range(3)]     # P' QD_i T, zero for a tangent vector
        return T, J

    def phi(self, P, chart, checks=None):
        Kv = self.Kv
        T, J = self.tangent(P, chart)
        a = [_qf(T, self.QD[i], T) for i in range(3)]
        if a[2].is_zero():
            raise ValueError('a3 = 0 within precision (a point of phi(P) above t = oo)')
        u1 = 2 * a[1] / a[2]; u0 = a[0] / a[2]
        discU = u1 * u1 - 4 * u0
        if discU.is_zero():
            raise ValueError('double t-root within precision')
        one = QA(Kv(1), Kv(0), u0, u1)
        th = QA(Kv(0), Kv(1), u0, u1)
        Mth = [[one * self.M[0][i][j] + th * (2 * self.M[1][i][j]) + th * th * self.M[2][i][j] for j in range(3)] for i in range(3)]
        zQ = one * Kv(0)
        G = [[Mth[i][j] if (i < 3 and j < 3) else zQ for j in range(4)] for i in range(4)]
        G[3][3] = one * (-self.delta)
        av = [one * P[0], one * P[1], one * P[2], one * P[3] + th * P[4]]
        bv = [one * T[0], one * T[1], one * T[2], one * T[3] + th * T[4]]
        iso = [_qf(av, G, av), _qf(av, G, bv), _qf(bv, G, bv)]
        Ga = [sum((G[i][j] * av[j] for j in range(4)), zQ) for i in range(4)]
        Gb = [sum((G[i][j] * bv[j] for j in range(4)), zQ) for i in range(4)]
        ev = [[one * (1 if i == j else 0) for j in range(4)] for i in range(4)]
        cands = []
        for (i, j) in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]:
            dt = _det([av, bv, ev[i], ev[j]])
            N = dt.norm()
            if N.is_zero():
                continue
            num = Ga[i] * Gb[j] - Gb[i] * Ga[j]
            cands.append((vex(N), (i, j), num / dt))
        assert cands, 'degenerate line'
        cands.sort(key=lambda t: t[0])
        Y = cands[0][2]
        fth = zQ
        for cf in reversed(self.f):
            fth = fth * th + one * cf
        res = dict(U=(u0, u1), V=(Y.a, Y.b), J=J, iso=iso, Ysq=Y * Y - fth, pair=cands[0][1],
                   Yalt=[(c[1], (c[2] - Y)) for c in cands[1:3]], a=a)
        if checks is not None:
            checks.append(res)
        return ((u0, u1), (Y.a, Y.b)), res

# ---------------- points of C(Q_2) from the disc data ----------------

def chart_poly(chart):
    # univariate data: F restricted to the chart, as a polynomial in (t, u) over QQ
    Rtu = PolynomialRing(QQ, 't,u'); t, u = Rtu.gens()
    if chart == 1:
        return _FQ(t, u, 1)
    if chart == 2:
        return _FQ(t, 1, u)
    raise ValueError

def disc_point(disc, X0, N):
    # disc = [chart, a0, b0, k, par] (par = 2: the dependent coordinate u = b0 + 2^k Y(X));
    # returns t0 (exact integer), an integer c and the certified precision m with |u* - c| <= 2^-m, where u* is the
    # dependent coordinate of the unique point P(X0) of the disc; certificate:
    #  (a) Newton polygon of G(X0, Y) = F(a0 + 2^k X0, b0 + 2^k Y) in Y: v(g1) < v(gj) (j >= 2), v(g0) >= v(g1):
    #      exactly one root Y* in the closed unit disc of C_2 (and it lies in Z_2);
    #  (b) Hensel: v(F(t0, c)) > 2 v(F_u(t0, c)) gives a unique root u* with v(u* - c) >= v(F(c)) - v(F_u(c)) =: m;
    #      m >= k and c = b0 mod 2^k, so (u* - b0)/2^k is in Z_2 and is the root Y* of (a).
    chart, a0, b0, k, par = disc
    assert par == 2
    Ft = chart_poly(chart)
    Ru = PolynomialRing(QQ, 'U'); U = Ru.gen()
    t0 = a0 + 2**k * X0
    g = Ft(t0, U)
    Y = PolynomialRing(QQ, 'Yv').gen()
    G = g(b0 + 2**k * Y)
    vs = [G[j].valuation(2) if G[j] != 0 else Infinity for j in range(G.degree() + 1)]
    assert all(vs[1] < vs[j] for j in range(2, len(vs))) and vs[0] >= vs[1], ('Newton polygon', vs)
    dg = g.derivative()
    Qbig = Qp(2, N + 200)
    cc = Qbig(b0)
    for _ in range(2 * N.bit_length() + 80):
        cc = (cc - g(cc) / dg(cc)).lift_to_precision(N + 200)
    c = Integer(cc.lift()) % 2**(N + 200)
    vF = g(c).valuation(2) if g(c) != 0 else Infinity
    vd = dg(c).valuation(2)
    assert vF > 2 * vd, 'Hensel certificate fails'
    m = min(vF - vd, 10**6)
    assert m >= k and (c - b0) % 2**k == 0
    return Integer(t0), c, m, vs

def disc_P3(Kv, disc, t0, c, m):
    chart = disc[0]
    Q2 = Kv.base_ring()
    uu = Kv(Q2(c).add_bigoh(m))
    tt = Kv(t0)
    if chart == 1:
        return [tt, uu, Kv(1)]
    return [tt, Kv(1), uu]
