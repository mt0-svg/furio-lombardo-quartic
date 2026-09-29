# genus2_log.sage: p-adic logarithm on the Jacobian of y^2 = f(x), deg f = 6, over a finite extension K of Q_2
# (Sage p-adic field, elementwise arithmetic with tracked precision), for omega_0 = dx/y, omega_1 = x dx/y.
# Needs genus2_group_law.sage.
#
# Method (explicit points, one tiny integral):
#   E = [P1 + P2 - D_oo] with P1, P2 the points over the splitting algebra L of u (L = K if u splits,
#   L = K[theta]/(u) a quadratic field otherwise, P1 = (theta, v(theta)), P2 its conjugate).  Since
#   P2 + hP2 ~ D_oo, E = [P1 - hP2] and log E = int_{hP2}^{P1} omega.  When hP2 lies in the disc around P1
#   on which the branch y(t) = sqrt(F(t)), F(t) = f(x1 + t), converges, this is the integral of the power
#   series of omega from t0 = x2 - x1 to 0 (or the same in the chart X = 1/x at infinity).
#   log D = log(N D) / N with N = m 2^j, m odd killing the odd torsion, j the first exponent for which
#   N D passes the convergence test.
#
# Rigorous bounds (valuations v normalised by v(pi_K) = 1 extended to L, v(2) = e; K totally ramified over Q_2):
#   F(t) = F(0) prod_i (1 - t/beta_i), beta_i the roots; |binom(-1/2, n)|_2 <= 4^n, so the coefficients of
#   1/y(t) satisfy v(a_n) >= -v(y1) - n rho, rho = v(4) + max_i v(beta_i), and max_i v(beta_i) =
#   max_j (v(F_0) - v(F_j))/j (first Newton polygon slope; lower bounds of v(F_j) give an upper bound).
#   The same bound holds for y(t) with v(b_n) >= v(y1) - n rho.  The tail sum_{n > M} of the integral is
#   bounded termwise; it is added as O(pi^T).  The branch through hP2 is checked (y(t0) = -y2, not +y2).

E2 = None   # v_pi(2) = e, set from the field by _set_field

def _set_field(K):
    # K totally ramified over Q_2 (residue field F_2): sets E2 = e and returns the uniformizer
    global E2
    assert K.prime() == 2 and K.absolute_f() == 1
    E2 = K.absolute_e()
    return K.uniformizer()

class QA:
    # element a + b theta of L = K[theta]/(theta^2 + s1 theta + s0) (irreducible over K)
    def __init__(self, a, b, s0, s1):
        self.a = a; self.b = b; self.s0 = s0; self.s1 = s1
    def _mk(self, a, b):
        return QA(a, b, self.s0, self.s1)
    def _lift(self, o):
        if isinstance(o, QA):
            return o
        return QA(self.a.parent()(o), self.a.parent()(0), self.s0, self.s1)
    def __add__(self, o):
        o = self._lift(o); return self._mk(self.a + o.a, self.b + o.b)
    __radd__ = __add__
    def __neg__(self):
        return self._mk(-self.a, -self.b)
    def __sub__(self, o):
        o = self._lift(o); return self._mk(self.a - o.a, self.b - o.b)
    def __rsub__(self, o):
        return self._lift(o) - self
    def __mul__(self, o):
        if not isinstance(o, QA):
            o = self.a.parent()(o)
            return self._mk(self.a * o, self.b * o)
        t = self.b * o.b
        return self._mk(self.a * o.a - t * self.s0, self.a * o.b + self.b * o.a - t * self.s1)
    __rmul__ = __mul__
    def conj(self):
        return self._mk(self.a - self.b * self.s1, -self.b)
    def norm(self):
        return self.a * self.a - self.a * self.b * self.s1 + self.b * self.b * self.s0
    def inverse(self):
        N = self.norm()
        if N.is_zero():
            raise ZeroDivisionError('QA element not invertible within precision')
        c = self.conj()
        return self._mk(c.a / N, c.b / N)
    def __truediv__(self, o):
        if not isinstance(o, QA):
            o = self.a.parent()(o)
            return self._mk(self.a / o, self.b / o)
        return self * o.inverse()
    def __rtruediv__(self, o):
        return self._lift(o) * self.inverse()
    def __pow__(self, n):
        r = self._lift(1)
        for _ in range(n):
            r = r * self
        return r
    def is_zero(self):
        return self.a.is_zero() and self.b.is_zero()
    def trace(self):
        return 2 * self.a - self.b * self.s1

def vlb(z):
    # lower bound for the valuation (the valuation itself when z is nonzero within its precision)
    if isinstance(z, QA):
        return vlb(z.norm()) / 2
    if z.is_zero():
        return QQ(z.precision_absolute())
    return QQ(z.valuation())

def vex(z):
    # exact valuation; fails when z is zero within its precision
    if isinstance(z, QA):
        return vex(z.norm()) / 2
    if z.is_zero():
        raise ValueError('valuation undetermined (zero within precision)')
    return QQ(z.valuation())

def is_square_own(d):
    # d = pi^v eps; square iff v even and eps = x0^2 mod pi^(2e+1) for a unit x0 = 1 + sum_{i<=e} c_i pi^i,
    # c_i in {0, 1} (x0 mod pi^(e+1) determines x0^2 mod pi^(2e+1); Hensel applies beyond 2 v(2 x0) = 2e)
    K = d.parent(); pi = _set_field(K); e = E2
    vd = d.valuation()
    if vd % 2:
        return False
    eps = d / pi**vd
    assert eps.precision_relative() >= 2 * e + 1
    for cs in cartesian_product([[0, 1]] * e):
        x0 = 1 + sum(cs[i - 1] * pi**i for i in range(1, e + 1))
        if (x0 * x0 - eps).valuation() >= 2 * e + 1:
            return True
    return False
    eps = d / pi**vd
    assert eps.precision_relative() >= 7
    for c1 in [0, 1]:
        for c2 in [0, 1]:
            for c3 in [0, 1]:
                x0 = 1 + c1 * pi + c2 * pi**2 + c3 * pi**3
                if (x0 * x0 - eps).valuation() >= 7:
                    return True
    return False

def quad_roots(u0, u1):
    # roots of x^2 + u1 x + u0: ('split', x1, x2) in K, or ('qa', x1, x2) in L = K(sqrt(d)), d = u1^2 - 4 u0,
    # written on a well conditioned basis (1, omega) of L: d = pi^(2k) d1 with v(d1) in {0, 1};
    # v(d1) = 1: omega = sqrt(d1) (Eisenstein omega^2 - d1);  d1 a unit: c in K with v(d1 - c^2) maximal
    # (improved digit by digit, the residue field being F_2), then sqrt(d1) = c + pi^j omega with
    # omega^2 + (2c/pi^j) omega + (c^2 - d1)/pi^(2j) = 0: Eisenstein if v(d1 - c^2) = 2j + 1 < 2e,
    # unramified (residue omega^2 + omega + 1) if v(d1 - c^2) = 2e (j = e), split if > 2e.
    K = u0.parent(); pi = _set_field(K)
    d = u1 * u1 - 4 * u0
    sq = is_square_own(d)
    assert sq == d.is_square()
    if sq:
        s = d.square_root()
        assert (s * s - d).is_zero()
        return 'split', (-u1 + s) / 2, (-u1 - s) / 2
    vd = d.valuation(); k = vd // 2
    d1 = d / pi**(2 * k)
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
    # x1 = (-u1 + pi^k sqrt(d1))/2, sqrt(d1) = c + pi^j omega; x2 its conjugate
    x1 = QA((-u1 + pi**k * c) / 2, pi**(k + j) / 2, s0, s1)
    return 'qa', x1, x1.conj()

def model_shift(m, c):
    # coefficients of m(c + t), m a list over K (lowest first), c in K or L
    n = len(m) - 1
    out = []
    for j in range(n + 1):
        acc = None
        for i in range(n, j - 1, -1):
            term = m[i] * binomial(i, j)
            acc = term if acc is None else c * acc + term
        out.append(acc)
    return out

def maxrootval_ub(F):
    v0 = vex(F[0])
    return max((v0 - vlb(F[j])) / j for j in range(1, len(F)))

def _tail_min(C0, mu, M, T_needed=None):
    # min over n > M of C0 + n mu - e v_2(n + 1) (lower bound C0 + n mu - e log_2(n + 1), increasing for
    # n + 1 >= e/(mu log 2)); exact v_2 used on a window, the log bound beyond it
    n0 = max(M + 1, ceil(E2 / (mu * log(2.0))) + 1)
    best = min([C0 + n * mu - E2 * valuation(n + 1, 2) for n in range(M + 1, n0 + 64)])
    beyond = C0 + (n0 + 64) * mu - E2 * log(n0 + 65, 2)
    return min(best, floor(beyond))

def branch_series(F, yc, M):
    # b = sqrt(F) with b_0 = yc, and a = 1/b, coefficients 0..M
    b = [yc]
    two_y = 2 * yc
    for n in range(1, M + 1):
        s = F[n] if n < len(F) else 0 * yc
        for i in range(1, n):
            s = s - b[i] * b[n - i]
        b.append(s / two_y)
    iy = 1 / yc
    a = [iy]
    for n in range(1, M + 1):
        s = b[1] * a[n - 1]
        for i in range(2, n + 1):
            s = s + b[i] * a[n - i]
        a.append(-s * iy)
    return b, a

def tiny(model, c, yc, t0, ytarget, gs, T_goal):
    # int_{(c, yc)}^{(c + t0, ytarget)} g(t) dt / y(t) for each numerator g in gs (lists, lowest first)
    F = model_shift(model, c)
    rho = E2 * 2 + maxrootval_ub(F)
    vt0 = vex(t0)
    mu = vt0 - rho
    if mu <= 0:
        return None
    vy = vex(yc)
    C0s = [-vy + min(vlb(g[i]) + i * rho for i in range(len(g))) + vt0 for g in gs]
    M = 1
    while _tail_min(min(C0s), mu, M) < T_goal:
        M += 1
    b, a = branch_series(F, yc, M)
    # branch check: y(t0) = ytarget, while the other branch gives -ytarget (difference 2 ytarget)
    ysum = b[0]; tp = t0
    for n in range(1, M + 1):
        ysum = ysum + b[n] * tp; tp = tp * t0
    ytail = floor(vy + (M + 1) * mu)
    dy = ysum - ytarget
    ok_branch = min(vlb(dy), ytail) > E2 + vy
    res = []
    for g, C0 in zip(gs, C0s):
        h = [sum((g[i] * a[n - i] for i in range(len(g)) if n - i >= 0), 0 * yc) for n in range(M + 1)]
        S = 0 * yc; tp = t0
        for n in range(M + 1):
            S = S + h[n] * tp / (n + 1); tp = tp * t0
        res.append((S, _tail_min(C0, mu, M)))
    return dict(I=res, mu=mu, rho=rho, M=M, branch=ok_branch, vt0=vt0)

def _chart_data(f, x1, y1, x2, y2, chart):
    # centre P1, target hP2 = (x2, -y2); returns (model, c, yc, t0, ytarget, numerators of omega_0, omega_1)
    if chart == 'aff':
        return f, x1, y1, x2 - x1, -y2, [[1 + 0 * x1], [x1, 1 + 0 * x1]]
    fs = list(reversed(f))
    X1 = 1 / x1; X2 = 1 / x2
    return fs, X1, y1 * X1**3, X2 - X1, -y2 * X2**3, [[-X1, -1 + 0 * X1], [-1 + 0 * X1]]

def _points(E):
    (u0, u1), (v0, v1) = E
    mode, x1, x2 = quad_roots(u0, u1)
    return mode, x1, x1 * v1 + v0, x2, x2 * v1 + v0

def near0_margin(f, E):
    # best convergence margin mu = v(t0) - rho over the two charts (None when neither applies); cheap
    mode, x1, y1, x2, y2 = _points(E)
    best = None
    for chart in ['aff', 'inf']:
        try:
            model, c, yc, t0, yt, gs = _chart_data(f, x1, y1, x2, y2, chart)
            mu = vex(t0) - (2 * E2 + maxrootval_ub(model_shift(model, c)))
        except (ValueError, ZeroDivisionError):
            continue
        if best is None or mu > best[1]:
            best = (chart, mu)
    return best

def log_near0(f, E, T_goal, chart):
    # log E = int_{hP2}^{P1} omega in the given chart; None if the convergence or branch test fails
    mode, x1, y1, x2, y2 = _points(E)
    r = tiny(*_chart_data(f, x1, y1, x2, y2, chart), T_goal=T_goal)
    if r is None or not r['branch']:
        return None
    out = []
    for S, T in r['I']:
        S = -S                                  # int_{hP2}^{P1} = -int_{P1}^{hP2}
        if mode == 'qa':
            # log E lies in K: log E = Tr(S + tail)/2, and v(Tr(tail)) >= v(tail)
            assert S.b.is_zero() or S.b.valuation() + vex(x1 - x2) >= T - 1, "log not in K"
            val = (S.trace() / 2).add_bigoh(T - E2)
        else:
            val = S.add_bigoh(T)
        out.append(val)
    return dict(log=out, chart=chart, mu=r['mu'], rho=r['rho'], M=r['M'], mode=mode)

def jlog(f, D, m, T_goal, mu_target=8, extra_max=4, jmax=60):
    # log D = log(N D)/N, N = m 2^j: j is the first exponent with a positive margin, raised by up to
    # extra_max further doublings until the margin reaches mu_target
    E = jmul(f, m, D)
    j = 0; jfirst = None
    while j <= jmax:
        mg = near0_margin(f, E)
        if mg is not None and mg[1] > 0 and jfirst is None:
            jfirst = j
        if jfirst is not None and (mg[1] >= mu_target or j >= jfirst + extra_max):
            r = log_near0(f, E, T_goal, mg[0])
            if r is None:
                raise ValueError('branch test failed')
            N = m * 2**j
            r['N'] = N; r['j'] = j; r['jfirst'] = jfirst
            r['logD'] = [z / N for z in r['log']]
            r['Eprec'] = min(c.precision_relative() for c in E[0] + E[1])
            return r
        E = jdbl(f, E); j += 1
    raise ValueError('no multiple passed the convergence test')

def refine(f, D, iters=20):
    # genuine pair (u, v') with the same u and v' the Hensel root of v^2 = f mod u near the given v
    (u0, u1), (v0, v1) = D
    one = u0.parent()(1)
    v = [v0, v1]
    for _ in range(iters):
        _, r = _pdivmod_monic(_padd(f, _pneg(_pmul(v, v))), [u0, u1, one])
        inv = _invmod([2 * v[0], 2 * v[1]], (u0, u1))
        corr = _mulmod(r, inv, (u0, u1))
        v = [v[0] + corr[0], v[1] + corr[1]]
    # Newton's lemma at each root x_j: the exact square root is within |f(x_j) - v(x_j)^2| / |2 v(x_j)|
    mode, x1, x2 = quad_roots(u0, u1)
    vd = vex(x1 - x2)
    bnd = []
    for xj in [x1, x2]:
        yj = xj * v[1] + v[0]
        rj = model_shift(f, xj)[0] - yj * yj
        vr = vlb(rj); vy2 = vex(2 * yj)
        assert vr > 2 * vy2
        bnd.append(vr - vy2)
    # v1 = (Y1 - Y2)/(x1 - x2), v0 = Y1 - v1 x1: coefficient errors from value errors of valuation >= beta
    beta = min(bnd)
    e = floor(min(beta, beta - vd, beta - vd + min(vex(x1), vex(x2))))
    return ((u0, u1), (v[0].add_bigoh(e), v[1].add_bigoh(e)))

def perturb_bound(f, Dp, eu, ev):
    # For every genuine D = (u, v) with v(u_i - u'_i) >= eu, v(v_i - v'_i) >= ev (D' = Dp genuine):
    # v(log_k D - log_k D') >= returned value, k = 0, 1.  log D - log D' = sum_j int_{P'_j}^{P_j} omega.
    (u0, u1), (v0, v1) = Dp
    mode, x1, x2 = quad_roots(u0, u1)
    vd = vex(x1 - x2)
    assert eu > vd
    out = []
    for xj in [x1, x2]:
        yj = xj * v1 + v0
        vx = vex(xj); vy = vex(yj)
        A = min(eu, eu + vx)
        assert A > 2 * vd, 'root perturbation not controlled'
        delta = A - vd                              # v(x_j(D) - x_j') >= delta
        assert delta > vx
        F = model_shift(f, xj)
        rho = 2 * E2 + maxrootval_ub(F)
        mu = delta - rho
        assert mu > E2, 'perturbation outside the convergence disc'
        # branch: v(y_series(t) - y') >= vy + mu > vy + 3, v(v(x_j) - y') >= min(ev + min(0, vx), v(v1') + delta)
        assert min(ev + min(0, vx), vlb(v1) + delta) > E2 + vy
        for g in [[1 + 0 * xj], [xj, 1 + 0 * xj]]:
            C0 = -vy + min(vlb(g[i]) + i * rho for i in range(len(g))) + delta
            out.append(min(C0, _tail_min(C0, mu, 0)))
    return floor(min(out))
