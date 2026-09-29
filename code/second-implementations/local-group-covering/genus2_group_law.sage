# genus2_group_law.sage: group law on the Jacobian of a genus 2 curve y^2 = f(x), deg f = 6 (even degree model),
# for generic Mumford pairs relative to D_oo = oo_+ + oo_- (the polar divisor of x).
#
# A pair D = ((u0, u1), (v0, v1)) stands for the class [P1 + P2 - D_oo], where P1, P2 are the points
# (x_j, v(x_j)), x_j the roots of u = x^2 + u1 x + u0, v = v1 x + v0, u | f - v^2.
# Only elementwise field operations are used (no polynomial gcd), so over a p-adic field Sage's precision
# tracking of every coefficient is sound.  Degenerate configurations (common root of u1, u2; a result
# involving a point at infinity) raise JacDegenerate; they have probability zero for p-adic inputs.
#
# Addition: w = unique cubic with w = v1 mod u1, w = v2 mod u2; div(y - w) = P1+..+P4 + R1 + R2 - 3 D_oo,
# so D1 + D2 = [hR1 + hR2 - D_oo] with u3 = (f - w^2)/(u1 u2) made monic, v3 = -w mod u3.
# Doubling: w = v + u s with u^2 | f - w^2, i.e. s = ((f - v^2)/u) (2v)^(-1) mod u.
# f is a list [f0, ..., f6] (lowest degree first).

class JacDegenerate(Exception):
    pass

def _pmul(a, b):
    r = [a[0].parent()(0)] * (len(a) + len(b) - 1)
    for i in range(len(a)):
        for j in range(len(b)):
            r[i + j] = r[i + j] + a[i] * b[j]
    return r

def _padd(a, b):
    n = max(len(a), len(b)); z = (a + b)[0].parent()(0)
    return [(a[i] if i < len(a) else z) + (b[i] if i < len(b) else z) for i in range(n)]

def _pneg(a):
    return [-c for c in a]

def _pdivmod_monic(a, m):
    # a = q m + r, m monic (leading coefficient 1 exactly), deg r < deg m
    a = list(a); dm = len(m) - 1
    if len(a) - 1 < dm:
        return [a[0].parent()(0)], a
    q = [a[0].parent()(0)] * (len(a) - dm)
    for i in range(len(a) - 1, dm - 1, -1):
        c = a[i]; q[i - dm] = c
        for j in range(dm + 1):
            a[i - dm + j] = a[i - dm + j] - c * m[j]
    return q, a[:dm]

def _mulmod(p, q, u):
    # (p0 + p1 x)(q0 + q1 x) mod x^2 + u1 x + u0
    u0, u1 = u
    t = p[1] * q[1]
    return [p[0] * q[0] - t * u0, p[0] * q[1] + p[1] * q[0] - t * u1]

def _invmod(l, u):
    # inverse of l = l0 + l1 x modulo x^2 + u1 x + u0: (l1 x + l0)(d x + e) = 1, N = resultant
    u0, u1 = u; C, A = l
    N = C * C - A * C * u1 + A * A * u0
    if N.is_zero():
        raise JacDegenerate('non invertible modulo u')
    return [(C - A * u1) / N, -A / N]

def _finish(f, w, U4):
    F = _padd(f, _pneg(_pmul(w, w)))
    q, rem = _pdivmod_monic(F, U4)
    assert len(q) == 3
    lc = q[2]
    if lc.is_zero():
        raise JacDegenerate('leading coefficient f6 - w3^2 vanishes')
    u3 = (q[0] / lc, q[1] / lc)
    _, wr = _pdivmod_monic(w, [u3[0], u3[1], lc.parent()(1)])
    return (u3, (-wr[0], -wr[1])), rem

def jneg(D):
    return (D[0], (-D[1][0], -D[1][1]))

def jadd(f, D1, D2, check=None):
    (a0, a1), (b0, b1) = D1
    (c0, c1), (d0, d1) = D2
    inv = _invmod([a0 - c0, a1 - c1], (c0, c1))           # u1^(-1) mod u2
    s = _mulmod([d0 - b0, d1 - b1], inv, (c0, c1))         # (v2 - v1) u1^(-1) mod u2
    w = _padd([b0, b1], _pmul([a0, a1, a0.parent()(1)], s))
    U4 = _pmul([a0, a1, a0.parent()(1)], [c0, c1, c0.parent()(1)])
    R, rem = _finish(f, w, U4)
    if check is not None:
        check.append(rem)
    return R

def jdbl(f, D, check=None):
    (u0, u1), (v0, v1) = D
    one = u0.parent()(1)
    g, rem1 = _pdivmod_monic(_padd(f, _pneg(_pmul([v0, v1], [v0, v1]))), [u0, u1, one])
    _, gm = _pdivmod_monic(g, [u0, u1, one])
    inv = _invmod([2 * v0, 2 * v1], (u0, u1))
    s = _mulmod(gm, inv, (u0, u1))
    w = _padd([v0, v1], _pmul([u0, u1, one], s))
    U4 = _pmul([u0, u1, one], [u0, u1, one])
    R, rem = _finish(f, w, U4)
    if check is not None:
        check.append(rem1); check.append(rem)
    return R

def jmul(f, n, D, check=None):
    # n D for n >= 1 by left to right double and add (generic: no intermediate result is 0)
    n = Integer(n)
    if n < 0:
        return jmul(f, -n, jneg(D), check)
    assert n >= 1
    R = D
    for bit in n.bits()[-2::-1]:
        R = jdbl(f, R, check)
        if bit:
            R = jadd(f, R, D, check)
    return R

def jcheck(f, D):
    # remainder of f - v^2 modulo u (zero for a genuine pair)
    (u0, u1), (v0, v1) = D
    _, r = _pdivmod_monic(_padd(f, _pneg(_pmul([v0, v1], [v0, v1]))), [u0, u1, u0.parent()(1)])
    return r
