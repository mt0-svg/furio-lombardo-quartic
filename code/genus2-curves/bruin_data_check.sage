# bruin_data_check.sage: second implementation (Sage) of the load-bearing data facts of WP2 of the M3a discharge, from the
# source data code/earlier-computations/bruin_form.gp only (own parser; nothing is read from the PARI outputs of WP2).
#  (1) f_k = -delta_k det(M1 + 2t M2 + t^2 M3) equals F_k of bruin_form.gp (M_i the symmetric matrices of Q_i).
#  (2) Factorization type of fRev_k = t^6 f_k(1/t) over K21: Sage's factor(), and an independent certificate: the
#      monic factors q, h (degrees 2 and 4) multiply back to fRev_k / lc, and both stay irreducible modulo a degree
#      one prime P = (p, b - r) at which their coefficients are P-integral (a factorization over K21 would reduce
#      to one over O/P = GF(p), since the coefficients of monic factors of a monic P-integral polynomial are P-integral).
#  (3) lc(fRev_k) = f_k(0) and d_k = disc(q_k) are not squares in K21: is_square(), and a non residue at a degree
#      one prime (own reduction map b -> r in GF(p)).
#  (4) d_k is a square in K21[T]/(h_k): h_k = A^2 - d_k B^2 with A, B in K21[T] (roots of a resolvent cubic over K21),
#      rechecked by multiplying out; then (A / B)^2 = d modulo h_k, rechecked in K21[T]/(h_k).
#  (5) The local fact behind GoodSextic at v (evidence only, not in Lean): f_k(0) is a non square at the place v
#      above 2 with e = 3 (a unit u of a dyadic field with v(2) = e is a square iff u = x^2 mod P^(2e + 1)).
# Run from code/genus2-curves: sage bruin_data_check.sage > bruin_data_check.out
import re, sys, time
T0 = time.time()
def say(s):
    print("%s  [%.0f s]" % (s, time.time() - T0), flush=True)

src = open('../earlier-computations/bruin_form.gp').read()
defs = {}
for m in re.finditer(r'^(\w+) = (.*?);\s*$', src, re.M):
    defs[m.group(1)] = m.group(2)

Qb.<b> = QQ[]
K21pol = Qb(sage_eval(defs['K21'], locals={'b': b}))
assert K21pol.degree() == 21 and K21pol.is_irreducible()
K.<b> = NumberField(K21pol)
R.<x, y, z> = K[]
S.<t> = K[]
loc = {'b': b, 'x': x, 'y': y, 'z': z, 't': t}
Q = [R(sage_eval(defs[n], locals=loc)) for n in ['Q1', 'Q2', 'Q3']]
dd = [K(sage_eval(defs[n], locals=loc)) for n in ['d0', 'd1']]
FF = [S(sage_eval(defs[n], locals=loc)) for n in ['F0', 'F1']]

def symmat(Qi):
    c = lambda m: Qi.monomial_coefficient(m)
    return matrix(K, [[c(x^2), c(x*y)/2, c(x*z)/2], [c(x*y)/2, c(y^2), c(y*z)/2], [c(x*z)/2, c(y*z)/2, c(z^2)]])

M = [symmat(Qi) for Qi in Q]
for i in range(3):
    v = vector(R, [x, y, z])
    assert v * M[i].change_ring(R) * v == Q[i]
say("p M_i p^T = Q_i: ok")
Mt = M[0].change_ring(S) + 2 * t * M[1].change_ring(S) + t^2 * M[2].change_ring(S)
fd = [-dd[k] * Mt.det() for k in range(2)]
for k in range(2):
    assert fd[k] == FF[k], k
say("(1) f_k = -d_k det(M1 + 2t M2 + t^2 M3) = F_k: ok for k = 0, 1")

# degree one primes of K21 (p not dividing the index of Z[b], so O/P = Z[b]/(p, b - r))
Zb.<w> = ZZ[]
fZ = Zb(K21pol)
disc = fZ.discriminant()
index2 = disc // K.discriminant()

def deg1_primes(pmax):
    out = []
    for p in primes(3, pmax):
        if index2 % p == 0 or disc % p == 0:
            continue
        for r, _ in fZ.change_ring(GF(p)).roots():
            out.append((p, ZZ(r)))
    return out

P1 = deg1_primes(200)

def red(c, p, r):
    """Image of c in GF(p) under b -> r, or None if a denominator is divisible by p."""
    pc = c.polynomial()
    if pc.denominator() % p == 0:
        return None
    return pc.change_ring(GF(p))(GF(p)(r))

def redpoly(g, p, r):
    cs = [red(c, p, r) for c in g.list()]
    if any(c is None for c in cs):
        return None
    return PolynomialRing(GF(p), 'T')(cs)

def nonres_prime(c):
    for (p, r) in P1:
        v = red(c, p, r)
        if v is not None and v != 0 and not v.is_square():
            return (p, r)
    return None

for k in range(2):
    f = fd[k]
    fr = S(list(reversed(f.list())))
    assert fr.degree() == 6 and fr == t^6 * f(1/t)
    lc = fr.leading_coefficient()
    assert lc == f[0]
    fa = fr.factor()
    degs = sorted(g.degree() for g, e in fa)
    mults = [e for g, e in fa]
    say("k = %d: (2) Sage factor() of fRev over K21: degrees %s, multiplicities %s" % (k, degs, mults))
    assert degs == [2, 4] and mults == [1, 1]
    q = [g for g, e in fa if g.degree() == 2][0].monic()
    h = [g for g, e in fa if g.degree() == 4][0].monic()
    assert lc * q * h == fr
    cq = next((pr for pr in P1 if redpoly(q, *pr) is not None and redpoly(q, *pr).is_irreducible()), None)
    ch = next((pr for pr in P1 if redpoly(h, *pr) is not None and redpoly(h, *pr).is_irreducible()), None)
    say("  lc q h = fRev: ok; q irreducible modulo %s, h irreducible modulo %s (degree one primes (p, b - r))" % (cq, ch))
    assert cq is not None and ch is not None
    # (3) non squares
    dq = q[1]^2 - 4 * q[0]
    say("  (3) lc = f_k(0): is_square %s, non residue at %s; d = disc q: is_square %s, non residue at %s"
          % (lc.is_square(), nonres_prime(lc), dq.is_square(), nonres_prime(dq)))
    assert not lc.is_square() and not dq.is_square()
    assert nonres_prime(lc) is not None and nonres_prime(dq) is not None
    # (4) d is a square modulo h: write h = (T^2 + u T + w)^2 - d (v T + z)^2 over K21 (h splits over K21(sqrt d)
    # into the conjugate quadratics A +- sqrt(d) B); u = h3 / 2, w = (h2 - u^2 + d V) / 2 with V = v^2 a root of the
    # cubic d V w^2 - (u w - h1 / 2)^2 - h0 d V (roots over K21 only, no factorization over K21(sqrt d)).
    Vv = polygen(K, 'V')
    u = h[3] / 2
    wV = (h[2] - u^2 + dq * Vv) / 2
    cub = dq * Vv * wV^2 - (u * wV - h[1] / 2)^2 - h[0] * dq * Vv
    found = None
    for V0, _ in cub.roots():
        if V0 != 0 and V0.is_square():
            v0 = V0.sqrt()
            w0 = wV(V0)
            z0 = (u * w0 - h[1] / 2) / (dq * v0)
            A = t^2 + u * t + w0
            B = v0 * t + z0
            if A^2 - dq * B^2 == h:
                found = (A, B)
                break
    assert found is not None
    A, B = found
    Sh = S.quotient(h)
    beta = Sh(A) / Sh(B)
    assert beta^2 == Sh(dq)
    say("  (4) h = A^2 - d B^2 with A, B in K21[T] (resolvent cubic), and (A/B)^2 = d in K21[T]/(h): ok, so d is a square in K21[T]/(fRev) (with 2T + q_1 modulo q)")
    # (2T + q_1)^2 = d modulo q
    assert (2 * t + q[1])^2 - dq == 4 * q

# (5) f_k(0) non square at v (e = 3): unit test modulo P^7
Pv = [P for P in K.primes_above(2) if P.ramification_index() == 3]
assert len(Pv) == 1 and Pv[0].residue_class_degree() == 1
Pv = Pv[0]
I7 = Pv^7
units7 = [xx for xx in I7.residues() if xx.valuation(Pv) == 0]
say("(5) the place v above 2 with e = 3, f = 1, and the %d units of O/P^7 found" % len(units7))
for k in range(2):
    c = fd[k][0]
    val = c.valuation(Pv)
    # write c = u * pi^val with pi a uniformizer; val is even for a square
    pi = K.uniformizer(Pv)
    assert pi.valuation(Pv) == 1
    u = c / pi^val
    # u is a square in K_v iff v(u - x^2) >= 7 for a unit x of O/P^7 (Hensel: 1 + 4 pi w is a square)
    is_sq_v = (val % 2 == 0) and any((u - xx^2).valuation(Pv) >= 7 for xx in units7)
    say("(5) k = %d: v(f_k(0)) = %d at v (e = 3), f_k(0) a square in K_v: %s" % (k, val, is_sq_v))
