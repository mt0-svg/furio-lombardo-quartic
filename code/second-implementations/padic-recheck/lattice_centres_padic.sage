# lattice_centres_padic.sage: an independent recomputation, in Sage p-adic arithmetic
# (Qp(2).extension(E), capped relative precision, no ball arithmetic), of the lattice data of p21_45 and of the values
# at the constant box centres of p21_46. Numerical evidence, not a proof: Sage's own precision tracking is trusted and the
# series are summed well past the target. Independent code for: the embedding K21 -> K_v (Newton from a low precision
# start, Hensel check), exact points near the stored divisors, Cantor's group law, the tiny logarithm (square root and
# inverse power series in z, not the w-recursion of pball), the lattice (ZZ-module spans, not PARI's mathnf), the
# saturation (Sage smith_form), the Abel-Prym map at the centres (cofactor kernel, quadric pencil, Pluecker ruling).
# Only the exact data are shared with the pipeline under review (text export m9cert_exp_k<k>.txt of m9cert_x1_export.gp).
# Usage (from code/earlier-computations): sage ../second-implementations/padic-recheck/lattice_centres_padic.sage k [centres: all | none | n]
import sys, time
k = int(sys.argv[1]); CEN = sys.argv[2] if len(sys.argv) > 2 else "all"
PREC2 = 1100                      # Q_2 digits, so 3300 pi-adic digits
TGT = 200                         # target pi-adic precision of the tiny logarithms (before division by N)
t00 = time.time()
DAT = {}
for line in open("m9cert_exp_k%d.txt" % k):
    key, val = line.split(" = ", 1); DAT[key] = pari(val.strip())
COM = {}
for line in open("m9cert_exp_common.txt"):
    key, val = line.split(" = ", 1); COM[key] = pari(val.strip())
Rx = PolynomialRing(ZZ, 'x')
Epol = Rx([ZZ(c) for c in DAT['E'].Vecrev()])
K = Qp(2, PREC2).extension(Epol, names='pi'); pi = K.gen()
Kb = PolynomialRing(QQ, 'b')
def topol(p):
    if p.type() in ('t_INT', 't_FRAC'): return Kb(QQ(p))
    return Kb([QQ(c) for c in p.Vecrev()])
def horner(P, a):
    r = K(0)
    for c in reversed(P.list()): r = r * a + K(c)
    return r
K21 = topol(DAT['K21']); dK21 = K21.derivative()
# embedding: start from the exported theta modulo pi^60 only, Newton, Hensel check
th = sum(K(QQ(c)) * pi**i for i, c in enumerate(DAT['TH'])).add_bigoh(60)
vK0, vD0 = horner(K21, th).valuation(), horner(dK21, th).valuation()
assert vK0 > 2 * vD0, "Hensel at the start"
th = th.lift_to_precision(K.precision_cap())
for it in range(14): th = th - horner(K21, th) / horner(dK21, th)
vK, vD = horner(K21, th).valuation(), horner(dK21, th).valuation()
g2v = horner(topol(DAT['GEN2']), th).valuation()
print("k = %d: Hensel start v(K21(th0)) = %d > 2 v(K21'(th0)) = %d; after Newton v(K21(th)) >= %s, v(K21') = %d, v(gen2(th)) = %d (place pr: %s)"
      % (k, vK0, 2 * vD0, vK, vD, g2v, g2v > 0))
def kv(p): return horner(topol(p), th)
f = [kv(c) for c in DAT['F']]
assert len(f) == 7
# ---------------- polynomials (lists, low degree first) and B = K[x]/(x^2 + u1 x + u0) as pairs
def pad(A, n): return list(A) + [K(0)] * (n - len(A))
def padd(A, B): n = max(len(A), len(B)); A, B = pad(A, n), pad(B, n); return [A[i] + B[i] for i in range(n)]
def pneg(A): return [-a for a in A]
def psub(A, B): return padd(A, pneg(B))
def pmul(A, B):
    C = [K(0)] * (len(A) + len(B) - 1)
    for i, a in enumerate(A):
        for j, bb in enumerate(B): C[i + j] += a * bb
    return C
def pdivrem(A, U):
    A = list(A); d = len(U) - 1; n = len(A) - 1
    if n < d: return [], pad(A, d)
    Q = [K(0)] * (n - d + 1)
    for i in range(n, d - 1, -1):
        q = A[i]; Q[i - d] = q
        for j in range(d): A[i - d + j] -= q * U[j]
        A[i] = K(0)
    return Q, A[:d]
def bm(a, c, U): return (a[0] * c[0] - a[1] * c[1] * U[0], a[0] * c[1] + a[1] * c[0] - a[1] * c[1] * U[1])
def bnorm(a, U): return a[0]**2 - a[0] * a[1] * U[1] + a[1]**2 * U[0]
def btr(a, U): return 2 * a[0] - a[1] * U[1]
def binv(a, U): N = bnorm(a, U); return ((a[0] - a[1] * U[1]) / N, -a[1] / N)
def badd(a, c): return (a[0] + c[0], a[1] + c[1])
def bsub(a, c): return (a[0] - c[0], a[1] - c[1])
def bsc(l, a): return (l * a[0], l * a[1])
def bfromx(P, U): r = pdivrem(pad(P, 2), [U[0], U[1], K(1)])[1]; return (r[0], r[1])
def bval(a): return min(a[0].valuation(), a[1].valuation())
# ---------------- Cantor for y^2 = f(x), deg f = 6; points [u, v], u = [u0, u1, 1], v = [v0, v1]; None = origin
RES = [10**9]
def red(u, v):
    q, r = pdivrem(psub(f, pmul(v, v)), u)
    RES[0] = min(RES[0], min(c.valuation() for c in r))       # u | f - v^2: the remainder must vanish
    assert len(q) == 3
    lc = q[2]; assert lc.valuation() < lc.precision_absolute(), "lc(u3) = 0"
    u3 = [q[0] / lc, q[1] / lc, K(1)]
    return (u3, pad(pdivrem(pneg(pad(v, 4)), u3)[1], 2))
def jadd(D1, D2):
    if D1 is None: return D2
    if D2 is None: return D1
    (u1, v1), (u2, v2) = D1, D2
    U2 = (u2[0], u2[1]); c = (u1[0] - u2[0], u1[1] - u2[1])
    kk = bm(bsub(v2, v1), binv(c, U2), U2)
    return red(pmul(u1, u2), padd(v1, pmul(u1, [kk[0], kk[1]])))
def jdbl(D):
    if D is None: return D
    u1, v1 = D; U1 = (u1[0], u1[1])
    w = pdivrem(psub(f, pmul(v1, v1)), u1)[0]
    kk = bm(bfromx(w, U1), binv((2 * v1[0], 2 * v1[1]), U1), U1)
    return red(pmul(u1, u1), padd(v1, pmul([kk[0], kk[1]], u1)))
def jmul(n, D):
    R = None
    for bit in bin(n)[2:]:
        R = jdbl(R)
        if bit == '1': R = jadd(R, D)
    return R
# ---------------- tiny logarithm, power series in z = x - x1 (independent of pball's w-recursion)
def tiny_x(fl, D, tgt):
    u, v = D; U = (u[0], u[1])
    x1 = (K(0), K(1)); s = (-u[1], K(-2)); y1 = (v[0], v[1]); y2 = (v[0] - v[1] * u[1], -v[1])
    pw = [(K(1), K(0))]
    for i in range(6): pw.append(bm(pw[-1], x1, U))
    F = [(K(0), K(0))] * 7
    for j in range(7):
        acc = (K(0), K(0))
        for i in range(j, 7): acc = badd(acc, bsc(binomial(i, j) * fl[i], pw[i - j]))
        F[j] = acc
    if bnorm(F[0], U).valuation() >= bnorm(F[0], U).precision_absolute(): return None
    # e_j = F_j s^j / F_0 must be small (analyticity on |z| <= |s|): lower bound of their valuations at the roots
    F0i = binv(F[0], U); sp = [(K(1), K(0))]
    for j in range(8): sp.append(bm(sp[-1], s, U))
    cmin = min(min(btr(bm(bm(F[j], F0i, U), sp[j], U), U).valuation(), bnorm(bm(bm(F[j], F0i, U), sp[j], U), U).valuation() / 2) for j in range(1, 7))
    if cmin <= 6: return None
    Y = [bsc(-1, y1)]; I2Y0 = binv(bsc(2, Y[0]), U)
    Gi = [binv(Y[0], U)]
    I1 = (K(0), K(0)); I2 = (K(0), K(0)); Ys = Y[0]
    sn1 = s; n = 0; small = 0
    while True:
        # term n of the integrals
        t1 = bsc(1 / K(n + 1), bm(Gi[n], sn1, U))
        t2 = badd(bsc(1 / K(n + 1), bm(bm(Gi[n], x1, U), sn1, U)), bsc(1 / K(n + 2), bm(bm(Gi[n], sn1, U), s, U)))
        I1 = badd(I1, t1); I2 = badd(I2, t2)
        vt = min(bval(t1), bval(t2))
        small = small + 1 if vt > tgt + 60 else 0
        if small >= 12 and n > 20: break
        n += 1
        acc = F[n] if n <= 6 else (K(0), K(0))
        for i in range(1, n): acc = bsub(acc, bm(Y[i], Y[n - i], U))
        Y.append(bm(acc, I2Y0, U))
        g = (K(0), K(0))
        for i in range(1, n + 1): g = badd(g, bm(Y[i], Gi[n - i], U))
        Gi.append(bsc(-1, bm(g, Gi[0], U)))
        sn1 = bm(sn1, s, U)
        Ys = badd(Ys, bm(Y[n], bm(sn1, binv(s, U), U), U))
        assert n < 4000
    # branch: the continuation Y(s) of -y1 must end at +y2 (right branch), not at -y2
    zr, zw = bval(bsub(Ys, y2)), bval(badd(Ys, y2))
    return dict(log=(I1[0], I2[0]), th=(I1[1], I2[1]), n=n, c=cmin, branch=(zr, zw))
def tiny(D, tgt):
    r = tiny_x(f, D, tgt)
    if r is not None and r['branch'][0] > r['branch'][1] + 50: r['chart'] = 'x'; return r
    u, v = D; ui = 1 / u[0]
    up = [ui, u[1] * ui, K(1)]
    vp = pad(pdivrem([K(0), K(0), v[1], v[0]], up)[1], 2)
    r2 = tiny_x(list(reversed(f)), (up, vp), tgt)
    assert r2 is not None and r2['branch'][0] > r2['branch'][1] + 50, "no chart"
    r2['log'] = (-r2['log'][1], -r2['log'][0]); r2['th'] = (-r2['th'][1], -r2['th'][0]); r2['chart'] = 'inf'
    return r2
NM = 4 * 3**2 * 5 * 7 * 11 * 13
def jlog(D, a=4):
    N = 2**a * NM; ND = jmul(N, D); r = tiny(ND, TGT)
    cap = TGT + 50 - 3 * valuation(N, 2)     # series truncation (terms summed until below pi^(TGT + 60)), not tracked by Sage
    return ((r['log'][0] / N).add_bigoh(cap), (r['log'][1] / N).add_bigoh(cap)), r
# ---------------- exact points near the stored local divisors (Newton for V in B, then the Lemma G test)
def genuine(u, V0):
    U = (u[0], u[1]); fB = bfromx(f, U); W = (V0[0], V0[1])
    for it in range(14): W = bsc(1 / K(2), badd(W, bm(fB, binv(W, U), U)))
    rho = bsub(bm(fB, binv(bm(W, W, U), U), U), (K(1), K(0)))
    return [u, [W[0], W[1]]], min(btr(rho, U).valuation(), bnorm(rho, U).valuation() / 2)
Ds = []
for i in range(len(DAT['DU'])):
    u = [kv(c) for c in DAT['DU'][i]]; V0 = pad([kv(c) for c in DAT['DV'][i]], 2)
    assert len(u) == 3 and u[2] == 1
    D, vr = genuine(u, V0); assert vr > 6, "Lemma G condition"
    Ds.append(D)
PH = []
for j in range(2):
    u = [kv(c) for c in DAT['PHIU'][j]]; v = pad([kv(c) for c in DAT['PHIV'][j]], 2)
    PH.append([u, v])
print("  D_1..D_7 exact near the stored ones (v(rho) > 2 v(2)); phi_a, phi_b from PHI (%.0f s)" % (time.time() - t00))
LOGS = []; INFO = []
for D in Ds + PH:
    l, r = jlog(D); LOGS.append(l); INFO.append(r)
print("  logs: chart %s, terms %s, c %s" % ([r['chart'] for r in INFO], [r['n'] for r in INFO], [r['c'] for r in INFO]))
print("  logs: absolute precisions %s; theta-coefficient valuations (should exceed the target) %s; branch margins %s; min v(remainder u | f - v^2) %d"
      % ([min(l[0].precision_absolute(), l[1].precision_absolute()) for l in LOGS], [min(x.valuation() for x in r['th']) for r in INFO],
         [r['branch'][0] - r['branch'][1] for r in INFO], RES[0]))
# two values of N (consistency)
l5 = [jlog(D, 5)[0] for D in Ds[:2]]
print("  log D_1, D_2 with N = 2^4 NM and 2^5 NM: valuations of the differences %s" % [min((l5[i][c] - LOGS[i][c]).valuation() for c in range(2)) for i in range(2)])
# comparison with the certified balls of p21_45
def pbval(i, c): return sum(K(QQ(q)) * pi**m for m, q in enumerate(DAT['PB_LOGS'][i][c]))
cmp = []
for i in range(9):
    dv = min((LOGS[i][c] - pbval(i, c)).valuation() for c in range(2)); mp = min(LOGS[i][c].precision_absolute() for c in range(2)); bp = min(ZZ(DAT["PB_PREC"][i][c]) for c in range(2))
    cmp.append((dv, mp, bp, dv >= min(mp, bp)))
print("  my log against the certified ball of p21_45, per point: (v(difference), my precision, certified precision, consistent): %s" % cmp)
# ---------------- the lattice, independently (ZZ-module spans of 2-adic approximations)
Q2f = Qp(2, PREC2)
def coords(l):
    # coordinates on (1, pi, pi^2) twice, as rationals, and the least absolute pi-adic precision m of the two entries
    out = []; mm = 10**9
    for c in l:
        m = c.precision_absolute(); mm = min(mm, m)
        pol = [Q2f(q) for q in c.polynomial().list()]
        pol = pol + [Q2f(0)] * (3 - len(pol))
        chk = sum(K(pol[i]) * pi**i for i in range(3)) - c
        assert chk.valuation() >= min(m, chk.precision_absolute()) - 3, "coordinates"
        for i in range(3):
            out.append(QQ(pol[i].lift()) if pol[i] != 0 else QQ(0))
    return vector(QQ, out), mm
CO = [coords(l) for l in LOGS]
jmin = min(p for (_, p) in CO[:7])
def pim(m): return diagonal_matrix(ZZ, [2**max(0, ceil((m - i) / 3)) for i in range(3)] * 2)
Gm = matrix(QQ, [CO[i][0] for i in range(7)]).transpose()
sc = lcm([QQ(e).denominator() for e in Gm.list()] + [1]); assert sc == 2**valuation(sc, 2)
def span_with(m):   # ZZ-span of the columns of sc*G and sc*pi^m O^2 (index a power of 2: the Z_(2)-lattice meets ZZ^6 in it)
    gens = [sc * Gm.column(i) for i in range(7)] + [sc * pim(m).column(i) for i in range(6)]
    return (ZZ**6).span([vector(ZZ, g) for g in gens])
def contains_pim(L, m): return all(vector(ZZ, sc * pim(m).column(i)) in L for i in range(6))
M = 6
assert contains_pim(span_with(M + 3), M) and jmin >= M + 3
Lam = span_with(M)
mL = M
while mL > 0 and contains_pim(Lam, mL - 1): mL -= 1
Hb = Lam.basis_matrix().transpose() / sc        # columns: a basis of Lambda (coordinates on 1, pi, pi^2 twice)
ed = [valuation(d, 2) - valuation(sc, 2) for d in (sc * Hb).change_ring(ZZ).elementary_divisors()]
print("  Lambda (independent): pi^%d O^2 in span(l_i) + pi^%d O^2 (Nakayama test), m_Lambda = %d (pi^%d O^2 not in Lambda: %s), index [O^2 : Lambda] = 2^%d, elementary divisors 2^%s"
      % (M, M + 3, mL, mL - 1, not contains_pim(Lam, mL - 1), valuation(Hb.det(), 2), ed))
Hi = Hb.inverse()
def lcoords(l):
    v, m = coords(l); y = Hi * v
    assert all(valuation(e.denominator(), 2) == 0 for e in y if e != 0), "vector in Lambda"
    return y, floor((m - mL) / 3)
def red2(y, j): return vector(ZZ, [ZZ(Integers(2**j)(e)) for e in y])
RhoD = matrix(GF(2), [red2(lcoords(LOGS[i])[0], 1) for i in range(7)]).transpose()
SC = matrix(GF(2), 7, int(DAT['SELCOEF'].matsize()[1]), lambda i, j: ZZ(DAT['SELCOEF'][i, j]))
KC = matrix(GF(2), 7, 3, lambda i, j: ZZ(DAT['KNOWNCOEF'][i, j]))
Wm = (RhoD * SC).column_space()
ya, ja = lcoords(LOGS[7]); yb, jb = lcoords(LOGS[8])
print("  rank rho = %d; rho(T) = 0: %s; rho(phi_a), rho(phi_b) from logs = from x - T classes: %s, %s; dim W = %d; coordinates of log phi_a, phi_b known mod 2^%d, 2^%d"
      % (RhoD.rank(), (RhoD * KC.column(0)) == 0, red2(ya, 1).change_ring(GF(2)) == RhoD * KC.column(1), red2(yb, 1).change_ring(GF(2)) == RhoD * KC.column(2), Wm.dimension(), ja, jb))
jj = min(ja, jb)
Ym = matrix(ZZ, [red2(ya, jj), red2(yb, jj)]).transpose()
Dm, Um, Vm = Ym.smith_form()
assert Um * Ym * Vm == Dm and abs(Um.det()) == 1
d1, d2 = sorted(valuation(Dm[i, i], 2) for i in range(2))
rpr = jj - d2
# saturation rows: Dm is diagonal in the first two rows (Sage), the projection is rows 2..5 of Um
def prj(y): return (Um * y)[2:6]
prW = matrix(GF(2), [prj(vector(ZZ, [ZZ(e) for e in w])) for w in Wm.basis()]).transpose() if Wm.dimension() else matrix(GF(2), 4, 0)
print("  saturation: elementary divisors 2^%d, 2^%d; pr known mod 2^%d; dim pr(W) = %d" % (d1, d2, rpr, prW.rank()))
def nu_class(y, jy):
    p = prj(y); nu = min(valuation(e, 2) for e in p if e != 0)
    t = max([0] + [-valuation(e, 2) for e in y if e != 0])
    ok = nu + 1 + t <= rpr and nu + 1 <= jy
    cl = vector(GF(2), [ZZ(Integers(2)(e / 2**nu)) for e in p])
    inW = prW.rank() == matrix(GF(2), prW.columns() + [cl]).transpose().rank() if prW.ncols() else cl == 0
    return nu, cl, inW, ok
E1MINE = {}
for j in range(2):
    c1 = (kv(DAT['C1'][j][0]), kv(DAT['C1'][j][1]))
    v, m = coords(c1); y = Hi * v
    nu, cl, inW, ok = nu_class(y, floor((m - mL) / 3))
    print("  x_%s: nu(pr c_1) = %d, class %s, in pr(W): %s, within precision: %s" % (DAT['PHIIDX'][j], nu, cl, inW, ok))
    E1MINE[j] = (nu, cl)
print("  (certified by p21_45: M = %s, m_Lambda = %s, d = %s, r = %s, E1 = %s)" % (DAT['PB_M'], DAT['PB_mL'], DAT['PB_d'], DAT['PB_r'], DAT['PB_E1']))
sys.stdout.flush()
if CEN == "none": sys.exit(0)
# ---------------- the Abel-Prym map at the centres, independently
QM = [matrix(K, 3, 3, [kv(DAT['QM'][i][r, c]) for r in range(3) for c in range(3)]) for i in range(3)]
dl = kv(DAT['DELTA'])
QD = []
for i in range(3):
    Eb = [matrix(K, 2, 2, [1, 0, 0, 0]), matrix(K, 2, 2, [0, 1/K(2), 1/K(2), 0]), matrix(K, 2, 2, [0, 0, 0, 1])][i]
    QD.append(block_matrix(K, [[QM[i], zero_matrix(K, 3, 2)], [zero_matrix(K, 2, 3), -dl * Eb]]))
Qx = PolynomialRing(QQ, 'x,y,z'); xx, yy, zz = Qx.gens()
Fq = xx**4 + 3*xx**3*yy - 3*xx**2*yy*zz - 3*xx**2*zz**2 + 6*xx*yy**3 - 6*xx*yy**2*zz + 3*xx*yy*zz**2 - 2*xx*zz**3 + 4*yy**4 + 2*yy**3*zz - 5*yy*zz**3
DISCS = [[ZZ(c) for c in d] for d in COM['DISCS']]
Z2 = Zp(2, PREC2)
def centre_point(d, X0):
    ch, a0, b0, kk = d[0], d[1], d[2], d[3]
    c1 = a0 + 2**kk * X0
    Tq = PolynomialRing(QQ, 'T'); T = Tq.gen()
    Fu = Fq(c1, T, 1) if ch == 1 else (Fq(c1, 1, T) if ch == 2 else Fq(1, c1, T))
    Fz = Fu.change_ring(Z2); dF = Fz.derivative()
    c = Z2(b0).lift_to_precision(PREC2 - 10)
    for it in range(40): c = c - Fz(c) / dF(c)
    assert Fz(c).valuation() > 2 * dF(c).valuation() and (c - b0).valuation() >= kk
    cq = K(c)
    return [K(c1), cq, K(1)] if ch == 1 else ([K(c1), K(1), cq] if ch == 2 else [K(1), K(c1), cq])
def ksqrt(a):
    va = a.valuation()
    if va % 2: return None
    bet = a / pi**va
    r0 = None
    for bits in cartesian_product([[0, 1]] * 6):
        cand = 1 + sum(bits[i] * pi**(i + 1) for i in range(6))
        if (bet - cand**2).valuation() >= 7: r0 = K(cand); break
    if r0 is None: return None
    r0 = r0.lift_to_precision(K.precision_cap())
    for it in range(14): r0 = (r0 + bet / r0) / 2
    assert (r0**2 - bet).valuation() > 1000
    return r0 * pi**(va // 2)
def star(A):
    B = matrix(A.base_ring(), 4, 4)
    B[0, 1] = A[2, 3]; B[0, 2] = A[3, 1]; B[0, 3] = A[1, 2]; B[1, 2] = A[0, 3]; B[1, 3] = A[2, 0]; B[2, 3] = A[0, 1]
    for i in range(4):
        for j in range(i): B[i, j] = -B[j, i]
    return B
def apm(P5):
    Pv = vector(K, P5)
    J = matrix(K, [QD[i] * Pv for i in range(3)])
    best = None
    for cs in Subsets(range(5), 3):
        cs = sorted(cs); mnr = J.matrix_from_columns(cs); dt = mnr.det()
        if dt != 0 and (best is None or dt.valuation() < best[1].valuation()): best = (cs, dt, mnr)
    cs, dt, mnr = best
    ad = mnr.adjugate(); Tsel = None
    for n in [q for q in range(5) if q not in cs]:
        Tn = [K(0)] * 5; Tn[n] = dt; sol = ad * J.column(n)
        for i in range(3): Tn[cs[i]] = -sol[i]
        Tv = vector(K, Tn); assert min(e.valuation() for e in J * Tv) > 500, "kernel vector"
        a0 = [Tv * QD[i] * Tv for i in range(3)]
        if a0[2] != 0 and (Tsel is None or a0[2].valuation() < Tsel[1][2].valuation()): Tsel = (Tv, a0)
    Tv, a0 = Tsel
    U = (a0[0] / a0[2], 2 * a0[1] / a0[2])
    th1 = (K(0), K(1)); th2 = bm(th1, th1, U)
    def Mt(i, j): return badd(badd((QM[0][i, j], K(0)), bsc(2 * QM[1][i, j], th1)), bsc(QM[2][i, j], th2))
    G = [[Mt(i, j) if (i < 3 and j < 3) else ((-dl, K(0)) if (i == 3 and j == 3) else (K(0), K(0))) for j in range(4)] for i in range(4)]
    av = [(Pv[0], K(0)), (Pv[1], K(0)), (Pv[2], K(0)), (Pv[3], Pv[4])]
    bw = [(Tv[0], K(0)), (Tv[1], K(0)), (Tv[2], K(0)), (Tv[3], Tv[4])]
    A = [[bsub(bm(av[i], bw[j], U), bm(bw[i], av[j], U)) for j in range(4)] for i in range(4)]
    def mm(X1, X2):
        return [[sum_pairs([bm(X1[i][l], X2[l][j], U) for l in range(4)]) for j in range(4)] for i in range(4)]
    GA = mm(mm(G, A), G)
    SA = [[None] * 4 for _ in range(4)]
    for (i, j, (p, q)) in [(0, 1, (2, 3)), (0, 2, (3, 1)), (0, 3, (1, 2)), (1, 2, (0, 3)), (1, 3, (2, 0)), (2, 3, (0, 1))]:
        SA[i][j] = A[p][q]; SA[j][i] = bsc(-1, A[p][q])
    for i in range(4): SA[i][i] = (K(0), K(0))
    piv = None
    for i in range(4):
        for j in range(i + 1, 4):
            nv = bnorm(SA[i][j], U)
            if nv != 0 and (piv is None or nv.valuation() < piv[2]): piv = (i, j, nv.valuation())
    Yv = bm(GA[piv[0]][piv[1]], binv(SA[piv[0]][piv[1]], U), U)
    chk1 = min(bval(bsub(GA[i][j], bm(Yv, SA[i][j], U))) for i in range(4) for j in range(4))
    chk2 = bval(bsub(bm(Yv, Yv, U), bfromx(f, U)))
    return [[U[0], U[1], K(1)], [Yv[0], Yv[1]]], chk1, chk2, bnorm((K(0), K(1)), U), U
def sum_pairs(L):
    r = (K(0), K(0))
    for p in L: r = badd(r, p)
    return r
PBC = [l for l in open("data/centres_twist%d.txt" % k).read().split("\n") if l.strip()]
rows = []
for l in PBC:
    v = [int(e) for e in l.replace('[', ' ').replace(']', ' ').replace(',', ' ').split()]
    rows.append(dict(di=v[0], X0=v[1], s=v[2], nu=v[3], cl=v[4:8], inW=v[8], vM=v[9]))
if CEN != "all": rows = rows[:int(CEN)]
nag = 0; t1 = time.time(); worst = 10**9; cmin1 = cmin2 = 10**9; DV = []
for rw in rows:
    P = centre_point(DISCS[rw['di'] - 1], rw['X0'])
    Pv = vector(K, P); q = [Pv * QM[i] * Pv for i in range(3)]
    r = ksqrt(q[0] / dl) if q[0] != 0 else None
    if r is not None: sv = q[1] / (dl * r)
    else: sv = ksqrt(q[2] / dl); r = q[1] / (dl * sv)
    D, chk1, chk2, ndisc, U = apm(P + [r, sv]); cmin1 = min(cmin1, chk1); cmin2 = min(cmin2, chk2)
    DV.append((U[1]**2 - 4 * U[0]).valuation())
    lam0, info = jlog(D); rw["lam0"] = lam0
    lam = (lam0[0] - LOGS[7][0], lam0[1] - LOGS[7][1])
    y, jy = lcoords(lam)
    nu, cl, inW, ok = nu_class(y, jy); rw["mycl"] = cl; rw["mynu"] = nu
    worst = min(worst, min(rpr, jy) - nu - 1)
    same = (nu == rw['nu']) and (inW == bool(rw['inW']))
    crit = rw['vM'] + 3 * rw['s'] >= 3 * (nu + 1) + mL
    if same and ok and crit and not inW: nag += 1
    else: print("  DISAGREE or not certified: %s: mine nu = %d, class %s, inW %s, within precision %s, criterion %s" % (rw, nu, cl, inW, ok, crit))
    sys.stdout.flush()
print("  centres: %d of %d agree with p21_46 (nu, not in pr(W)) and satisfy the criterion with the independent m_Lambda; least precision margin %d; least valuations of GAG - Y star(A) and Y^2 - f over the centres %d, %d (%.0f s)"
      % (nag, len(rows), worst, cmin1, cmin2, time.time() - t1))
print("  valuations of disc U of phi(P) at the centres: min %d, max %d" % (min(DV), max(DV)))
# ---------------- known-answer test against the exact tiny series of p21_9_tiny (normalisation of phi and log, signs)
KNOWN = {0: [(0, 1, 0, 0), (1, 1, 1, 2)], 1: [(0, 3, 0, 1), (1, 2, -1, -1)]}[k]   # (j in PHI order, disc, X_i, x(P_i))
TW = [[[kv(c) for c in DAT['TINYW'][j][0]], [kv(c) for c in DAT['TINYW'][j][1]]] for j in range(2)]
out = []
for rw in rows:
    for (j, di, Xi, xi) in KNOWN:
        if rw['di'] != di or valuation(rw['X0'] - Xi, 2) < 3: continue
        d = DISCS[di - 1]; tau = K(d[1] + 2**d[3] * rw['X0'] - xi)
        ser = [sum(TW[j][c][m - 1] / m * tau**m for m in range(1, len(TW[j][c]) + 1)) for c in range(2)]
        lj = LOGS[7 + j]
        dp = min((rw['lam0'][c] - lj[c] - ser[c]).valuation() for c in range(2))
        dm = min((-rw['lam0'][c] - lj[c] - ser[c]).valuation() for c in range(2))
        out.append((rw['di'], rw['X0'], valuation(rw['X0'] - Xi, 2), min(ser[c].valuation() for c in range(2)), max(dp, dm), '+' if dp > dm else '-'))
print("  tiny-series KAT (disc, X0, v2(X0 - X_i), v(series), v(log phi(P) - log phi(x_i) - series) for the better sign, sign): %s" % out)
# ---------------- numerical test of the box claims at random points (9.5 to 9.7): constant boxes and tail boxes
def lam_at(di, X):
    P = centre_point(DISCS[di - 1], X)
    Pv = vector(K, P); q = [Pv * QM[i] * Pv for i in range(3)]
    r = ksqrt(q[0] / dl) if q[0] != 0 else None
    if r is not None: sv = q[1] / (dl * r)
    else: sv = ksqrt(q[2] / dl); r = q[1] / (dl * sv)
    D = apm(P + [r, sv])[0]
    l0 = jlog(D)[0]
    lam = (l0[0] - LOGS[7][0], l0[1] - LOGS[7][1])
    y, jy = lcoords(lam)
    return l0, nu_class(y, jy)
set_random_seed(20260927)
bad = 0; nt = 0; slackmin = 10**9
for rw in rows:
    for rep in range(2):
        rr = ZZ.random_element(1, 2**20)
        X = rw['X0'] + 2**rw['s'] * rr
        l0, (nu, cl, inW, ok) = lam_at(rw['di'], X)
        # compare with the centre (either lift: l0 or -l0)
        dv = max(min((l0[c] - rw['lam0'][c]).valuation() for c in range(2)), min((-l0[c] - rw['lam0'][c]).valuation() for c in range(2)))
        bound = rw['vM'] + 3 * valuation(X - rw['X0'], 2)
        nt += 1; slackmin = min(slackmin, dv - bound)
        if not (nu == rw['mynu'] and cl == rw['mycl'] and ok and dv >= bound):
            bad += 1; print("  BOX TEST FAILS: %s at X = %s: nu %d, class %s, v(difference) %d, bound %d" % ((rw['di'], rw['X0'], rw['s']), X, nu, cl, dv, bound))
print("  constant boxes, 2 random points each: %d tests, %d failures; least v(lambda(X) - lambda(X0)) - (vM + 3 v2(X - X0)) = %d" % (nt, bad, slackmin))
# tail boxes: nu = nu1 + j and class e1 for v2(X - X_i) = j >= J0
TB = []
for l in open("data/boxes_twist%d.txt" % k):
    if "tail at x_" in l:
        v = l.split('"')[0].replace('[', ' ').replace(',', ' ').split()
        idx = int(l.split("tail at x_")[1].split(' ')[0]); TB.append((int(v[0]), int(v[1]), int(v[2]), idx))
KX = {0: {0: 0, 2: 1}, 1: {1: 0, 3: 1}}[k]
XI = {0: 0, 2: 1, 1: 0, 3: -1}
tb_out = []
for (di, Xm, J0, idx) in TB:
    j = KX[idx]; nu1 = E1MINE[j][0] + DISCS[di - 1][3]; e1 = E1MINE[j][1]
    for jj in [J0, J0 + 1, J0 + 3]:
        uu = 2 * ZZ.random_element(0, 2**15) + 1
        X = XI[idx] + 2**jj * uu
        l0, (nu, cl, inW, ok) = lam_at(di, X)
        tb_out.append((idx, jj, nu, nu == nu1 + jj, cl == e1, ok))
print("  tail boxes (x_i, j = v2(X - X_i), nu, nu = nu1 + j, class = e1, certified precision): %s" % tb_out)
print("done (%.0f s)" % (time.time() - t00))
