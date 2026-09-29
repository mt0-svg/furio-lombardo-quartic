# box_bounds.sage: the sup bounds of the covering and its box criteria (see the paper), plus three
# independent checks of the box lists: the disc hypotheses, the covering (disjoint congruence classes of
# total measure 1 in each disc) and the exclusions.
#
# Disc d = (chart, a0, b0, k): G(X, Y) = F(a0 + 2^k X, b0 + 2^k Y) = sum g_ij X^i Y^j with v(g_ij) > v(g01) for
# j >= 1, (i, j) != (0, 1), and v(g_i0) >= v(g01) (checked); then |F_u| = 2^(k - v(g01)) on the disc and
# |Y(X) - Y(X')| <= |X - X'|. A disc of radius 2^-R' in X around X0 has |t - t0|, |u - u0| <= 2^-(k + R') around
# the rational point (t0, u0) (u0 the dependent coordinate modulo 2^200, far below every radius used).
# Taylor bound (9.2) at v (e = 3): for a quadric q, v(q(P) - q(t0, u0)) >= TB(q, R) :=
#   min(min(v q_t, v q_u) + 3R, min(v q_tt/2, v q_tu, v q_uu/2) + 6R), all values exact in K21, taken at v.
# Sup bound (9.4) on the parent disc B of radius 2^-(s-1) (R = k + s - 1): branch Q1 if TB(Q1) > v(Q1(t0, u0)) + 6
# (then r = r0 (Q1/Q1(t0, u0))^(1/2) is analytic on B, v(r) = v(Q1(t0, u0)/delta)/2 constant, and
# s = Q2/(delta r) has v(s) >= min(v Q2(t0, u0), TB(Q2)) - v(delta) - v(r)); branch Q3 symmetrically.
#   vM = 3k + min(v(a12) + inf v(s), v(a21) + inf v(r)) - 3 (v(g01) - k)      (w = dlambda/dX, pi-adic valuation)
# Constant box (9.6): vM + 3s >= 3 (nu0 + 1) + m_Lambda with nu0 from centres (own values).
# Tail box at x_i (9.7): B the disc of radius 2^-(s0-1) around X_i (s0 from the verdict, and the least s0 for which
# a branch is analytic), nu1 = nu(pr c_1) + k, J0 = max(s0, ceil((3 (nu1 + 1 + s0) + m_Lambda - vM)/3)) <= level.
# Exclusion (9.3): on the box S itself (R = k + s), q = Q1 or Q3 with TB(q) > v(q(t0, u0)) + 6 and q(t0, u0)/delta a
# non-square in K_v.
# Usage: sage box_bounds.sage PREC_CENTRES   (reads lattice.sobj, centres_prec<PREC>.sobj; writes box_bounds_twist<k>.txt)
import sys, re
load('loader.sage'); load('jacobian_log.sage')
PC = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
X = s3_exact(); S = s3_setup(300, X); Kv = S['Kv']; emb = S['emb']
LAT = load('lattice.sobj'); CEN = load('centres_prec%d.sobj' % PC)
DISCS = s3_discs(); TI = s3_tiny(X)
XI = {0: (1, 0), 2: (1, 1), 1: (3, 0), 3: (2, -1)}
Qk = X['Qc']

def vK(z):
    # exact pi-adic valuation at v of an exact K21 element (via the certified embedding); +oo for 0
    if z == 0:
        return Infinity
    return vex(emb(z))

def bivar(q, chart):
    # q(x, y, z) quadratic form, coefficients (x2, xy, xz, y2, yz, z2) -> (A, B, C, D, E, F0) of
    # A t^2 + B t u + C u^2 + D t + E u + F0 in the chart (t = x; u = y for chart 1 (z = 1), u = z for chart 2 (y = 1))
    c1, c2, c3, c4, c5, c6 = q
    if chart == 1:
        return (c1, c2, c4, c3, c5, c6)
    return (c1, c3, c6, c2, c5, c4)

def taylor(q, chart, t0, u0):
    A, B, C, D, E, F0 = bivar(q, chart)
    val = A * t0^2 + B * t0 * u0 + C * u0^2 + D * t0 + E * u0 + F0
    lin = [2 * A * t0 + B * u0 + D, B * t0 + 2 * C * u0 + E]
    quad = [A, B, C]
    return val, min(vK(z) for z in lin), min(vK(z) for z in quad)

def TB(tq, R):
    return min(tq[1] + 3 * R, tq[2] + 6 * R)

def gcoefs(disc):
    chart, a0, b0, k, par = disc
    Ft = chart_poly(chart)
    R2 = PolynomialRing(QQ, 'Xv,Yv'); Xv, Yv = R2.gens()
    G = Ft(a0 + 2^k * Xv, b0 + 2^k * Yv)
    return {(e[0], e[1]): c for e, c in G.dict().items()}

def disc_ok(disc):
    g = gcoefs(disc)
    v01 = g[(0, 1)].valuation(2)
    ok = all(c.valuation(2) > v01 for (i, j), c in g.items() if j >= 1 and (i, j) != (0, 1))
    ok = ok and all(c.valuation(2) >= v01 for (i, j), c in g.items() if j == 0)
    return ok, v01

def point(disc, X0):
    t0, c, m, vs = disc_point(disc, X0, 200)
    assert m >= 150
    return QQ(t0), QQ(c)

def supbound(disc, t0, u0, R, k_tw):
    chart, a0, b0, k, par = disc
    dl = X['delta'][k_tw]; vdl = vK(dl)
    T = [taylor(q, chart, t0, u0) for q in Qk]
    tb = [TB(tq, R) for tq in T]
    vq = [vK(tq[0]) for tq in T]
    A = TI[[i for i in TI if TI[i]['k'] == k_tw][0]]['A']
    va12 = vK(A[0, 1]); va21 = vK(A[1, 0])
    okd, v01 = disc_ok(disc)
    assert okd
    vFu = 3 * (v01 - k)
    out = []
    if vq[0] < Infinity and tb[0] > vq[0] + 6:
        vr = (vq[0] - vdl) / 2
        vs = min(vq[1], tb[1]) - vdl - vr
        out.append(('Q1', 3 * k + min(va12 + vs, va21 + vr) - vFu, vr, vs))
    if vq[2] < Infinity and tb[2] > vq[2] + 6:
        vs = (vq[2] - vdl) / 2
        vr = min(vq[1], tb[1]) - vdl - vs
        out.append(('Q3', 3 * k + min(va12 + vs, va21 + vr) - vFu, vr, vs))
    if not out:
        return None
    return max(out, key=lambda o: o[1])

allok = True
# (0) the five discs cover C(Q_2): P^2(Q_2) = {z = 1: x, y in Z_2} u {y = 1: x in Z_2, z in 2 Z_2} u {x = 1: y, z in 2 Z_2};
# in chart z = 1 the residue class (x, y) = (0, 1) mod 2 and the whole chart x = 1 have no point, since there
# G = F(a0 + 2 X, b0 + 2 Y) has v(g00) < v(g_ij) for all (i, j) != (0, 0) (so |G| = |g00| on Z_2^2).
R2c = PolynomialRing(QQ, "Xv,Yv"); Xc, Yc = R2c.gens()
Fq3 = _FQ
empties = [("chart z = 1, (x, y) = (0, 1) mod 2", Fq3(2 * Xc, 1 + 2 * Yc, 1)), ("chart x = 1, y, z in 2 Z_2", Fq3(1, 2 * Xc, 2 * Yc))]
for lab, G in empties:
    cs = {tuple(e): c for e, c in G.dict().items()}; v00 = cs.get((0, 0), 0).valuation(2)
    emp = all(c.valuation(2) > v00 for e, c in cs.items() if e != (0, 0))
    print("(0) %s: no Q_2-point (v(g00) = %d below all other coefficients): %s" % (lab, v00, emp))
    allok = allok and emp
cov = sorted((d[0], d[1] % 2, d[2] % 2, d[3]) for d in DISCS)
print("(0) discs (chart, a0 mod 2, b0 mod 2, k):", cov, "; chart z = 1 classes (0,0), (1,0), (1,1) and chart y = 1 classes x = 0, 1 mod 2 (z in 2 Z_2) are the five discs:",
      cov == [(1, 0, 0, 1), (1, 1, 0, 1), (1, 1, 1, 1), (2, 0, 0, 1), (2, 1, 0, 1)])
allok = allok and cov == [(1, 0, 0, 1), (1, 1, 0, 1), (1, 1, 1, 1), (2, 0, 0, 1), (2, 1, 0, 1)]
for k in [0, 1]:
    print('\n==== twist k = %d ====' % k)
    L = LAT[k]; mL = L['mL']
    boxes = s3_boxes(k)
    # (a) disc hypotheses of 9.1
    for dd in sorted(set(b['disc'] for b in boxes)):
        ok, v01 = disc_ok(DISCS[dd - 1])
        print(' disc %d = %s: hypotheses of 9.1 %s, v(g01) = %d' % (dd, DISCS[dd - 1], ok, v01))
        allok = allok and ok
    # (b) covering: in each disc the boxes are disjoint congruence classes of total measure 1
    for dd in sorted(set(b["disc"] for b in boxes)):
        bl = [(b['X0'] % 2^b['level'], b['level']) for b in boxes if b['disc'] == dd]
        meas = sum(QQ(1) / 2^s for (x0, s) in bl)
        disj = all(not ((x1 - x0) % 2^min(s0, s1) == 0) for a, (x0, s0) in enumerate(bl) for (x1, s1) in bl[a + 1:])
        print(' disc %d: %d boxes, total measure %s, pairwise disjoint %s' % (dd, len(bl), meas, disj))
        allok = allok and meas == 1 and disj
    print(' discs without any box: %s' % [dd for dd in range(1, 6) if dd not in set(b['disc'] for b in boxes)])
    cen = {(o['disc'], o['X0'], o['level']): o for o in CEN[k]}
    fo = open('box_bounds_twist%d.txt' % k, 'w')
    fo.write('# [disc, X0, level, verdict kind, vM (own), branch, own nu0 (constant) or J0 (tail), criterion holds, slack]\n')
    nex = ncon = ntail = 0; minslack = None
    for b in boxes:
        d = DISCS[b['disc'] - 1]; chart, a0, b0, kk, par = d
        v = b['verdict']
        if v.startswith('excluded'):
            t0, u0 = point(d, b['X0'])
            R = kk + b['level']
            chart_ = chart
            res = None
            for qi in [0, 2]:
                tq = taylor(Qk[qi], chart_, t0, u0)
                vq = vK(tq[0])
                if vq < Infinity and TB(tq, R) > vq + 6:
                    sq = csqrt(emb(tq[0] / X['delta'][k]))
                    if sq is None:
                        res = 'Q%d' % (qi + 1); break
            ok = res is not None
            allok = allok and ok; nex += 1
            fo.write(str([b['disc'], b['X0'], b['level'], 'excluded', None, res, None, ok, None]) + '\n')
            if not ok:
                print(' EXCLUSION NOT CONFIRMED:', b)
            continue
        if v.startswith('constant'):
            s = b['level']; assert s >= 1
            t0, u0 = point(d, b['X0'])
            sb = supbound(d, t0, u0, kk + s - 1, k)
            assert sb is not None, 'no analytic branch on the parent box'
            o = cen[(b['disc'], b['X0'], b['level'])]
            lhs = sb[1] + 3 * s; rhs = 3 * (o['nu0'] + 1) + mL
            ok = lhs >= rhs
            allok = allok and ok; ncon += 1
            minslack = lhs - rhs if minslack is None else min(minslack, lhs - rhs)
            m_ = re.search(r'vM = (\d+)', v)
            fo.write(str([b['disc'], b['X0'], b['level'], 'constant', sb[1], sb[0], o['nu0'], ok, lhs - rhs, int(m_.group(1)) if m_ else None]) + '\n')
            continue
        if v.startswith('tail'):
            i_ = int(re.search(r'x_(\d)', v).group(1))
            s0v = int(re.search(r'radius 2\^-(\d+)', v).group(1)) + 1
            di, Xi = XI[i_]
            assert di == b['disc'] and (b['X0'] - Xi) % 2^b['level'] == 0
            # the centre of the tail disc is P_i itself (exact rational point)
            Pi = [p for p in X['PHI'][i_]['x'][:3]]
            t0 = QQ(Pi[0]); u0 = QQ(Pi[1]) if chart == 1 else QQ(Pi[2])
            assert t0 == a0 + 2^kk * Xi
            least = None
            for s0 in range(1, 12):
                if supbound(d, t0, u0, kk + s0 - 1, k) is not None:
                    least = s0; break
            sb = supbound(d, t0, u0, kk + s0v - 1, k)
            assert sb is not None
            nu1 = L["NU1"][i_] + kk          # nu(pr g0), g0 = 2^k c_1 (lattice layer)
            J0 = max(s0v, ceil((3 * (nu1 + 1 + s0v) + mL - sb[1]) / 3))
            ok = J0 <= b['level'] and not (L['E1'][i_] in L['prW'])
            allok = allok and ok; ntail += 1
            m_ = re.search(r'vM = (\d+)', v)
            fo.write(str([b['disc'], b['X0'], b['level'], 'tail x_%d' % i_, sb[1], sb[0], J0, ok, b['level'] - J0, int(m_.group(1)) if m_ else None, s0v, least, nu1]) + '\n')
            print(' tail box at x_%d: level %d, s0 %d (least analytic s0 %s), vM %s (%s), nu1 %d, J0 %d, J0 <= level: %s, e1 outside pr(W): %s'
                  % (i_, b['level'], s0v, least, sb[1], sb[0], nu1, J0, J0 <= b['level'], not (L['E1'][i_] in L['prW'])))
            continue
        raise ValueError(v)
    fo.close()
    print(" %d excluded boxes (exclusion confirmed at each, else reported above); %d constant boxes, least slack of vM + 3s - 3(nu0 + 1) - m_Lambda: %s; %d tail boxes" % (nex, ncon, minslack, ntail))
print('\nALL CHECKS PASS' if allok else '\nSOME CHECK FAILED')
