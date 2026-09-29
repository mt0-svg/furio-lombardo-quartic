# compare_lattice_basis.sage: basis matching with the PARI lattice data (code/earlier-computations/data/lattice_twist<k>.bin, read after the own
# results were committed). Compares: the Eisenstein polynomials (same uniformizer), the logarithms of D_1..D_7,
# phi_a, phi_b as vectors of K_v^2, the lattices Lambda, the saturations (kernels of pr), and the classes through the
# change of basis G in GL_4(F_2) with pr_PARI = G pr_Sage modulo 2 on Lambda.
load('exact_data.sage')
LG = load('logs_prec1000.sobj'); LAT = load('lattice.sobj'); CEN = load('centres_prec1000.sobj')
def pget(L, key):
    return pari('mapget')(L, pari('"%s"' % key))
for k in [0, 1]:
    print('==== twist k = %d ====' % k)
    L = pari('read("../../earlier-computations/data/lattice_twist%d.bin")' % k)
    EP = pget(L, 'E')
    EPc = [ZZ(EP.polcoef(i)) for i in range(4)]
    X = s3_exact()
    load('completion_kv_eisenstein.sage'); load('genus2_log.sage')
    import itertools
    # own E: recompute at PREC 100 (only for the comparison of the polynomials)
    Q2 = Qp(2, 200)
    fac = X['K21pol'].change_ring(Q2).factor()
    g = [gg for gg, e in fac if gg.degree() == 3][0]; g = g / g.leading_coefficient()
    Cm = companion_matrix(g, format='right'); pgq = X['pg'].polynomial()
    Mpi = sum((Q2(pgq[i]) * Cm**i for i in range(pgq.degree() + 1)), matrix(Q2, 3, 3))
    ES = Mpi.charpoly('y')
    agree = min((ZZ(ES[i].lift()) - EPc[i]).valuation(2) if ZZ(ES[i].lift()) != EPc[i] else 200 for i in range(3))
    print(' Eisenstein polynomials agree modulo 2^%d (own E known modulo 2^200): same uniformizer pi = image of prgen[2]' % agree)
    logsP = pget(L, 'logs')
    def pvec(entry):
        out = []; precs = []
        for comp in entry:
            z = comp[0].lift(); m = ZZ(comp[1])
            out += [ZZ(z.polcoef(i)) for i in range(3)]; precs.append(m)
        return out, min(precs)
    mine = LG[k]['logD'] + [LG[k]['logphi'][LG[k]['ia']], LG[k]['logphi'][LG[k]['ib']]]
    labels = ['D%d' % (i + 1) for i in range(7)] + ['phi_a', 'phi_b']
    worst = None
    for lab, e, v6 in zip(labels, logsP, mine):
        pv, mp = pvec(e)
        ms = min(min(3 * v6[3 * c + j][1] + j for j in range(3)) for c in range(2))
        m = min(mp, ms)
        # agreement: pi-adic valuation of the difference, from the coordinates (v(sum a_i pi^i) = min(3 v(a_i) + i))
        dv = []
        for c in range(2):
            vals = []
            for j in range(3):
                d = QQ(v6[3 * c + j][0]) - pv[3 * c + j]
                vals.append(3 * d.valuation(2) + j if d != 0 else Infinity)
            dv.append(min(vals))
        ok = min(dv) >= m
        worst = min(dv) - m if worst is None else min(worst, min(dv) - m)
        print('  log %-6s PARI precision pi^%d, Sage pi^%d: difference has valuation >= %s -> equal within the common precision: %s' % (lab, mp, ms, min(dv), ok))
    # lattices: PARI H (columns) versus the own basis B (rows)
    H = matrix(ZZ, pget(L, 'H').sage()).transpose()      # rows = PARI basis vectors (PARI H has them as columns)
    B = LAT[k]['B']
    Binv = B.inverse(); Hinv = H.inverse()
    inS = all((h * Binv).denominator() % 2 == 1 for h in H.rows())
    inP = all((b * Hinv).denominator() % 2 == 1 for b in B.rows())
    print(' Lambda_PARI = Lambda_Sage (each basis inside the other lattice): %s' % (inS and inP))
    # pr maps on Lambda, in coordinates of the own basis B: pr_S(x) = prm x; pr_P(y) = rows orow of U applied to the
    # PARI coordinates y = Hinv-coordinates. Express both on the own basis vectors b_i.
    orow = [ZZ(t) - 1 for t in pget(L, 'orow')]
    Um = matrix(QQ, pget(L, 'U').sage())
    PP = matrix(QQ, [Um.row(i) for i in orow])            # 4 x 6 on PARI coordinates (column vectors)
    prm = LAT[k]['prm']
    # coordinates change: a vector with own coordinates x (row, v = x B) has PARI coordinates y = v Hinv = x B Hinv
    C = B * Hinv                                            # rows: own basis vectors in PARI coordinates
    to2 = lambda q: GF(2)(ZZ(q.numerator() * inverse_mod(q.denominator(), 2)) % 2)
    PPs = matrix(GF(2), [[to2(t) for t in (PP * C.row(i))] for i in range(6)]).transpose()   # 4 x 6: pr_P on own basis, mod 2
    PSs = matrix(GF(2), [[GF(2)(t) for t in prm.column(i)] for i in range(6)]).transpose()
    same_kernel = PPs.right_kernel() == PSs.right_kernel()
    print(' kernels of pr mod 2 on Lambda/2Lambda (the image of Gsat) agree: %s' % same_kernel)
    # G with PPs = G PSs (PSs has full rank 4)
    Gm = PSs.solve_left(PPs)
    assert Gm * PSs == PPs and Gm.is_invertible()
    print(' change of basis G (pr_PARI = G pr_Sage mod 2):', [list(r) for r in Gm.rows()])
    e1S = LAT[k]['E1'][LAT[k]['ia']]
    E1P = pget(L, 'E1')
    e1P = vector(GF(2), [ZZ(t) for t in E1P[0][2]])
    print(' e1: Sage %s -> G e1 = %s; PARI %s: equal %s' % (list(e1S), list(Gm * e1S), list(e1P), Gm * e1S == e1P))
    prWP = matrix(ZZ, pget(L, 'prW').sage())
    wP = vector(GF(2), [prWP[i, 0] for i in range(4)])
    wS = [w for w in LAT[k]['prW'] if w != 0][0]
    print(' pr(W): Sage nonzero element %s -> G w = %s; PARI %s: equal %s' % (list(wS), list(Gm * wS), list(wP), Gm * wS == wP))
    pr_rows = [sage_eval(l) for l in open('../../earlier-computations/data/centres_twist%d.txt' % k) if l.strip()]
    mc = {(o['disc'], o['X0'], o['level']): o for o in CEN[k]}
    agreeC = all(Gm * mc[(r[0], r[1], r[2])]['cl'] == vector(GF(2), r[4]) for r in pr_rows)
    print(' centre classes: G (Sage class) = PARI class at all %d centres: %s' % (len(pr_rows), agreeC))
