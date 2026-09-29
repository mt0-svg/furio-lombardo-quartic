# centres.sage: task 2, the constant box centres. For each box of data/boxes_twist<k>.txt whose verdict starts with
# "constant": the point P(X0) of C(Q_2) (disc_point: Newton polygon + Hensel certificate), a lift to D_delta(K_v)
# (csqrt certificate), phi of the lift (BruinKv.phi, balls), lambda = log phi(P) - log phi_a (jlog with explicit
# tail), coordinates in Lambda (lattice.sobj), nu0 and the leading class of pr lambda, and the test "class in
# pr(W)". Near a known lift x_i the result is also compared with the tiny series sum_{m <= 22} c_m tau^m of
# pullback_known_lifts.gp (a known-answer test of phi and log at 2-adic points; the series is truncated, so the agreement
# is only expected up to about v(tau^23)).
# Usage: sage centres.sage PREC   (writes centres_twist<k>_prec<PREC>.txt and centres_prec<PREC>.sobj)
import sys, time
load('loader.sage'); load('jacobian_log.sage')
PREC = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
MU = 8
t00 = time.time()
X = s3_exact(); S = s3_setup(PREC, X); Kv = S['Kv']; emb = S['emb']
T_GOAL = S['cap'] // 2
LAT = load('lattice.sobj')
DISCS = s3_discs()
TI = s3_tiny(X)
XI = {0: (1, 0), 2: (1, 1), 1: (3, 0), 3: (2, -1)}      # known lift i -> (disc index, parameter X_i)
print('PREC %d, cap %d, T_GOAL %d' % (PREC, S['cap'], T_GOAL))

def pprec_pair(l):
    return min(z.precision_absolute() for z in l)

def classify(lam, L):
    # coordinates of lam in the basis of Lambda, nu and leading class of pr(lam)
    B = L['B']; Binv = B.inverse(); mL = L['mL']; prm = L['prm']; jS = L['jS']
    v6 = vec6c(lam)
    m = min(min(3 * v6[3 * c + j][1] + j for j in range(3)) for c in range(2))
    y = vector(QQ, [QQ(a) for (a, nj) in v6])
    x = y * Binv
    jl = floor((m - mL) / 3)
    assert all(c.denominator() % 2 == 1 for c in x), 'lambda not in Lambda'
    py = [sum(prm[r, i] * x[i] for i in range(6)) for r in range(4)]
    known = min(jl, jS)
    vals = [c.valuation(2) if c != 0 else Infinity for c in py]
    nu = min(vals)
    assert nu + 1 <= known, 'precision too low for the leading class'
    cl = vector(GF(2), [ZZ((c / 2^nu).numerator() * inverse_mod((c / 2^nu).denominator(), 2)) % 2 if c != 0 else 0 for c in py])
    return nu, cl, known - (nu + 1), m, jl

RES = {}
for k in [0, 1]:
    print('\n==== twist k = %d ====' % k)
    L = LAT[k]; tw = X['tw'][k]
    Bk = BruinKv(S, X, k); f = Bk.f
    ia, ib = L['ia'], L['ib']
    phK = {}
    for a in [ia, ib]:
        U, V = tw['phi'][a]
        phK[a] = ((emb(U[0]), emb(U[1])), (emb(V[0]), emb(V[1])))
    la, _ = s3_log(f, phK[ia], T_GOAL, mu=MU)
    lb, _ = s3_log(f, phK[ib], T_GOAL, mu=MU)
    lphi = {ia: la, ib: lb}
    boxes = [bx for bx in s3_boxes(k) if bx['verdict'].startswith('constant')]
    print(' %d constant boxes' % len(boxes))
    out = []
    fo = open('centres_twist%d_prec%d.txt' % (k, PREC), 'w')
    fo.write('# [disc, X0, level, nu0, class (basis of pr of lattice.sobj), class in pr(W), class == e1, margin j - (nu0 + 1), '
             'branch (1: r from Q1, 3: s from Q3), v(Q1/delta), lambda precision pi^m, near x_i, tiny series check v(diff)]\n')
    for bx in boxes:
        t1 = time.time()
        d = DISCS[bx['disc'] - 1]
        t0, c, m, vs = disc_point(d, bx['X0'], PREC)
        P3 = disc_P3(Kv, d, t0, c, m)
        q1 = Bk.Qval(0, P3)
        L_ = Bk.lift(P3)
        assert L_ is not None, 'centre does not lift'
        P = P3 + list(L_)
        branch = 1 if not q1.is_zero() else 3
        D, res = Bk.phi(P, d[0])
        chk = [vlb(z) for z in res['J']] + [vlb(z) for z in res['iso']] + [vlb(res['Ysq'])]
        lP, rl = s3_log(f, D, T_GOAL, mu=MU)
        lam = [lP[j] - la[j] for j in range(2)]
        nu0, cl, margin, mprec, jl = classify(lam, L)
        inW = cl in L['prW']
        eqe1 = (cl == L['E1'][ia]) and (cl == L['E1'][ib])
        # tiny series check near a known lift
        near = None; tv = None
        for i_, (di, Xi) in XI.items():
            if TI[i_]['k'] == k and di == bx['disc']:
                near = i_
        if near is not None:
            Xi = XI[near][1]
            tau = Kv(2 * (bx['X0'] - Xi))          # tau = x(P) - x(P_i) (k = 1 in every disc)
            ser = [sum((emb(TI[near]['w%d' % s][mm]) / (mm + 1) * tau**(mm + 1) for mm in range(len(TI[near]['w0']))), Kv(0)) for s in range(2)]
            # lift through x_i: log phi(P) = log phi_i + S; the other lift: log phi(P) = -(log phi_i + S)
            dp = min(vlb(lP[s] - lphi[near][s] - ser[s]) for s in range(2)); dm = min(vlb(lP[s] + lphi[near][s] + ser[s]) for s in range(2))
            tv = (max(dp, dm), '+' if dp > dm else '-', 23 * ZZ(2 * (bx['X0'] - Xi)).valuation(2) * 3)
        row = [bx['disc'], bx['X0'], bx['level'], nu0, list(cl), inW, eqe1, margin, branch, vex(q1 / Bk.delta) if branch == 1 else None, mprec,
               near, tv]
        out.append(dict(disc=bx['disc'], X0=bx['X0'], level=bx['level'], nu0=nu0, cl=cl, inW=inW, eqe1=eqe1, margin=margin,
                        branch=branch, mprec=mprec, near=near, tiny=tv, checks=min(chk), N=rl['N'], chart=rl['chart']))
        fo.write(str(row) + '\n'); fo.flush()
        print(' box [%d, %d, %d]: nu0 = %d, class %s, in pr(W) %s, = e1 %s, margin %d, lambda to pi^%d (N = %d*2^%d), checks >= %s, tiny %s, %.1fs'
              % (bx['disc'], bx['X0'], bx['level'], nu0, list(cl), inW, eqe1, margin, mprec, rl['N'] // 2^rl['j'], rl['j'], min(chk), tv, time.time() - t1))
        sys.stdout.flush()
    fo.close()
    RES[k] = out
    print(' summary k = %d: %d centres, nu0 values %s, classes %s, any in pr(W): %s, all equal to e1: %s, least margin %d'
          % (k, len(out), sorted(set(o['nu0'] for o in out)), sorted(set(tuple(o['cl']) for o in out)), any(o['inW'] for o in out),
             all(o['eqe1'] for o in out), min(o['margin'] for o in out)))
save(RES, 'centres_prec%d.sobj' % PREC)
print('\ntime %.1fs' % (time.time() - t00))
