# pullback_kat.sage: independent test of the pullback identity used by the sup bound of the covering
# (see the paper): phi^*(dt/Y) = a12 s Omega, phi^*(t dt/Y) = a21 r Omega, Omega = (x dy - y dx)/F_z (= dt/F_u in chart z = 1,
# -dt/F_u in chart y = 1), with A from pullback_known_lifts.gp. At points P(t0) of C(Q_2) (2-adic, not global) the difference
# quotient (lambda(P(t0 + h)) - lambda(P(t0)))/h of the own phi and log, h = 2^H, is compared with the value of the
# pulled back differential at P(t0); the lift at t0 + h is the continuation of the lift at t0 (r close to r0).
# Usage: sage pullback_kat.sage PREC H
import sys
load('loader.sage'); load('jacobian_log.sage')
PREC = int(sys.argv[1]) if len(sys.argv) > 1 else 600
H = int(sys.argv[2]) if len(sys.argv) > 2 else 60
set_random_seed(4242)
X = s3_exact(); S = s3_setup(PREC, X); Kv = S['Kv']; emb = S['emb']
TI = s3_tiny(X); DISCS = s3_discs()
T_GOAL = S['cap'] // 2
ok_all = True
for k in [0, 1]:
    Bk = BruinKv(S, X, k); f = Bk.f
    A = TI[[i for i in TI if TI[i]['k'] == k][0]]['A']
    a12 = emb(A[0, 1]); a21 = emb(A[1, 0])
    cnt = {}
    for d in DISCS:
        for trial in range(30):
            if cnt.get(tuple(d), 0) >= 2:
                break
            X0 = randint(0, 2^16)
            pts = []
            for dX in [0, 2^(H - 1)]:
                t0, c, m, vs = disc_point(d, X0 + dX, PREC)
                P3 = disc_P3(Kv, d, t0, c, m)
                L_ = Bk.lift(P3)
                pts.append((t0, P3, L_))
            if pts[0][2] is None or pts[1][2] is None:
                continue
            r0, s0 = pts[0][2]; r1, s1 = pts[1][2]
            if (r1 - r0).valuation() <= (r0).valuation() + 3:
                r1, s1 = -r1, -s1
            lam = []
            for (t0, P3, L_), (rr, ss) in zip(pts, [(r0, s0), (r1, s1)]):
                D, res = Bk.phi(P3 + [rr, ss], d[0])
                l, _ = s3_log(f, D, T_GOAL)
                lam.append(l)
            h = Kv(pts[1][0] - pts[0][0])
            quot = [(lam[1][j] - lam[0][j]) / h for j in range(2)]
            x, y, z = pts[0][1]
            dF = [g(x, y, z) for g in _FD]
            if d[0] == 1:
                Fu = dF[1]; eps = 1
            else:
                Fu = dF[2]; eps = -1
            pred = [eps * a12 * s0 / Fu, eps * a21 * r0 / Fu]
            dv = [vlb(quot[j] - pred[j]) - vex(pred[j]) for j in range(2)]
            good = min(dv) >= 3 * H - 20
            ok_all = ok_all and good
            cnt[tuple(d)] = cnt.get(tuple(d), 0) + 1
            print(' k = %d, disc %s, X0 = %d: v(pred) = %s, relative agreement of the difference quotient with (a12 s, a21 r) eps/F_u: pi^%s (h = 2^%d): %s'
                  % (k, d, X0, [vex(p) for p in pred], dv, H, good))
print('ALL PASS' if ok_all else 'SOME FAILED')
