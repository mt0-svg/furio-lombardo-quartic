# logs.sage: logs of the local basis D'_1..D'_7 (exported u_i exactly, V refined to the genuine Hensel root),
# of phi_a, phi_b (exact global images), with known-answer tests. Saves logs_prec<PREC>.sobj.
# Usage: sage logs.sage PREC MU
import sys, time
load('loader.sage'); load('jacobian_log.sage')
PREC = int(sys.argv[1]) if len(sys.argv) > 1 else 500
MU = int(sys.argv[2]) if len(sys.argv) > 2 else 8
t00 = time.time()
X = s3_exact(); S = s3_setup(PREC, X); Kv = S['Kv']; emb = S['emb']
T_GOAL = S['cap'] // 2
print('PREC %d, cap %d, T_GOAL %d, MU %d; root certified to pi^%s' % (PREC, S['cap'], T_GOAL, MU, S['info']['r_prec']))
def pr_(z):
    return '(v %s, prec %s)' % (vlb(z) if not z.is_zero() else 'O', z.precision_absolute())
def dl(f, D, lab, **kw):
    t1 = time.time()
    l, r = s3_log(f, D, T_GOAL, mu=kw.get('mu', MU), m=kw.get('m', ODD))
    print('  log %-9s N = %d*2^%d, chart %s, %s, margin mu %s, M %d, log %s %s  %.1fs' % (lab, r['N'] // 2^r['j'], r['j'], r['chart'], r['mode'], r['mu'], r['M'], pr_(l[0]), pr_(l[1]), time.time() - t1))
    return l
def vd(a, b):
    return [vlb(a[i] - b[i]) for i in range(2)]
OUT = {}
for k in [0, 1]:
    print('\n==== twist k = %d ====' % k)
    tw = X['tw'][k]
    f = [emb(c) for c in tw['f']]
    Ds = []
    for i in range(7):
        U, V = tw['D'][i]
        assert U[2] == 1
        Dg = ((emb(U[0]), emb(U[1])), (emb(V[0]), emb(V[1])))
        Dp = refine(f, Dg)
        dv = [vlb(Dp[1][j] - Dg[1][j]) for j in range(2)]
        print(' D%d: u exact (prec %s), V refined: v(V\' - V_export) >= %s, certified precision of V\' %s' % (i + 1, min(z.precision_absolute() for z in Dp[0]), min(dv), min(z.precision_absolute() for z in Dp[1])))
        Ds.append(Dp)
    logD = [dl(f, Ds[i], 'D%d' % (i + 1)) for i in range(7)]
    ia, ib = sorted(tw['phi'].keys())
    ph = {}
    for a in [ia, ib]:
        U, V = tw['phi'][a]
        ph[a] = ((emb(U[0]), emb(U[1])), (emb(V[0]), emb(V[1])))
    logphi = {a: dl(f, ph[a], 'phi%d' % a) for a in [ia, ib]}
    TT = torsion_T(X, S, k)
    print(' KAT T genuine: f mod u_T =', [pr_(z) for z in jcheck(f, TT)])
    l12 = dl(f, jadd(f, Ds[0], Ds[1]), 'D1+D2')
    print(' KAT additivity v(log(D1+D2) - log D1 - log D2) >=', vd(l12, [logD[0][j] + logD[1][j] for j in range(2)]))
    l1T = dl(f, jadd(f, Ds[0], TT), 'D1+T')
    print(' KAT torsion v(log(D1+T) - log D1) >=', vd(l1T, logD[0]))
    laT = dl(f, jadd(f, ph[ia], TT), 'phia+T')
    print(' KAT torsion v(log(phi_a+T) - log phi_a) >=', vd(laT, logphi[ia]))
    l1b = dl(f, Ds[0], 'D1 3N', m=3 * ODD, mu=MU + 6)
    print(' KAT multiplier v(log D1 [3N] - log D1) >=', vd(l1b, logD[0]))
    lbb = dl(f, ph[ib], 'phib 3N', m=3 * ODD, mu=MU + 6)
    print(' KAT multiplier v(log phi_b [3N] - log phi_b) >=', vd(lbb, logphi[ib]))
    OUT[k] = dict(logD=[vec6c(l) for l in logD], logphi={a: vec6c(logphi[a]) for a in logphi}, ia=ia, ib=ib,
                  prec=min(min(z.precision_absolute() for z in l) for l in logD + list(logphi.values())))
    print(' least precision of the saved logs: pi^%d' % OUT[k]['prec'])
    sys.stdout.flush()
save(OUT, 'logs_prec%d.sobj' % PREC)
print('\ntime %.1fs' % (time.time() - t00))
