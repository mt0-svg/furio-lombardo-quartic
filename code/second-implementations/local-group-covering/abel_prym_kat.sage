# abel_prym_kat.sage: known-answer tests of the Abel-Prym map over K_v (task 1).
#  (a) at the lifts x_0, x_2 (k = 0), x_1, x_3 (k = 1): phi over K_v equals +- the image of the exact phi(x_i);
#  (b) at random points of D_delta(K_v): phi(iota P) = -phi(P);
#  (c) Y^2 = f(t) in K_v[t]/(U), P' QD_i T = 0, isotropy of the projected line, independence of Y from the
#      choice of (c, e).
# Usage: sage abel_prym_kat.sage PREC NRANDOM
import sys, time
load('loader.sage')
PREC = int(sys.argv[1]) if len(sys.argv) > 1 else 300
NR = int(sys.argv[2]) if len(sys.argv) > 2 else 6
set_random_seed(20260927)
t00 = time.time()
X = s3_exact()
S = s3_setup(PREC, X)
Kv = S['Kv']; pi = S['pi']
print('PREC %d, K_v cap %d; E =' % (PREC, S['cap']), S['info']['Eq'].change_ring(Integers(2^40)), '(mod 2^40)')
print('embedding: v(K21(R)) >= %s, v(K21\'(R)) = %s, root certified to pi^%s; v(prgen2(r)) = %s; v(prgen2(r) - pi) >= %s'
      % (S['info']['v_K21_R'], S['info']['v_dK21_R'], S['info']['r_prec'], S['info']['v_pg_r'], S['info']['pg_minus_pi']))
def mn(lst):
    return min(vlb(z) for z in lst)
def show_res(res):
    return 'min v(P QD_i T) %s, isotropy %s, v(Y^2 - f) %s, v(Y - Y_alt) %s, pair %s' % (
        mn(res['J']), min(vlb(z) for z in res['iso']), vlb(res['Ysq']), [vlb(d) for (pr_, d) in res['Yalt']], res['pair'])
ok_all = True
for k in [0, 1]:
    B = BruinKv(S, X, k)
    print('\n==== twist k = %d: v(delta) = %s, valuations of f:' % (k, vex(B.delta)), [vlb(c) for c in B.f])
    for i, ph in sorted(X['PHI'].items()):
        if ph['k'] != k:
            continue
        P = [S['emb'](c) for c in ph['x']]
        D, res = B.phi(P, 1)
        e = X['tw'][k]['phi'][i]
        Ue = [S['emb'](c) for c in e[0]]; Ve = [S['emb'](c) for c in e[1]]
        assert (Ue[2] - 1).is_zero()
        dU = [D[0][0] - Ue[0], D[0][1] - Ue[1]]
        dVp = [D[1][0] - Ve[0], D[1][1] - Ve[1]]
        dVm = [D[1][0] + Ve[0], D[1][1] + Ve[1]]
        sg = '+' if all(z.is_zero() for z in dVp) else ('-' if all(z.is_zero() for z in dVm) else 'none')
        good = all(z.is_zero() for z in dU) and sg != 'none'
        ok_all = ok_all and good
        print(' x_%d = %s, r = 0: %s: v(U - U_exact) >= %s, v(V - V_exact) >= %s, v(V + V_exact) >= %s -> equal with sign %s; precision of U %s, of V %s'
              % (i, ph['x'][:3], P[3].is_zero(), mn(dU), mn(dVp), mn(dVm), sg, min(z.precision_absolute() for z in D[0]), min(z.precision_absolute() for z in D[1])))
        print('    ' + show_res(res))
    # random points of D(K_v)
    discs = s3_discs(); cnt = 0; tries = 0
    todo = [d for d in discs for _ in range(40)]
    percnt = {}
    for d in todo:
        if percnt.get(tuple(d), 0) >= NR:
            continue
        X0 = randint(0, 2^20)
        t0, c, m, vs = disc_point(d, X0, 3 * PREC)
        P3 = disc_P3(Kv, d, t0, c, m)
        L = B.lift(P3)
        if L is None:
            continue
        P = P3 + list(L)
        iP = P3 + [-L[0], -L[1]]
        D1, r1 = B.phi(P, d[0]); D2, r2 = B.phi(iP, d[0])
        dU = [D1[0][j] - D2[0][j] for j in range(2)]; dV = [D1[1][j] + D2[1][j] for j in range(2)]
        good = all(z.is_zero() for z in dU + dV)
        ok_all = ok_all and good
        cnt += 1; percnt[tuple(d)] = percnt.get(tuple(d), 0) + 1
        print(' random point: disc %s, X0 = %d, v(Q1/delta) = %s: phi(iota P) = -phi(P): %s (v(U - U\') >= %s, v(V + V\') >= %s; prec U %s)'
              % (d, X0, vex(B.Qval(0, P3) / B.delta), good, mn(dU), mn(dV), min(z.precision_absolute() for z in D1[0])))
        print('    ' + show_res(r1))
print("\nrandom points per disc and twist: see above")
print("\nALL KAT PASS" if ok_all else "\nSOME KAT FAILED")
print('time %.1fs' % (time.time() - t00))
