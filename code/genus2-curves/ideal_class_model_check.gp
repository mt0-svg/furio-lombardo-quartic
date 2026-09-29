\\ ideal_class_model_check.gp: check of the ideal class model of A = Jac(F_k).
\\ The model A(K) = ker(ClassGroup(K[t,Y]/(Y^2 - f)) -> Z/2) is Pic^0 only when the leading coefficient of f is not a
\\ square in K. Check lc(F_k) in K21 and at every place above 2 (and above 7, real places, for information), and, if needed,
\\ search a rational t0 with F_k(t0) a non square at v (then t = t0 + 1/s gives a model with leading coefficient F_k(t0)).
\\ Run from code/genus2-curves: gp -q ideal_class_model_check.gp
default(parisizemax, 4 * 10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../earlier-computations/bruin_form.gp");
nfK = nfinit([K21, [2, 7]]);
P2 = idealprimedec(nfK, 2); P7 = idealprimedec(nfK, 7);
printf("places above 2: %s (e, f)\n", apply(q -> [q.e, q.f], P2));
printf("places above 7: %s (e, f)\n", apply(q -> [q.e, q.f], P7));
printf("signature %s\n", nfK.sign);
lsq(al, q) = nfislocalpower(nfK, q, al, 2);
{
  for (k = 0, 1,
    my(f = if (k == 0, F0, F1), c = pollead(f, t), dd = if (k == 0, d0, d1));
    printf("k = %d: deg f = %d, lc(f) a square in K21: %d\n", k, poldegree(f, t), #nfroots(nfK, 'X^2 - lift(Mod(c, K21))) > 0);
    printf("  lc local square at places above 2 (e = %s): %s\n", apply(q -> q.e, P2), apply(q -> lsq(c, q), P2));
    printf("  lc local square at places above 7: %s\n", apply(q -> lsq(c, q), P7));
    printf("  signs of lc at real places: %s\n", vector(nfK.sign[1], i, nfeltsign(nfK, c, i)));
    printf("  valuations of lc at places above 2: %s, above 7: %s\n", apply(q -> nfeltval(nfK, c, q), P2), apply(q -> nfeltval(nfK, c, q), P7));
    my(v = [q | q <- P2, q.e == 3][1], found = List());
    for (t0 = -6, 6, my(val = subst(f, t, t0)); if (val != 0 && !lsq(val, v), listput(found, t0)));
    printf("  integers t0 in [-6, 6] with f(t0) a non square at v (e = 3): %s\n", Vec(found));
    my(foundK = List());
    for (t0 = -6, 6, my(val = subst(f, t, t0)); if (val != 0 && #nfroots(nfK, 'X^2 - lift(Mod(val, K21))) == 0, listput(foundK, t0)));
    printf("  integers t0 in [-6, 6] with f(t0) a non square in K21: %s\n", Vec(foundK));
  );
}
quit;
