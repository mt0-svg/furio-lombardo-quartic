\\ local_steps_design.gp: design of the local steps of the Lean sieve of M1 (which primes above 2 and 3 kill which of
\\ the 8 survivors of the good prime sieve). Exploration only, nothing here is trusted.
\\ Inputs: /tmp/m1_gensLean.gp (see descent_bruin_data.gp) and /tmp/m1w/surv.gp, extracted from DataSieve.lean by
\\   awk '/def sieveSurv/,/\]\]/' ../../FurioLombardo/M1/DataSieve.lean | sed '1d' | tr -d '\n ' \
\\     | sed 's/true/1/g; s/false/0/g; s/^/surv = /; s/$/;\n/' > /tmp/m1w/surv.gp
\\ Charts (complete, disjoint): (x, y, 1); (1, y, z) with p | z; (x, 1, z) with p | x, p | z.
\\ Run: gp -q local_steps_design.gp < /dev/null
default(parisizemax, 3*10^9); default(nbthreads, 1);
read("descent_data_lib.gp");
read("/tmp/m1_gensLean.gp");
read("/tmp/m1w/surv.gp");
Gz = vector(18, i, gensLean[i]~);
Gel(e) = prod(i = 1, 18, if (e[i], Mod(zkr(Gz[i]), K21), 1));
Fi(P) = substvec(F, [x, y, z], P);
ev(Q, P) = substvec(Q, [x, y, z], P);
issq(a) = #nfroots(K21, X^2 - lift(a)) > 0;
qsel(P) = { my(q = Mod(ev(Q1, P), K21)); if (q == 0, q = Mod(ev(Q3, P), K21)); q };
known = vector(4, k, my(P = [[0,0,1],[1,1,1],[2,0,1],[-1,0,1]][k], c = [i | i <- [1..#surv], issq(qsel(P) * Gel(surv[i]))]); if (#c != 1, error("known ", k)); c[1]);
print("known survivor indices (P0, P1, P2, P3): ", known);
rest = setminus(Set([1..#surv]), Set(known));
print("to kill: ", rest);
survE = vector(#surv, i, Gel(surv[i]));
\\ exact local test at one prime pr | p, adaptive refinement (as descent_set_exact_probe.gp but per prime)
det1(P, p, m, pr) = {
  my(q1 = Mod(ev(Q1, P), K21), q3 = Mod(ev(Q3, P), K21), e = pr.e, s = if (p == 2, 2 * e + 1, 1));
  foreach([q1, q3], q, if (q != 0, my(v = nfeltval(nf, lift(q), pr)); if (m * e >= v + s, return(q))));
  0;
}
seeds(p) = {
  my(L = List());
  for (s1 = 0, p - 1, for (s2 = 0, p - 1,
    listput(L, [[s1, s2, 1], 1, [1, 2]]);
    if (s2 % p == 0, listput(L, [[1, s1, s2], 1, [2, 3]]));
    if (s1 % p == 0 && s2 % p == 0, listput(L, [[s1, 1, s2], 1, [1, 3]]))));
  L;
}
localkill(p, pr) = {
  my(keep = vector(#surv), nleaf = 0, maxm = 0, stack = seeds(p));
  while (#stack,
    my(it = stack[#stack], P = it[1], m = it[2], fr = it[3]); listpop(stack);
    if (Fi(P) % p^m != 0, next);
    maxm = max(maxm, m);
    my(q = det1(P, p, m, pr));
    if (q != 0,
      nleaf++;
      for (k = 1, #surv, if (!keep[k] && nfislocalpower(nf, pr, lift(survE[k] * q), 2), keep[k] = 1));
      next);
    if (m >= 30, error("depth"));
    for (d1 = 0, p - 1, for (d2 = 0, p - 1, my(Q = P); Q[fr[1]] += d1 * p^m; Q[fr[2]] += d2 * p^m; listput(stack, [Q, m + 1, fr]))));
  [keep, nleaf, maxm];
}
{
foreach([2, 3], p,
  my(prs = idealprimedec(nf, p));
  for (i = 1, #prs, my(pr = prs[i], r = localkill(p, pr));
    print("p = ", p, " prime ", i, " (e = ", pr.e, ", f = ", pr.f, "): killed ", [k | k <- [1..#surv], !r[1][k]], ", leaves ", r[2], ", max m ", r[3])));
}
\\ the degree one prime above 3 with theta = -1 mod 3: residues in Z/3^k
r3 = [r | r <- polrootspadic(K21, 3, 8), valuation(r + 1, 3) > 0];
print("3-adic roots near -1: ", #r3);
{
if (#r3 == 1,
  my(r = truncate(r3[1]));
  for (k = 2, 5,
    my(N = 3^k, rk = lift(Mod(r, N)), rhoN = (a -> Mod(subst(lift(Mod(a, K21) * Dz), b, rk), N) / Mod(Dz, N)), sqN = Set(vector(N, s, Mod(s - 1, N)^2)), pts = List(), killed = List());
    if (Mod(subst(K21, b, rk), N) != 0, error("root"));
    foreach(seeds(3), sd, my(P0 = sd[1], fr = sd[3]);
      for (d1 = 0, N / 3 - 1, for (d2 = 0, N / 3 - 1, my(P = P0); P[fr[1]] += 3 * d1; P[fr[2]] += 3 * d2; if (Fi(P) % N == 0, listput(pts, P)))));
    my(qv = apply(P -> [rhoN(ev(Q1, P)), rhoN(ev(Q3, P))], Vec(pts)));
    for (kk = 1, #surv, my(g = rhoN(lift(survE[kk])), dead = 1);
      for (j = 1, #qv, if (setsearch(sqN, qv[j][1] * g) && setsearch(sqN, qv[j][2] * g), dead = 0; break));
      if (dead, listput(killed, kk)));
    print("Z/3^", k, " (theta -> ", rk, "): ", #pts, " normalized points, killed ", Vec(killed))));
}
