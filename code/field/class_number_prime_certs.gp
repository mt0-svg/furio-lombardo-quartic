\\ class_number_prime_certs.gp: per-prime certificates of M2 (decoded by FurioLombardo.M2.decode, checked by
\\ FurioLombardo.M2.checkPrime). Every check that the Lean kernel runs is replayed here with
\\ exact arithmetic before a record is written; any failure is an error.
\\ (no default() here: default(parisizemax) inside a read() file silently ends the read; the driver sets it)
f = x^21 - 7*x^20 + 14*x^19 - 84*x^16 + 98*x^15 + 2*x^14 + 175*x^13 - 609*x^12 + 980*x^11 - 770*x^10 - 280*x^9 + 1008*x^8 - 1072*x^7 + 560*x^6 + 28*x^5 - 336*x^4 + 252*x^3 - 112*x^2 + 28*x - 4;
\\ call g4init() after reading this file (a nested read of a binary file ends the enclosing read)
g4init() = {
  bnf = read("field_bnf.bin"); nf = bnf.nf; n = 21;
  zk = nf.zk; D = lcm(vector(n, j, denominator(content(zk[j]))));
  Wp = vector(n, j, D * zk[j]);
}
Bnd = 120000; kK = 512;
ResZ = polcoef(polresultantext(f, f')[3], 0);
zzenc(z) = if (z >= 0, 2 * z, -2 * z - 1);
\\ fields: list of [value, width]; returns sum value * 2^offset
packfields(F) = { my(N = 0, off = 0); for (i = 1, #F, if (F[i][1] < 0 || F[i][1] >= 2^F[i][2], error("field overflow ", F[i])); N += F[i][1] << off; off += F[i][2]); N; }
liftp(g, p, len) = vector(len, i, lift(polcoef(g, i - 1)));
maxabs(v) = vecmax(apply(abs, v));
\\ exact balanced digits of an integer polynomial (coefficient bound check)
polbound(g) = if (g == 0, 0, maxabs(Vec(g)));
\\ generator certificate of (p, L(theta)); returns the list of fields
gencert(p, L) = {
  my(pr, g, a, c, A, C, H, Q, d = poldegree(L), fields, Cm, t, sp, up, gg);
  pr = idealhnf(nf, p, nfalgtobasis(nf, Mod(lift(L), f)));
  g = bnfisprincipal(bnf, pr, 1);
  if (g[1] != 0 && #g[1] > 0, error("not principal ", p));
  a = g[2];
  if (idealhnf(nf, a) != pr, error("generator ", p));
  c = nfeltdiv(nf, p, a);
  if (denominator(c) != 1, error("c not integral ", p));
  if (maxabs(a) > 2^15 || maxabs(c) > 2^27, error("coordinate bound ", p));
  A = sum(j = 1, n, a[j] * Wp[j]); C = sum(j = 1, n, c[j] * Wp[j]);
  if (denominator(content(A)) != 1 || denominator(content(C)) != 1, error("W"));
  H = A * C - p * D^2;
  Q = H \ f; if (H - Q * f != 0, error("alpha c != p ", p));
  if (poldegree(Q) > 19, error("deg Q"));
  if (polbound(Q) > 2^425, error("Q bound ", p));
  if (polbound(C) > 2^112, error("C bound ", p));
  if (poldegree(C) > 20, error("deg C"));
  fields = List();
  listput(fields, [d, 8]);
  for (i = 0, d - 1, listput(fields, [lift(polcoef(L, i)), 17]));
  for (j = 1, n, listput(fields, [zzenc(a[j]), 16]));
  for (j = 1, n, listput(fields, [zzenc(c[j]), 28]));
  if (d == 1,
    my(l0 = lift(polcoef(L, 0)), E);
    if (subst(C, x, -l0) % p == 0, error("C(r) = 0 mod p ", p));
    E = (x + l0) * C - polcoef(C, 20) * f;
    if (poldegree(E) > 20, error("lin check degree ", p));
    if (E != 0 && denominator(content(E / p)) != 1, error("lin check ", p));
  ,
    my(Lz = lift(L), R2, Cb, Lb, uv);
    R2 = (Lz * C) % f;
    if (R2 != 0 && denominator(content(R2 / p)) != 1, error("hi check ", p));
    Cb = Mod(1, p) * C; Lb = Mod(1, p) * Lz;
    uv = gcdext(Cb, Lb);
    if (poldegree(uv[3]) != 0, error("gcd ", p));
    sp = uv[1] / uv[3]; up = uv[2] / uv[3];
    if (poldegree(sp) > d - 1 || poldegree(up) > 20, error("bezout degrees ", p));
    for (i = 0, d - 1, listput(fields, [lift(polcoef(sp, i)), 17]));
    for (i = 0, 20, listput(fields, [lift(polcoef(up, i)), 17]));
    my(Bz = C * lift(sp) + Lz * lift(up) - 1);
    if (Bz != 0 && denominator(content(Bz / p)) != 1, error("bezout check ", p)));
  Vec(fields);
}
\\ record for the prime p
primerec(p) = {
  my(E, fp, F, facs = List(), fields = List(), ss = List(), T);
  if (ResZ % p == 0, error("p divides Res ", p));
  E = 0; while (p^(E + 1) <= Bnd, E++);
  if (E < 1, error("E"));
  fp = Mod(1, p) * f;
  F = factormod(f, p);
  for (i = 1, #F~, if (F[i, 2] != 1, error("not squarefree ", p)); if (poldegree(F[i, 1]) <= E, listput(facs, F[i, 1])));
  listput(fields, [#facs, 8]); listput(fields, [E, 8]);
  for (i = 1, #facs, my(gf = gencert(p, facs[i])); for (k = 1, #gf, listput(fields, gf[k])));
  for (e = 1, E,
    my(Re, He, s, uv);
    Re = lift(Mod(Mod(1, p) * x, fp)^(p^e));
    He = Mod(1, p); for (i = 1, #facs, if (e % poldegree(facs[i]) == 0, He *= facs[i]));
    He = Mod(1, p) * He;
    if (Re == Mod(1, p) * x,
      if (He != fp, error("He != f ", p, " ", e)); s = 0,
      uv = gcdext(Re - x, fp);
      if (uv[3] / pollead(uv[3]) != He / pollead(He), error("gcd != He ", p, " ", e));
      s = (uv[1] * He / uv[3]) % fp);
    if (((s * (Re - x)) - He) % fp != 0, error("s check ", p, " ", e));
    for (i = 0, 20, listput(fields, [lift(polcoef(Mod(1, p) * s, i)), 17])));
  packfields(Vec(fields));
}
\\ writes the Lean list of records for the primes in [lo, hi] (special primes skipped)
genblock(lo, hi, name, file) = {
  my(first = 1, cnt = 0);
  system(concat("rm -f ", file));
  write(file, "import FurioLombardo.M2.Check");
  write(file, "");
  write(file, "namespace FurioLombardo.M2");
  write(file, "");
  write(file, concat(concat("/-- Certificates for the primes in [", lo), concat(concat(", ", hi), "] (generated by code/field/class_number_prime_certs.gp). -/")));
  write(file, concat(concat("def ", name), " : List (ℕ × ℕ) := ["));
  forprime(p = max(lo, 3), hi,
    if (p == 7 || p == 45613, next);
    my(N = primerec(p));
    write(file, concat(concat(if (first, "  (", "  , ("), concat(concat(p, ", "), N)), ")"));
    first = 0; cnt++);
  write(file, "  ]");
  write(file, "");
  write(file, "end FurioLombardo.M2");
  cnt;
}
