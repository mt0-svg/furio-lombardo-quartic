\\ local_images_7_inf_check.gp: referee sanity checks of the local analysis of the two-descent at 7 and at infinity
\\ (Im_7 = 0, Im_inf = 0). These conditions turn out to be implied by the norm condition on O_S^x/squares
\\ (fake_selmer_group_check.gp), so they do not affect dim Sel_fake; the samples test the framework (Proposition 3 and the
\\ orbit analysis) on points.
\\ Needs geometry_check.dat. Run: gp -q -D parisizemax=4000000000 local_images_7_inf_check.gp

FAIL = 0;
chk(name, c) = if(c, print("ok   ", name), FAIL++; print("FAIL ", name));
\\ variable priorities fixed before any varlower: x > y > z > X > Y > w > a > u
[x, y, z, 'X, 'Y];
w = varlower("w"); a = varlower("a"); u = varlower("u");
A3pol = a^8+2*a^7+7*a^4-14*a^2-8*a+5;
GEOM = read("geometry_check.dat");
GAint = liftpol(GEOM[1]); GAint = GAint * denominator(content(GAint));
evGA(pt) = Mod(subst(subst(subst(GAint, x, pt[1]), y, pt[2]), z, pt[3]), A3pol);
F = x^4+3*x^3*y-3*x^2*y*z-3*x^2*z^2+6*x*y^3-6*x*y^2*z+3*x*y*z^2-2*x*z^3+4*y^4+2*y^3*z-5*y*z^3;
F1 = subst(F, z, 1);
\\ Hensel certificate at the prime p for an integer approximation t of a root of Q
hens(Q, t, p) = my(f = subst(Q, 'Y, t), d = subst(deriv(Q, 'Y), 'Y, t), fv, dv); if(f == 0, return(10^6)); fv = valuation(f, p); dv = if(d == 0, 10^6, valuation(d, p)); if(fv > 2*dv, fv - dv, -1);
triv7(al) = my(ok = 0); foreach([1, 3, 7, 21], d, if(!ok && nfislocalpower(nf, P7a, lift(al*d), 2) && nfislocalpower(nf, P7b, lift(al*d), 2), ok = 1)); ok;

{
nf = nfinit(A3pol);
P7 = idealprimedec(nf, 7); P7a = if(P7[1].e == 1, P7[1], P7[2]); P7b = if(P7[1].e == 7, P7[1], P7[2]);
g1 = evGA([1,1,1]);
print("== Q_7-points: delta(P - P1) should be trivial in A_7^x/A_7^x2 Q_7^x");
n7 = 0; bad7 = 0; skip7 = 0;
for(x0 = -150, 150,
  Q = subst(subst(F1, y, 'Y), x, x0);
  r = polrootspadic(Q, 7, 40);
  for(i = 1, #r, t = lift(Mod(truncate(r[i]), 7^40)); k = hens(Q, t, 7);
    if(k <= 0, skip7++; next);
    gv = evGA([x0, t, 1]); if(gv == 0, skip7++; next);
    va = nfeltval(nf, gv, P7a); vb = nfeltval(nf, gv, P7b);
    if(k <= va || 7*k <= vb, skip7++; next);
    n7++; if(!triv7(gv * g1), bad7++)));   \\ gv g1 has the class of gv / g1 and is integral
print("   certified Q_7-points: ", n7, ", skipped: ", skip7);
chk(Str("all ", n7, " classes delta(P - P1), P in C(Q_7), are trivial at 7"), n7 > 100 && bad7 == 0);

print("== real points: sign(sigma_1(alpha)) = sign(sigma_2(alpha)) for alpha = G_A(P)/G_A(P1)");
default(realprecision, 100);
rts = polroots(A3pol); rr = [real(t) | t <- rts, abs(imag(t)) < 10^-80];
chk("two real embeddings", #rr == 2);
nR = 0; badR = 0; skipR = 0;
for(i = -400, 400, x0 = i / 37;
  ys = polroots(subst(F1, x, x0));
  for(j = 1, #ys, if(abs(imag(ys[j])) > 10^-60, next); y0 = real(ys[j]);
    vv = vector(2, s, subst(subst(subst(subst(GAint, x, x0), y, y0), z, 1), a, rr[s]) / subst(subst(subst(subst(GAint, x, 1), y, 1), z, 1), a, rr[s]));
    if(abs(vv[1]) < 10^-40 || abs(vv[2]) < 10^-40, skipR++; next);
    nR++; if(sign(vv[1]) != sign(vv[2]), badR++)));
print("   real points: ", nR, ", skipped (near a zero of G_A): ", skipR);
chk(Str("all ", nR, " real points give the same sign at both real places (floating point, 100 digits)"), nR > 500 && badR == 0);

print("== summary: ", FAIL, " failure(s)");
}
