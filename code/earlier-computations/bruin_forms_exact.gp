\\ Exact Bruin forms over the field of eta from the numerical data of bruin_forms_numeric.gp, for the orbit of
\\ size ORB (21 or 14): interpolation of each coefficient as a polynomial in theta over the ORB conjugates,
\\ rational reconstruction, exact verification Q1*Q3 - Q2^2 = c*F, then transport to Q[b]/(K21pol or K14pol).
\\ Run: gp -q bruin_forms_exact.gp < /dev/null   (ORB set below)
default(parisizemax, 4*10^9); default(nbthreads, 1);
default(realprecision, 800);
[x, y, z, m, k, X, t, b];
F = x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3;
read("prym_fields.gp");
ORB = if (type(ORB) == "t_INT", ORB, 21);
[bruin, th, fa63] = read("bruin_forms_numeric.bin");
mons2 = [x^2, x*y, x*z, y^2, y*z, z^2];
coef2(Q) = vector(6, j, polcoef(polcoef(polcoef(Q, poldegree(mons2[j], x), x), poldegree(mons2[j], y), y), poldegree(mons2[j], z), z));
fo = 0; for (i = 1, #fa63~, if (poldegree(fa63[i,1]) == ORB, fo = fa63[i,1]));
fo = fo / pollead(fo);
print("orbit polynomial: degree ", poldegree(fo), ", log10 of max |coefficient| ", round(log(vecmax(abs(Vec(fo)))) / log(10)));
idx = select(e -> abs(subst(fo, X, th[e])) < 1e-300 * (1 + abs(th[e]))^ORB, [1..#th]);
print("etas in the orbit: ", #idx);
if (#idx != ORB, error("orbit size"));
Kref = if (ORB == 21, K21pol, K14pol);
iso = nfisisom(fo, Kref);
if (#iso < 1, error("orbit field not isomorphic to the reference field"));
phiX = lift(iso[1]);                      \\ theta = phiX(root of Kref)
nfr = nfinit(Kref); zk = nfr.zk;
rr = polroots(Kref);
\\ match each eta with the root b_e of Kref such that phiX(b_e) = theta_e
be = vector(ORB, i, my(d = vector(ORB, j, abs(subst(phiX, X, rr[j]) - th[idx[i]])), jm = 1); for (j = 2, ORB, if (d[j] < d[jm], jm = j)); if (d[jm] > 1e-500, error("no matching root")); rr[jm]);
print("distinct roots matched: ", #Set(vector(ORB, i, round(real(be[i]) * 10^20) + I * round(imag(be[i]) * 10^20))) == ORB);
V = matrix(ORB, ORB, i, j, subst(zk[j], X, be[i]));
Vi = V^(-1);
\\ element of Q[X]/(fo) with conjugates vals (a vector over idx)
recog(vals) = {
  my(u = Vi * vals~, ur, err);
  err = vecmax(abs(imag(u)));
  ur = vector(ORB, j, bestappr(real(u[j]), 10^120));
  if (vecmax(abs(vector(ORB, j, real(u[j]) - ur[j]))) > 1e-600 || err > 1e-600, error("recognition failed: max |u| = ", vecmax(abs(u))));
  Mod(sum(j = 1, ORB, ur[j] * zk[j]), Kref);
}
cq = vector(3, s, vector(6, j, recog(vector(ORB, i, coef2(bruin[idx[i]][s])[j]))));
cc = recog(vector(ORB, i, bruin[idx[i]][4]));
QQ = vector(3, s, sum(j = 1, 6, cq[s][j] * mons2[j]));
[Q1, Q2, Q3] = QQ;
chk(c, msg) = if (!c, error("FAILED: ", msg), print("ok: ", msg));
chk(Q1*Q3 - Q2^2 == cc * F, "Q1*Q3 - Q2^2 = c*F exactly over the reference field");
chk(substvec(Q1, [x,y,z], [0,0,1]) == 0, "Q1 passes through P0");
chk(substvec(Q3, [x,y,z], [1,1,1]) == 0, "Q3 passes through P1");
Kb = subst(Kref, X, b);
tob(e) = Mod(subst(lift(e), X, b), Kb);
formb(Q) = { if (type(Q) == "t_POLMOD", return(tob(Q))); if (type(Q) == "t_INT" || type(Q) == "t_FRAC", return(Mod(Q, Kb))); my(v = variable(Q)); sum(i = 0, poldegree(Q, v), formb(polcoef(Q, i, v)) * v^i); }
R1 = formb(Q1); R2 = formb(Q2); R3 = formb(Q3); cR = tob(cc);
chk(R1*R3 - R2^2 == cR * F, "Bruin form over Q[b]/(reference polynomial)");
fn = Str("bruin", ORB, "_raw.gp"); system(Str("rm -f ", fn));   \\ write appends
write(fn, "\\\\ Bruin form of C for eta in the orbit of size ", ORB, " (code/earlier-computations/bruin_forms_exact.gp): R1*R3 - R2^2 = cR*F");
write(fn, "Kb = ", Kb, ";");
write(fn, "R1 = ", lift(R1), ";");
write(fn, "R2 = ", lift(R2), ";");
write(fn, "R3 = ", lift(R3), ";");
write(fn, "cR = ", lift(cR), ";");
print("written ", fn);
quit;
