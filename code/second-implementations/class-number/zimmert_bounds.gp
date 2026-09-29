\\ zimmert_bounds.gp: Zimmert's bounds for ideals of small norm, Invent. Math. 62 (1981) 367-380.
\\ Transcribed from the published paper. psi = Gamma'/Gamma.
\\
\\ Satz 2 (every ideal class R contains an integral ideal a, namely one of least norm in R, with, for all gamma > alpha > 0,
\\   log(d^(1/2)/N a) >= S2(gamma, alpha)):
\\   S2 = r1 (-psi((1+g)/2) - lngamma(1/2+g) + lngamma(1+g) + log(pi)/2)
\\      + r2 (-2 psi(1+g) + 2 log 2 + log(1/2+g) + log pi)
\\      - 2/(g-al) - log((1 + 1/al) (1 + 1/g)^(-2) (1 + 1/(2g-al))^(-1)).
\\   Bemerkung 1: best al = g - g(g+1)/sqrt(1+3g+3g^2).
\\ Korollar 1 (twin classes): for every class R there are integral a in R and b in D R^(-1) (D the class of the different)
\\   with log(d/(N a N b)) >= F_{r1+r2, r2}(g) + n log pi, for all g > 0; hence min(N a, N b) <= d^(1/2) exp(-c),
\\   c = (F + n log pi)/2. PARI's zimmertbound tabulates exp(-c) sqrt(d) for n <= 20 (buch3.c).
\\   F_{a,b}(g) = a Sa(g) + b Sb(g) + T(g), with C = 2(1+2g), k = 2/(1+2g):
\\   Sa = sum_{l>=1} [k (psi((2l+3g)/C) - psi((2l-1+g)/C)) - 1/(2l-2-g) - 1/(2l-1+g)] - (psi(1/2+g/2) + psi(-g/2))/2
\\   Sb = sum_{l>=1} [k (psi((2l+1+3g)/C) - psi((2l+g)/C)) - 1/(2l-1-g) - 1/(2l+g)] - (psi(1+g/2) + psi(1/2-g/2))/2
\\   T  = -4/g + k (psi((1+g)/C) - psi((1+3g)/C) + psi((2+5g)/C) - psi((2+3g)/C))
\\ Known-answer tests: Zimmert's Tables 1 and 3 (printed gamma and values) and PARI's table of constants.
\\ Run from code/second-implementations/class-number: gp -q zimmert_bounds.gp < /dev/null
default(parisizemax, 10^9); default(nbthreads, 1); default(realprecision, 50);
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));

S2(r1, r2, g, al) = r1 * (-psi((1+g)/2) - lngamma(1/2+g) + lngamma(1+g) + log(Pi)/2) + r2 * (-2*psi(1+g) + 2*log(2) + log(1/2+g) + log(Pi)) - 2/(g-al) - log((1 + 1/al) * (1 + 1/g)^(-2) * (1 + 1/(2*g-al))^(-1));
bestal(g) = g - g*(g+1)/sqrt(1 + 3*g + 3*g^2);
S2b(r1, r2, g) = S2(r1, r2, g, bestal(g));

\\ summands of Sa, Sb (O(l^-3)); PARI sumnum is unreliable here (off by 1e-4, cancellation), so plain partial sums
\\ S(L), S(2L), S(4L) and Richardson extrapolation for a tail c2/L^2 + c3/L^3 + O(L^-4)
ta(l, g) = my(C = 2*(1+2*g), k = 2/(1+2*g)); k*(psi((2*l+3*g)/C) - psi((2*l-1+g)/C)) - 1/(2*l-2-g) - 1/(2*l-1+g);
tb(l, g) = my(C = 2*(1+2*g), k = 2/(1+2*g)); k*(psi((2*l+1+3*g)/C) - psi((2*l+g)/C)) - 1/(2*l-1-g) - 1/(2*l+g);
Ssum(t, g) = my(L = RL, s1 = sum(l = 1, L, t(l, g)), s2 = s1 + sum(l = L + 1, 2*L, t(l, g)), s4 = s2 + sum(l = 2*L + 1, 4*L, t(l, g))); (32*s4 - 12*s2 + s1)/21;
RL = 1000;
Sa(g) = Ssum(ta, g) - (psi(1/2 + g/2) + psi(-g/2))/2;
Sb(g) = Ssum(tb, g) - (psi(1 + g/2) + psi(1/2 - g/2))/2;
T(g) = my(C = 2*(1+2*g), k = 2/(1+2*g)); -4/g + k*(psi((1+g)/C) - psi((1+3*g)/C) + psi((2+5*g)/C) - psi((2+3*g)/C));
Fab(a, b, g) = a*Sa(g) + b*Sb(g) + T(g);
ctwin(r1, r2, g) = (Fab(r1 + r2, r2, g) + (r1 + 2*r2)*log(Pi))/2;

\\ check of the extrapolated series against much longer partial sums (Richardson at L = 10000, i.e. 40000 terms)
{
my(g = 47/100, a1 = Ssum(ta, g), b1 = Ssum(tb, g), a2, b2);
RL = 10000; a2 = Ssum(ta, g); b2 = Ssum(tb, g); RL = 1000;
print("series at g = 0.47: Sa sum ", a1, " (L = 1000) vs ", a2, " (L = 10000); Sb sum ", b1, " vs ", b2);
chk(abs(a1 - a2) < 1e-11 && abs(b1 - b2) < 1e-11, "extrapolated series stable to 1e-11");
}
\\ cache [Sa, Sb, T] per gamma (independent of the signature)
SVC = Map();
SV(g) = my(v); if (mapisdefined(SVC, g, &v), return(v)); v = [Sa(g), Sb(g), T(g)]; mapput(SVC, g, v); v;
ctw(r1, r2, g) = my(v = SV(g)); ((r1 + r2)*v[1] + r2*v[2] + v[3] + (r1 + 2*r2)*log(Pi))/2;
ctwin(r1, r2, g) = ctw(r1, r2, g);
\\ maximise f on a shared grid gamma = lo + i h (integers skipped: removable singularities), then golden section
GRID(lo, hi, h) = [g | g <- vector(round((hi - lo)/h) + 1, i, lo + (i - 1)*h), abs(g - round(g)) > 1e-9];
vertex(x0, x1, x2, y0, y1, y2) = my(d = (x0 - x1)*(x0 - x2)*(x1 - x2), A = (x2*(y1 - y0) + x1*(y0 - y2) + x0*(y2 - y1))/d, B = (x2^2*(y0 - y1) + x1^2*(y2 - y0) + x0^2*(y1 - y2))/d); -B/(2*A);
gmax(f, grid) = {
  my(best = -oo, ib = 0, h = grid[2] - grid[1], v, w, e);
  for (i = 1, #grid, my(y = f(grid[i])); if (y > best, best = y; ib = i));
  if (ib == 1 || ib == #grid, error("maximum at the end of the grid"));
  v = vertex(grid[ib-1], grid[ib], grid[ib+1], f(grid[ib-1]), best, f(grid[ib+1]));
  e = h/20; w = vertex(v - e, v, v + e, f(v - e), f(v), f(v + e));
  [w, f(w)];
}
\\ ---- KAT 1: Zimmert Table 1 (Satz 2): [n, r1, r2, gamma, printed lower bound for d^(1/2)/N a, rounded down]
TAB1 = [[1,1,0,5.35,0.8991],[2,2,0,2.41,1.760],[2,0,1,2.98,1.400],[3,3,0,1.56,4.636],[3,1,1,1.84,3.355],[4,4,0,1.18,14.45],[4,2,1,1.34,9.749],[4,0,2,1.54,6.792],[5,5,0,0.96,50.21],[5,3,1,1.07,32.12],[5,1,2,1.20,21.11],[6,6,0,0.83,188.1],[6,0,3,1.09,46.74],[8,8,0,0.66,3088],[8,0,4,0.87,385.5],[10,10,0,0.56,5.854e4],[10,0,5,0.74,3560],[20,20,0,0.36,4.332e11],[20,0,10,0.46,5.736e8],[100,100,0,0.14,8.448e72],[100,0,50,0.18,2.417e55]];
{
my(bad = 0);
for (i = 1, #TAB1, my(e = TAB1[i], v = exp(S2b(e[2], e[3], e[4])), rel = v/e[5] - 1);
  printf("Table 1  n=%3d r1=%3d r2=%2d g=%.2f  printed %.4g  computed %.6g  rel %.2e\n", e[1], e[2], e[3], e[4], e[5], v, rel);
  \\ printed values are rounded down to 4 significant digits: 0 <= rel < 10^-3 expected
  if (rel < -1e-9 || rel > 1.2e-3, bad++));
chk(bad == 0, "Satz 2 reproduces all 21 entries of Zimmert's Table 1 (printed value = computed value rounded down to 4 digits)");
}
\\ ---- KAT 2: Zimmert Table 3 (Korollar 1): printed exp(c) at printed gamma, 3 significant digits, rounded down
TAB3 = [[1,1,0,5.23,0.952],[2,2,0,2.36,1.98],[2,0,1,2.94,1.55],[3,3,0,1.53,5.56],[3,1,1,1.82,3.95],[4,4,0,1.15,18.5],[4,2,1,1.31,12.1],[4,0,2,1.53,8.32],[5,5,0,0.95,68.5],[5,3,1,1.06,42.7],[5,1,2,1.19,27.4],[6,6,0,0.82,273],[6,0,3,1.09,62.9],[8,8,0,0.66,5110],[8,0,4,0.87,570],[10,10,0,0.56,1.10e5],[10,0,5,0.74,5.77e3],[20,20,0,0.36,1.63e12],[20,0,10,0.47,1.48e9],[100,100,0,0.13,1.5e76],[100,0,50,0.18,3.5e57]];
\\ number of significant digits printed in Table 3 (appended as 6th field)
TAB3 = vector(#TAB3, i, concat(TAB3[i], if (i >= 20, 2, 3)));
\\ v truncated to k significant digits equals the printed value P
truncok(v, P, k) = my(e = floor(log(v)/log(10)), u = 10^(e - k + 1)); floor(v/u) == round(P/u);
{
my(bad = 0);
for (i = 1, #TAB3, my(e = TAB3[i], v = exp(ctwin(e[2], e[3], e[4])), rel = v/e[5] - 1);
  printf("Table 3  n=%3d r1=%3d r2=%2d g=%.2f  printed %.4g  computed %.6g  rel %.2e\n", e[1], e[2], e[3], e[4], e[5], v, rel);
  if (!truncok(v, e[5], e[6]), bad++));
chk(bad == 0, "Korollar 1 reproduces all 21 entries of Zimmert's Table 3 (printed value = computed value truncated to the printed digits)");
}
GR = GRID(25/100, 35/10, 1/100);
\\ ---- KAT 3: PARI's table (buch3.c, zimmertbound), c[n][r2] for 2 <= n <= 20
PC = [[0.6931,0.45158],[1.71733859,1.37420604],[2.91799837,2.50091538,2.11943331],[4.22701425,3.75471588,3.31196660],[5.61209925,5.09730381,4.60693851,4.14303665],[7.05406203,6.50550021,5.97735406,5.47145968],[8.54052636,7.96438858,7.40555445,6.86558259,6.34608077],[10.0630022,9.46382812,8.87952524,8.31139202,7.76081149],[11.6153797,10.9966020,10.3907654,9.79895170,9.22232770,8.66213267],[13.1930961,12.5573772,11.9330458,11.3210061,10.7222412,10.1378082],[14.7926394,14.1420915,13.5016616,12.8721114,12.2542699,11.6490374,11.0573775],[16.4112395,15.7475710,15.0929680,14.4480777,13.8136054,13.1903162,12.5790381],[18.0466672,17.3712806,16.7040780,16.0456127,15.3964878,14.7573587,14.1289364,13.5119848],[19.6970961,19.0111606,18.3326615,17.6620757,16.9999233,16.3467686,15.7032228,15.0699480],[21.3610081,20.6655103,19.9768082,19.2953176,18.6214885,17.9558093,17.2988108,16.6510652,16.0131906],[23.0371259,22.3329066,21.6349299,20.9435607,20.2591899,19.5822454,18.9131878,18.2525157,17.6007672],[24.7243611,24.0121449,23.3056902,22.6053167,21.9113705,21.2242247,20.5442836,19.8719830,19.2077941,18.5522234],[26.4217792,25.7021950,24.9879497,24.2793271,23.5766321,22.8801952,22.1903709,21.5075437,20.8321263,20.1645647],[28.1285704,27.4021674,26.6807314,25.9645140,25.2537867,24.5488420,23.8499943,23.1575823,22.4719720,21.7935548,21.1227537]];
{
my(maxd = 0, nb = 0, cnt = 0);
for (n = 2, 20, for (r2 = 0, n\2,
  if (r2 + 1 > #PC[n-1], next);
  my(r1 = n - 2*r2, pc = PC[n-1][r2+1], m = gmax(g -> ctwin(r1, r2, g), GR), dd = m[2] - pc);
  cnt++;
  printf("PARI  n=%2d r2=%2d  PARI %.8f  own max %.8f at g=%.4f  diff %.2e\n", n, r2, pc, m[2], m[1], dd);
  if (n > 2, maxd = max(maxd, abs(dd)); if (abs(dd) > 1e-6, nb++))));
print("entries compared: ", cnt, ", max |diff| for n >= 3: ", maxd);
chk(nb == 0, "optimised Korollar 1 constant agrees with every PARI entry for 3 <= n <= 20 to 1e-6");
}
\\ ---- the field K21: n = 21, r1 = 3, r2 = 9, |d| = 2^22 7^27
{
my(r1 = 3, r2 = 9, n = 21, sd = sqrt(2^22 * 7^27), m2 = gmax(g -> S2b(r1, r2, g), GRID(1/100, 4, 1/100)), mt = gmax(g -> ctwin(r1, r2, g), GR), MK = sd * (4/Pi)^9 * 21!/21^21);
print("K21: Minkowski bound ", MK);
print("K21: Satz 2 (every class): max S2 = ", m2[2], " at g = ", m2[1], ", bound sqrt(d) exp(-S2) = ", sd*exp(-m2[2]));
print("K21: Korollar 1 (twin classes): max c = ", mt[2], " at g = ", mt[1], ", bound sqrt(d) exp(-c) = ", sd*exp(-mt[2]));
\\ rigorous values at a fixed rational gamma (the theorems hold for every gamma > alpha > 0)
my(g2 = 45/100, al2 = bestal(45/100), gt = 45/100);
print("K21: Satz 2 at g = 0.45, al = ", al2, ": bound ", sd*exp(-S2(r1, r2, g2, al2)));
print("K21: Korollar 1 at g = 0.45: bound ", sd*exp(-ctwin(r1, r2, gt)));
}
quit;
