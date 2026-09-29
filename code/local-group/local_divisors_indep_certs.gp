\\ local_divisors_indep_certs.gp: certificates for the independence of the x - T classes [U_1(T)], ..., [U_7(T)] of the local divisors
\\ D_1..D_7 in H(g), g = (fRev k)^sigma over K_v (lean/FurioLombardo/Discharge/SelmerSpan/Indep.lean, data IData.lean).
\\ Model (as local_divisors_independence.gp): N' = K_v(w'), w'^2 = dl = sigma(d)/4 = h1^2 - q0 (h1 = q1/2), tau = -h1 + w' a root of q;
\\ P1 = a1 + B1 w', P0 = a0 + B0 w' (B_i = 2 b_i), M' = N'(x0), x0^2 = -P0 - P1 x0 (x0 a root of h). Characters:
\\   psi1(y) = N_{N'/K_v}(y(tau)) in K_v, psi2(y) = N_{M'/N'}(y(x0)) in N', psi3(y) = y(x0) y(tau) in M';
\\ each is a square when y = c w^2 (c in K_v). For U = X^2 + p X + r:
\\   U(tau) = (h1^2 + dl - p h1 + r) + (p - 2 h1) w',  U(x0) = (r - P0) + (p - P1) x0.
\\ Every residue is computed with the exact triple arithmetic of the Lean checks (modulo 2^P, reduction after each
\\ operation), and compared with the p-adic model (completion_kv_lib.gp). Per factor the value is scaled by a square
\\ (pi^a / 2^b)^2 (normT), per combination c in F_2^7 - 0 the first character that is not a square gets a certificate:
\\   level 1: SqTest of the product of the psi1 (searched in the kernel, no data);
\\   level 2: ZOK of the product of the psi2 in N' (data: b, r, P, ip, jp, im, jm);
\\   level 3: the M'-test of the product z of the psi3: n^2 = N(z) with n = <s/2, y/s>, m^2 = x^2 - dl y^2,
\\            s^2 = 2 (x + m) ((x, y) = N(z)), and E+-, = s^2 (Tr z +- 2 n) = 2 (x + m) Tr z +- 2 s (x + m, y), not squares
\\            in N' (ZOK each).
\\ Run from code/local-group: gp -q local_divisors_indep_certs.gp (LEANOUT=<dir>/ writes IData.lean to <dir> instead)
default(parisizemax, 3*10^9); default(nbthreads, 1);
[t, x, y, z, X, u, w, a, s, b];
read("../descent/descent_data_lib.gp");
read("completion_kv_lib.gp");
read("lean_data_reader.gp");
LD = "../../FurioLombardo/Discharge/SelmerSpan/DData.lean";
pDataL = leandef(LD, "pData"); rDataL = leandef(LD, "rData"); pDenL = leandef(LD, "pDen"); rDenL = leandef(LD, "rDen");
pJOL = leandef(LD, "pJO"); rJOL = leandef(LD, "rJO"); pOiL = leandef(LD, "pOi"); rOiL = leandef(LD, "rOi");
PI = 48;
\\ high precision residues (lean/FurioLombardo/Discharge/SelmerSpan/Sigma.lean): theta1 = theta* mod 2^70, f(theta1) = 0 mod 2^70,
\\ so |theta* - theta1| <= 2^-63 and the residues of sigma(zkE l) are known modulo 2^58
NTH = 70; NZ = 58;
TH1 = trip(th, NTH);
fLL = Vecrev(K21);
chq(fLL == [-4, 28, -112, 252, -336, 28, 560, -1072, 1008, -280, -770, 980, -609, 175, 2, 98, -84, 0, 0, 14, -7, 1], "fL of M1");
chq(dvdT(hornerZ(TH1, fLL), 2^NTH), "f(theta1) = 0 mod 2^70");
chq(dvdT(TH1 - th0, 2^33), "theta1 = theta0 mod 2^33");
uOdd1 = lift(Mod(1, 2^NZ) / Dodd);
zresOK1(l) = dvdT(hornerZ(TH1, combo(l)), 32);
zres1(l) = mulZ(hornerZ(TH1, combo(l)) / 32, [uOdd1, 0, 0]);
sQok1(l, j, o, oi, P) = zresOK1(l) && P + j <= NZ && P >= 1 && dvdT(modT(zres1(l), P + j), 2^j) && modT(mulZ([o, 0, 0], [oi, 0, 0]), P) == [1, 0, 0];
sQres1(l, j, oi, P) = mulZ(modT(zres1(l), P + j) / 2^j, [oi, 0, 0]);
oinv1(o) = lift(Mod(1, 2^NZ) / o);
addT(x, y, P) = modT(x + y, P);
subT(x, y, P) = modT(x - y, P);
mulT(x, y, P) = modT(mulZ(x, y), P);
cT(c) = [c, 0, 0];
minv2(v) = min(v2(v[1]), min(v2(v[2]), v2(v[3])));
\\ N' pairs
addN(u, w, P) = [addT(u[1], w[1], P), addT(u[2], w[2], P)];
subN(u, w, P) = [subT(u[1], w[1], P), subT(u[2], w[2], P)];
scN(c, u, P) = [mulT(c, u[1], P), mulT(c, u[2], P)];
mulN(u, w, dl, P) = [addT(mulT(u[1], w[1], P), mulT(dl, mulT(u[2], w[2], P), P), P), addT(mulT(u[1], w[2], P), mulT(u[2], w[1], P), P)];
normN(u, dl, P) = subT(mulT(u[1], u[1], P), mulT(dl, mulT(u[2], u[2], P), P), P);
\\ M' pairs of N' pairs: re = z0 v0 - P0 z1 v1, im = z0 v1 + z1 v0 - P1 z1 v1
mulM(z, v, dl, Q0, Q1, P) = { my(zz = mulN(z[2], v[2], dl, P));
  [subN(mulN(z[1], v[1], dl, P), mulN(Q0, zz, dl, P), P),
   subN(addN(mulN(z[1], v[2], dl, P), mulN(z[2], v[1], dl, P), P), mulN(Q1, zz, dl, P), P)] };
normM(z, dl, Q0, Q1, P) = addN(subN(mulN(z[1], z[1], dl, P), mulN(Q1, mulN(z[1], z[2], dl, P), dl, P), P), mulN(Q0, mulN(z[2], z[2], dl, P), dl, P), P);
\\ scaling by (pi^a / 2^b)^2 as Lean's normT: divT (modT (mulZ (modT t P) (pvT (2a))) P) (2^(2b)), precision P - 2b
normT(t, P, aa, bb) = { my(u = modT(mulZ(modT(t, P), pvT(2 * aa)), P)); chq(dvdT(u, 2^(2 * bb)), "normT divisibility"); u / 2^(2 * bb) };
\\ p-adic model of N' and M' (as local_divisors_independence.gp)
pmulN(u, v, dl) = [u[1]*v[1] + dl*u[2]*v[2], u[1]*v[2] + u[2]*v[1]];
pnormN(u, dl) = u[1]^2 - dl*u[2]^2;
paddN(u, v) = [u[1] + v[1], u[2] + v[2]];
psc(c, u) = [c * u[1], c * u[2]];
pmulM(z, v, dl, Q0, Q1) = { my(zz = pmulN(z[2], v[2], dl));
  [paddN(pmulN(z[1], v[1], dl), psc(-1, pmulN(Q0, zz, dl))), paddN(paddN(pmulN(z[1], v[2], dl), pmulN(z[2], v[1], dl)), psc(-1, pmulN(Q1, zz, dl)))] };
pnormM(z, dl, Q0, Q1) = paddN(paddN(pmulN(z[1], z[1], dl), psc(-1, pmulN(Q1, pmulN(z[1], z[2], dl), dl))), pmulN(Q0, pmulN(z[2], z[2], dl), dl));
nsq(z, dl) = { my(n); if (z[2] == 0 || vpi(z[2]) > 2000, return(ksq(z[1]) || ksq(z[1] / dl)));
  if (!ksq(pnormN(z, dl)), return(0)); n = ksqrt(pnormN(z, dl)); ksq(2 * (z[1] + n)) || ksq(2 * (z[1] - n)) };
nvp(z) = min(vpi(z[1]), vpi(z[2]));
\\ the square-test search of the kernel (level 1): i < 3, j < 12
sqSearch(t, e, P) = { for (i = 0, 2, for (j = 0, 11, if (sqTest(t, i, j, e, P), return([i, j])))); 0 };
\\ non-square certificate of z = z0 + z1 w' in N' (residues tz at precision M, p-adic value zp):
\\   [0, i, j]: SqTest of the norm z0^2 - dl z1^2 (not a square in K_v), or [1, b, r, P, ip, jp, im, jm]: ZOK
zokCert(tz, zp, dl, pdl, M) = { my(tN = normN(tz, dl, M), nn, bb, r, P, cp, cm, c0);
  c0 = sqSearch(tN, 0, M);
  if (type(c0) == "t_VEC", chq(!ksq(pnormN(zp, pdl)), "norm test consistent"); return([0, c0[1], c0[2]]));
  chq(ksq(pnormN(zp, pdl)), "zok: norm not a square");
  nn = ksqrt(pnormN(zp, pdl)); bb = trip(nn, M);
  chq(modT(mulZ(bb, bb), M) == modT(tN, M), "zok: b^2 = N mod 2^M");
  r = max(3, minv2(bb) + 3); P = M - r;
  chq(lowOK(bb, r - 3) && 2 * r < M && P + r <= M, "zok: precision");
  cp = sqSearch(tz[1] + bb, 1, P); cm = sqSearch(tz[1] - bb, 1, P);
  chq(type(cp) == "t_VEC" && type(cm) == "t_VEC", "zok: square tests");
  [1, bb, r, P, cp[1], cp[2], cm[1], cm[2]] };
zokOK(t0, tN, bb, M, r, P, ip, jp, im, jm) = modT(mulZ(bb, bb), M) == modT(tN, M) && lowOK(bb, r - 3) && 3 <= r && 2 * r < M && P + r <= M && sqTest(t0 + bb, ip, jp, 1, P) && sqTest(t0 - bb, im, jm, 1, P);
atomD(l, m) = { my(js = splitm(m)); [l, m, js[1], js[2], oinv1(js[2])] };
zkv(l, m) = sg(nfbasistoalg(nf, l~) / m);
OUT = vector(2); OI = vector(2, k, vector(7));
{
  for (k = 1, 2,
    my(At = vector(7), tA = vector(7), pA = vector(7), dl, Q0, Q1, pdl, pQ0, pQ1, fac = vector(7), sc = vector(7), Pc = [0, 0, 0],
       lev = vector(127), dat2 = List(), dat3 = List(), cnt = [0, 0, 0]);
    \\ atoms: h1 = q1/2, q0, a0, a1, B0 = 2 b0, B1 = 2 b1 (Lean lists qData, abData; denominators 2 qDen, qDen, maDen, mbDen/2)
    chq(mbDenL[k] % 2 == 0, "mbDen even");
    At[1] = atomD(qDataL[k][2], 2 * qDenL[k]); At[2] = atomD(qDataL[k][1], qDenL[k]);
    At[3] = atomD(abDataL[k][1], maDenL[k]); At[4] = atomD(abDataL[k][2], maDenL[k]);
    At[5] = atomD(abDataL[k][3], mbDenL[k] / 2); At[6] = atomD(abDataL[k][4], mbDenL[k] / 2);
    for (j = 1, 6, chq(sQok1(At[j][1], At[j][3], At[j][4], At[j][5], PI), Str("sQok1 atom ", j));
      tA[j] = sQres1(At[j][1], At[j][3], At[j][5], PI); pA[j] = zkv(At[j][1], At[j][2]);
      chq(modT(tA[j], PI) == trip(pA[j], PI), Str("atom ", j, " agrees with sigma")));
    my(th1 = tA[1], tq0 = tA[2]);
    dl = subT(mulT(th1, th1, PI), tq0, PI); Q1 = [tA[4], tA[6]]; Q0 = [tA[3], tA[5]];
    pdl = pA[1]^2 - pA[2]; pQ1 = [pA[4], pA[6]]; pQ0 = [pA[3], pA[5]];
    chq(vpi(pdl - zkv(dnDataL[k], 4 * qDenL[k]^2)) > 2000, "dl = sigma(d)/4");
    dlc = dl;
    printf("---- twist %d: atoms j = %s, v(dl) %d\n", k - 1, vector(6, j, At[j][3]), vpi(pdl));
    for (i = 1, 7,
      my(pJ = pJOL[k][i], rJ = rJOL[k][i], tp, tr, pp, rr, X1, Y1, ps1, u0, u1, ps2, ps3, pX, pY, pu0, pu1, pps1, pps2, pps3, b1, b2, b3, poi, roi);
      poi = oinv1(pJ[2]); roi = oinv1(rJ[2]); OI[k][i] = [poi, roi];
      chq(pJ[1] + PI <= NZ && rJ[1] + PI <= NZ, "precision of p, r");
      chq(pDenL[k][i] == 2^pJ[1] * pJ[2] && rDenL[k][i] == 2^rJ[1] * rJ[2], "denominators of p, r");
      chq(sQok1(pDataL[k][i], pJ[1], pJ[2], poi, PI) && sQok1(rDataL[k][i], rJ[1], rJ[2], roi, PI), "sQok1 p, r");
      tp = sQres1(pDataL[k][i], pJ[1], poi, PI); tr = sQres1(rDataL[k][i], rJ[1], roi, PI);
      pp = zkv(pDataL[k][i], pDenL[k][i]); rr = zkv(rDataL[k][i], rDenL[k][i]);
      chq(modT(tp, PI) == trip(pp, PI) && modT(tr, PI) == trip(rr, PI), "p, r agree");
      \\ U(tau)
      X1 = addT(subT(addT(mulT(th1, th1, PI), dl, PI), mulT(tp, th1, PI), PI), tr, PI);
      Y1 = subT(tp, mulT(cT(2), th1, PI), PI);
      ps1 = normN([X1, Y1], dl, PI);
      \\ U(x0) = (r - P0) + (p - P1) x0
      u0 = [subT(tr, tA[3], PI), subT([0, 0, 0], tA[5], PI)]; u1 = [subT(tp, tA[4], PI), subT([0, 0, 0], tA[6], PI)];
      ps2 = normM([u0, u1], dl, Q0, Q1, PI);
      ps3 = [mulN(u0, [X1, Y1], dl, PI), mulN(u1, [X1, Y1], dl, PI)];
      \\ p-adic
      pX = pA[1]^2 + pdl - pp * pA[1] + rr; pY = pp - 2 * pA[1];
      pps1 = pnormN([pX, pY], pdl);
      pu0 = [rr - pA[3], -pA[5]]; pu1 = [pp - pA[4], -pA[6]];
      pps2 = pnormM([pu0, pu1], pdl, pQ0, pQ1);
      pps3 = [pmulN(pu0, [pX, pY], pdl), pmulN(pu1, [pX, pY], pdl)];
      chq(modT(ps1, PI) == trip(pps1, PI), "psi1 agrees");
      chq(modT(ps2[1], PI) == trip(pps2[1], PI) && modT(ps2[2], PI) == trip(pps2[2], PI), "psi2 agrees");
      \\ scalings (a = 0, b = floor(v / 6))
      b1 = vpi(pps1) \ 6; b2 = nvp(pps2) \ 6; b3 = min(nvp(pps3[1]), nvp(pps3[2])) \ 6;
      sc[i] = [b1, b2, b3];
      fac[i] = [normT(ps1, PI, 0, b1), [normT(ps2[1], PI, 0, b2), normT(ps2[2], PI, 0, b2)],
                [[normT(ps3[1][1], PI, 0, b3), normT(ps3[1][2], PI, 0, b3)], [normT(ps3[2][1], PI, 0, b3), normT(ps3[2][2], PI, 0, b3)]],
                pps1 / 4^b1, psc(1 / 4^b2, pps2), [psc(1 / 4^b3, pps3[1]), psc(1 / 4^b3, pps3[2])]];
      printf("  D_%d: v(psi1) %d, v(psi2) %d, v(psi3) %d; scalings 2^(2b), b = %s\n", i, vpi(pps1), nvp(pps2), min(nvp(pps3[1]), nvp(pps3[2])), sc[i]));
    for (c = 1, 3, Pc[c] = PI - 2 * vecmax(vector(7, i, sc[i][c])));
    printf("  common precisions %s\n", Pc);
    \\ the combinations: index n = sum c_i 2^(i-1)
    for (n = 1, 127,
      my(cb = vector(7, i, bittest(n, i - 1)), t1 = cT(1), t2 = [cT(1), cT(0)], t3 = [[cT(1), cT(0)], [cT(0), cT(0)]], p1 = 1, p2 = [1, 0], p3 = [[1, 0], [0, 0]], s1);
      for (i = 1, 7, if (cb[i],
        t1 = mulT(t1, modT(fac[i][1], Pc[1]), Pc[1]); t2 = mulN(t2, [modT(fac[i][2][1], Pc[2]), modT(fac[i][2][2], Pc[2])], modT(dl, Pc[2]), Pc[2]);
        t3 = mulM(t3, [[modT(fac[i][3][1][1], Pc[3]), modT(fac[i][3][1][2], Pc[3])], [modT(fac[i][3][2][1], Pc[3]), modT(fac[i][3][2][2], Pc[3])]],
          modT(dl, Pc[3]), [modT(Q0[1], Pc[3]), modT(Q0[2], Pc[3])], [modT(Q1[1], Pc[3]), modT(Q1[2], Pc[3])], Pc[3]);
        p1 = p1 * fac[i][4]; p2 = pmulN(p2, fac[i][5], pdl); p3 = pmulM(p3, fac[i][6], pdl, pQ0, pQ1)));
      chq(modT(t1, Pc[1]) == trip(p1, Pc[1]), "product psi1 agrees");
      s1 = sqSearch(t1, 0, Pc[1]);
      if (type(s1) == "t_VEC", lev[n] = 1; cnt[1]++; chq(!ksq(p1), "level 1 consistent"); next);
      if (!ksq(p1), printf("  FAIL c = %s: v(p1) %d, t1 = %s, p1 = %s\n", cb, vpi(p1), t1, trip(p1, Pc[1])); next);
      if (!nsq(p2, pdl),
        my(cz = zokCert(t2, p2, modT(dl, Pc[2]), pdl, Pc[2]));
        chq(cz[1] == 0 || zokOK(t2[1], normN(t2, modT(dl, Pc[2]), Pc[2]), cz[2], Pc[2], cz[3], cz[4], cz[5], cz[6], cz[7], cz[8]), "zokOK level 2");
        lev[n] = 2; cnt[2]++; listput(dat2, [n, cz]);
        printf("  c = %s: level 2, v(psi2) %d, cert %s\n", cb, nvp(p2), if (cz[1] == 0, cz, [cz[1], cz[3], cz[4]])); next);
      \\ level 3: z = product of the psi3, scaled by (1/2^bz)^2, then n^2 = N(z) from m, s, then E+- (scaled)
      my(bz = min(nvp(p3[1]), nvp(p3[2])) \ 6, M3 = Pc[3] - 2 * bz, t3n, p3n, dlm, Q0m, Q1m, Nz, pNz, mm, bm, sm, Pm,
         sgn, bs, sss, Ps, xm, tr, pTr, Ep, Em, pEp, pEm, cp, cm, ps, bEp, bEm, PEp, PEm);
      t3n = [[normT(t3[1][1], Pc[3], 0, bz), normT(t3[1][2], Pc[3], 0, bz)], [normT(t3[2][1], Pc[3], 0, bz), normT(t3[2][2], Pc[3], 0, bz)]];
      p3n = [psc(1 / 4^bz, p3[1]), psc(1 / 4^bz, p3[2])];
      dlm = modT(dl, M3); Q0m = [modT(Q0[1], M3), modT(Q0[2], M3)]; Q1m = [modT(Q1[1], M3), modT(Q1[2], M3)];
      Nz = normM(t3n, dlm, Q0m, Q1m, M3); pNz = pnormM(p3n, pdl, pQ0, pQ1);
      chq(modT(Nz[1], M3) == trip(pNz[1], M3) && modT(Nz[2], M3) == trip(pNz[2], M3), "N(z) agrees");
      chq(nsq(pNz, pdl), "N(z) a square in N'");
      mm = ksqrt(pnormN(pNz, pdl));
      sgn = if (ksq(2 * (pNz[1] + mm)), 1, -1); mm = sgn * mm; chq(ksq(2 * (pNz[1] + mm)), "2 (x + m) square");
      bm = trip(mm, M3); sm = minv2(bm);
      chq(2 * sm + 4 <= M3 && lowOK(bm, sm) && modT(mulZ(bm, bm), M3) == modT(normN(Nz, dlm, M3), M3), "Hensel m");
      Pm = M3 - (sm + 2);
      ps = ksqrt(2 * (pNz[1] + mm)); bs = trip(ps, Pm); sss = minv2(bs);
      xm = addT(modT(Nz[1], Pm), modT(bm, Pm), Pm);
      chq(2 * sss + 4 <= Pm && lowOK(bs, sss) && modT(mulZ(bs, bs), Pm) == mulT(cT(2), xm, Pm), "Hensel s");
      Ps = Pm - (sss + 2);
      chq(modT(bs, Ps) != [0, 0, 0], "s != 0");
      my(dls = modT(dl, Ps), Q1s = [modT(Q1[1], Ps), modT(Q1[2], Ps)], z0 = [modT(t3n[1][1], Ps), modT(t3n[1][2], Ps)], z1 = [modT(t3n[2][1], Ps), modT(t3n[2][2], Ps)],
         xms = modT(xm, Ps), ys = modT(Nz[2], Ps), bss = modT(bs, Ps), A1, A2);
      tr = subN(scN(cT(2), z0, Ps), mulN(Q1s, z1, dls, Ps), Ps);
      A1 = scN(mulT(cT(2), xms, Ps), tr, Ps); A2 = scN(mulT(cT(2), bss, Ps), [xms, ys], Ps);
      Ep = addN(A1, A2, Ps); Em = subN(A1, A2, Ps);
      pTr = paddN(psc(2, p3n[1]), psc(-1, pmulN(pQ1, p3n[2], pdl)));
      pEp = paddN(psc(2 * (pNz[1] + mm), pTr), psc(2 * ps, [pNz[1] + mm, pNz[2]]));
      pEm = paddN(psc(2 * (pNz[1] + mm), pTr), psc(-2 * ps, [pNz[1] + mm, pNz[2]]));
      chq(modT(Ep[1], Ps) == trip(pEp[1], Ps) && modT(Ep[2], Ps) == trip(pEp[2], Ps), "E+ agrees");
      chq(modT(Em[1], Ps) == trip(pEm[1], Ps) && modT(Em[2], Ps) == trip(pEm[2], Ps), "E- agrees");
      chq(!nsq(pEp, pdl) && !nsq(pEm, pdl), "E+- not squares in N'");
      bEp = nvp(pEp) \ 6; bEm = nvp(pEm) \ 6; PEp = Ps - 2 * bEp; PEm = Ps - 2 * bEm;
      cp = zokCert([normT(Ep[1], Ps, 0, bEp), normT(Ep[2], Ps, 0, bEp)], psc(1 / 4^bEp, pEp), modT(dl, PEp), pdl, PEp);
      cm = zokCert([normT(Em[1], Ps, 0, bEm), normT(Em[2], Ps, 0, bEm)], psc(1 / 4^bEm, pEm), modT(dl, PEm), pdl, PEm);
      lev[n] = 3; cnt[3]++; listput(dat3, [n, bz, [bm, sm, bs, sss], bEp, cp, bEm, cm]);
      printf("  c = %s: level 3; v(z) %d %d, bz %d; v(N(z)) %d %d; v(m) %d, v(s) %d; v(E+-) %d, %d; precisions %d -> %d -> %d -> %d, %d; certs %s %s\n", cb,
        nvp(p3[1]), nvp(p3[2]), bz, vpi(pNz[1]), vpi(pNz[2]), vpi(mm), vpi(ps), nvp(pEp), nvp(pEm), M3, Pm, Ps, PEp, PEm,
        if (cp[1] == 0, cp, [1, cp[3], cp[4]]), if (cm[1] == 0, cm, [1, cm[3], cm[4]])));
    printf("  levels: %s\n", cnt); chq(cnt[1] + cnt[2] + cnt[3] == 127, "every combination certified");
    OUT[k] = [At, sc, Pc, Vec(dat2), Vec(dat3), modT(dl, PI), [modT(Q0[1], PI), modT(Q0[2], PI)], [modT(Q1[1], PI), modT(Q1[2], PI)],
      vector(7, i, modT(fac[i][1], Pc[1])), vector(7, i, [modT(fac[i][2][1], Pc[2]), modT(fac[i][2][2], Pc[2])]),
      vector(7, i, [[modT(fac[i][3][1][1], Pc[3]), modT(fac[i][3][1][2], Pc[3])], [modT(fac[i][3][2][1], Pc[3]), modT(fac[i][3][2][2], Pc[3])]])]);
}
\\ ---------------------------------------------------------------- Lean output (IData.lean)
trl(v) = Str("(", v[1], ", ", v[2], ", ", v[3], ")");
bl(n) = { my(s = "["); for (i = 0, 6, s = Str(s, if (bittest(n, i), "true", "false"), if (i < 6, ", ", ""))); Str(s, "]") };
ncert(c) = if (c[1] == 0, Str("(0, (0, 0, 0), 0, 0, ", c[2], ", ", c[3], ", 0, 0)"), Str("(1, ", trl(c[2]), ", ", c[3], ", ", c[4], ", ", c[5], ", ", c[6], ", ", c[7], ", ", c[8], ")"));
joinL(V, sep) = { my(s = ""); for (i = 1, #V, s = Str(s, V[i], if (i < #V, sep, ""))); s };
out = Str(if (#getenv("LEANOUT"), getenv("LEANOUT"), "../../FurioLombardo/Discharge/SelmerSpan/"), "IData.lean");
system(Str("rm -f ", out));
write(out, "/-! Data of the independence certificates (lane SelmerSpan; generated by code/local-group/local_divisors_indep_certs.gp,\nPARI/GP). Per twist `k`: `atJO[k]`: `(j, o, oi)` of the atoms `q1/2, q0, a0, a1, 2 b0, 2 b1` (denominator `2^j o`, `oi` an\ninverse of `o` modulo `2^58`); `prOI[k][i]`: inverses modulo `2^58` of the odd parts of the denominators of `p_i`, `r_i`;\n`scalD[k][i] = (b1, b2, b3)`: the scalings `4^(-b)` of the three character values of `U_i(T)`; `pcD[k]`: the common\nprecisions of the three products; `lev2D[k]`, `lev3D[k]`: the certificates of the combinations (keys: the bits) that the\nfirst character does not detect. -/\n\nnamespace FurioLombardo.Discharge.SelmerSpan\n\nset_option maxRecDepth 100000\n");
write(out, "/-- The working precision of the independence certificates. -/\ndef PI : Nat := ", PI, "\n");
write(out, "def atJO : List (List (Nat × Nat × Int)) :=\n  [", joinL(vector(2, k, Str("[", joinL(vector(6, j, Str("(", OUT[k][1][j][3], ", ", OUT[k][1][j][4], ", ", OUT[k][1][j][5], ")")), ", "), "]")), ",\n   "), "]\n");
write(out, "def prOI : List (List (Int × Int)) :=\n  [", joinL(vector(2, k, Str("[", joinL(vector(7, i, Str("(", OI[k][i][1], ", ", OI[k][i][2], ")")), ", "), "]")), ",\n   "), "]\n");
write(out, "def scalD : List (List (Nat × Nat × Nat)) :=\n  [", joinL(vector(2, k, Str("[", joinL(vector(7, i, trl(OUT[k][2][i])), ", "), "]")), ",\n   "), "]\n");
write(out, "def pcD : List (Nat × Nat × Nat) :=\n  [", joinL(vector(2, k, trl(OUT[k][3])), ", "), "]\n");
trp(v) = Str("(", trl(v[1]), ", ", trl(v[2]), ")");
trq(v) = Str("(", trp(v[1]), ", ", trp(v[2]), ")");
write(out, "/-- Residues modulo `2^PI` of `δ' = (q1/2)^2 - q0`, `P0 = (a0, 2 b0)`, `P1 = (a1, 2 b1)`. -/\ndef dlD : List (Int × Int × Int) :=\n  [", joinL(vector(2, k, trl(OUT[k][6])), ", "), "]\n");
write(out, "def P0D : List ((Int × Int × Int) × (Int × Int × Int)) :=\n  [", joinL(vector(2, k, trp(OUT[k][7])), ", "), "]\n");
write(out, "def P1D : List ((Int × Int × Int) × (Int × Int × Int)) :=\n  [", joinL(vector(2, k, trp(OUT[k][8])), ", "), "]\n");
write(out, "/-- The scaled character values of `U_i(T)` modulo `2^Pc`. -/\ndef F1D : List (List (Int × Int × Int)) :=\n  [", joinL(vector(2, k, Str("[", joinL(vector(7, i, trl(OUT[k][9][i])), ", "), "]")), ",\n   "), "]\n");
write(out, "def F2D : List (List ((Int × Int × Int) × (Int × Int × Int))) :=\n  [", joinL(vector(2, k, Str("[", joinL(vector(7, i, trp(OUT[k][10][i])), ",\n    "), "]")), ",\n   "), "]\n");
write(out, "def F3D : List (List (((Int × Int × Int) × (Int × Int × Int)) × ((Int × Int × Int) × (Int × Int × Int)))) :=\n  [", joinL(vector(2, k, Str("[", joinL(vector(7, i, trq(OUT[k][11][i])), ",\n    "), "]")), ",\n   "), "]\n");
write(out, "def lev2D : List (List (List Bool × (Nat × (Int × Int × Int) × Nat × Nat × Nat × Nat × Nat × Nat))) :=\n  [", joinL(vector(2, k, Str("[", joinL(vector(#OUT[k][4], j, Str("(", bl(OUT[k][4][j][1]), ", ", ncert(OUT[k][4][j][2]), ")")), ",\n    "), "]")), ",\n   "), "]\n");
{ write(out, "def lev3D : List (List (List Bool × (Nat × (Int × Int × Int) × Nat × (Int × Int × Int) × Nat × Nat ×\n    (Nat × (Int × Int × Int) × Nat × Nat × Nat × Nat × Nat × Nat) × Nat ×\n    (Nat × (Int × Int × Int) × Nat × Nat × Nat × Nat × Nat × Nat)))) :=\n  [",
  joinL(vector(2, k, Str("[", joinL(vector(#OUT[k][5], j, my(d = OUT[k][5][j]); Str("(", bl(d[1]), ", (", d[2], ", ", trl(d[3][1]), ", ", d[3][2], ", ", trl(d[3][3]), ", ", d[3][4], ", ", d[4], ", ", ncert(d[5]), ", ", d[6], ", ", ncert(d[7]), "))")), ",\n    "), "]")), ",\n   "), "]\n"); }
write(out, "end FurioLombardo.Discharge.SelmerSpan");
printf("theta1 = %s, uOdd1 = %d\n", TH1, uOdd1);
quit;
