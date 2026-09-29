\\ prym_lib.gp: unramified double covers of smooth plane quartics in Bruin form and their Prym varieties.
\\ Reference: N. Bruin, "The arithmetic of Prym varieties in genus 3", Compositio Math. 144 (2008),
\\ arXiv math/0408069, Theorem 5.1 (Table 2, case 4) and Section 8.
\\   C : Q1*Q3 = Q2^2  (Q_i ternary quadratic forms in x,y,z over a field K),
\\   D_delta : Q1 = delta r^2, Q2 = delta r s, Q3 = delta s^2   (canonical genus 5 curve in P^4),
\\   Prym(D_delta/C) = Jac(F_delta),  F_delta : Y^2 = -delta * det(M1 + 2 t M2 + t^2 M3),
\\ M_i the symmetric matrix of Q_i (Q(v) = v^t M v).
\\ Variables: forms in (x, y, z); the Prym curve in t. Coefficients may be POLMODs (number field elements);
\\ the number field variable must have lower priority than x, y, z, t (declare it after them).
[x, y, z, t];
qmat(Q) = matrix(3, 3, i, j, simplify(deriv(deriv(Q, [x, y, z][i]), [x, y, z][j]) / 2));
prymf(Q1, Q2, Q3, delta) = -delta * matdet(qmat(Q1) + 2*t*qmat(Q2) + t^2*qmat(Q3));

\\ isomorphism over the algebraic closure of two genus 2 curves Y^2 = f(t), Y^2 = g(t):
\\ equality of the Igusa invariants [J2, J4, J6, J8, J10] in weighted projective space (weights 1..5)
g2isqbar(f, g) = {
  my(A = genus2igusa(f), B = genus2igusa(g));
  for (i = 1, 5, for (j = 1, 5,
    if (A[i]^j * B[j]^i != A[j]^i * B[i]^j, return(0))));
  for (i = 1, 5, if ((A[i] == 0) != (B[i] == 0), return(0)));
  1;
}

\\ ---------- point counts over a prime field (known-answer tests) ----------
\\ Inputs with rational (or already reduced) coefficients. Returns [#C(F_p), sum_P chi(delta Q(P))],
\\ where Q = Q1, or Q3 where Q1 vanishes; the sum is #D_delta(F_p) - #C(F_p) = -tr(Frob | H^1(Prym)).
chi_at(Q1, Q3, delta, P, p) = {
  my(a = Mod(substvec(Q1, [x,y,z], P), p) * delta);
  if (a == 0, a = Mod(substvec(Q3, [x,y,z], P), p) * delta);
  if (a == 0, error("Q1 and Q3 both vanish at a point of C mod ", p));
  kronecker(lift(a), p);
}
prymsum_p(Q1, Q2, Q3, delta, p) = {
  my(s = 0, pts = 0, Fq = Q1*Q3 - Q2^2, P);
  for (a = 0, p-1, for (b = 0, p-1,
    P = [a, b, 1]; if (Mod(substvec(Fq, [x,y,z], P), p) == 0, pts++; s += chi_at(Q1, Q3, delta, P, p))));
  for (a = 0, p-1, P = [a, 1, 0]; if (Mod(substvec(Fq, [x,y,z], P), p) == 0, pts++; s += chi_at(Q1, Q3, delta, P, p)));
  P = [1, 0, 0]; if (Mod(substvec(Fq, [x,y,z], P), p) == 0, pts++; s += chi_at(Q1, Q3, delta, P, p));
  [pts, s];
}
\\ #F(F_p) for Y^2 = f(t), deg f = 5 or 6 over F_p; returns -1 if the degree drops mod p
g2count_p(f, p) = {
  my(fp = f * Mod(1, p), n = 0, d = poldegree(fp));
  for (a = 0, p-1, n += 1 + kronecker(lift(subst(fp, t, a)), p));
  if (d == 5, n += 1, if (d == 6, n += 1 + kronecker(lift(pollead(fp)), p), return(-1)));
  n;
}
