\\ abel_prym_lib.gp: the map phi : D_delta -> Jac(F_delta) of Bruin, "The arithmetic of Prym varieties in genus 3"
\\ (arXiv math/0408069, section 6 "Mapping D into Prym(D/C)", Lemma 6.1 = lemma:phimap and Proposition 6.2 = prop:Demb of the arXiv source), with 2 (iota - id)(P) = [phi(P) - kappa_F].
\\
\\   C : Q1 Q3 = Q2^2 (ternary quadratic forms in x, y, z), D_delta in P^4 (coordinates x, y, z, r, s):
\\       Q1 = delta r^2, Q2 = delta r s, Q3 = delta s^2,
\\   F_delta : Y^2 = f(t) = -delta det(M1 + 2 t M2 + t^2 M3)   (M_i the symmetric matrix of Q_i).
\\
\\ For P in D: T is a second point of the tangent line of D at P; the two points of phi(P) on F have
\\ t-coordinates the roots of  T'QD1 T + 2 t T'QD2 T + t^2 T'QD3 T = 0  (QD_i the 5x5 matrices of Q_i - delta (r^2, rs, s^2)).
\\ For such a root t0 the plane spanned by P, T and the vertex (0:0:0:t0:-1) lies on the rank 4 quadric
\\ Q_t0 = M_t0(x, y, z) - delta (r + t0 s)^2; the Y-coordinate encodes the ruling of Q_t0 containing that plane.
\\ Ruling rule (Galois equivariant, algebraic in t0): in W = (x, y, z, rho = r + t0 s) with Gram matrix
\\ G = diag(M_t0, -delta), det G = f(t0), a totally isotropic plane with basis a, b has Pluecker matrix
\\ A = a b' - b a' satisfying  G A G = Y * star(A)  with Y^2 = det G  (star = Hodge star of the standard
\\ volume form on k^4); Y is the Y-coordinate of the point of F. Swapping the two rulings changes Y to -Y.
\\ The rule is checked at every call (G A G proportional to star(A), Y^2 = f(t0), U | V^2 - f).
\\
\\ Output: Mumford pair [U, V], U monic of degree 2 in t, deg V <= 1, U | V^2 - f; the point of Jac(F) is
\\ [(t1, V(t1)) + (t2, V(t2)) - D_infinity] (D_infinity = the divisor above t = infinity, ~ kappa_F).
\\
\\ Coefficients: any exact field (Q, number field as POLMODs in a variable of lower priority than t, F_p as
\\ INTMODs, F_q as FFELTs). The caller passes sq(d): a square root of d in the base field, or [] if none.
\\ Variables used: t (Prym curve), x, y, z (forms). Declare them before the number field variable.

[t, x, y, z];
apm_qmat(Q) = matrix(3, 3, i, j, simplify(deriv(deriv(Q, [x, y, z][i]), [x, y, z][j]) / 2));
\\ S = [M1, M2, M3, QD1, QD2, QD3, delta, f]
apm_init(Q1, Q2, Q3, delta) = {
  my(M = [apm_qmat(Q1), apm_qmat(Q2), apm_qmat(Q3)], E = [[1, 0; 0, 0], [0, 1/2; 1/2, 0], [0, 0; 0, 1]], QD, f);
  QD = vector(3, i, matconcat([M[i], matrix(3, 2); matrix(2, 3), -delta * E[i]]));
  f = -delta * matdet(M[1] + 2*t*M[2] + t^2*M[3]);
  [M[1], M[2], M[3], QD[1], QD[2], QD[3], delta, f];
}
\\ Hodge star on antisymmetric 4x4 matrices: (star A)_{ij} = sum_{k<l} eps_{ijkl} A_{kl}
apm_star(A) = {
  my(B = matrix(4, 4));
  B[1,2] = A[3,4]; B[1,3] = A[4,2]; B[1,4] = A[2,3]; B[2,3] = A[1,4]; B[2,4] = A[3,1]; B[3,4] = A[1,2];
  for (i = 1, 4, for (j = 1, i - 1, B[i,j] = -B[j,i]));
  B;
}
\\ point of D on the quadrics?
apm_ondp(S, P) = { my(v = P~); for (i = 4, 6, if (P * S[i] * v != 0, return(0))); 1; }
\\ second point of the tangent line of D at P (P a row vector of length 5)
apm_tangent(S, P) = {
  my(Jm = matrix(3, 5, i, j, (S[3 + i] * P~)[j]), K = matker(Jm), T);
  if (#K != 2, error("apm_tangent: tangent space of dimension ", #K - 1, " (P singular or not on D?)"));
  T = K[, 1]~; if (matrank(Mat([P~, T~])) < 2, T = K[, 2]~);
  if (matrank(Mat([P~, T~])) < 2, error("apm_tangent: degenerate kernel"));
  T;
}
\\ Y-coordinate for the root t0 (in the base field or in an extension given by POLMODs in t)
apm_ruling(S, P, T, t0) = {
  my(G, Mt, a, b, A, GA, SA, Y = 0, i0 = 0, j0 = 0);
  Mt = S[1] + 2*t0*S[2] + t0^2*S[3];
  G = matconcat([Mt, matrix(3, 1); matrix(1, 3), Mat(-S[7])]);
  a = [P[1], P[2], P[3], P[4] + t0*P[5]]; b = [T[1], T[2], T[3], T[4] + t0*T[5]];
  A = a~ * b - b~ * a;
  GA = G * A * G; SA = apm_star(A);
  for (i = 1, 4, for (j = i + 1, 4, if (i0 == 0 && SA[i,j] != 0, i0 = i; j0 = j)));
  if (i0 == 0, error("apm_ruling: the projected plane is degenerate (vertex on the tangent line)"));
  Y = GA[i0, j0] / SA[i0, j0];
  if (GA != Y * SA, error("apm_ruling: G A G is not proportional to star(A) (plane not isotropic?)"));
  if (Y^2 != matdet(G), error("apm_ruling: Y^2 != det G"));
  Y;
}
\\ phi(P) as a Mumford pair [U, V]; sq(d) returns a square root of d in the base field or []
apm_phi(S, P, sq) = {
  my(T = apm_tangent(S, P), a, U, Dq, s, x1, x2, Y1, Y2, V, f = S[8]);
  if (!apm_ondp(S, P), error("apm_phi: P is not on D"));
  a = vector(3, i, T * S[3 + i] * T~);
  if (a[3] == 0, error("apm_phi: a point of phi(P) lies above t = infinity (change coordinates)"));
  U = t^2 + 2*a[2]/a[3]*t + a[1]/a[3];
  Dq = a[2]^2 - a[1]*a[3];
  if (Dq == 0,
    x1 = -a[2]/a[3]; Y1 = apm_ruling(S, P, T, x1);
    if (Y1 == 0, error("apm_phi: double Weierstrass point"));
    V = Y1 + subst(deriv(f, t), t, x1) / (2*Y1) * (t - x1),
  \\ else
    s = sq(Dq);
    if (type(s) != "t_VEC",
      x1 = (-a[2] + s)/a[3]; x2 = (-a[2] - s)/a[3];
      Y1 = apm_ruling(S, P, T, x1); Y2 = apm_ruling(S, P, T, x2);
      V = (Y1*(t - x2) - Y2*(t - x1)) / (x1 - x2),
    \\ else: the two points are conjugate over the quadratic extension base[t]/U
      Y1 = apm_ruling(S, P, T, Mod(t, U));
      V = lift(Y1)));
  if (poldegree(V, t) > 1, error("apm_phi: deg V > 1"));
  if ((V^2 - f) % U != 0, error("apm_phi: U does not divide V^2 - f"));
  [U, V];
}
\\ the involution iota of D over C
apm_iota(P) = [P[1], P[2], P[3], -P[4], -P[5]];
