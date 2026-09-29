\\ jacobian_order_f3_f11.gp : #J(F_3) and #J(F_11) from brute force point counts over F_{p^k}, k <= 3,
\\ for the torsion argument J(Q)_tors = 0 (both primes are of good reduction: the only bad primes of
\\ the model are 2 and 7, refutMW_1_qside.out).
Fh(a,b,c) = a^4+3*a^3*b-3*a^2*b*c-3*a^2*c^2+6*a*b^3-6*a*b^2*c+3*a*b*c^2-2*a*c^3+4*b^4+2*b^3*c-5*b*c^3;
nroots(fa, q) = poldegree(gcd(fa, lift(Mod('Y, fa)^q) - 'Y));
cnt(p, k) = {
  my(g = ffgen(ffinit(p, k), 'w), q = p^k, N = 0, a, one = g^0);
  forvec(c = vector(k, i, [0, p - 1]),
    a = sum(i = 1, k, c[i] * g^(i - 1)) + 0*g;
    N += nroots(Fh(a, 'Y * one, one), q));
  N += nroots(Fh('Y * one, one, 0*one), q);
  if (Fh(one, 0*one, 0*one) == 0, N++);
  N;
}
\\ control: brute force over P^2(F_p) for k = 1
cnt1(p) = my(N = 0); for(a=0,p-1, for(b=0,p-1, if(Mod(Fh(a,b,1),p)==0, N++))); for(a=0,p-1, if(Mod(Fh(a,1,0),p)==0, N++)); if(Mod(Fh(1,0,0),p)==0, N++); N;
L1(p) = {
  my(Ns = vector(3, k, cnt(p, k)), s = vector(3, k, p^k + 1 - Ns[k]), e1, e2, e3, c);
  if (cnt1(p) != Ns[1], error("count mismatch"));
  e1 = s[1]; e2 = (e1*s[1] - s[2])/2; e3 = (e2*s[1] - e1*s[2] + s[3])/3;
  c = [-e1, e2, -e3];
  print("p = ", p, ": N1..N3 = ", Ns, ", L(T) = 1 + (", c[1], ")T + (", c[2], ")T^2 + (", c[3], ")T^3 + ...");
  1 + c[1] + c[2] + c[3] + p*c[2] + p^2*c[1] + p^3;
}
{
  my(a = L1(3), b = L1(11));
  print("#J(F_3) = ", a, " = ", factor(a));
  print("#J(F_11) = ", b, " = ", factor(b));
  print("gcd = ", gcd(a, b));
}
