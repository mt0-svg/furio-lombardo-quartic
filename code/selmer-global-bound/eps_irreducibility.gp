\\ eps_irreducibility.gp: eps, its inverse, and an odd prime p with a root r of f mod p at which eps is not a square
\\ (so X^2 - eps is irreducible over K21). Run from code/descent: gp -q ../selmer-global-bound/eps_irreducibility.gp < /dev/null
default(parisizemax, 2*10^9); default(nbthreads, 1);
read("descent_search_lib.gp");
chk(cc, msg) = if (!cc, error("FAILED: ", msg), print("ok: ", msg));
DB = -8570350497446051858808595293666336011461519865865907911223905181971605934233878528;
chk(DB % Dz == 0, "Dz divides DB");
eps = G[1]; foreach([2, 5, 7, 10, 11], i, eps = mulz(eps, G[i]));
epsi = inv(eps);
print("epsL = ", lst(eps~)); print("epsInvL = ", lst(epsi~));
\\ Dz * eps = combo(eps, zkNum)(theta) as a polynomial numerator
cmb(a) = sum(i = 1, 21, a[i] * Pol(Vecrev(zkNum[i]), X));
{forprime(p = 3, 1000, if (DB % p == 0, next);
  my(rs = polrootsmod(subst(K21, b, X), p));
  for (i = 1, #rs, my(r = lift(rs[i]), v = Mod(subst(cmb(eps), X, r), p) / Dz);
    if (kronecker(lift(v), p) == -1, print("p = ", p, ", r = ", r, ", eps(r) = ", lift(v), " is a non-residue"); break(2))));}
