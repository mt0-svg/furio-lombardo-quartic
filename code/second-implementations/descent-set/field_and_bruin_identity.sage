# Step 1: the field K21, the Bruin identity, the known points, primes above the small rational primes.
load('descent_set_lib.sage')
print("degree", K.degree(), "signature", K.signature())
print("K21 irreducible over Q:", K21pol.is_irreducible())
# Bruin identity Q1 Q3 - Q2^2 = cB F, exact
print("Q1*Q3 - Q2^2 == cB*F:", Q1*Q3 - Q2^2 == cB*F)
print("known points on C:", [F(*P) == 0 for P in PTS])
dK = K.discriminant()
print("disc(K) =", factor(dK))
dpol = K21pol.discriminant()
print("disc(pol) =", factor(dpol))
ind2 = ZZ(dpol / dK)
print("index^2 = disc(pol)/disc(K) =", factor(ind2), " index =", factor(ind2.sqrt()))
for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 439]:
    fac = K.ideal(p).factor()
    print(p, ":", [(P.ramification_index(), P.residue_class_degree(), mult) for P, mult in fac])
# denominators of the coefficients of Q1, Q2, Q3 (power basis)
dens = lcm([c.denominator() for Q in [Q1, Q2, Q3] for c in coeffs2(Q)] + [cB.denominator()])
print("lcm of power basis denominators of Q1, Q2, Q3, cB:", factor(dens))
