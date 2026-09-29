# Step 3: a basis of K21(S,2) = O_S^x / O_S^x2 (h(K21) = 1, claim h-K21).
# Dirichlet: dim O_S^x/O_S^x2 = r1 + r2 - 1 + |S| + 1 (torsion {+-1}) = 3 + 9 - 1 + 6 + 1 = 18, unconditionally.
# The generators are found by Sage's S_unit_group with proof=False (GRH), then checked unconditionally:
# (a) each one is an S-unit (exact factorization of its principal ideal), (b) the 18 are independent in K^x/K^x2
# (quadratic residue characters at degree one primes outside S give F_2-rank 18). (a) and (b) with the dimension
# count prove that they form a basis of O_S^x/O_S^x2, hence of K21(S,2).
load('descent_set_lib.sage')
D, Sgens = load('support_set.sobj')
S = [K.ideal(list(g)) for g in Sgens]
assert all(P.is_prime() for P in S) and len(S) == 6
r1, r2 = K.signature()
dimK = r1 + r2 - 1 + len(S) + 1
print("expected dim K(S,2) =", dimK)
U = K.S_unit_group(S=S, proof=False)
gens = [K(g) for g in U.gens_values()]
print("number of generators from S_unit_group:", len(gens), " torsion order:", U.torsion_generator().order())
assert len(gens) == dimK
# (a) exact S-unit check
for i, u in enumerate(gens):
    fac = K.ideal(u).factor()
    assert all(P in S for P, _ in fac), ("not an S-unit", i)
print("(a) all", len(gens), "generators are S-units: exact factorization of (u) supported on S")
print("max height (digits) of generator coefficients:", max(max(len(str(c.numerator())) + len(str(c.denominator())) for c in list(u)) for u in gens))
# (b) characters at degree one primes (p, b - r) with p outside 2*3*7*439*index*denominators
bad_primes = set([2, 3, 7, 439]) | set(prime_divisors(lcm([c.denominator() for u in gens for c in list(u)])))
rows = []
chars = []
p = 23
Fp_rank = 0
while Fp_rank < dimK:
    p = next_prime(p)
    if p in bad_primes:
        continue
    Fp = GF(p)
    for r, _ in K21pol.change_ring(Fp).roots():
        vec = []
        for u in gens:
            ur = sum(Fp(c) * r^i for i, c in enumerate(list(u)))
            assert ur != 0
            vec.append(0 if ur.is_square() else 1)
        chars.append((p, ZZ(r)))
        rows.append(vec)
    Fp_rank = matrix(GF(2), rows).rank()
Mch = matrix(GF(2), rows).transpose()   # 18 x (number of characters)
print("(b) characters used:", len(chars), " up to p =", p, " F_2-rank =", Mch.rank())
assert Mch.rank() == dimK
save((gens, chars), 'sunits_basis.sobj')
print("saved sunits_basis.sobj")
