# Step 2: the determinant D of (Q1, Q2, Q3, dJ/dx, dJ/dy, dJ/dz), J = det(dQi/dxj), its support S,
# and integrality of Q1, Q2, Q3 outside S.
# Lemma: if Q1, Q2, Q3 have pr-integral coefficients and a
# common zero over the algebraic closure of O/pr, then D = 0 mod pr (any characteristic).
load('descent_set_lib.sage')
Jm = matrix(R, 3, 3, [[Q.derivative(v) for v in (x, y, z)] for Q in (Q1, Q2, Q3)])
J = Jm.det()
six = [Q1, Q2, Q3, J.derivative(x), J.derivative(y), J.derivative(z)]
assert all(q.is_homogeneous() and q.degree() == 2 for q in six)
M = matrix(K, [coeffs2(q) for q in six])
D = M.det()
print("D != 0:", D != 0)
ND = D.norm()
print("N(D) =", factor(ND))
facD = K.ideal(D).factor()
S = [P for P, e in facD]
print("support of (D): (p, e, f, v_P(D)) =", [(P.smallest_integer(), P.ramification_index(), P.residue_class_degree(), e) for P, e in facD])
print("|S| =", len(S))
# every prime of S above 2, 3, 7, 439; list which primes above 3 and 439 are in S
for p in [2, 3, 7, 439]:
    allp = [P for P, _ in K.ideal(p).factor()]
    print(p, ": primes above p:", len(allp), " in S:", sum(1 for P in allp if P in S),
          " (e, f) of those in S:", [(P.ramification_index(), P.residue_class_degree()) for P in allp if P in S])
# integrality: every coefficient of Q1, Q2, Q3 has nonnegative valuation outside S
bad = []
for i, Q in enumerate([Q1, Q2, Q3]):
    for c in coeffs2(Q):
        if c == 0:
            continue
        for P, e in K.ideal(c).factor():
            if e < 0 and P not in S:
                bad.append((i + 1, P))
print("coefficients of Q1, Q2, Q3 with a pole outside S:", bad)
# minimal valuation of the coefficients of Q1, Q3 at each prime of S (used by the constancy bounds of step 5)
for P in S:
    for nm, Q in [("Q1", Q1), ("Q3", Q3)]:
        cmin = min(c.valuation(P) for c in coeffs2(Q) if c != 0)
        print("  prime above", P.smallest_integer(), "(e =", P.ramification_index(), ") min v(coeff", nm, ") =", cmin)
save((D, [P.gens_two() for P in S]), 'support_set.sobj')
