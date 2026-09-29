# Step 4: the good prime sieve.
# For P in C(Q) (primitive integer coordinates) and a prime pr of K21 outside S above p, with Pbar = P mod p in
# C(F_p): if Q1(Pbar) != 0 mod pr the class of delta(P) at pr is the quadratic character of Q1(Pbar); otherwise
# Q2(Pbar) = 0 mod pr (from Q1 Q3 - Q2^2 = cB F, cB integral), Q3(Pbar) != 0 mod pr (no common zero, step 2), and
# the class is the character of Q3(Pbar). So the vector of characters of delta(P) at the primes above p lies in
# the image I_p of C(F_p): a sound over-approximation for exclusion.
# Residue fields: p does not divide the index of Z[b] (step 1), so the primes above p are (p, g(b)) for the
# irreducible factors g of K21 mod p (Dedekind) and the residue map is b -> class of X in F_p[X]/(g).
load('descent_set_lib.sage')
import sys
gens, chars = load('sunits_basis.sobj')
n = len(gens)
index_primes = [2, 45613, 462191, 249279053]
denp = set(prime_divisors(lcm([c.denominator() for u in gens for c in list(u)]
                              + [c.denominator() for Q in (Q1, Q2, Q3, R(cB)) for c in Q.coefficients()])))

def residue_fields(p):
    fl = []
    for g, e in K21pol.change_ring(GF(p)).factor():
        assert e == 1
        Fq = GF(p^g.degree(), 'w', modulus=g) if g.degree() > 1 else GF(p)
        w = Fq.gen() if g.degree() > 1 else -g[0]
        fl.append((g, Fq, w))
    return fl

def red(c, Fq, w):
    """Residue of an element of K21 with p-integral power basis coefficients."""
    return sum(Fq(ci) * w^i for i, ci in enumerate(list(c)))

def red_form(Q, Fq, w):
    Rq = PolynomialRing(Fq, 'X,Y,Z')
    X, Y, Z = Rq.gens()
    return sum(red(c, Fq, w) * X^m.degree(x) * Y^m.degree(y) * Z^m.degree(z) for c, m in zip(Q.coefficients(), Q.monomials()))

def proj_points(p):
    Fp = GF(p)
    pts = [(Fp(a), Fp(c), Fp(1)) for a in Fp for c in Fp]
    pts += [(Fp(a), Fp(1), Fp(0)) for a in Fp] + [(Fp(1), Fp(0), Fp(0))]
    return pts

def local_data(p):
    assert p not in index_primes and p not in denp and p not in [3, 7, 439]
    fl = residue_fields(p)
    Xs = PolynomialRing(GF(p), 'X,Y,Z'); X, Y, Z = Xs.gens()
    Fmod = (X^4 + 3*X^3*Y - 3*X^2*Y*Z - 3*X^2*Z^2 + 6*X*Y^3 - 6*X*Y^2*Z + 3*X*Y*Z^2 - 2*X*Z^3
            + 4*Y^4 + 2*Y^3*Z - 5*Y*Z^3)
    pts = [P for P in proj_points(p) if Fmod(*P) == 0]
    image = set()
    chi = []   # chi[j][i] = character of gens[i] at the j-th prime above p
    for g, Fq, w in fl:
        chi.append([0 if red(u, Fq, w).is_square() else 1 for u in gens])
    forms = [(red_form(Q1, Fq, w), red_form(Q2, Fq, w), red_form(Q3, Fq, w)) for g, Fq, w in fl]
    for P in pts:
        vec = []
        for (g, Fq, w), (q1, q2, q3) in zip(fl, forms):
            Pq = [Fq(t) for t in P]
            a = q1(*Pq)
            if a == 0:
                assert q2(*Pq) == 0
                a = q3(*Pq)
                assert a != 0
            vec.append(0 if a.is_square() else 1)
        image.add(tuple(vec))
    return fl, pts, chi, image

primes = [5, 11, 13, 17, 19, 23]
extra = [p for p in prime_range(29, 200) if p not in index_primes and p not in denp and p not in [3, 7, 439]]
V = VectorSpace(GF(2), n)
surv = None
log = []
for p in primes + extra:
    fl, pts, chi, image = local_data(p)
    Mp = matrix(GF(2), chi).transpose()   # n x (#primes above p)
    if surv is None:
        cand = [c for c in V]
    else:
        cand = surv
    surv = [c for c in cand if tuple(ZZ(t) for t in (c * Mp)) in image]
    line = "p = %d: primes above p of degrees %s, #C(F_p) = %d, #image = %d, survivors = %d" % (
        p, [g.degree() for g, _, _ in fl], len(pts), len(image), len(surv))
    print(line); sys.stdout.flush()
    log.append((p, len(pts), len(image), len(surv)))
    if p == 23:
        surv23 = list(surv)
        save(surv23, 'sieve_survivors.sobj')
        # structure: surv23 = s0 + V3 ?
        s0 = surv23[0]
        diffs = [c - s0 for c in surv23]
        W = V.subspace(diffs)
        print("after p = 23: survivors form a coset s0 + W with dim W =", W.dimension(),
              "; coset closed:", set(tuple(s0 + w) for w in W) == set(tuple(c) for c in surv23))
print("survivors after all primes up to 199:", len(surv))
