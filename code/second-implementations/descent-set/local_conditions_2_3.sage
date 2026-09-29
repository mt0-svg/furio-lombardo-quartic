# Step 5: local conditions at 2 and 3 on the 8 survivors of the good prime sieve.
#
# Covering. Every point of P^2(Q_p) has exactly one representative t in one chart:
#   A = (x, y, 1), x, y in Z_p;  B = (x, 1, z), x in Z_p, z in pZ_p;  C = (1, y, z), y, z in pZ_p.
# A box is {t0 + p^m h : h in Z_p on the free coordinates, 0 on the coordinate equal to 1}. F has integer
# coefficients, so F(t) = F(t0) mod p^m on the box; if v_p(F(t0)) < m the box has no point of C (discarded).
# Constancy at a prime pr above p: for Q in (Q1, Q3) (integral coefficients, step 2), Q(t) - Q(t0) is a sum of
# coefficients times differences of monomials in Z_p, so v_pr(Q(t) - Q(t0)) >= m e_pr. If
# m e_pr >= v_pr(Q(t0)) + 2 v_pr(2) + 1, then Q(t)/Q(t0) is in 1 + pr^(2 v_pr(2) + 1), a subset of the squares
# of K_pr, so Q(t) != 0 and the class of Q(t) in K_pr^x/K_pr^x2 is that of Q(t0) on the whole box. When both
# Q1(t), Q3(t) are nonzero their classes agree (Q1 Q3 = Q2^2 on C, Q2(t) != 0), so the class of delta at pr
# is that of the chosen Q(t0), whatever choice is made at the other primes.
# At the primes above 3 outside S (unramified, residue degrees 8, 8, 4) the class of delta(t) depends only on
# t mod 3 (the good prime rule of step 4), so it is constant on every box.
# The kept leaves over-approximate the image of C(Q_p): sound for exclusion.
#
# Square tests in K_pr, pr above 2 (all three have f = 1, residue field F_2, e = v_pr(2)):
#   odd valuation: not a square. Unit w, k = v(w - 1):
#   k > 2e: square (binomial series);  k < 2e odd: not a square;  k = 2e: not a square (residue field F_2);
#   k < 2e even: replace w by w / (1 + pi^(k/2))^2, which raises k strictly.
# At the degree one prime of S above 3 (K_pr = Q_3, uniformizer 3): unit w is a square iff v(w - 1) >= 1.
load('descent_set_lib.sage')
import sys
D, Sgens = load('support_set.sobj')
S = [K.ideal(list(g)) for g in Sgens]
gens, chars = load('sunits_basis.sobj')
surv = load('sieve_survivors.sobj')
n = len(gens)

def elt(c):
    return prod(g^ZZ(ci) for g, ci in zip(gens, c))

def uniformizer(P):
    for cand in [b - c for c in range(-8, 9)] + [b^2 - c for c in range(-8, 9)] + list(P.gens()):
        if cand != 0 and cand.valuation(P) == 1:
            return cand
    raise ValueError("no uniformizer found")

def local_square_dyadic(a, P, pi, e, cert=None):
    """Is a a square in K_P, P above 2 with residue field F_2 and ramification e? Exact, by valuations only."""
    assert a != 0
    v = a.valuation(P)
    if v % 2 == 1:
        if cert is not None: cert.append(('odd valuation', v))
        return False
    w = a / pi^v
    steps = 0
    while True:
        if w == 1:
            if cert is not None: cert.append(('exact square', steps))
            return True
        k = (w - 1).valuation(P)
        assert k >= 1
        if k > 2*e:
            if cert is not None: cert.append(('1 + P^(2e+1)', k, steps))
            return True
        if k == 2*e:
            if cert is not None: cert.append(('Artin-Schreier level 2e', k, steps))
            return False
        if k % 2 == 1:
            if cert is not None: cert.append(('odd level below 2e', k, steps))
            return False
        w = w / (1 + pi^(k//2))^2
        steps += 1

def local_square_q3(a, P):
    """P of degree one above 3 with e = 1."""
    v = a.valuation(P)
    if v % 2 == 1:
        return False
    w = a / K(3)^v
    return (w - 1).valuation(P) >= 1

# the primes above 2 and 3
P2 = [P for P, _ in K.ideal(2).factor()]
e2 = {P: P.ramification_index() for P in P2}
pi2 = {P: uniformizer(P) for P in P2}
P3all = [P for P, _ in K.ideal(3).factor()]
P3S = [P for P in P3all if P in S]
P3N = [P for P in P3all if P not in S]
assert len(P3S) == 1 and P3S[0].residue_class_degree() == 1
print("primes above 2: e =", [e2[P] for P in P2], " uniformizers checked")
print("primes above 3: S prime of degree", P3S[0].residue_class_degree(), "; outside S, degrees", [P.residue_class_degree() for P in P3N])

# good prime rule at the primes above 3 outside S (3 does not divide the index; Dedekind)
denp = set(prime_divisors(lcm([c.denominator() for u in gens for c in list(u)]
                              + [c.denominator() for Q in (Q1, Q2, Q3) for c in Q.coefficients()])))
assert 3 not in denp
fl3 = []
for g, mult in K21pol.change_ring(GF(3)).factor():
    Fq = GF(3^g.degree(), 'w', modulus=g) if g.degree() > 1 else GF(3)
    w = Fq.gen() if g.degree() > 1 else -g[0]
    Pg = K.ideal(3, g.change_ring(ZZ)(b))
    fl3.append((Pg, Fq, w))
def red(c, Fq, w):
    return sum(Fq(ci) * w^i for i, ci in enumerate(list(c)))
fl3N = [(Pg, Fq, w) for Pg, Fq, w in fl3 if Pg not in S]
assert len(fl3N) == 3 and all(Pg in P3N for Pg, _, _ in fl3N)
def chi3N(u):
    return tuple(0 if red(u, Fq, w).is_square() else 1 for Pg, Fq, w in fl3N)
def cls3N_point(t):
    out = []
    for Pg, Fq, w in fl3N:
        vals = []
        for Q in (Q1, Q2, Q3):
            vals.append(sum(red(c, Fq, w) * prod(Fq(ti)^mi for ti, mi in zip(t, mo.exponents()[0])) for c, mo in zip(Q.coefficients(), Q.monomials())))
        a = vals[0]
        if a == 0:
            assert vals[1] == 0 and vals[2] != 0
            a = vals[2]
        out.append(0 if a.is_square() else 1)
    return tuple(out)

def Fint(t):
    X, Y, Z = t
    return (X^4 + 3*X^3*Y - 3*X^2*Y*Z - 3*X^2*Z^2 + 6*X*Y^3 - 6*X*Y^2*Z + 3*X*Y*Z^2 - 2*X*Z^3
            + 4*Y^4 + 2*Y^3*Z - 5*Y*Z^3)

def initial_boxes(p):
    boxes = []
    for i in range(p):
        for j in range(p):
            boxes.append(((i, j, 1), (0, 1), 1))
    for i in range(p):
        boxes.append(((i, 1, 0), (0, 2), 1))
    boxes.append(((1, 0, 0), (1, 2), 1))
    return boxes

def children(box, p):
    t0, free, m = box
    out = []
    for i in range(p):
        for j in range(p):
            t = list(t0)
            t[free[0]] += i * p^m
            t[free[1]] += j * p^m
            out.append((tuple(t), free, m + 1))
    return out

def cover(p, primes, twoval, mmax=12):
    """Leaves: (t0, m, {P: (name, value)}). primes: the primes above p where constancy must be checked."""
    todo = initial_boxes(p)
    leaves = []
    ndiscard = 0
    while todo:
        box = todo.pop()
        t0, free, m = box
        if ZZ(Fint(t0)).valuation(p) < m:
            ndiscard += 1
            continue
        choice = {}
        ok = True
        for P in primes:
            eP = P.ramification_index()
            found = None
            for nm, Q in (("Q1", Q1), ("Q3", Q3)):
                a = Q(*[K(t) for t in t0])
                if a != 0 and m * eP >= a.valuation(P) + 2 * twoval[P] + 1:
                    found = (nm, a)
                    break
            if found is None:
                ok = False
                break
            choice[P] = found
        if ok:
            leaves.append((t0, m, choice))
        else:
            assert m < mmax, ("no termination", box)
            todo.extend(children(box, p))
    return leaves, ndiscard

# ---------------- p = 2 ----------------
leaves2, nd2 = cover(2, P2, {P: e2[P] for P in P2})
print("p = 2: leaves =", len(leaves2), " max m =", max(m for _, m, _ in leaves2), " discarded boxes =", nd2)
sys.stdout.flush()
kept2 = []
detail2 = {}
for idx, c in enumerate(surv):
    u = elt(c)
    hits = []
    for t0, m, choice in leaves2:
        if all(local_square_dyadic(u * choice[P][1], P, pi2[P], e2[P]) for P in P2):
            hits.append((t0, m))
    detail2[idx] = hits
    if hits:
        kept2.append(idx)
    print("  survivor", idx, ": leaves at 2 with matching class:", len(hits), hits[:4]); sys.stdout.flush()
print("p = 2 keeps survivors", kept2)

# ---------------- p = 3 ----------------
tw3 = {P: 0 for P in P3S}
leaves3, nd3 = cover(3, P3S, tw3)
print("p = 3: leaves =", len(leaves3), " max m =", max(m for _, m, _ in leaves3), " discarded boxes =", nd3)
kept3S = []
kept3 = []
for idx, c in enumerate(surv):
    u = elt(c)
    cu = chi3N(u)
    hitsS = []
    hits = []
    for t0, m, choice in leaves3:
        P = P3S[0]
        if local_square_q3(u * choice[P][1], P):
            hitsS.append((t0, m))
            if cls3N_point(t0) == cu:
                hits.append((t0, m))
    if hitsS: kept3S.append(idx)
    if hits: kept3.append(idx)
    print("  survivor", idx, ": leaves at 3 matching at the S prime:", len(hitsS), "; at all primes above 3:", len(hits), hits[:4]); sys.stdout.flush()
print("p = 3 (S prime only) keeps", kept3S, "; p = 3 (all primes above 3) keeps", kept3)
final = sorted(set(kept2) & set(kept3))
finalS = sorted(set(kept2) & set(kept3S))
print("final survivors (2 and all primes above 3):", final, "; (2 and the S prime above 3):", finalS)
save((surv, final, [(t0, m) for t0, m, _ in leaves2], [(t0, m) for t0, m, _ in leaves3]), 'local_conditions_2_3.sobj')
