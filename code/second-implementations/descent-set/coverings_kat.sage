# Step 7: known-answer tests of the coverings of C(Q_2) and C(Q_3) in all three charts.
# Points of C(Q_p) are found by Hensel (Sage p-adic roots of F restricted to a line); each must lie in exactly
# one leaf of step 5, and its class (from Q1 at the point, Q3 when Q1 is too small) must be the class recorded
# for that leaf, at every prime above p where step 5 checks constancy, and (p = 3) at the primes outside S.
load('descent_set_lib.sage')
src = open('local_conditions_2_3.sage').read().split('# ---------------- p = 2 ----------------')[0]
src = src.replace("load('descent_set_lib.sage')", "")
exec(preparse(src))

def in_leaf(t, t0, m, free):
    return all((t[i] - t0[i]) % p_^m == 0 for i in free) and all(t[i] == t0[i] for i in range(3) if i not in free)

def chart_free(t0, p):
    if t0[2] == 1:
        return (0, 1)
    if t0[1] == 1:
        return (0, 2)
    return (1, 2)

def roots_line(p, N, fam):
    """fam(T) returns a triple of polynomials in T; roots T in Z_p of F(triple) = 0."""
    Zpp = Zp(p, N + 10)
    Rp.<T> = Zpp[]
    tr = fam(T)
    f = (tr[0]^4 + 3*tr[0]^3*tr[1] - 3*tr[0]^2*tr[1]*tr[2] - 3*tr[0]^2*tr[2]^2 + 6*tr[0]*tr[1]^3
         - 6*tr[0]*tr[1]^2*tr[2] + 3*tr[0]*tr[1]*tr[2]^2 - 2*tr[0]*tr[2]^3 + 4*tr[1]^4 + 2*tr[1]^3*tr[2]
         - 5*tr[1]*tr[2]^3)
    if f == 0:
        return []
    out = []
    for r, _ in f.roots():
        if r.precision_absolute() < N:
            continue
        rr = ZZ(r.lift()) % p^N
        out.append(rr)
    return out

def points_all_charts(p, N, rng):
    pts = []
    for c in rng:
        for r in roots_line(p, N, lambda T: (c, T, 1)):          # chart A
            pts.append((c, r, 1))
        for r in roots_line(p, N, lambda T: (T, 1, p * c)):      # chart B, z = p c
            pts.append((r, 1, p * c))
        for r in roots_line(p, N, lambda T: (1, p * c, p * T)):  # chart C, y = p c, z = p T
            pts.append((1, p * c, p * r))
    return pts

def check(p, leaves, primes, extra=None, N=50):
    global p_
    p_ = p
    pts = points_all_charts(p, N, range(-30, 31))
    counts = {"A": 0, "B": 0, "C": 0}
    bad = 0
    for t in pts:
        ch = "A" if t[2] == 1 else ("B" if t[1] == 1 else "C")
        counts[ch] += 1
        inl = [(t0, m, c) for t0, m, c in leaves if in_leaf(t, t0, m, chart_free(t0, p))]
        if len(inl) != 1:
            bad += 1
            continue
        t0, m, c = inl[0]
        for P in primes:
            qa = Q1(*[K(v) for v in t])
            if qa == 0 or qa.valuation(P) > 30:
                qa = Q3(*[K(v) for v in t])
            same = local_square_dyadic(qa * c[P][1], P, pi2[P], e2[P]) if p == 2 else local_square_q3(qa * c[P][1], P)
            if not same:
                bad += 1
                break
        if extra is not None and extra[0](t) != extra[1](t0):
            bad += 1
    return len(pts), counts, bad

leaves2 = cover(2, P2, {P: e2[P] for P in P2})[0]
print("KAT p = 2:", check(2, leaves2, P2))
leaves3 = cover(3, P3S, {P: 0 for P in P3S})[0]
# at the primes above 3 outside S: the class of the point computed at full precision equals the good prime rule
def cls3N_exact(t):
    out = []
    for Pg, Fq, w in fl3N:
        a = Q1(*[K(v) for v in t])
        if a == 0 or a.valuation(Pg) > 0:
            a = Q3(*[K(v) for v in t])
        assert a.valuation(Pg) == 0
        out.append(0 if red(a, Fq, w).is_square() else 1)
    return tuple(out)
print("KAT p = 3:", check(3, leaves3, P3S, extra=(cls3N_exact, cls3N_point)))

# KAT 3: every local decision of step 5 (8 survivors x leaves x primes at 2, and at the S prime above 3) agrees
# with PARI's nfislocalpower (a test of the square tests only; step 5 does not use nfislocalpower)
gens, chars = load('sunits_basis.sobj')
surv = load('sieve_survivors.sobj')
nfp = K.pari_nf()
ntest = 0; nmis = 0
for c in surv:
    u = elt(c)
    for t0, m, ch in leaves2:
        for P in P2:
            a = u * ch[P][1]
            ntest += 1
            if local_square_dyadic(a, P, pi2[P], e2[P]) != bool(nfp.nfislocalpower(P.pari_prime(), a.__pari__(), 2)):
                nmis += 1
    for t0, m, ch in leaves3:
        P = P3S[0]
        a = u * ch[P][1]
        ntest += 1
        if local_square_q3(a, P) != bool(nfp.nfislocalpower(P.pari_prime(), a.__pari__(), 2)):
            nmis += 1
print("KAT 3 (step 5 local decisions vs nfislocalpower):", ntest, "decisions,", nmis, "mismatches")
