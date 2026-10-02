# Step 6: identification of the two final classes with delta(P0) = delta(P2) and delta(P1) = delta(P3),
# the non-square certificates used at 2, and known-answer tests of the local square test and of the covering.
load('descent_set_lib.sage')
import sys
D, Sgens = load('support_set.sobj')
S = [K.ideal(list(g)) for g in Sgens]
gens, chars = load('sunits_basis.sobj')
surv, final, leaves2t, leaves3t = load('local_conditions_2_3.sobj')
# reuse the square tests and covering of step 5 without rerunning its main part
src = open('local_conditions_2_3.sage').read().split('# ---------------- p = 2 ----------------')[0]
src = src.replace("load('descent_set_lib.sage')", "")
exec(preparse(src), globals())  # one namespace, so that generator expressions in src see its names

print("final survivors (indices into the 8):", final)
reps = [delta_rep(P) for P in PTS]
print("which Q gives delta(P_i):", ["Q1" if Q1(*P) != 0 else "Q3" for P in PTS])
# delta(P_i) has even valuation outside S (a check of step 2 on the known points)
for i, a in enumerate(reps):
    odd = [(Pq.smallest_integer(), e) for Pq, e in K.ideal(a).factor() if Pq not in S and e % 2 == 1]
    assert not odd, (i, odd)
print("delta(P_i) has even valuation at every prime outside S, i = 0..3")
# exact global identification
table = {}
for j in final:
    u = elt(surv[j])
    table[j] = [bool((u * a).is_square()) for a in reps]
    print("survivor", j, ": u * delta(P_i) is a square in K21 for i = 0..3:", table[j])
# the classes of d0, d1 of bruin_form.gp
print("d0 * delta(P0), d1 * delta(P1) squares in K21:", (d0 * reps[0]).is_square(), (d1 * reps[1]).is_square())
# delta0 != delta1: a non-residue certificate at a degree one prime outside S
a01 = reps[0] * reps[1]
cert = None
for p in prime_range(5, 400):
    if p in [7, 439] or p in denp:
        continue
    for r, _ in K21pol.change_ring(GF(p)).roots():
        val = sum(GF(p)(c) * r^i for i, c in enumerate(list(a01)))
        if val != 0 and not val.is_square():
            cert = (p, r)
            break
    if cert:
        break
print("delta(P0) delta(P1) is a unit non-residue at the degree one prime (p, b - r) =", cert)
assert cert is not None

# certificates of the exclusions at 2: for each excluded survivor and each leaf, the first prime above 2 whose
# local test fails and the reason
print("exclusion certificates at 2 (survivor, count of leaves, reasons):")
reasons = {}
for idx, c in enumerate(surv):
    u = elt(c)
    rs = []
    for t0, m, choice in cover(2, P2, {P: e2[P] for P in P2})[0]:
        for P in P2:
            ct = []
            if not local_square_dyadic(u * choice[P][1], P, pi2[P], e2[P], ct):
                rs.append((e2[P], ct[0][0]))
                break
        else:
            rs.append(None)
    summary = {}
    for r in rs:
        summary[r] = summary.get(r, 0) + 1
    print("  survivor", idx, summary)
    for r in rs:
        if r is not None:
            reasons[r[1]] = reasons.get(r[1], 0) + 1
print("reasons used at 2 over all (survivor, leaf) exclusions:", reasons)
sys.stdout.flush()

# KAT 1: the dyadic square test against PARI's nfislocalpower on random elements (test only, not in the chain)
nfp = K.pari_nf()
set_random_seed(20260927)
nmis = 0; ntest = 0
for P in P2:
    prp = P.pari_prime()
    for _ in range(150):
        a = K([ZZ.random_element(-20, 21) for _ in range(21)])
        if a == 0:
            continue
        for aa in (a, a^2, a * (1 + 2^6 * b)):
            ours = local_square_dyadic(aa, P, pi2[P], e2[P])
            theirs = bool(nfp.nfislocalpower(prp, aa.__pari__(), 2))
            ntest += 1
            if ours != theirs:
                nmis += 1
print("KAT 1 (dyadic square test vs nfislocalpower):", ntest, "tests,", nmis, "mismatches")
# KAT 2: points of C(Q_2) found by Hensel lie in exactly one leaf, and the class of the point (from Q1 at the point,
# Q3 if Q1 is too small) is the class recorded for the leaf at each prime above 2
leaves2full = cover(2, P2, {P: e2[P] for P in P2})[0]
Zp2 = Zp(2, 60)
Rp.<Yv> = Zp2[]
npts = 0; bad = 0
for x0 in range(-40, 41):
    f = (x0^4 + 3*x0^3*Yv - 3*x0^2*Yv - 3*x0^2 + 6*x0*Yv^3 - 6*x0*Yv^2 + 3*x0*Yv - 2*x0 + 4*Yv^4 + 2*Yv^3 - 5*Yv)
    for yr, _ in f.roots():
        assert yr.precision_absolute() >= 50
        Y0 = ZZ(yr.lift()) % 2^50
        t = (x0, Y0, 1)
        inl = [(t0, m, ch) for t0, m, ch in leaves2full if t0[2] == 1 and all((t[i] - t0[i]) % 2^m == 0 for i in (0, 1))]
        npts += 1
        if len(inl) != 1:
            bad += 1
            continue
        t0, m, ch = inl[0]
        for P in P2:
            qa = Q1(*[K(v) for v in t])
            if qa == 0 or qa.valuation(P) > 40:
                qa = Q3(*[K(v) for v in t])
            if not local_square_dyadic(qa * ch[P][1], P, pi2[P], e2[P]):
                bad += 1
                break
print("KAT 2: Q_2 points (x0 in [-40, 40], chart A):", npts, "; failures (not in exactly one leaf, or class mismatch):", bad)
