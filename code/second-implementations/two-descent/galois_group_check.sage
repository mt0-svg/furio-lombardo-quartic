# galois_group_check.sage: Galois group of A3 with Sage's bundled PARI (which has galdata), plus Frobenius cycle types.
# Run: sage galois_group_check.sage
from collections import Counter
R.<t> = QQ[]
f = t^8 + 2*t^7 + 7*t^4 - 14*t^2 - 8*t + 5
print("polgalois:", pari(f).polgalois())
K.<a> = NumberField(f)
print("Sage galois_group:", K.galois_group(), "order", K.galois_group().order())
types = Counter()
for p in primes(3, 20000):
    if p in (2, 7):
        continue
    types[tuple(sorted(g.degree() for g, e in f.change_ring(GF(p)).factor() for _ in range(e)))] += 1
print("Frobenius cycle types for 3 <= p < 20000, p != 7:")
for k in sorted(types):
    print("  ", k, types[k])
