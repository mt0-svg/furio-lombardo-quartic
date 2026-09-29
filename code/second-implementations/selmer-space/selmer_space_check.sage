# selmer_space_check.sage: independent recomputation (Sage, GF(2)) of the Selmer space X of sigma_v_injective.gp from the
# generator matrix G and the local images (text export of selmer_space_export.gp): X = {c in F_2^82 : the local
# coordinates G_j c lie in the local image at every place j}. Checks dim X = 19, that G X is the space spanned by the
# cached columns GX used by p21_31, p21_35 and sigma_check.sage, and that its image at v modulo the local scalars has
# dimension 4 (sigma_v injective, given dim Sel = dim X - 15, the bound of prym_two_descent.gp).
# Run from code/second-implementations/selmer-space: sage selmer_space_check.sage > selmer_space_check.out
import re
F = GF(2)

def parse_mat(s, nrows=None):
    s = s.strip()
    body = s[1:-1].strip()
    if body in ('', ';'):
        return None
    return matrix(F, [[int(e) for e in r.split(',')] for r in body.split(';')])

def load(fn):
    d = {}
    for m in re.finditer(r'^(\w+) = (.*?);$', open(fn).read(), re.M):
        name, val = m.group(1), m.group(2)
        if val.startswith('['):
            if name.startswith('off'):
                d[name] = [int(e) for e in val[1:-1].split(',')]
            else:
                d[name] = parse_mat(val)
        elif val.startswith('"'):
            d[name] = val.strip('"')
        else:
            d[name] = int(val)
    return d

G = load('selmer_space_generators.txt')['G']
print('G: %d x %d, rank %d' % (G.nrows(), G.ncols(), G.rank()))
ok = True
def check(c, msg):
    global ok
    print(('PASS ' if c else 'FAIL ') + msg)
    ok = ok and c

V82 = VectorSpace(F, G.ncols())
for k in [0, 1]:
    d = load('selmer_space_local_twist%d.txt' % k)
    sg = load('sigma_twist%d.txt' % k)
    print('---- twist k = %d' % k)
    X = V82
    for j in range(1, d['nplaces'] + 1):
        o, n = d['off%d' % j]
        Gj = G[o:o + n, :]
        Lj = d['loc%d' % j]
        Vn = VectorSpace(F, n)
        Wj = Vn.subspace(Lj.columns()) if Lj is not None else Vn.subspace([])
        # c is allowed iff Gj c lies in Wj: kernel of c -> Gj c modulo Wj
        Q = Vn.quotient(Wj)
        M = matrix(F, [Q(Gj * b) for b in V82.basis()]) if Q.dimension() > 0 else matrix(F, G.ncols(), 0)
        Kj = M.left_kernel() if M.ncols() > 0 else V82
        X = X.intersection(Kj)
        print('  place %d (%s): %d coordinates, local image of dimension %d, dim X so far %d' % (j, d['name%d' % j], n, Wj.dimension(), X.dimension()))
    check(X.dimension() == d['dX'] == 19, 'dim X = 19 (k = %d)' % k)
    GXs = matrix(F, [G * b for b in X.basis()]).transpose()
    V164 = VectorSpace(F, G.nrows())
    S1 = V164.subspace(GXs.columns()); S2 = V164.subspace(d['GX'].columns())
    check(S1 == S2, 'G X equals the span of the cached columns GX (k = %d)' % k)
    o, n = d['off1']
    check(d['name1'].startswith('p = 2 (e = 3'), 'place 1 is the place v with e = 3')
    KMv = sg['KMv']
    Xv = GXs[o:o + n, :]
    r0 = KMv.rank()
    dS = block_matrix(F, [[KMv, Xv]], subdivide=False).rank() - r0
    check(dS == 4, 'image of X at v modulo the local scalars has dimension 4 (k = %d)' % k)
    Vv = VectorSpace(F, n)
    check(Vv.subspace(list(KMv.columns()) + list(Xv.columns())) == Vv.subspace(list(KMv.columns()) + list(sg['GXv'].columns())), 'the same subspace at v as the columns GXv of sigma_check (k = %d)' % k)
print('RESULT', 'PASS' if ok else 'FAIL')
