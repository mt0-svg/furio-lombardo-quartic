# sigma_check.sage: second implementation (Sage, GF(2)) of the linear algebra at the place v above 2 with e = 3
# behind sigma_v injective (sigma_v_injective.gp) and the D-basis coordinates of selmer_image_v.gp, from the text export
# sigma_twist<k>.txt of sigma_export.gp (exact 0/1 matrices; the rows themselves were checked in an independent review of the
# 2-descent). Own parser, own linear algebra.
# Run from code/second-implementations/selmer-space: sage sigma_check.sage > sigma_check.out
import re
F = GF(2)

def parse_mat(s):
    s = s.strip()
    assert s[0] == '[' and s[-1] == ']', s[:40]
    body = s[1:-1].strip()
    if body in ('', ';'):
        return None
    rows = [r.strip() for r in body.split(';')]
    return matrix(F, [[int(e) for e in r.split(',')] for r in rows])

def load(k):
    txt = open('sigma_twist%d.txt' % k).read()
    d = {}
    for m in re.finditer(r'^(\w+) = (.*?);$', txt, re.M):
        name, val = m.group(1), m.group(2)
        if val.startswith('['):
            d[name] = parse_mat(val)
        elif val.startswith('"'):
            d[name] = val.strip('"')
        else:
            d[name] = int(val)
    return d

def colspace_rank(*Ms):
    Ms = [M for M in Ms if M is not None]
    return block_matrix(F, [Ms], subdivide=False).rank()

ok = True
def check(c, msg):
    global ok
    print(('PASS ' if c else 'FAIL ') + msg)
    ok = ok and c

for k in [0, 1]:
    d = load(k)
    print('---- twist k = %d, place %s' % (k, d['place']))
    GXv, KMv, LVv, Cv, KMbar, LV = d['GXv'], d['KMv'], d['LVv'], d['Cv'], d['KMbar'], d['LV']
    dSel = d['dX'] - 15
    r0 = KMv.rank()
    dS = colspace_rank(KMv, GXv) - r0
    print('rows at v: %d; rank of the K_v^x image: %d; dim sigma_v(Sel) = %d; dim Sel = dX - 15 = %d' % (GXv.nrows(), r0, dS, dSel))
    check(dS == dSel, 'sigma_v injective on Sel^2 (k = %d)' % k)
    # the D_i: basis of the local image modulo the K_v^x image
    B = block_matrix(F, [[Cv, KMv]], subdivide=False)
    check(Cv.ncols() == 7 and B.rank() == 7 + r0 and KMv.rank() == KMv.ncols(), 'c_1..c_7 independent modulo the K_v^x image, which has independent columns (k = %d)' % k)
    # coordinates of the Selmer columns and of the known classes in the basis [D_1..D_7 | K_v^x]
    def coords(M):
        Z = B.solve_right(M)          # raises if not in the span
        assert B * Z == M
        return Z[:7, :]
    SC = coords(GXv); KC = coords(LVv)
    check(SC == d['SelCoef'], 'SelCoef equals the stored matrix of rho_k%d.bin' % k)
    check(KC == d['KnCoef'], 'KnCoef equals the stored matrix of rho_k%d.bin' % k)
    print('KnCoef columns (T, phi_a, phi_b):', [list(KC.column(j)) for j in range(3)])
    print('rank of sigma_v(Sel) in the D basis:', SC.rank())
    # T in the D basis, and T not in 2A(k_v): its local class is nonzero
    check(KC.column(0) != 0, 'the class of T at v is nonzero (T not in 2A(k_v)) (k = %d)' % k)
    # relations among T, phi_a, phi_b from the full localisation: kernel of [KMbar | LV], last three coordinates
    M = block_matrix(F, [[KMbar, LV]], subdivide=False)
    K = M.right_kernel()
    rel = span(F, [vector(F, list(v)[-3:]) for v in K.basis()])
    print('relations (T, phi_a, phi_b) modulo 2J(K21):', [list(v) for v in rel.basis()])
    check(rel == span(F, [vector(F, [0, 1, 1])]), 'the only relation is phi_a + phi_b (k = %d)' % k)
    check(colspace_rank(KMbar, LV) - KMbar.rank() == 2, 'the known classes span 2 dimensions modulo the local scalars (k = %d)' % k)

print('RESULT', 'PASS' if ok else 'FAIL')
