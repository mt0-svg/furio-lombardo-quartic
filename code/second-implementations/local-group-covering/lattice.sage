# lattice.sage: the lattice layer (task 3) with exact integer linear algebra over Z.
# Coordinates: K_v^2 -> Q_2^6 on the basis (1, pi, pi^2) of each component; pi^m O_v^2 is the diagonal lattice
# D_m = diag(2^ceil((m - j)/3)) (j = 0, 1, 2 in each component).
# Lemma N (Nakayama). l_i approximations of l*_i = log D'_i with l*_i - l_i in pi^(M+3) O_v^2, Lambda = sum Z_2 l*_i.
#   If D_M is inside sum Z_2 l_i + D_(M+3), then D_M is inside Lambda and Lambda = sum Z_2 l_i + D_M.
# Z-lattices: L = sum Z l_i + D_M (integer representatives) contains 2^K Z^6, so Z^6/L is a 2-group and the
# Z_2-completion of L is Lambda; membership of an integer vector in L and in Lambda agree, so the HNF over Z decides
# every inclusion test below exactly.
# Lemma S (saturation from approximations, see the paper), applied to the Smith form over Z of
# an integer approximation of the coordinates of log phi_a, log phi_b.
# Usage: sage lattice.sage logs_prec<PREC>.sobj   (writes lattice.sobj)
import sys
load('loader.sage'); load('jacobian_log.sage')
fn = sys.argv[1] if len(sys.argv) > 1 else 'logs_prec1000.sobj'
LG = load(fn)
PREC_C1 = 400
X = s3_exact(); S = s3_setup(PREC_C1, X); emb = S['emb']

def pprec(v6):
    # pi-adic precision of each component from the per-coordinate 2-adic precisions
    return [min(3 * v6[3 * c + j][1] + j for j in range(3)) for c in range(2)]

def Dm(m):
    return diagonal_matrix(ZZ, [2^max(0, ceil((m - j) / 3)) for c in range(2) for j in range(3)])

def intvec(v6, n=None):
    out = []
    for (a, nj) in v6:
        a = QQ(a)
        assert a.denominator() % 2 == 1 or a == 0, 'non integral coordinate'
        out.append(ZZ(a.numerator() * inverse_mod(a.denominator(), 2^(nj + 8))) % 2^(nj + 8) if a != 0 else ZZ(0))
    return vector(ZZ, out)

def in_lattice(Hrows, v):
    # v in the Z-row span of the HNF matrix Hrows (full rank, upper triangular)
    try:
        sol = Hrows.solve_left(v)
    except ValueError:
        return False
    return all(c in ZZ for c in sol)

RES = {}
for k in [0, 1]:
    print('\n==== twist k = %d ====' % k)
    Lk = LG[k]
    tw = X['tw'][k]
    precs = [min(pprec(l)) for l in Lk['logD']]
    print(' pi-adic precision of the logs of D\'_1..D\'_7:', precs)
    l = [intvec(v) for v in Lk['logD']]
    # ---- Nakayama at M, for M = 6 (the claim) and a larger M as a consistency check
    proofs = {}
    for M in [6, 12, 30]:
        assert min(precs) >= M + 3
        H = matrix(ZZ, [list(v) for v in l] + Dm(M + 3).rows()).hermite_form(include_zero_rows=False)
        ok = all(in_lattice(H, r) for r in Dm(M).rows())
        proofs[M] = ok
        print(' Lemma N with M = %d: D_M inside sum Z l_i + D_(M+3): %s' % (M, ok))
    M = 6
    assert proofs[M]
    HL = matrix(ZZ, [list(v) for v in l] + Dm(M).rows()).hermite_form(include_zero_rows=False)
    assert HL.nrows() == 6
    # least m with D_m inside Lambda
    mL = None
    for m in range(0, M + 1):
        if all(in_lattice(HL, r) for r in Dm(m).rows()):
            mL = m; break
    print(' Lambda = sum Z_2 l_i + pi^6 O_v^2 (exact); least m with pi^m O_v^2 in Lambda: m_Lambda = %d' % mL)
    idx = HL.det().abs()
    print(' index [O_v^2 : Lambda] = %s = 2^%d; HNF diagonal (row HNF, coordinates (1, pi, pi^2) twice) 2-valuations:' % (idx, idx.valuation(2)),
          [HL[i, i].valuation(2) for i in range(6)])
    # consistency check: the Lambda from M = 30 is the same lattice
    HL30 = matrix(ZZ, [list(v) for v in l] + Dm(30).rows()).hermite_form(include_zero_rows=False)
    same = all(in_lattice(HL, r) for r in HL30.rows()) and all(in_lattice(HL30, r) for r in HL.rows())
    print(' sum Z_2 l_i + D_30 == sum Z_2 l_i + D_6: %s' % same)
    B = HL                       # rows: a Z_2-basis of Lambda
    Binv = B.inverse()
    def coords(v6):
        # coordinates in the basis B of a vector known modulo pi^m (m = min precision of its components), known
        # modulo 2^j, j = floor((m - m_Lambda)/3)
        m = min(pprec(v6))
        y = vector(QQ, [QQ(a) for (a, nj) in v6])
        x = y * Binv
        return x, floor((m - mL) / 3)
    rho = []
    for i in range(7):
        x, j = coords(Lk['logD'][i])
        assert all(c.denominator() % 2 == 1 for c in x) and j >= 1
        rho.append(vector(GF(2), [ZZ(c.numerator() * inverse_mod(c.denominator(), 2)) % 2 for c in x]))
    Rm = matrix(GF(2), rho).transpose()          # 6 x 7: rho(D_i) as columns
    print(' rank of rho on A(K_v)/2A(K_v) = %d (expected 6, kernel = <T>)' % Rm.rank())
    kerR = Rm.right_kernel()
    print(' kernel of rho (in the basis D_1..D_7):', [list(w) for w in kerR.basis()], '; KnCoef T column:', list(tw['Kn'].column(0)))
    V6 = VectorSpace(GF(2), 6)
    W = V6.subspace([Rm * tw['Sel'].column(s) for s in range(19)])
    print(' dim sigma_v(Sel) = %d, dim W = rho(sigma_v(Sel)) = %d' % (tw['Sel'].rank(), W.dimension()))
    ia, ib = Lk['ia'], Lk['ib']
    xa, ja = coords(Lk['logphi'][ia]); xb, jb = coords(Lk['logphi'][ib])
    for x_ in (xa, xb):
        assert all(c.denominator() % 2 == 1 for c in x_)
    m2 = lambda x_: vector(GF(2), [ZZ(c.numerator() * inverse_mod(c.denominator(), 2)) % 2 for c in x_])
    print(' KAT rho(T) = 0:', Rm * tw['Kn'].column(0) == 0, '; rho(phi_a) = x - T class:', m2(xa) == Rm * tw['Kn'].column(1),
          '; rho(phi_b):', m2(xb) == Rm * tw['Kn'].column(2))
    jY = min(ja, jb)
    print(' coordinates of log phi_a, log phi_b in Lambda known modulo 2^%d' % jY)
    def zrep(c, n):
        return ZZ(c.numerator() * inverse_mod(c.denominator(), 2^n)) % 2^n
    Yp = matrix(ZZ, [[zrep(xa[i], jY), zrep(xb[i], jY)] for i in range(6)])
    Dsm, Usm, Vsm = Yp.smith_form()
    d1 = Dsm[0, 0].valuation(2); d2 = Dsm[1, 1].valuation(2)
    assert jY > d2
    print(' elementary divisors of <log phi_a, log phi_b> in Lambda: 2^%d, 2^%d (Lemma S applies: j = %d > d2)' % (d1, d2, jY))
    jS = jY - d2
    print(' saturation Gsat and pr known modulo 2^(j - d2) = 2^%d' % jS)
    prm = Usm[2:, :]                               # pr : Z_2^6 -> Z_2^4 (rows 3..6 of U)
    Gsat2 = V6.subspace([vector(GF(2), (Usm.inverse()).column(c)) for c in range(2)])
    prW = VectorSpace(GF(2), 4).subspace([vector(GF(2), prm * vector(ZZ, [ZZ(t) for t in w])) for w in W.basis()])
    print(' dim pr(W) = %d; nonzero element of pr(W):' % prW.dimension(), [list(w) for w in prW if w != 0])
    print(' KAT image(Gsat) mod 2 inside W: %s; dim image(Gsat) cap W = %d' % (Gsat2.is_subspace(W), Gsat2.intersection(W).dimension()))
    WG = V6.subspace([m2(xa), m2(xb)])
    print(' dim W_Gamma (T, phi_a, phi_b) = %d' % WG.dimension())
    # halving data (basis free)
    halv = [(ea, eb) for ea in range(4) for eb in range(4) if (ea, eb) != (0, 0) and all(((ea * xa[i] + eb * xb[i]) / 4).denominator() % 2 == 1 for i in range(6))]
    print(' (alpha, beta) mod 4 with (alpha log phi_a + beta log phi_b)/4 in Lambda:', halv)
    # c_1 at the known lifts
    E1 = {}; NU1 = {}
    for a in [ia, ib]:
        c1 = tw['c1'][a]
        v6 = vec6c([emb(c1[0]), emb(c1[1])])
        x, jc = coords(v6)
        t = max([0] + [-c.valuation(2) for c in x if c != 0])
        y = [c * 2^t for c in x]
        py = [sum(prm[r, i] * y[i] for i in range(6)) for r in range(4)]
        vals = [c.valuation(2) if c != 0 else Infinity for c in py]
        nu_t = min(vals)
        assert nu_t + 1 <= jS and nu_t + 1 <= jc + t, "precision"
        nu = nu_t - t
        cl = vector(GF(2), [ZZ((c / 2^nu_t).numerator() * inverse_mod((c / 2^nu_t).denominator(), 2)) % 2 if c != 0 else 0 for c in py])
        E1[a] = cl; NU1[a] = nu
        print(' x_%d: 2^%d c_1 in Lambda; nu(pr c_1) = %d; class e1 = %s; e1 in pr(W): %s; margin (j - d2) - (nu + 1 + t) = %d'
              % (a, t, nu, list(cl), cl in prW, jS - (nu_t + 1)))
    print(' e1(x_%d) == e1(x_%d): %s' % (ia, ib, E1[ia] == E1[ib]))
    RES[k] = dict(B=B, mL=mL, M=M, W=W, prm=prm, jS=jS, d=(d1, d2), prW=prW, E1=E1, NU1=NU1, Rm=Rm, ia=ia, ib=ib,
                  idx=idx, hnfdiag=[HL[i, i].valuation(2) for i in range(6)])
save(RES, 'lattice.sobj')
print('\nsaved lattice.sobj')
