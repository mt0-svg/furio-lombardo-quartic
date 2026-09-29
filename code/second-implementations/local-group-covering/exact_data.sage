# exact_data.sage: exact input data of the M9 chain over K21 (Sage number field), read from text exports only.
# Sources (exact data, no p-adic values):
#   code/earlier-computations/export/field_and_place.txt, sextic_twist<k>.txt, local_divisors_twist<k>.txt, phi_known_twist<k>.txt, selmer_coords_twist<k>.txt, tiny_integral_c1_twist<k>.txt (PARI syntax)
#   exact_global_data.sage (Bruin quadrics Q1, Q2, Q3, twists d0, d1, lifts x_i of P0..P3 and phi(x_i))
#   code/earlier-computations/pullback_known_lifts.gp (pullback matrices A and tiny series coefficients at x_i)
#   code/earlier-computations/discs_q2.txt, data/boxes_twist<k>.txt (disc data and box lists)
# Usage: load('exact_data.sage'); X = s3_exact()

S3DIR = '../../earlier-computations/'

def _gp_file(fn):
    named = {}; unnamed = []
    for line in open(fn):
        line = line.split('\\\\')[0].strip()
        if not line:
            continue
        head = line.split('=')[0].strip()
        if '=' in line and head.replace('_', '').isalnum():
            named[head] = pari(line.split('=', 1)[1].strip().rstrip(';'))
        else:
            unnamed.append(pari(line.rstrip(';')))
    return named, unnamed

FQ_STR = 'x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3 + 4*y^4 + 2*y^3*z - 5*y*z^3'

def s3_exact():
    c, _ = _gp_file(S3DIR + 'export/field_and_place.txt')
    Qb = PolynomialRing(QQ, 'bb')
    K21pol = Qb(c['K21'])
    K = NumberField(K21pol, 'b'); b = K.gen()
    def el(z):
        z = pari(z)
        if z.type() == 't_POLMOD':
            z = z.lift()
        return K(Qb(z).list()) if z.type() in ('t_POL',) else K(QQ(z))
    pg = el(c['prgen'][1])
    NM = Integer(c['NM'])
    ref = {}
    sage_eval_ns = {}
    exec(preparse(open(S3DIR + '../second-implementations/local-group-covering/exact_global_data.sage').read()), globals(), sage_eval_ns)
    assert list(K21pol) == [QQ(t) for t in sage_eval_ns['K21c']]
    elc = lambda cl: K([QQ(t) for t in cl])
    Qc = [[elc(cf) for cf in sage_eval_ns[nm]] for nm in ('Q1c', 'Q2c', 'Q3c')]   # monomials x2 xy xz y2 yz z2
    dl = [elc(sage_eval_ns['d0c']), elc(sage_eval_ns['d1c'])]
    PHI = {}
    for (i, kk, xc, Uc, Vc) in sage_eval_ns['PHIc']:
        PHI[int(i)] = dict(k=int(kk), x=[elc(t) for t in xc], U=[elc(t) for t in Uc], V=[elc(t) for t in Vc])
    R3 = PolynomialRing(K, 'x,y,z'); x, y, z = R3.gens()
    Fq = R3(FQ_STR)
    mons = [x^2, x*y, x*z, y^2, y*z, z^2]
    Q = [sum(cf * m for cf, m in zip(q, mons)) for q in Qc]
    tw = {}
    for k in [0, 1]:
        F, _ = _gp_file(S3DIR + 'export/sextic_twist%d.txt' % k)
        f = [el(t) for t in F['fvecrev']]
        Dd, _ = _gp_file(S3DIR + 'export/local_divisors_twist%d.txt' % k)
        Ds = []
        for i in range(1, 8):
            U, V = Dd['D%d' % i]
            Ds.append(([el(t) for t in U], [el(t) for t in V]))
        Ph, _ = _gp_file(S3DIR + 'export/phi_known_twist%d.txt' % k)
        phis = {int(nm[3:]): ([el(t) for t in Ph[nm][0]], [el(t) for t in Ph[nm][1]]) for nm in Ph}
        S, _ = _gp_file(S3DIR + 'export/selmer_coords_twist%d.txt' % k)
        Sel = matrix(GF(2), [[int(S['SelCoef'][i, j]) for j in range(19)] for i in range(7)])
        Kn = matrix(GF(2), [[int(S['KnCoef'][i, j]) for j in range(3)] for i in range(7)])
        C1, _ = _gp_file(S3DIR + 'export/tiny_integral_c1_twist%d.txt' % k)
        c1 = {int(nm[3:]): (el(C1[nm][0]), el(C1[nm][1])) for nm in C1}
        tw[k] = dict(f=f, D=Ds, phi=phis, Sel=Sel, Kn=Kn, c1=c1, delta=dl[k])
    return dict(K=K, b=b, K21pol=K21pol, pg=pg, NM=NM, Qc=Qc, Q=Q, R3=R3, Fq=Fq, delta=dl, PHI=PHI, tw=tw, el=el)

def s3_tiny(X):
    txt = open(S3DIR + 'pullback_known_lifts.gp').read()
    body = txt[txt.index('TINY'):]
    body = body.split('=', 1)[1].strip().rstrip(';').strip().rstrip(';')
    T = pari(body)
    out = {}
    for ent in T:
        i = int(ent[0]); kk = int(ent[1])
        A = matrix(X['K'], 2, 2, [X['el'](ent[2][r, cc]) for r in range(2) for cc in range(2)])
        w0 = [X['el'](t) for t in ent[3]]; w1 = [X['el'](t) for t in ent[4]]
        out[i] = dict(k=kk, A=A, w0=w0, w1=w1)
    return out

def s3_discs():
    n, _ = _gp_file(S3DIR + 'discs_q2.txt')
    return [[int(t) for t in d] for d in n['DISCS']]

def s3_boxes(k):
    out = []
    for line in open(S3DIR + 'data/boxes_twist%d.txt' % k):
        line = line.strip()
        if not line:
            continue
        v = pari(line)
        out.append(dict(disc=int(v[0]), X0=Integer(v[1]), level=int(v[2]), verdict=str(v[3])))
    return out
