# Blind second implementation of claim selmer-set-K21 (lane M0b), shared library.
# Input data: code/earlier-computations/bruin_form.gp (K21, Q1, Q2, Q3, cB, d0, d1) and the equation of C from PROBLEM.md.
# Nothing here is taken from code/descent/selset_*.gp or code/descent/impl4/ss2_*.sage.
# Run every script from this directory: cd code/second-implementations/descent-set && sage ssb_<n>.sage

import os, re
PROB = os.path.abspath(os.path.join(os.getcwd(), '..', '..', '..'))
DATA = os.path.join(PROB, 'code', 'earlier-computations', 'bruin_form.gp')
assert os.path.exists(DATA), "run from code/second-implementations/descent-set"

def read_gp_data(path):
    txt = open(path).read()
    txt = '\n'.join(l for l in txt.split('\n') if not l.startswith('\\\\'))
    out = {}
    for stmt in txt.split(';'):
        stmt = stmt.strip()
        if not stmt:
            continue
        name, rhs = stmt.split('=', 1)
        out[name.strip()] = re.sub(r'\s+', '', rhs)
    return out

_raw = read_gp_data(DATA)
Qb.<bb> = QQ[]
K21pol = Qb(_raw['K21'].replace('b', 'bb'))
K.<b> = NumberField(K21pol)
R.<x, y, z> = PolynomialRing(K)
def _parse(s):
    return R(sage_eval(s, locals={'b': b, 'x': x, 'y': y, 'z': z}))
Q1 = _parse(_raw['Q1']); Q2 = _parse(_raw['Q2']); Q3 = _parse(_raw['Q3'])
cB = K(sage_eval(_raw['cB'], locals={'b': b}))
d0 = K(sage_eval(_raw['d0'], locals={'b': b}))
d1 = K(sage_eval(_raw['d1'], locals={'b': b}))
# equation of C (PROBLEM.md)
F = (x^4 + 3*x^3*y - 3*x^2*y*z - 3*x^2*z^2 + 6*x*y^3 - 6*x*y^2*z + 3*x*y*z^2 - 2*x*z^3
     + 4*y^4 + 2*y^3*z - 5*y*z^3)
PTS = [(0, 0, 1), (1, 1, 1), (2, 0, 1), (-1, 0, 1)]
MONS2 = [x^2, x*y, x*z, y^2, y*z, z^2]

def coeffs2(Q):
    """Coefficient vector of a ternary quadratic form on the monomial basis MONS2."""
    return [Q.monomial_coefficient(m) for m in MONS2]

def delta_rep(P):
    """Q1(P), or Q3(P) when Q1(P) = 0: the representative of delta(P) used in the claim."""
    v = Q1(*P)
    return v if v != 0 else Q3(*P)
