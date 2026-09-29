# abel_prym_data_check.sage: second implementation (Sage) of the WP4 known answers.
# Reads the Lean data files as text (lean/FurioLombardo/M1/DataField.lean for the zk basis, M1/Basic.lean for f,
# Discharge/M3a/DataBruin.lean, AbelPrymData.lean, AbelPrymData2.lean) and code/earlier-computations/phi_known_lifts.gp, decodes every zk
# list with Lean's own basis (zkNum / Dz, theta a root of fL), and checks in Sage, independently of PARI's
# construction:
#   (1) U'_i, V'_i of AbelPrymData.lean are the Mumford pairs of phi_known_lifts.gp transported to the reversed model
#       (U' = U^rev / U(0), V' = t^3 V(1/t) mod U');
#   (2) Bruin's construction from the data: T is tangent to D at P' = (p, s, r) for the swapped forms, U' =
#       t^2 + 2 (a2/a3) t + a1/a3, U' | V'^2 - fRev, and the entry (1, 3) identity (G A G)_{13} - m V' = (a3 U') w;
#   (3) the conic certificate of AbelPrymData2.lean: D_j R_j^4 = sum_i (D_j a_{j,i}) Q_{i+1}.
# Run from code/genus2-curves: sage abel_prym_data_check.sage
import re, ast

LEAN = "../../FurioLombardo/"

def lean_def(path, name):
    txt = open(path).read()
    m = re.search(r"def " + name + r" : [^=]*:=\s*", txt)
    if m is None:
        raise ValueError("no def " + name)
    i = m.end()
    if txt[i] == "[":
        depth = 0
        for j in range(i, len(txt)):
            if txt[j] == "[":
                depth += 1
            elif txt[j] == "]":
                depth -= 1
                if depth == 0:
                    return ast.literal_eval(txt[i:j + 1])
    return ast.literal_eval(re.match(r"-?\d+", txt[i:]).group(0))

fL = lean_def(LEAN + "M1/Basic.lean", "fL")
Dz = lean_def(LEAN + "M1/DataField.lean", "Dz")
zkNum = lean_def(LEAN + "M1/DataField.lean", "zkNum")
R.<X> = QQ[]
K.<th> = NumberField(R(fL))
zk = [sum(c * th**e for e, c in enumerate(W)) / Dz for W in zkNum]
def dec(a):
    return sum(QQ(c) * zk[j] for j, c in enumerate(a))

S.<t> = K[]
def chk(cond, msg):
    if not cond:
        raise RuntimeError("FAILED: " + msg)
    print("ok: " + msg)

# Bruin's data
QcData = lean_def(LEAN + "Discharge/M3a/DataBruin.lean", "QcData")
dData = lean_def(LEAN + "Discharge/M3a/DataBruin.lean", "dData")
FnData = lean_def(LEAN + "Discharge/M3a/DataBruin.lean", "FnData")
liftData = lean_def(LEAN + "Discharge/M3a/DataBruin.lean", "liftData")
Qc = [[dec(c) for c in QcData[i]] for i in range(3)]
def Msym(c):
    return matrix(K, 3, 3, [c[0], c[1] / 2, c[2] / 2, c[1] / 2, c[3], c[4] / 2, c[2] / 2, c[4] / 2, c[5]])
M = [Msym(Qc[i]) for i in range(3)]
delta = [dec(d) for d in dData]
fRev = [sum(dec(FnData[k][6 - j]) / 4 * t**j for j in range(7)) for k in range(2)]
for k in range(2):
    chk(fRev[k] == -delta[k] * (M[2] + 2 * t * M[1] + t**2 * M[0]).det(), "fRev_%d = -delta det(M3 + 2t M2 + t^2 M1)" % k)

# phi_known_lifts.gp
phitxt = open("../earlier-computations/phi_known_lifts.gp").read().split("\n")[1]
phitxt = phitxt[phitxt.index("=") + 1:].strip().rstrip(";").replace("^", "**")
PHI = sage_eval(phitxt, locals={"b": th, "t": t})

apM = lean_def(LEAN + "Discharge/M3a/AbelPrymData.lean", "apM")
apT = lean_def(LEAN + "Discharge/M3a/AbelPrymData.lean", "apT")
apUd = lean_def(LEAN + "Discharge/M3a/AbelPrymData.lean", "apUd")
apU = lean_def(LEAN + "Discharge/M3a/AbelPrymData.lean", "apU")
apD = lean_def(LEAN + "Discharge/M3a/AbelPrymData.lean", "apD")
apV = lean_def(LEAN + "Discharge/M3a/AbelPrymData.lean", "apV")
apW = lean_def(LEAN + "Discharge/M3a/AbelPrymData.lean", "apW")
pts = [(0, 0, 1), (1, 1, 1), (2, 0, 1), (-1, 0, 1)]
twist = [0, 1, 0, 1]
for i in range(4):
    k = twist[i]
    p = vector(K, pts[i])
    r, s = dec(liftData[i][0]), dec(liftData[i][1])
    chk(all(p * M[j] * p == delta[k] * [r**2, r * s, s**2][j] for j in range(3)), "x%d on D" % i)
    # (1) transport of phi_known_lifts.gp
    U = S(PHI[i][3]); V = S(PHI[i][4])
    chk(PHI[i][2] == [p[0], p[1], p[2], r, s], "x%d = the lift of phi_known_lifts.gp" % i)
    Ur = S(list(reversed(U.list()))) / U[0]
    Vr = (V[0] * t**3 + V[1] * t**2) % Ur
    Ul = (dec(apU[i][0]) + dec(apU[i][1]) * t) / apUd[i] + t**2
    Vl = (dec(apV[i][0]) + dec(apV[i][1]) * t) / apD[i]
    chk(Ul == Ur, "x%d: Lean's U' = transported U of phi_known_lifts.gp" % i)
    chk(Vl == Vr, "x%d: Lean's V' = transported V of phi_known_lifts.gp" % i)
    chk((Vl**2 - fRev[k]) % Ul == 0, "x%d: U' | V'^2 - fRev" % i)
    # (2) Bruin's construction for the swapped forms at P' = (p, s, r)
    m = apM[i]
    Tp = vector(K, [m, dec(apT[i][0]), 0]); T3, T4 = dec(apT[i][1]), dec(apT[i][2])
    Ms = [M[2], M[1], M[0]]
    P1, P2 = s, r
    w = [2 * P1 * T3, P1 * T4 + P2 * T3, 2 * P2 * T4]
    chk(all(2 * (Tp * Ms[j] * p) - delta[k] * w[j] == 0 for j in range(3)), "x%d: T tangent at P'" % i)
    a = [Tp * Ms[j] * Tp - delta[k] * [T3**2, T3 * T4, T4**2][j] for j in range(3)]
    chk(a[2] != 0 and Ul == t**2 + 2 * a[1] / a[2] * t + a[0] / a[2], "x%d: U' = t^2 + 2 (a2/a3) t + a1/a3" % i)
    Mt = Ms[0] + 2 * t * Ms[1] + t**2 * Ms[2]
    G = block_diagonal_matrix(Mt, matrix(S, 1, 1, [-delta[k]]))
    av = vector(S, [p[0], p[1], p[2], P1 + t * P2]); bv = vector(S, [Tp[0], Tp[1], Tp[2], T3 + t * T4])
    A = av.column() * bv.row() - bv.column() * av.row()
    chk(A[2, 0] == m, "x%d: Hodge entry (1, 3) = m" % i)
    GAG = G * A * G
    wl = (dec(apW[i][0]) + dec(apW[i][1]) * t) / apD[i]
    chk(GAG[1, 3] - m * Vl == (a[2] * t**2 + 2 * a[1] * t + a[0]) * wl, "x%d: (G A G)_{13} - m V' = (a3 U') w" % i)
    # the ruling identity at every entry, modulo U'
    Hd = matrix(S, 4, 4, [0, A[2, 3], A[3, 1], A[1, 2], -A[2, 3], 0, A[0, 3], A[2, 0],
                          -A[3, 1], -A[0, 3], 0, A[0, 1], -A[1, 2], -A[2, 0], -A[0, 1], 0])
    chk(all((GAG[u, v] - Vl * Hd[u, v]) % Ul == 0 for u in range(4) for v in range(4)), "x%d: G A G = V' star(A) mod U'" % i)

# (3) the conic certificate
cfDen = lean_def(LEAN + "Discharge/M3a/AbelPrymData2.lean", "cfDen")
cfData = lean_def(LEAN + "Discharge/M3a/AbelPrymData2.lean", "cfData")
P3.<x, y, z> = K[]
mons2 = [x**2, x * y, x * z, y**2, y * z, z**2]
Q = [sum(Qc[i][m] * mons2[m] for m in range(6)) for i in range(3)]
for j in range(3):
    lhs = sum(sum(dec(cfData[j][i][m]) * mons2[m] for m in range(6)) * Q[i] for i in range(3))
    chk(lhs == cfDen[j] * [x, y, z][j]**4, "D_%d R_%d^4 = sum_i (D a) Q_i" % (j, j))
print("all checks passed")
