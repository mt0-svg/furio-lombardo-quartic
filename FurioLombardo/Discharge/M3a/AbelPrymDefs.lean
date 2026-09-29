import FurioLombardo.Discharge.M3a.ConcreteDefs
import FurioLombardo.Discharge.M3a.AbelPrymData

/-!
# Kronecker expressions of the Abel-Prym certificates (WP4 of the M3a discharge)

The reversed model uses Bruin's construction for the swapped forms `(Q3, Q2, Q1)` (matrices
`Mmat 2, Mmat 1, Mmat 0`) at the swapped point `P' = (p, s, r)` of a lift `(p, r, s)`. For the known
lift of index `i` (`liftData`, twist `k`, `p = (a : b : 1)`), with the data of AbelPrymData.lean
(code/genus2-curves/abel_prym_data.gp):

* the tangent vector `T = (m, t1, 0, t3, t4)` (`TE`, `t3E`, `t4E`);
* `tanE j`: the polar form `polarD j P' T` of the swapped quadric `j` of `D_δ`;
* `q2E j`: `2 quadD j T` (twice `a_(j+1)` of abel_prym_lib.gp);
* `u0Chk`, `u1Chk`: `U' = X² + (2 a₂/a₃) X + a₁/a₃` has the coefficients of `apU`;
* `nChk`: the component `apNj` of `N = (r² M3 - 2rs M2 + s² M1) p` (the rank condition);
* `entLhs`, `entRhs`: `(G A G)_{13} - m V' = (a₃ X² + 2a₂ X + a₁) w`, cleared of denominators;
* `detLhsS`, `detRhsS`: `fRev = -δ det(M3 + 2t M2 + t² M1)`.

The kernel checks are in AbelPrymCheck.lean, their meaning in AbelPrymKnown.lean.
-/

namespace FurioLombardo.Discharge.M3a.Bruin

open FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a

/-! ## The swapped pencil and its determinant -/

/-- The entry `(a, b)` of `2 (M3 + 2t M2 + t² M1)`. -/
def NPs (a b : Fin 3) : List KE := [NE 2 a b, .mul (.int 2) (NE 1 a b), NE 0 a b]

/-- `2 · (4 fRev_k)`. -/
def detLhsS (k : ℕ) : List KE := smulP (.int 2) (frevL k)

/-- `-δ_k · det(2 (M3 + 2t M2 + t² M1))`. -/
def detRhsS (k : ℕ) : List KE := smulP (.mul (.int (-1)) (.lin (dL k))) (detP NPs)

/-! ## Data accessors -/

def apMN (i : ℕ) : ℕ := apM.getD i 1

def apTL (i j : ℕ) : List ℤ := (apT.getD i []).getD j []

def apUdN (i : ℕ) : ℕ := apUd.getD i 1

def apUL (i j : ℕ) : List ℤ := (apU.getD i []).getD j []

def apDN (i : ℕ) : ℕ := apD.getD i 1

def apVL (i j : ℕ) : List ℤ := (apV.getD i []).getD j []

def apWL (i j : ℕ) : List ℤ := (apW.getD i []).getD j []

def apNjN (i : ℕ) : Fin 3 := ⟨apNj.getD i 0 % 3, Nat.mod_lt _ (by norm_num)⟩

def apNL (i : ℕ) : List ℤ := apN.getD i []

/-! ## Expressions -/

/-- `u ⬝ v`. -/
def dot3E (u v : Fin 3 → KE) : KE :=
  .add (.add (.mul (u 0) (v 0)) (.mul (u 1) (v 1))) (.mul (u 2) (v 2))

/-- `2 (u ⬝ M_(j+1) v)`. -/
def bil2E (j : Fin 3) (u v : Fin 3 → KE) : KE := dot3E u (fun a => dot3E (NE j a) v)

/-- The swap `0 ↦ 2, 1 ↦ 1, 2 ↦ 0` of the forms. -/
def sw (j : Fin 3) : Fin 3 := ![2, 1, 0] j

/-- `p = (a, b, 1)`. -/
def pE (a b : ℤ) : Fin 3 → KE := ![.int a, .int b, .int 1]

/-- The first three coordinates `(m, t1, 0)` of `T`. -/
def TE (i : ℕ) : Fin 3 → KE := ![.int (apMN i), .lin (apTL i 0), .int 0]

def rE (i : ℕ) : KE := .lin (liftR i)

def sE (i : ℕ) : KE := .lin (liftS i)

def dE (k : ℕ) : KE := .lin (dL k)

def t3E (i : ℕ) : KE := .lin (apTL i 1)

def t4E (i : ℕ) : KE := .lin (apTL i 2)

/-- The `(r, s)` part of the polar form at `P' = (p, s, r)` in the direction `T`. -/
def wE (i : ℕ) (j : Fin 3) : KE :=
  ![.mul (.int 2) (.mul (sE i) (t3E i)), .add (.mul (sE i) (t4E i)) (.mul (rE i) (t3E i)),
    .mul (.int 2) (.mul (rE i) (t4E i))] j

/-- The polar form of the swapped quadric `j` of `D_δ` at `P'` in the direction `T`. -/
def tanE (i k : ℕ) (a b : ℤ) (j : Fin 3) : KE :=
  .sub (bil2E (sw j) (TE i) (pE a b)) (.mul (dE k) (wE i j))

/-- The `(r, s)` part of the swapped quadric `j` at `T`. -/
def sqE (i : ℕ) (j : Fin 3) : KE :=
  ![.mul (t3E i) (t3E i), .mul (t3E i) (t4E i), .mul (t4E i) (t4E i)] j

/-- `2 quadD j T` for the swapped forms. -/
def q2E (i k : ℕ) (j : Fin 3) : KE :=
  .sub (bil2E (sw j) (TE i) (TE i)) (.mul (.int 2) (.mul (dE k) (sqE i j)))

/-- `Ud · a₁/a₃ = u0`, as `u0 · (2 a₃) - Ud · (2 a₁)`. -/
def u0Chk (i k : ℕ) : KE := .sub (.mul (.lin (apUL i 0)) (q2E i k 2)) (.mul (.int (apUdN i)) (q2E i k 0))

/-- `Ud · 2a₂/a₃ = u1`, as `u1 · (2 a₃) - 2 Ud · (2 a₂)`. -/
def u1Chk (i k : ℕ) : KE :=
  .sub (.mul (.lin (apUL i 1)) (q2E i k 2)) (.mul (.int (2 * apUdN i)) (q2E i k 1))

/-- Row `j` of `2 (r² M3 - 2rs M2 + s² M1)`. -/
def nRowE (i : ℕ) (j : Fin 3) (c : Fin 3) : KE :=
  .add (.sub (.mul (.mul (rE i) (rE i)) (NE 2 j c)) (.mul (.mul (.int 2) (.mul (sE i) (rE i))) (NE 1 j c)))
    (.mul (.mul (sE i) (sE i)) (NE 0 j c))

/-- `apN - 2 N_j` for `j = apNj`. -/
def nChk (i : ℕ) (a b : ℤ) : KE := .sub (.lin (apNL i)) (dot3E (nRowE i (apNjN i)) (pE a b))

/-- The entry `u` of `plk P' ∧ plk T` in the last column: `p_u (t3 + X t4) - T_u (s + X r)`. -/
def auL (i : ℕ) (a b : ℤ) (u : Fin 3) : List KE :=
  [.sub (.mul (pE a b u) (t3E i)) (.mul (TE i u) (sE i)),
   .sub (.mul (pE a b u) (t4E i)) (.mul (TE i u) (rE i))]

/-- `2 (G A G)_{13}`. -/
def gag2L (i k : ℕ) (a b : ℤ) : List KE :=
  smulP (.mul (.int (-1)) (dE k))
    (addP (addP (mulP (NPs 1 0) (auL i a b 0)) (mulP (NPs 1 1) (auL i a b 1)))
      (mulP (NPs 1 2) (auL i a b 2)))

/-- `2 (a₁ + 2a₂ X + a₃ X²)`. -/
def uTL (i k : ℕ) : List KE := [q2E i k 0, .mul (.int 2) (q2E i k 1), q2E i k 2]

/-- `D V'`. -/
def vL (i : ℕ) : List KE := [.lin (apVL i 0), .lin (apVL i 1)]

/-- `D w`. -/
def wL (i : ℕ) : List KE := [.lin (apWL i 0), .lin (apWL i 1)]

/-- `D · 2 (G A G)_{13} - 2m · D V'`. -/
def entLhs (i k : ℕ) (a b : ℤ) : List KE :=
  subP (smulP (.int (apDN i)) (gag2L i k a b)) (smulP (.int (2 * apMN i)) (vL i))

/-- `2 (a₁ + 2a₂ X + a₃ X²) · D w`. -/
def entRhs (i k : ℕ) : List KE := mulP (uTL i k) (wL i)

/-- The coefficients of `Ud U'`. -/
def uL (i : ℕ) : List KE := [.lin (apUL i 0), .lin (apUL i 1), .int (apUdN i)]

end FurioLombardo.Discharge.M3a.Bruin
