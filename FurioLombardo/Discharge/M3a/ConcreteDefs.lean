import FurioLombardo.Discharge.M3a.PolyK
import FurioLombardo.Discharge.M3a.DataBruin

/-!
# The concrete objects of the route over K21: definitions (WP2 of the M3a discharge)

Data from DataBruin.lean (code/genus2-curves/bruin_data.gp); every element of K21 is lane
M1's `zkE` of its zk coordinates. For the twists `k = 0, 1`:

* `Mmat i` (`i = 0, 1, 2`): the symmetric matrices of Bruin's quadrics `Q1, Q2, Q3`
  (code/earlier-computations/bruin_form.gp), diagonal = coefficients of `x², y², z²`, off diagonal
  = half the coefficients of `xy, xz, yz`; `δ k` = `d0`, `d1` of bruin_form.gp (`δ0`, `δ1`);
* `fδ k = -δ_k det(M1 + 2t M2 + t² M3)` (as `pQ 4` of explicit coefficients) and the reversed
  sextic `fRev k` (the same coefficients in the reverse order);
* `c k`, `q k`, `h k`: `fRev k = C (c k) * q k * h k` with `q k`, `h k` monic of degrees 2, 4;
* `d k = disc (q k)`, and `β k`, `γ k` with `β² - d = fRev · γ`;
* the lists of Kronecker expressions whose coefficientwise equality the kernel checks
  (ConcreteCheck.lean).
-/

namespace FurioLombardo.Discharge.M3a.Bruin

open Polynomial Matrix FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a

/-! ## Bruin's quadrics and the twists -/

/-- zk coordinates of the coefficient `j` (on `x², xy, xz, y², yz, z²`) of `Q_(i+1)`. -/
def QcL (i j : ℕ) : List ℤ := (QcData.getD i []).getD j []

/-- The coefficient `j` (on `x², xy, xz, y², yz, z²`) of `Q_(i+1)`. -/
noncomputable def Qc (i : Fin 3) (j : Fin 6) : K21 := zkE (QcL i j)

/-- The symmetric matrix of `Q_(i+1)`. -/
noncomputable def Mmat (i : Fin 3) : Matrix (Fin 3) (Fin 3) K21 :=
  !![Qc i 0, Qc i 1 / 2, Qc i 2 / 2; Qc i 1 / 2, Qc i 3, Qc i 4 / 2; Qc i 2 / 2, Qc i 4 / 2, Qc i 5]

/-- The ternary quadratic form `Q_(i+1)` with its six coefficients. -/
noncomputable def Qform (i : Fin 3) (p : Fin 3 → K21) : K21 :=
  Qc i 0 * p 0 ^ 2 + Qc i 1 * (p 0 * p 1) + Qc i 2 * (p 0 * p 2) + Qc i 3 * p 1 ^ 2 +
    Qc i 4 * (p 1 * p 2) + Qc i 5 * p 2 ^ 2

/-- zk coordinates of `δ_k`. -/
def dL (k : ℕ) : List ℤ := dData.getD k []

/-- The twists `δ0 = d0`, `δ1 = d1` of bruin_form.gp. -/
noncomputable def δ (k : Fin 2) : K21 := zkE (dL k)

noncomputable abbrev δ0 : K21 := δ 0

noncomputable abbrev δ1 : K21 := δ 1

/-! ## The Prym sextics -/

/-- Coefficient `j` of `4 f_k`. -/
def FE (k j : ℕ) : KE := .lin ((FnData.getD k []).getD j [])

/-- The coefficients of `4 f_k`, constant term first. -/
def fdeltaL (k : ℕ) : List KE := [FE k 0, FE k 1, FE k 2, FE k 3, FE k 4, FE k 5, FE k 6]

/-- The coefficients of `4 fRev_k`: those of `4 f_k` in the reverse order. -/
def frevL (k : ℕ) : List KE := [FE k 6, FE k 5, FE k 4, FE k 3, FE k 2, FE k 1, FE k 0]

/-- The Prym sextic `f_k(t) = -δ_k det(M1 + 2t M2 + t² M3)` (theorem `fδ_eq_det`). -/
noncomputable def fδ (k : Fin 2) : K21[X] := pQ 4 (fdeltaL k)

/-- The reversed Prym sextic `fRev_k(s) = s⁶ f_k(1/s)` (theorem `fRev_eq_reverse`). -/
noncomputable def fRev (k : Fin 2) : K21[X] := pQ 4 (frevL k)

/-- The matrix `M1 + 2t M2 + t² M3` over `K21[t]`. -/
noncomputable def Mt : Matrix (Fin 3) (Fin 3) K21[X] :=
  Matrix.of fun a b => C (Mmat 0 a b) + 2 * X * C (Mmat 1 a b) + X ^ 2 * C (Mmat 2 a b)

/-- Position of the entry `(a, b)` of a symmetric matrix among `x², xy, xz, y², yz, z²`. -/
def idx (a b : Fin 3) : ℕ := ![![0, 1, 2], ![1, 3, 4], ![2, 4, 5]] a b

/-- The entry `(a, b)` of `2 M_(i+1)` as an expression. -/
def NE (i : Fin 3) (a b : Fin 3) : KE :=
  if a = b then .mul (.int 2) (.lin (QcL i (idx a b))) else .lin (QcL i (idx a b))

/-- The entry `(a, b)` of `2 (M1 + 2t M2 + t² M3)`. -/
def NP (a b : Fin 3) : List KE := [NE 0 a b, .mul (.int 2) (NE 1 a b), NE 2 a b]

/-- The determinant of a `3 × 3` matrix of coefficient lists (the formula of `det_fin_three`). -/
def detP (E : Fin 3 → Fin 3 → List KE) : List KE :=
  subP (addP (addP (subP (subP (mulP (mulP (E 0 0) (E 1 1)) (E 2 2))
    (mulP (mulP (E 0 0) (E 1 2)) (E 2 1))) (mulP (mulP (E 0 1) (E 1 0)) (E 2 2)))
    (mulP (mulP (E 0 1) (E 1 2)) (E 2 0))) (mulP (mulP (E 0 2) (E 1 0)) (E 2 1)))
    (mulP (mulP (E 0 2) (E 1 1)) (E 2 0))

/-- `2 · (4 f_k)`. -/
def detLhs (k : ℕ) : List KE := smulP (.int 2) (fdeltaL k)

/-- `-δ_k · det(2 (M1 + 2t M2 + t² M3))`. -/
def detRhs (k : ℕ) : List KE := smulP (.mul (.int (-1)) (.lin (dL k))) (detP NP)

/-! ## The factorization `fRev = c q h` -/

/-- Denominator of `q_k`. -/
def qDenN (k : ℕ) : ℕ := qDen.getD k 1

/-- Denominator of `h_k`. -/
def hDenN (k : ℕ) : ℕ := hDen.getD k 1

/-- Coefficient `j` of `qDen · q_k`. -/
def qE (k j : ℕ) : KE := .lin ((qData.getD k []).getD j [])

/-- Coefficient `j` of `hDen · h_k`. -/
def hE (k j : ℕ) : KE := .lin ((hData.getD k []).getD j [])

/-- The coefficients of `qDen · q_k`. -/
def qL (k : ℕ) : List KE := [qE k 0, qE k 1, .int (qDenN k)]

/-- The coefficients of `hDen · h_k`. -/
def hL (k : ℕ) : List KE := [hE k 0, hE k 1, hE k 2, hE k 3, .int (hDenN k)]

/-- The monic quadratic factor of `fRev_k`: `T = [⟨q, Y⟩]` is the rational 2-torsion point. -/
noncomputable def q (k : Fin 2) : K21[X] := pQ (qDenN k) (qL k)

/-- The monic quartic factor of `fRev_k`. -/
noncomputable def h (k : Fin 2) : K21[X] := pQ (hDenN k) (hL k)

/-- The leading coefficient `f_k(0)` of `fRev_k`. -/
noncomputable def c (k : Fin 2) : K21 := (4 : K21)⁻¹ * evK (FE k 0)

/-- `4 qDen hDen · (4 fRev_k)`. -/
def facLhs (k : ℕ) : List KE := smulP (.int ((4 * qDenN k * hDenN k : ℕ) : ℤ)) (frevL k)

/-- `4 · (4 c_k) (qDen q_k) (hDen h_k)`. -/
def facRhs (k : ℕ) : List KE :=
  smulP (.int ((4 : ℕ) : ℤ)) (mulP (mulP [FE k 0] (qL k)) (hL k))

/-! ## Separability (Bezout certificate) -/

/-- `A` of `A R + B R' = m`, `R = 4 fRev_k`. -/
def bezAL (k : ℕ) : List KE := (bezA.getD k []).map .lin

/-- `B` of `A R + B R' = m`. -/
def bezBL (k : ℕ) : List KE := (bezB.getD k []).map .lin

/-- `m` of `A R + B R' = m`. -/
def bezMZ (k : ℕ) : ℤ := bezM.getD k 0

/-- `A R + B R'`. -/
def bezLhs (k : ℕ) : List KE := addP (mulP (bezAL k) (frevL k)) (mulP (bezBL k) (derivP (frevL k)))

/-! ## The discriminant of `q` and its square root modulo `fRev` -/

/-- The discriminant of `q_k`. -/
noncomputable def d (k : Fin 2) : K21 := (q k).coeff 1 ^ 2 - 4 * (q k).coeff 0

/-- zk coordinates of `qDen² d_k`. -/
def dnL (k : ℕ) : List ℤ := dnData.getD k []

/-- `(qDen q_1)² - 4 qDen (qDen q_0)`. -/
def dnRhs (k : ℕ) : KE := .sub (.mul (qE k 1) (qE k 1)) (.mul (.int (4 * qDenN k)) (qE k 0))

/-- Denominator of `β_k`. -/
def betaDenN (k : ℕ) : ℕ := betaDen.getD k 1

/-- Denominator of `γ_k`. -/
def gamDenN (k : ℕ) : ℕ := gamDen.getD k 1

/-- The coefficients of `betaDen · β_k`. -/
def betaL (k : ℕ) : List KE := (betaData.getD k []).map .lin

/-- The coefficients of `gamDen · γ_k`. -/
def gamL (k : ℕ) : List KE := (gamData.getD k []).map .lin

/-- A square root of `d_k` modulo `fRev_k` (theorem `β_sq_sub`). -/
noncomputable def β (k : Fin 2) : K21[X] := pQ (betaDenN k) (betaL k)

/-- The cofactor `γ_k = (β_k² - d_k) / fRev_k`. -/
noncomputable def γ (k : Fin 2) : K21[X] := pQ (gamDenN k) (gamL k)

/-- `4 gamDen · (qDen² (betaDen β)² - betaDen² (qDen² d))`. -/
def sqLhs (k : ℕ) : List KE :=
  smulP (.int ((4 * gamDenN k : ℕ) : ℤ))
    (subP (smulP (.int ((qDenN k * qDenN k : ℕ) : ℤ)) (mulP (betaL k) (betaL k)))
      (smulP (.int ((betaDenN k * betaDenN k : ℕ) : ℤ)) [.lin (dnL k)]))

/-- `betaDen² qDen² · (4 fRev) (gamDen γ)`. -/
def sqRhs (k : ℕ) : List KE :=
  smulP (.int ((betaDenN k * betaDenN k * (qDenN k * qDenN k) : ℕ) : ℤ))
    (mulP (frevL k) (gamL k))

/-! ## The known lifts -/

/-- zk coordinates of `r` at the known point `P_i`. -/
def liftR (i : ℕ) : List ℤ := (liftData.getD i []).getD 0 []

/-- zk coordinates of `s` at the known point `P_i`. -/
def liftS (i : ℕ) : List ℤ := (liftData.getD i []).getD 1 []

/-- `Q_(i+1)(a, b, c)` as an expression. -/
def qformE (i : Fin 3) (a b c : ℤ) : KE :=
  .add (.add (.add (.add (.add (.mul (.int (a * a)) (.lin (QcL i 0)))
    (.mul (.int (a * b)) (.lin (QcL i 1)))) (.mul (.int (a * c)) (.lin (QcL i 2))))
    (.mul (.int (b * b)) (.lin (QcL i 3)))) (.mul (.int (b * c)) (.lin (QcL i 4))))
    (.mul (.int (c * c)) (.lin (QcL i 5)))

/-- The three equations of `D_δ` at the known point `P_i = (a : b : c)` of the twist `k`:
`Q1 - δ r²`, `Q2 - δ r s`, `Q3 - δ s²`. -/
def liftEqs (i k : ℕ) (a b c : ℤ) : List KE :=
  [.sub (qformE 0 a b c) (.mul (.lin (dL k)) (.mul (.lin (liftR i)) (.lin (liftR i)))),
   .sub (qformE 1 a b c) (.mul (.lin (dL k)) (.mul (.lin (liftR i)) (.lin (liftS i)))),
   .sub (qformE 2 a b c) (.mul (.lin (dL k)) (.mul (.lin (liftS i)) (.lin (liftS i))))]

end FurioLombardo.Discharge.M3a.Bruin
