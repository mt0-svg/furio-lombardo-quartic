import FurioLombardo.Discharge.M3a.ConcreteDefs
import FurioLombardo.Discharge.SelmerBasis.SchaeferCertData

/-!
# Certificates of the global Schaefer lemma for `fRev k`: definitions

Data of SchaeferCertData.lean (code/selmer-global-bound/schaefer_certs.gp), all integral zk
coordinates (lane M1's `zkE`). Composition of coefficient lists (`compP`, `pK_compP`) and reflection
(`reflect_pK`) turn the changes of model of SchaeferModel.lean into list identities, and the
Kronecker expressions below are the identities the kernel checks (SchaeferCertCheck.lean):

* `compCheck`: `m1 · (4 fRev)(a + π X) = 4 π⁶ F` (`F = m1 f1`, `a = -469`);
* `bez1Check`: `A F + B F' = e1 F₆`, `eCheck`: `e1 e = 14 ^ N`;
* `revCheck`: `F2 = X⁶ F(i + 1/X)`, `bez2Check`: `A2 F2 + B2 F2' = R2`;
* `yzCheck`: `y m1 F₆ + z F2₆ R2 = 14 ^ N m1²`; `piCheck`: `π · (1317 / π) = 1317`.
-/

namespace FurioLombardo.Discharge.SelmerBasis.Cert

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3a.Bruin

/-! ## Composition and reflection of coefficient lists -/

/-- The coefficient list of `(pK l).comp (pK m)` (Horner). -/
def compP : List KE → List KE → List KE
  | [], _ => []
  | [e], _ => [e]
  | e :: a :: l, m => addP [e] (mulP m (compP (a :: l) m))

theorem pK_compP (m : List KE) : ∀ l : List KE, pK (compP l m) = (pK l).comp (pK m)
  | [] => by simp [compP]
  | [e] => by simp [compP]
  | e :: a :: l => by
    rw [compP, pK_addP, pK_mulP, pK_compP m (a :: l), pK_cons, pK_cons (e := e), pK_nil, add_comp,
      C_comp, mul_comp, X_comp]
    ring

theorem reflect_pK (n : ℕ) (l : List KE) (hl : l.length = n + 1) :
    reflect n (pK l) = pK l.reverse := by
  ext j
  rw [coeff_reflect, coeff_pK, coeff_pK]
  by_cases hj : j ≤ n
  · rw [revAt_le hj, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by omega)]
    congr 3
    omega
  · rw [revAt_eq_self_of_lt (by omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by simp; omega)]

/-! ## The data as expressions -/

/-- Integer coordinate lists as atoms. -/
def linL (l : List (List ℤ)) : List KE := l.map .lin

def m1N (k : ℕ) : ℕ := m1Data.getD k 1

def FL (k : ℕ) : List KE := linL (FData.getD k [])

def AL (k : ℕ) : List KE := linL (AData.getD k [])

def BL (k : ℕ) : List KE := linL (BData.getD k [])

def e1L (k : ℕ) : List ℤ := e1Data.getD k []

def eL (k : ℕ) : List ℤ := eData.getD k []

def F2L (k i : ℕ) : List KE := linL ((F2Data.getD k []).getD i [])

def A2L (k i : ℕ) : List KE := linL ((A2Data.getD k []).getD i [])

def B2L (k i : ℕ) : List KE := linL ((B2Data.getD k []).getD i [])

def R2L (k i : ℕ) : List ℤ := (R2Data.getD k []).getD i []

def yL (k i : ℕ) : List ℤ := (yData.getD k []).getD i []

def zL (k i : ℕ) : List ℤ := (zData.getD k []).getD i []

/-- The shift `a = -469` of the affine model. -/
def aE : KE := .int (-469)

/-- `π` as an atom. -/
def piE : KE := .lin piL

/-- `π`, a generator of `pr3 pr439`. -/
noncomputable def piK : K21 := zkE piL

/-! ## The identities checked by the kernel -/

/-- `m1 · (4 fRev)(a + π X) = 4 π⁶ F`. -/
def compCheck (k K : ℕ) : Bool :=
  eqCheck K (smulP (.int (m1N k)) (compP (frevL k) [aE, piE]))
    (smulP (.int 4) (smulP (piE.pow 6) (FL k)))

/-- `A F + B F' = e1 F₆`. -/
def bez1Check (k K : ℕ) : Bool :=
  eqCheck K (addP (mulP (AL k) (FL k)) (mulP (BL k) (derivP (FL k))))
    [.mul (.lin (e1L k)) ((FL k).getD 6 (.int 0))]

/-- `e1 e = 14 ^ N`. -/
def eCheck (k K : ℕ) : Bool :=
  checkK K (.sub (.mul (.lin (e1L k)) (.lin (eL k))) (.int (14 ^ expN)))

/-- `F2 = X⁶ F(i + 1/X)`. -/
def revCheck (k i K : ℕ) : Bool :=
  eqCheck K (compP (FL k) [.int i, .int 1]).reverse (F2L k i)

/-- `A2 F2 + B2 F2' = R2`. -/
def bez2Check (k i K : ℕ) : Bool :=
  eqCheck K (addP (mulP (A2L k i) (F2L k i)) (mulP (B2L k i) (derivP (F2L k i))))
    [.lin (R2L k i)]

/-- `y m1 F₆ + z F2₆ R2 = 14 ^ N m1²`. -/
def yzCheck (k i K : ℕ) : Bool :=
  checkK K (.sub (.add (.mul (.lin (yL k i)) (.mul (.int (m1N k)) ((FL k).getD 6 (.int 0))))
    (.mul (.lin (zL k i)) (.mul ((F2L k i).getD 6 (.int 0)) (.lin (R2L k i)))))
    (.int (14 ^ expN * (m1N k : ℤ) ^ 2)))

/-- `π · (1317 / π) = 1317`. -/
def piCheck (K : ℕ) : Bool := checkK K (.sub (.mul (.lin piL) (.lin piInvL)) (.int 1317))

end FurioLombardo.Discharge.SelmerBasis.Cert
