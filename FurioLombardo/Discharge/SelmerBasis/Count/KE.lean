import FurioLombardo.Discharge.SelmerBasis.Count.Base
import FurioLombardo.Discharge.M3a.PolyK
import FurioLombardo.Discharge.M3a.ConcreteDefs
import FurioLombardo.Discharge.M3a.LocalFacts
import FurioLombardo.Discharge.SelmerBasis.Count.Tors

/-!
# Count lane: Kronecker expressions of the translates of `fRev k`

For a global abscissa `x = evK xE` (lane M1's `KE`): `shiftP` shifts a coefficient list by `x`
(Horner's scheme, `pK_shiftP`), `gE k xE j` is the expression of coefficient `j` of `4 fRev_k(X + x)`
(`gAt_coeff_eq`, `fRev_eval_eq`), and `nE k xE` that of `4⁴ nAt k x` (`nAt_eq`), so one Kronecker
test `nE · ν = D`, `D ≠ 0`, proves `nAt k x ≠ 0` (`nAt_ne_zero_of_check`). Square classes: `4 c k`,
`46² d k` and `46² ndK 1` are the atoms `FE k 0`, `dnL k`, `zL 1 2` (`four_mul_c`, `d_mul`, `ndK_mul`).
-/

set_option autoImplicit false

open Polynomial
open FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
open FurioLombardo.Discharge.M3a.Bruin (fRev frevL FE c d dnL qDenN zQ zL zM)
open FurioLombardo.Discharge.M3a (QE)
open FurioLombardo.Vendor.Toolbox.G2Formal.Taylor (tN0)

namespace FurioLombardo.Discharge.SelmerBasis.Count

/-- The coefficient list of `p(X + x)` from that of `p` (Horner's scheme). -/
def shiftP (xE : KE) : List KE → List KE
  | [] => []
  | a :: l => addP [a] (mulP [xE, .int 1] (shiftP xE l))

theorem pK_shiftP (xE : KE) : ∀ l : List KE, pK (shiftP xE l) = (pK l).comp (X + C (evK xE))
  | [] => by simp [shiftP]
  | a :: l => by
    rw [shiftP, pK_addP, pK_mulP, pK_shiftP xE l, pK_cons, pK_cons, pK_cons, pK_cons, pK_nil]
    simp only [evK_int, Int.cast_one, map_one, mul_zero, add_zero, mul_one, add_comp, C_comp,
      mul_comp, X_comp]
    ring

/-- The expression of coefficient `j` of `4 fRev_k (X + x)`, `x = evK xE`. -/
def gE (k : ℕ) (xE : KE) (j : ℕ) : KE := (shiftP xE (frevL k)).getD j (.int 0)

theorem gAt_coeff_eq (k : Fin 2) (xE : KE) (j : ℕ) :
    4 * (gAt k (evK xE)).coeff j = evK (gE k xE j) := by
  have h : gAt k (evK xE) = pQ 4 (shiftP xE (frevL k)) := by
    rw [gAt, fRev, pQ, pQ, mul_comp, C_comp, pK_shiftP]
  rw [h, coeff_pQ, gE, ← mul_assoc, Nat.cast_ofNat, mul_inv_cancel₀ (by norm_num), one_mul]

theorem fRev_eval_eq (k : Fin 2) (xE : KE) :
    4 * (fRev k).eval (evK xE) = evK (gE k xE 0) := by
  rw [← gAt_coeff_eq, gAt_coeff_zero]

/-- `tN0` as an expression. -/
def tN0E (c0 c1 c2 c3 c4 : KE) : KE :=
  .sub (.add (.sub (.sub (.mul (.int 64) (.mul (.mul (.mul c0 c0) c0) c4))
    (.mul (.int 16) (.mul (.mul c0 c0) (.mul c2 c2))))
    (.mul (.int 32) (.mul (.mul (.mul c0 c0) c1) c3)))
    (.mul (.int 24) (.mul (.mul (.mul c0 c1) c1) c2)))
    (.mul (.int 5) (.mul (.mul (.mul c1 c1) c1) c1))

theorem evK_tN0E (c0 c1 c2 c3 c4 : KE) :
    evK (tN0E c0 c1 c2 c3 c4) = tN0 (evK c0) (evK c1) (evK c2) (evK c3) (evK c4) := by
  simp only [tN0E, tN0, evK_sub, evK_add, evK_mul, evK_int]; push_cast; ring

/-- The expression of `4⁴ nAt k x`. -/
def nE (k : ℕ) (xE : KE) : KE :=
  tN0E (gE k xE 0) (gE k xE 1) (gE k xE 2) (gE k xE 3) (gE k xE 4)

theorem nAt_eq (k : Fin 2) (xE : KE) : 256 * nAt k (evK xE) = evK (nE k xE) := by
  rw [nE, evK_tN0E, ← gAt_coeff_eq, ← gAt_coeff_eq, ← gAt_coeff_eq, ← gAt_coeff_eq, ← gAt_coeff_eq,
    nAt]
  simp only [tN0]; ring

/-- `nAt k x ≠ 0` from `4⁴ nAt · ν = D`, `D ≠ 0`. -/
theorem nAt_ne_zero_of_check (k : Fin 2) (xE : KE) (νL : List ℤ) (D : ℤ) (hD : D ≠ 0) (N : ℕ)
    (h : checkK N (.sub (.mul (nE k xE) (.lin νL)) (.int D)) = true) : nAt k (evK xE) ≠ 0 := by
  intro h0
  have e := evK_eq_of_check _ _ _ h
  simp only [evK_mul, evK_lin, evK_int, ← nAt_eq, h0, mul_zero, zero_mul] at e
  exact hD (by exact_mod_cast e.symm)

theorem four_mul_c (k : Fin 2) : 4 * c k = evK (FE k 0) := by
  rw [c, ← mul_assoc, mul_inv_cancel₀ (by norm_num), one_mul]

theorem qDenN_eq (k : Fin 2) : qDenN k = 46 := by fin_cases k <;> rfl

theorem d_mul (k : Fin 2) : (46 : K21) ^ 2 * d k = zkE (dnL k) := by
  rw [Bruin.d_eq, qDenN_eq, ← mul_assoc, Nat.cast_mul, Nat.cast_ofNat, ← sq,
    mul_inv_cancel₀ (by norm_num), one_mul]

theorem ndK_mul : (46 : K21) ^ 2 * ndK 1 = zkE (zL 1 2) := by
  rw [ndK_eq, Bruin.zQ, QE.ev_atom, show zM ((1 : Fin 2) : ℕ) 2 = 46 ^ 2 from rfl, ← mul_assoc,
    Nat.cast_pow, Nat.cast_ofNat, mul_inv_cancel₀ (by norm_num), one_mul]
  rfl

end FurioLombardo.Discharge.SelmerBasis.Count
