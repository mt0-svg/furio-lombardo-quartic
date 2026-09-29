import FurioLombardo.M1.Residue
import FurioLombardo.M1.DataGens

/-!
# The generators of K21(S,2) and the relations at 2, 7, 3, 439 (kernel checked)

`gO i` (`i < 18`) are the generators: `-1`, 11 fundamental units, `la, lb, lc` (the primes above 2),
`pi7`, `pi3`, `pi439` (DataGens.lean, from bnfinit; nothing here uses that they are fundamental).
The kernel checks (Kronecker test, `checkK`):
* `g_i * g_i' = 1` for `i < 12` and `e * e' = 1` for the unit cofactors `e2, et, e1, e7`;
* `2 = e2 la^3 lb^12 lc^6`, `θ = et lb^2`, `θ - 1 = e1 la^4 lc^3`, `7 = e7 pi7^7`;
* `la c0 = 2`, `lb c1 = 2`, `lc c2 = 2`, `pi7 c3 = 7`, `pi3 c4 = 3`, `pi439 c5 = 439`;
* `(θ^49 - θ) u7 = 1 + 7 v7`.
-/

namespace FurioLombardo.M1

open Polynomial NumberField Kron

/-- The `i`-th generator as an expression. -/
def gE (i : ℕ) : KE := .lin (gensL.getD i [])
/-- Inverse of the `i`-th generator (`i < 12`). -/
def gIE (i : ℕ) : KE := .lin (gensInvL.getD i [])
/-- Unit cofactor `e2, et, e1, e7`. -/
def eE (i : ℕ) : KE := .lin (unitsL.getD i [])
/-- Inverse of the unit cofactor. -/
def eIE (i : ℕ) : KE := .lin (unitsInvL.getD i [])
/-- The cofactors `2/la, 2/lb, 2/lc, 7/pi7, 3/pi3, 439/pi439`. -/
def cE (i : ℕ) : KE := .lin (cofL.getD i [])
/-- `θ`. -/
def θE : KE := .lin (unitL 2)

/-- The prime generators among the 18 (`la, lb, lc, pi7, pi3, pi439`). -/
def primeIdx : List ℕ := [12, 13, 14, 15, 16, 17]
/-- The primes they divide. -/
def primeOf : List ℤ := [2, 2, 2, 7, 3, 439]

/-! ## Kernel checks -/

theorem ck_units : ((List.range 12).all fun i =>
    checkK 1024 (.sub (.mul (gE i) (gIE i)) (.int 1))) = true := by decide +kernel
theorem ck_cof_units : ((List.range 4).all fun i =>
    checkK 2048 (.sub (.mul (eE i) (eIE i)) (.int 1))) = true := by decide +kernel
theorem ck_two : checkK 8192
    (.sub (.int 2) (KE.prod [eE 0, (gE 12).pow 3, (gE 13).pow 12, (gE 14).pow 6])) = true := by
  decide +kernel
theorem ck_θ : checkK 2048 (.sub θE (.mul (eE 1) ((gE 13).pow 2))) = true := by decide +kernel
theorem ck_θ_sub_one : checkK 4096
    (.sub (.sub θE (.int 1)) (KE.prod [eE 2, (gE 12).pow 4, (gE 14).pow 3])) = true := by
  decide +kernel
theorem ck_seven : checkK 4096 (.sub (.int 7) (.mul (eE 3) ((gE 15).pow 7))) = true := by
  decide +kernel
theorem ck_cof : ((List.range 6).all fun i =>
    checkK 1024 (.sub (.mul (gE (primeIdx.getD i 0)) (cE i)) (.int (primeOf.getD i 0)))) = true := by
  decide +kernel
theorem ck_res7 : checkK 8192 (.sub (.mul (.sub (θE.pow 49) θE) (.lin u7L))
    (.add (.int 1) (.mul (.int 7) (.lin v7L)))) = true := by decide +kernel

/-! ## The elements in `𝓞 K21` -/

/-- The `i`-th generator in `𝓞 K21`. -/
noncomputable def gO (i : ℕ) : 𝓞 K21 := zkO (gensL.getD i [])
/-- The inverse of the `i`-th generator (`i < 12`). -/
noncomputable def gIO (i : ℕ) : 𝓞 K21 := zkO (gensInvL.getD i [])
/-- The unit cofactors. -/
noncomputable def eO (i : ℕ) : 𝓞 K21 := zkO (unitsL.getD i [])
/-- Their inverses. -/
noncomputable def eIO (i : ℕ) : 𝓞 K21 := zkO (unitsInvL.getD i [])
/-- The cofactors. -/
noncomputable def cO (i : ℕ) : 𝓞 K21 := zkO (cofL.getD i [])

@[simp] theorem evK_gE (i : ℕ) : evK (gE i) = ((gO i : 𝓞 K21) : K21) := rfl
@[simp] theorem evK_gIE (i : ℕ) : evK (gIE i) = ((gIO i : 𝓞 K21) : K21) := rfl
@[simp] theorem evK_eE (i : ℕ) : evK (eE i) = ((eO i : 𝓞 K21) : K21) := rfl
@[simp] theorem evK_eIE (i : ℕ) : evK (eIE i) = ((eIO i : 𝓞 K21) : K21) := rfl
@[simp] theorem evK_cE (i : ℕ) : evK (cE i) = ((cO i : 𝓞 K21) : K21) := rfl

theorem zkNum_two : zkNum.getD 2 [] = 0 :: (Dz : ℤ) :: List.replicate 19 0 := by decide +kernel

theorem zkE_unitL_two : zkE (unitL 2) = θ := by
  rw [← wK, wK_eq 2 (by norm_num), zkNum_two, wv]
  simp [evalL, List.replicate]
  linear_combination θ * dInv_mul

@[simp] theorem evK_θE : evK θE = ((θO : 𝓞 K21) : K21) := zkE_unitL_two

theorem gO_mul_gIO (i : ℕ) (hi : i < 12) : gO i * gIO i = 1 := by
  apply RingOfIntegers.coe_injective
  have h := List.all_eq_true.mp ck_units i (List.mem_range.mpr hi)
  simpa using evK_eq_of_check _ _ _ h

theorem eO_mul_eIO (i : ℕ) (hi : i < 4) : eO i * eIO i = 1 := by
  apply RingOfIntegers.coe_injective
  have h := List.all_eq_true.mp ck_cof_units i (List.mem_range.mpr hi)
  simpa using evK_eq_of_check _ _ _ h

theorem two_eq : (2 : 𝓞 K21) = eO 0 * gO 12 ^ 3 * gO 13 ^ 12 * gO 14 ^ 6 := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_two
  simp [evK_prod, evK_pow] at h
  simp only [map_mul, map_pow, map_ofNat]
  rw [h]; ring

theorem θO_eq : θO = eO 1 * gO 13 ^ 2 := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_θ
  simp [evK_pow] at h
  simp only [map_mul, map_pow]
  exact h

theorem θO_sub_one_eq : θO - 1 = eO 2 * gO 12 ^ 4 * gO 14 ^ 3 := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_θ_sub_one
  simp [evK_prod, evK_pow] at h
  simp only [map_mul, map_pow, map_sub, map_one]
  rw [show (algebraMap (𝓞 K21) K21) θO = θ from rfl, h]; ring

theorem seven_eq : (7 : 𝓞 K21) = eO 3 * gO 15 ^ 7 := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_seven
  simp [evK_pow] at h
  simp only [map_mul, map_pow, map_ofNat]
  exact h

theorem gO_mul_cO (i : ℕ) (hi : i < 6) :
    gO (primeIdx.getD i 0) * cO i = (primeOf.getD i 0 : 𝓞 K21) := by
  apply RingOfIntegers.coe_injective
  have h := List.all_eq_true.mp ck_cof i (List.mem_range.mpr hi)
  have := evK_eq_of_check _ _ _ h
  simp only [evK_mul, evK_gE, evK_cE, evK_int] at this
  simp only [map_mul, map_intCast]
  exact this

theorem residue_seven :
    (θO ^ 49 - θO) * zkO u7L = 1 + 7 * zkO v7L := by
  apply RingOfIntegers.coe_injective
  have h := evK_eq_of_check _ _ _ ck_res7
  simp [evK_pow] at h
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat]
  exact h

end FurioLombardo.M1
