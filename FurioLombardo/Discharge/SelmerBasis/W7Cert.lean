import FurioLombardo.Discharge.SelmerBasis.W7Gen
import FurioLombardo.Discharge.SelmerBasis.W7Spec
import FurioLombardo.Discharge.SelmerBasis.PlaceWCert

/-!
# Soundness of the certificates of W7Spec.lean (lane selmer-p7)

Generic over a complete ultrametric field `F` with a ring hom `σ : K21 →+* F` under which every zk list is
integral (`hint`) and `π = σ al7` is a norm uniformizer with `‖2‖ = 1` (at `w7`: W7Model.lean).

* `evK_alPw`: `alPw tab d` evaluates to `al7 ^ d` when `tab` is the table of squarings;
* `unitOK_eq`, `norm_unit`: a unit certificate gives `‖σ U‖ = 1`;
* `norm_evK_le_one`: every `KE` value is integral;
* `KCert.sound`: a passing `KCert` makes `x · π^a0 · (-1)^a1` a square for every `x` within `‖π‖^N` of
  `σ X`;
* `FCert.sound`: the same at `F' = QF F A 0` (`‖A‖ = ‖π‖`, `A` within `‖π‖^N` of `σ (al7 E4U)`);
* `PtSq.sound`: `fRev_1(x)` is a nonzero square at `σ`;
* the approximations: `norm_XLp_sub`, `norm_XLm_sub`, `norm_XNs_sub` (the values of `ι₊`, `ι₋`,
  `ι_N (±)` against `σ` of the expressions), `iota'_evN` (the coordinates of `ι'` in `F'`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.SelmerBasis
  FurioLombardo.Discharge.SelmerBasis.Tower FurioLombardo.Discharge.M3b FurioLombardo.Discharge
open FurioLombardo.M2.Special (al7)

namespace FurioLombardo.Discharge.SelmerBasis.W7

/-! ## Algebra of the checks -/

theorem powOK_sq {tab : List (List ℤ)} {k i : ℕ} (h : powOK tab k i = true) :
    zkE (tab.getD (i + 1) []) = zkE (tab.getD i []) ^ 2 := by
  unfold powOK at h
  have e := evK_eq_of_check _ _ _ h
  simp only [evK_mul, evK_lin] at e
  rw [← e, sq]

/-- `alPw tab d = c ^ d` when `tab_i` evaluates to `c ^ 2 ^ i`. -/
theorem evK_alPw_aux : ∀ (c : K21) (tab : List (List ℤ)),
    (∀ i, i < tab.length → zkE (tab.getD i []) = c ^ 2 ^ i) →
    ∀ d, d < 2 ^ tab.length → evK (alPw tab d) = c ^ d
  | c, [], _, d, hd => by
    have hd0 : d = 0 := by simpa using hd
    subst hd0
    simp [alPw, evK_int]
  | c, P :: tab, h, d, hd => by
    have hP : zkE P = c := by simpa using h 0 (by simp)
    have ih := evK_alPw_aux (c ^ 2) tab (fun i hi => by
      have hi' := h (i + 1) (by simp only [List.length_cons]; omega)
      rw [List.getD_cons_succ] at hi'
      rw [hi', ← pow_mul, ← pow_succ'])
    have hd2 : d / 2 < 2 ^ tab.length := by
      simp only [List.length_cons, pow_succ] at hd
      omega
    unfold alPw
    split_ifs with e0 e1 e2
    · subst e0
      simp [evK_int]
    · have hd1 : d = 1 := by omega
      subst hd1
      rw [evK_lin, hP, pow_one]
    · rw [evK_mul, evK_lin, hP, ih _ hd2, ← pow_mul, ← pow_succ']
      congr 1
      omega
    · rw [ih _ hd2, ← pow_mul]
      congr 1
      omega

/-- **`alPw tab d = al7 ^ d`** for the table of squarings of `al7`. -/
theorem evK_alPw {tab : List (List ℤ)} (h0 : tab.getD 0 [] = al7)
    (hsq : ∀ i, i + 1 < tab.length → zkE (tab.getD (i + 1) []) = zkE (tab.getD i []) ^ 2) {d : ℕ}
    (hd : d < 2 ^ tab.length) : evK (alPw tab d) = zkE al7 ^ d := by
  refine evK_alPw_aux _ tab (fun i hi => ?_) d hd
  induction i with
  | zero => rw [h0, pow_zero, pow_one]
  | succ i ih => rw [hsq i hi, ih (by omega), ← pow_mul, ← pow_succ]

theorem unitOK_eq {k : ℕ} {U Ui Uc : List ℤ} (h : unitOK k U Ui Uc = true) :
    zkE U * zkE Ui = 1 + zkE al7 * zkE Uc := by
  unfold unitOK at h
  have e := evK_eq_of_check _ _ _ h
  simpa only [evK_mul, evK_lin, evK_add, evK_int, Int.cast_one] using e

theorem evK_sgnE (b : Bool) : evK (sgnE b) = (-1) ^ (if b then 1 else 0) := by
  cases b <;> simp [sgnE]

theorem bitv2_vals : bitv 2 0 = ![0, 0] ∧ bitv 2 1 = ![1, 0] ∧ bitv 2 2 = ![0, 1] ∧
    bitv 2 3 = ![1, 1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Norms at a place -/

section Place

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (σ : K21 →+* F)
  (hint : ∀ a : List ℤ, ‖σ (zkE a)‖ ≤ 1)

include hint in
/-- Every `KE` value is integral. -/
theorem norm_evK_le_one (e : KE) : ‖σ (evK e)‖ ≤ 1 :=
  SelmerBasis.norm_evK_le_one σ hint e

include hint in
/-- A unit certificate gives a unit. -/
theorem norm_unit (hπ : NormUnif (σ (zkE al7))) {k : ℕ} {U Ui Uc : List ℤ}
    (h : unitOK k U Ui Uc = true) : ‖σ (zkE U)‖ = 1 := by
  have e := congrArg σ (unitOK_eq h)
  simp only [map_mul, map_add, map_one] at e
  have hs : ‖σ (zkE al7) * σ (zkE Uc)‖ < 1 := by
    rw [norm_mul]
    calc ‖σ (zkE al7)‖ * ‖σ (zkE Uc)‖ ≤ ‖σ (zkE al7)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hint Uc) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hπ.norm_lt_one
  have h1 : ‖σ (zkE U)‖ * ‖σ (zkE Ui)‖ = 1 := by
    rw [← norm_mul, e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hs.ne'),
      norm_one, max_eq_left hs.le]
  have hU := hint U
  have hUi := hint Ui
  refine le_antisymm hU ?_
  nlinarith [norm_nonneg (σ (zkE U)), norm_nonneg (σ (zkE Ui))]

end Place

/-! ## Soundness of the square certificates -/

section Sound

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [ProperSpace F]
  (σ : K21 →+* F) (hint : ∀ a : List ℤ, ‖σ (zkE a)‖ ≤ 1) (hπ : NormUnif (σ (zkE al7)))
  (h2 : ‖(2 : F)‖ = 1) {tab : List (List ℤ)} (h0 : tab.getD 0 [] = al7)
  (hsq : ∀ i, i + 1 < tab.length → zkE (tab.getD (i + 1) []) = zkE (tab.getD i []) ^ 2)

include hint hπ h2 h0 hsq in
/-- **A `KCert` at a component `F`.** -/
theorem KCert.sound {N : ℕ} {X : KE} {c : KCert} (hc : c.ok tab N X = true) {x : F}
    (hx : ‖x - σ (evK X)‖ ≤ ‖σ (zkE al7)‖ ^ N) :
    IsSquare (x * ∏ i : Fin 2, ![σ (zkE al7), -1] i ^ (bitv 2 c.bits i).val) := by
  obtain ⟨a0, a1, h, U, Ui, Uc, n, R, k1, k2⟩ := c
  simp only [KCert.ok, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hhn, hhN⟩, hn⟩, hk⟩, hu⟩ := hc
  have e := evK_eq_of_check _ _ _ hk
  have hA : evK (if a0 then KE.lin al7 else KE.int 1) = zkE al7 ^ (if a0 then 1 else 0) := by
    cases a0 <;> simp
  simp only [evK_mul, evK_add, evK_lin, hA, evK_sgnE,
    evK_alPw h0 hsq (show 2 * h < 2 ^ tab.length by omega), evK_alPw h0 hsq hn] at e
  have eσ := congrArg σ e
  simp only [map_mul, map_add, map_pow, map_neg, map_one] at eσ
  have hU1 : ‖σ (zkE U)‖ = 1 := norm_unit σ hint hπ hu
  have hπ0 : 0 < ‖σ (zkE al7)‖ := norm_pos_iff.mpr hπ.ne_zero
  have hπ1 := hπ.norm_lt_one
  have hU0 : σ (zkE U) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hU1; exact zero_ne_one hU1
  have hs0 : σ (zkE al7) ^ h * σ (zkE U) ≠ 0 := mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hU0
  have hs2 : ‖σ (zkE al7) ^ h * σ (zkE U)‖ ^ 2 = ‖σ (zkE al7)‖ ^ (2 * h) := by
    rw [norm_mul, norm_pow, hU1, mul_one, ← pow_mul, mul_comm]
  have hprod : ∏ i : Fin 2, ![σ (zkE al7), -1] i ^
      (bitv 2 (KCert.bits ⟨a0, a1, h, U, Ui, Uc, n, R, k1, k2⟩) i).val =
      σ (zkE al7) ^ (if a0 then 1 else 0) * (-1) ^ (if a1 then 1 else 0) := by
    have v1 : (1 : ZMod 2).val = 1 := rfl
    obtain ⟨b0, b1, b2, b3⟩ := bitv2_vals
    rw [Fin.prod_univ_two]
    cases a0 <;> cases a1 <;> simp [KCert.bits, b0, b1, b2, b3, v1]
  rw [hprod, ← mul_assoc]
  refine isSquare_of_near hπ h2 hs0
    (X := σ (evK X) * σ (zkE al7) ^ (if a0 then 1 else 0) * (-1) ^ (if a1 then 1 else 0)) ?_ ?_
  · rw [← sub_mul, ← sub_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
      mul_one, hs2]
    calc ‖x - σ (evK X)‖ * ‖σ (zkE al7)‖ ^ (if a0 then 1 else 0) ≤ ‖σ (zkE al7)‖ ^ N * 1 :=
          mul_le_mul hx (pow_le_one₀ (norm_nonneg _) hπ1.le) (by positivity) (by positivity)
      _ < ‖σ (zkE al7)‖ ^ (2 * h) := by
          rw [mul_one]; exact pow_lt_pow_right_of_lt_one₀ hπ0 hπ1 hhN
  · rw [eσ, hs2]
    have hsq' : σ (zkE al7) ^ (2 * h) * (σ (zkE U) * σ (zkE U)) + σ (zkE al7) ^ n * σ (zkE R) -
        (σ (zkE al7) ^ h * σ (zkE U)) ^ 2 = σ (zkE al7) ^ n * σ (zkE R) := by ring
    rw [hsq', norm_mul, norm_pow]
    calc ‖σ (zkE al7)‖ ^ n * ‖σ (zkE R)‖ ≤ ‖σ (zkE al7)‖ ^ n * 1 :=
          mul_le_mul_of_nonneg_left (hint R) (by positivity)
      _ < ‖σ (zkE al7)‖ ^ (2 * h) := by
          rw [mul_one]; exact pow_lt_pow_right_of_lt_one₀ hπ0 hπ1 hhn

omit [CompleteSpace F] [ProperSpace F] in
theorem norm_pow_sub_pow_le {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ∀ j : ℕ, ‖a ^ j - b ^ j‖ ≤ ‖a - b‖
  | 0 => by simp
  | j + 1 => by
    have e : a ^ (j + 1) - b ^ (j + 1) = (a - b) * a ^ j + b * (a ^ j - b ^ j) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow]
      calc ‖a - b‖ * ‖a‖ ^ j ≤ ‖a - b‖ * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ha) (norm_nonneg _)
        _ = ‖a - b‖ := mul_one _
    · rw [norm_mul]
      calc ‖b‖ * ‖a ^ j - b ^ j‖ ≤ 1 * ‖a - b‖ :=
            mul_le_mul hb (norm_pow_sub_pow_le ha hb j) (norm_nonneg _) zero_le_one
        _ = ‖a - b‖ := one_mul _

omit [ProperSpace F] in
theorem qf_mul_Z {A : F} [Fact (∀ r : F, r ^ 2 ≠ A + 0 * r)] (x y : F) :
    QF.mk F A 0 x y * QF.mk F A 0 0 1 = QF.mk F A 0 (A * y) x := by
  change (⟨x, y⟩ : QuadraticAlgebra F A 0) * ⟨0, 1⟩ = ⟨A * y, x⟩
  ext
  · simp only [QuadraticAlgebra.re_mul]; ring
  · simp only [QuadraticAlgebra.im_mul]; ring

omit [ProperSpace F] in
theorem qf_mul_neg_one {A : F} [Fact (∀ r : F, r ^ 2 ≠ A + 0 * r)] (x y : F) :
    QF.mk F A 0 x y * (-1) = QF.mk F A 0 (x * -1) (y * -1) := by
  change (⟨x, y⟩ : QuadraticAlgebra F A 0) * (-1) = ⟨x * -1, y * -1⟩
  ext
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]; ring
  · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]; ring

omit [ProperSpace F] in
theorem qf_Z_sq {A : F} [Fact (∀ r : F, r ^ 2 ≠ A + 0 * r)] :
    QF.mk F A 0 0 1 * QF.mk F A 0 0 1 = algebraMap F (QF F A 0) A := by
  rw [qf_mul_Z, mul_one]
  change (⟨A, 0⟩ : QuadraticAlgebra F A 0) = algebraMap F (QuadraticAlgebra F A 0) A
  exact QuadraticAlgebra.ext (QuadraticAlgebra.algebraMap_re (a := A) (b := 0) A).symm
    (QuadraticAlgebra.algebraMap_im (a := A) (b := 0) A).symm

include hint hπ h2 in
/-- The core of `FCert.sound`: `x' ε + y' ε Z` is a square when `x'` is near `ξ`, `ξ ε` near
`A^j (π^h U)²`, and `y'` near `η = π^(j+2h) Ry`. -/
theorem fcert_core {A : F} [Fact (∀ r : F, r ^ 2 ≠ A + 0 * r)] (hA : ‖A‖ = ‖σ (zkE al7)‖) {N : ℕ}
    {E4U : List ℤ} (hAE : ‖A - σ (zkE al7 * zkE E4U)‖ ≤ ‖σ (zkE al7)‖ ^ N) {j h n : ℕ}
    (hjn : j + 2 * h < n) (hjN : j + 2 * h < N) {U R Ry : List ℤ} (hU1 : ‖σ (zkE U)‖ = 1)
    {ε x' y' ξ η : F} (hε : ‖ε‖ = 1) (hx' : ‖x' - ξ‖ ≤ ‖σ (zkE al7)‖ ^ N)
    (hy' : ‖y' - η‖ ≤ ‖σ (zkE al7)‖ ^ N)
    (hξ : ξ * ε = σ (zkE al7) ^ (j + 2 * h) * σ (zkE E4U) ^ j * (σ (zkE U) * σ (zkE U)) +
      σ (zkE al7) ^ n * σ (zkE R))
    (hη : η = σ (zkE al7) ^ (j + 2 * h) * σ (zkE Ry)) :
    IsSquare (QF.mk F A 0 (x' * ε) (y' * ε)) := by
  have hπ0 : 0 < ‖σ (zkE al7)‖ := norm_pos_iff.mpr hπ.ne_zero
  have hπ1 := hπ.norm_lt_one
  have hA0 : A ≠ 0 := by rw [← norm_pos_iff, hA]; exact hπ0
  have hU0 : σ (zkE U) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hU1; exact zero_ne_one hU1
  have hB : ‖(0 : F)‖ < 1 := by rw [norm_zero]; exact one_pos
  set t := A ^ j * (σ (zkE al7) ^ h * σ (zkE U)) ^ 2 with ht_def
  have htn : ‖t‖ = ‖σ (zkE al7)‖ ^ (j + 2 * h) := by
    rw [ht_def, norm_mul, norm_pow, norm_pow, norm_mul, norm_pow, hA, hU1, mul_one]; ring
  have htpos : 0 < ‖t‖ := by rw [htn]; positivity
  have ht0 : t ≠ 0 := norm_pos_iff.mp htpos
  have hsq : IsSquare (algebraMap F (QF F A 0) t) := by
    refine ⟨QF.mk F A 0 0 1 ^ j * algebraMap F (QF F A 0) (σ (zkE al7) ^ h * σ (zkE U)), ?_⟩
    have e : QF.mk F A 0 0 1 ^ j * algebraMap F (QF F A 0) (σ (zkE al7) ^ h * σ (zkE U)) *
        (QF.mk F A 0 0 1 ^ j * algebraMap F (QF F A 0) (σ (zkE al7) ^ h * σ (zkE U))) =
        (QF.mk F A 0 0 1 * QF.mk F A 0 0 1) ^ j *
          algebraMap F (QF F A 0) ((σ (zkE al7) ^ h * σ (zkE U)) ^ 2) := by
      rw [map_pow]; ring
    rw [e, qf_Z_sq, ← map_pow, ← map_mul]
  have hbound : ∀ k : ℕ, j + 2 * h < k → ‖σ (zkE al7)‖ ^ k < ‖t‖ := fun k hk => by
    rw [htn]; exact pow_lt_pow_right_of_lt_one₀ hπ0 hπ1 hk
  have hNt := hbound N hjN
  refine qfE_isSquare_of_cert hπ hA hB h2 ht0 hsq ?_ ?_
  · have e : x' * ε - t = (x' - ξ) * ε + σ (zkE al7) ^ (2 * h) * (σ (zkE U) * σ (zkE U)) *
        ((σ (zkE al7 * zkE E4U)) ^ j - A ^ j) + σ (zkE al7) ^ n * σ (zkE R) := by
      rw [sub_mul, hξ, ht_def, map_mul]; ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
      · rw [norm_mul, hε, mul_one]; exact hx'.trans_lt hNt
      · rw [norm_mul, norm_mul, norm_pow, norm_mul, hU1, mul_one]
        have hAle : ‖A‖ ≤ 1 := by rw [hA]; exact hπ1.le
        have hEle : ‖σ (zkE al7 * zkE E4U)‖ ≤ 1 := by
          rw [map_mul, norm_mul]
          exact (mul_le_mul hπ1.le (hint E4U) (norm_nonneg _) zero_le_one).trans (one_mul 1).le
        have hAE' : ‖σ (zkE al7 * zkE E4U) - A‖ ≤ ‖σ (zkE al7)‖ ^ N := by
          rw [norm_sub_rev]; exact hAE
        have hd := (norm_pow_sub_pow_le hEle hAle j).trans hAE'
        calc ‖σ (zkE al7)‖ ^ (2 * h) * 1 * ‖σ (zkE al7 * zkE E4U) ^ j - A ^ j‖ ≤
              1 * 1 * ‖σ (zkE al7)‖ ^ N :=
            mul_le_mul (mul_le_mul (pow_le_one₀ (norm_nonneg _) hπ1.le) le_rfl zero_le_one zero_le_one)
              hd (norm_nonneg _) (by norm_num)
          _ < ‖t‖ := by rw [one_mul, one_mul]; exact hNt
    · rw [norm_mul, norm_pow]
      calc ‖σ (zkE al7)‖ ^ n * ‖σ (zkE R)‖ ≤ ‖σ (zkE al7)‖ ^ n * 1 :=
            mul_le_mul_of_nonneg_left (hint R) (by positivity)
        _ < ‖t‖ := by rw [mul_one]; exact hbound n hjn
  · have hZ1 : ‖QF.mk F A 0 0 1‖ < 1 := qfE_Y_lt_one hπ hA hB
    have hy1 : ‖y'‖ ≤ ‖t‖ := by
      have e : y' = (y' - η) + η := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy'.trans hNt.le) ?_)
      rw [hη, norm_mul, norm_pow, htn]
      calc ‖σ (zkE al7)‖ ^ (j + 2 * h) * ‖σ (zkE Ry)‖ ≤ ‖σ (zkE al7)‖ ^ (j + 2 * h) * 1 :=
            mul_le_mul_of_nonneg_left (hint Ry) (by positivity)
        _ = _ := mul_one _
    rw [norm_mul, hε, mul_one]
    calc ‖y'‖ * ‖QF.mk F A 0 0 1‖ ≤ ‖t‖ * ‖QF.mk F A 0 0 1‖ :=
          mul_le_mul_of_nonneg_right hy1 (norm_nonneg _)
      _ < ‖t‖ * 1 := mul_lt_mul_of_pos_left hZ1 htpos
      _ = ‖t‖ := mul_one _

include hint hπ h2 h0 hsq in
/-- **An `FCert` at `F' = QF F A 0`.** -/
theorem FCert.sound {A : F} [Fact (∀ r : F, r ^ 2 ≠ A + 0 * r)] (hA : ‖A‖ = ‖σ (zkE al7)‖) {N : ℕ}
    {E4U : List ℤ} (hAE : ‖A - σ (zkE al7 * zkE E4U)‖ ≤ ‖σ (zkE al7)‖ ^ N) {X Y : KE} {c : FCert}
    (hc : c.ok tab N E4U X Y = true) {x y : F} (hx : ‖x - σ (evK X)‖ ≤ ‖σ (zkE al7)‖ ^ N)
    (hy : ‖y - σ (evK Y)‖ ≤ ‖σ (zkE al7)‖ ^ N) :
    IsSquare (QF.mk F A 0 x y * ∏ i : Fin 2, ![QF.mk F A 0 0 1, -1] i ^ (bitv 2 c.bits i).val) := by
  obtain ⟨a0, a1, j, h, U, Ui, Uc, n, R, Ry, k1, k2, k3⟩ := c
  simp only [FCert.ok, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hjn, hjN⟩, hn⟩, hk1⟩, hu⟩, hk3⟩ := hc
  have hU1 : ‖σ (zkE U)‖ = 1 := norm_unit σ hint hπ hu
  have e1 := evK_eq_of_check _ _ _ hk1
  have e3 := evK_eq_of_check _ _ _ hk3
  simp only [evK_mul, evK_add, evK_lin, evK_pow, evK_sgnE,
    evK_alPw h0 hsq (show j + 2 * h < 2 ^ tab.length by omega), evK_alPw h0 hsq hn] at e1 e3
  have e1σ := congrArg σ e1
  have e3σ := congrArg σ e3
  simp only [map_mul, map_add, map_pow, map_neg, map_one] at e1σ e3σ
  have hπ1 := hπ.norm_lt_one
  have hδ1 : ‖σ (zkE al7)‖ ^ N ≤ 1 := pow_le_one₀ (norm_nonneg _) hπ1.le
  have v1 : (1 : ZMod 2).val = 1 := rfl
  obtain ⟨b0, b1, b2, b3⟩ := bitv2_vals
  have hy1 : ‖y‖ ≤ 1 := by
    have e : y = (y - σ (evK Y)) + σ (evK Y) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hy.trans hδ1) (norm_evK_le_one σ hint Y))
  have hAy : ‖A * y - σ (zkE al7) * σ (zkE E4U) * σ (evK Y)‖ ≤ ‖σ (zkE al7)‖ ^ N := by
    have e : A * y - σ (zkE al7) * σ (zkE E4U) * σ (evK Y) =
        (A - σ (zkE al7 * zkE E4U)) * y + σ (zkE al7 * zkE E4U) * (y - σ (evK Y)) := by
      rw [map_mul]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖A - σ (zkE al7 * zkE E4U)‖ * ‖y‖ ≤ ‖σ (zkE al7)‖ ^ N * 1 :=
            mul_le_mul hAE hy1 (norm_nonneg _) (by positivity)
        _ = _ := mul_one _
    · rw [norm_mul]
      have hE : ‖σ (zkE al7 * zkE E4U)‖ ≤ 1 := by
        rw [map_mul, norm_mul]; exact (mul_le_mul hπ1.le (hint E4U) (norm_nonneg _) zero_le_one).trans (one_mul 1).le
      calc ‖σ (zkE al7 * zkE E4U)‖ * ‖y - σ (evK Y)‖ ≤ 1 * ‖σ (zkE al7)‖ ^ N :=
            mul_le_mul hE hy (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  cases a0 <;> cases a1 <;>
    simp only [FCert.X', FCert.Y', Bool.false_eq_true, ↓reduceIte, evK_mul, evK_lin, map_mul,
      pow_zero, pow_one] at e1σ e3σ
  · -- (false, false)
    have hp : ∏ i : Fin 2, ![QF.mk F A 0 0 1, -1] i ^ (bitv 2
        (FCert.bits ⟨false, false, j, h, U, Ui, Uc, n, R, Ry, k1, k2, k3⟩) i).val = 1 := by
      rw [Fin.prod_univ_two]; simp [FCert.bits, b0]
    rw [hp, mul_one, show QF.mk F A 0 x y = QF.mk F A 0 (x * 1) (y * 1) by rw [mul_one, mul_one]]
    exact fcert_core σ hint hπ h2 hA hAE hjn hjN hU1 norm_one hx hy e1σ e3σ
  · -- (false, true)
    have hp : ∏ i : Fin 2, ![QF.mk F A 0 0 1, -1] i ^ (bitv 2
        (FCert.bits ⟨false, true, j, h, U, Ui, Uc, n, R, Ry, k1, k2, k3⟩) i).val = -1 := by
      rw [Fin.prod_univ_two]; simp [FCert.bits, b2, v1]
    rw [hp, qf_mul_neg_one]
    exact fcert_core σ hint hπ h2 hA hAE hjn hjN hU1 (by simp) hx hy e1σ e3σ
  · -- (true, false)
    have hp : ∏ i : Fin 2, ![QF.mk F A 0 0 1, -1] i ^ (bitv 2
        (FCert.bits ⟨true, false, j, h, U, Ui, Uc, n, R, Ry, k1, k2, k3⟩) i).val =
        QF.mk F A 0 0 1 := by
      rw [Fin.prod_univ_two]; simp [FCert.bits, b1, v1]
    rw [hp, qf_mul_Z, show QF.mk F A 0 (A * y) x = QF.mk F A 0 (A * y * 1) (x * 1) by
      rw [mul_one, mul_one]]
    exact fcert_core σ hint hπ h2 hA hAE hjn hjN hU1 norm_one hAy hx e1σ e3σ
  · -- (true, true)
    have hp : ∏ i : Fin 2, ![QF.mk F A 0 0 1, -1] i ^ (bitv 2
        (FCert.bits ⟨true, true, j, h, U, Ui, Uc, n, R, Ry, k1, k2, k3⟩) i).val =
        QF.mk F A 0 0 1 * -1 := by
      rw [Fin.prod_univ_two]; simp [FCert.bits, b3, v1]
    rw [hp, ← mul_assoc, qf_mul_Z, qf_mul_neg_one]
    exact fcert_core σ hint hπ h2 hA hAE hjn hjN hU1 (by simp) hAy hx e1σ e3σ

include hint hπ h2 h0 hsq in
/-- **A point at a global abscissa**: `fRev_1(x)` is a nonzero square at `σ`. -/
theorem PtSq.sound {p : PtSq} (hp : p.ok tab = true) :
    IsSquare (σ ((M3a.Bruin.fRev 1).eval (zkE p.x))) ∧ (M3a.Bruin.fRev 1).eval (zkE p.x) ≠ 0 := by
  simp only [PtSq.ok, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨hm, c1⟩, c2⟩, hu⟩ := hp
  have e1 := evK_eq_of_check _ _ _ c1
  have e2 := evK_eq_of_check _ _ _ c2
  have hf : evK (Count.gE 1 (.lin p.x) 0) = 4 * (M3a.Bruin.fRev 1).eval (zkE p.x) :=
    (Count.fRev_eval_eq 1 (.lin p.x)).symm
  simp only [evK_sub, evK_mul, evK_lin, hf, evK_alPw h0 hsq hm,
    evK_alPw h0 hsq (show p.m < 2 ^ tab.length by omega)] at e1 e2
  have e1σ := congrArg σ e1
  have e2σ := congrArg σ e2
  simp only [map_mul, map_sub, map_pow, map_ofNat] at e1σ e2σ
  have hπ0 : 0 < ‖σ (zkE al7)‖ := norm_pos_iff.mpr hπ.ne_zero
  have hπ1 := hπ.norm_lt_one
  have hB1 : ‖σ (zkE p.B)‖ = 1 := norm_unit σ hint hπ hu
  have hs2 : ‖σ (zkE p.T)‖ ^ 2 = ‖σ (zkE al7)‖ ^ p.m := by
    rw [sq, ← norm_mul, e2σ, norm_mul, norm_pow, hB1, mul_one]
  have hs0 : σ (zkE p.T) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hs2
    have := pow_pos hπ0 p.m
    rw [← hs2] at this; norm_num at this
  have hd : 4 * σ ((M3a.Bruin.fRev 1).eval (zkE p.x)) - σ (zkE p.T) ^ 2 =
      σ (zkE al7) ^ (p.m + 1) * σ (zkE p.A) := by rw [sq]; exact e1σ
  have hdn : ‖4 * σ ((M3a.Bruin.fRev 1).eval (zkE p.x)) - σ (zkE p.T) ^ 2‖ < ‖σ (zkE p.T)‖ ^ 2 := by
    rw [hd, hs2, norm_mul, norm_pow]
    calc ‖σ (zkE al7)‖ ^ (p.m + 1) * ‖σ (zkE p.A)‖ ≤ ‖σ (zkE al7)‖ ^ (p.m + 1) * 1 :=
          mul_le_mul_of_nonneg_left (hint p.A) (by positivity)
      _ < ‖σ (zkE al7)‖ ^ p.m := by
          rw [mul_one]; exact pow_lt_pow_right_of_lt_one₀ hπ0 hπ1 (Nat.lt_succ_self _)
  have h20 : (2 : F) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2
  refine ⟨?_, ?_⟩
  · have h4 : IsSquare (4 * σ ((M3a.Bruin.fRev 1).eval (zkE p.x))) :=
      isSquare_of_near hπ h2 hs0 (by rw [sub_self, norm_zero]; positivity) hdn
    refine isSquare_of_sq_mul h20 ?_
    rw [show (2 : F) ^ 2 = 4 by norm_num]; exact h4
  · intro hf0
    rw [hf0, map_zero, mul_zero, zero_sub, norm_neg, norm_pow] at hdn
    exact lt_irrefl _ hdn

end Sound

/-! ## The approximations -/

section Approx

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (σ : K21 →+* F)
  (hint : ∀ a : List ℤ, ‖σ (zkE a)‖ ≤ 1)

include hint in
/-- `ι₊ x = σ x0 - σ x1 r` against `σ (x0 - x1 y0)`. -/
theorem norm_XLp_sub {y0 : List ℤ} {r : F} {δ : ℝ} (hr : ‖r - σ (zkE y0)‖ ≤ δ)
    (hu : -r * -r = σ epsK + σ 0 * -r) (x : LC) :
    ‖qaLift σ (-r) hu (evL x) - σ (evK (XLp y0 x))‖ ≤ δ := by
  have hδ_nonneg : 0 ≤ δ := by
    have := norm_nonneg (r - σ (zkE y0))
    linarith
  have h_qaLift : qaLift σ (-r) hu (evL x) = σ (evK x.1) + σ (evK x.2) * (-r) := by
    rw [qaLift_apply σ (-r) hu (evL x)]
    rfl
  have h_evK_XLp : σ (evK (XLp y0 x)) = σ (evK x.1) - σ (evK x.2) * σ (zkE y0) := by
    rw [XLp, evK_sub, evK_mul, evK_lin, map_sub, map_mul]
  rw [h_qaLift, h_evK_XLp]
  have h_diff : (σ (evK x.1) + σ (evK x.2) * (-r)) - (σ (evK x.1) - σ (evK x.2) * σ (zkE y0)) = σ (evK x.2) * (σ (zkE y0) - r) := by
    ring
  rw [h_diff]
  rw [norm_mul]
  have h_norm_sub : ‖σ (zkE y0) - r‖ ≤ δ := by
    rw [norm_sub_rev]
    exact hr
  have h_norm_evK : ‖σ (evK x.2)‖ ≤ 1 := norm_evK_le_one σ hint x.2
  have h_mul : ‖σ (evK x.2)‖ * ‖σ (zkE y0) - r‖ ≤ 1 * δ :=
    mul_le_mul h_norm_evK h_norm_sub (norm_nonneg _) (by norm_num)
  linarith

include hint in
/-- `ι₋ x = σ x0 + σ x1 r` against `σ (x0 + x1 y0)`. -/
theorem norm_XLm_sub {y0 : List ℤ} {r : F} {δ : ℝ} (hr : ‖r - σ (zkE y0)‖ ≤ δ)
    (hu : r * r = σ epsK + σ 0 * r) (x : LC) :
    ‖qaLift σ r hu (evL x) - σ (evK (XLm y0 x))‖ ≤ δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hr
  have e : qaLift σ r hu (evL x) - σ (evK (XLm y0 x)) = σ (evK x.2) * (r - σ (zkE y0)) := by
    have h1 : (evL x).re = evK x.1 := rfl
    have h2 : (evL x).im = evK x.2 := rfl
    rw [qaLift_apply, h1, h2, XLm, evK_add, evK_mul, evK_lin, map_add, map_mul]
    ring
  rw [e, norm_mul]
  calc ‖σ (evK x.2)‖ * ‖r - σ (zkE y0)‖ ≤ 1 * δ :=
        mul_le_mul (norm_evK_le_one σ hint x.2) hr (norm_nonneg _) zero_le_one
    _ = δ := one_mul δ

include hint in
theorem norm_qaLift_evL_le {r : F} (hr1 : ‖r‖ ≤ 1) (hu : r * r = σ epsK + σ 0 * r) (x : LC) :
    ‖qaLift σ r hu (evL x)‖ ≤ 1 := by
  rw [qaLift_apply]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_evK_le_one σ hint x.1) ?_)
  rw [norm_mul]
  calc ‖σ (evK x.2)‖ * ‖r‖ ≤ 1 * 1 :=
        mul_le_mul (norm_evK_le_one σ hint x.2) hr1 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

include hint in
/-- `ι_N (±) (X + X' Ω) = ι₊ X ± ι₊ X' S` against `σ (XNs y0 S0 b x)`. -/
theorem norm_XNs_sub (h2 : (2 : F) ≠ 0) {y0 S0 : List ℤ} {r S : F} {δ : ℝ} (hδ : δ ≤ 1)
    (hr : ‖r - σ (zkE y0)‖ ≤ δ) (hS : ‖S - σ (zkE S0)‖ ≤ δ) (hu : -r * -r = σ epsK + σ 0 * -r) (b : Bool)
    (hs : (if b then S / 2 else -S / 2) * (if b then S / 2 else -S / 2) =
      qaLift σ (-r) hu eN + qaLift σ (-r) hu 0 * (if b then S / 2 else -S / 2)) (x : NC) :
    ‖qaLift (qaLift σ (-r) hu) (if b then S / 2 else -S / 2) hs (evN x) - σ (evK (XNs y0 S0 b x))‖ ≤ δ := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hr
  have hadd : ∀ u v : F, ‖u‖ ≤ δ → ‖v‖ ≤ δ → ‖u + v‖ ≤ δ := fun u v hu hv =>
    (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv)
  have hsub : ∀ u v : F, ‖u‖ ≤ δ → ‖v‖ ≤ δ → ‖u - v‖ ≤ δ := fun u v hu hv => by
    rw [sub_eq_add_neg]
    exact hadd u (-v) hu (by rwa [norm_neg])
  have hmul : ∀ u v : F, ‖u‖ ≤ 1 → ‖v‖ ≤ δ → ‖u * v‖ ≤ δ := fun u v hu hv => by
    rw [norm_mul]
    calc ‖u‖ * ‖v‖ ≤ 1 * δ := mul_le_mul hu hv (norm_nonneg _) zero_le_one
      _ = δ := one_mul δ
  have hr1 : ‖r‖ ≤ 1 := by
    have e : r = (r - σ (zkE y0)) + σ (zkE y0) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr.trans hδ) (hint y0))
  have hb : ‖σ (evK x.2.1) - σ (evK x.2.2) * r‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_evK_le_one σ hint _) ?_)
    rw [norm_neg, norm_mul]
    calc ‖σ (evK x.2.2)‖ * ‖r‖ ≤ 1 * 1 :=
          mul_le_mul (norm_evK_le_one σ hint _) hr1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hrS : ‖(r - σ (zkE y0)) * σ (zkE S0)‖ ≤ δ := by
    rw [norm_mul]
    calc ‖r - σ (zkE y0)‖ * ‖σ (zkE S0)‖ ≤ δ * 1 := mul_le_mul hr (hint S0) (norm_nonneg _) hδ0
      _ = δ := mul_one δ
  have hT : ‖(σ (evK x.2.1) - σ (evK x.2.2) * r) * (S - σ (zkE S0)) -
      σ (evK x.2.2) * ((r - σ (zkE y0)) * σ (zkE S0))‖ ≤ δ :=
    hsub _ _ (hmul _ _ hb hS) (hmul _ _ (norm_evK_le_one σ hint _) hrS)
  have hA : ‖-(σ (evK x.1.2) * (r - σ (zkE y0)))‖ ≤ δ := by
    rw [norm_neg]
    exact hmul _ _ (norm_evK_le_one σ hint _) hr
  have hre : (evN x).re = evL x.1 := rfl
  have him : (evN x).im = ⟨2 * evK x.2.1, 2 * evK x.2.2⟩ := rfl
  have hl1 : (evL x.1).re = evK x.1.1 := rfl
  have hl2 : (evL x.1).im = evK x.1.2 := rfl
  rw [qaLift_apply, hre, him, qaLift_apply, hl1, hl2, qaLift_mk]
  cases b
  · calc _ = ‖-(σ (evK x.1.2) * (r - σ (zkE y0))) -
          ((σ (evK x.2.1) - σ (evK x.2.2) * r) * (S - σ (zkE S0)) -
            σ (evK x.2.2) * ((r - σ (zkE y0)) * σ (zkE S0)))‖ := by
          congr 1
          simp only [XNs, XLp, evK_sub, evK_mul, evK_lin, map_sub, map_mul, map_ofNat,
            Bool.false_eq_true, ↓reduceIte]
          field_simp
          ring
      _ ≤ δ := hsub _ _ hA hT
  · calc _ = ‖-(σ (evK x.1.2) * (r - σ (zkE y0))) +
          ((σ (evK x.2.1) - σ (evK x.2.2) * r) * (S - σ (zkE S0)) -
            σ (evK x.2.2) * ((r - σ (zkE y0)) * σ (zkE S0)))‖ := by
          congr 1
          simp only [XNs, XLp, evK_add, evK_sub, evK_mul, evK_lin, map_add, map_sub, map_mul,
            map_ofNat, ↓reduceIte]
          field_simp
          ring
      _ ≤ δ := hadd _ _ hA hT

end Approx

/-- **The coordinates of `ι'`**: `ι' (X + X' Ω) = ι₋ X + ι₋ X' Z` in `F' = QF F A 0`. -/
theorem iota'_evN {F : Type*} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
    {A : F} [Fact (∀ r : F, r ^ 2 ≠ A + 0 * r)] (h2 : (2 : F) ≠ 0) (ιm : L42 →+* F)
    (hu : QF.mk F A 0 0 (1 / 2) * QF.mk F A 0 0 (1 / 2) =
      (algebraMap F (QF F A 0)).comp ιm eN + (algebraMap F (QF F A 0)).comp ιm 0 * QF.mk F A 0 0 (1 / 2))
    (x : NC) :
    qaLift ((algebraMap F (QF F A 0)).comp ιm) (QF.mk F A 0 0 (1 / 2)) hu (evN x) =
      QF.mk F A 0 (ιm (evL x.1)) (ιm (evL x.2)) := by
  have hre : (evN x).re = evL x.1 := rfl
  have him : (evN x).im = evL x.2 + evL x.2 := QuadraticAlgebra.ext (two_mul _) (two_mul _)
  have hc : ιm (evL x.2) + ιm (evL x.2) = 2 * ιm (evL x.2) := (two_mul _).symm
  rw [qaLift_apply, hre, him, RingHom.comp_apply, RingHom.comp_apply, map_add ιm, hc,
    qf_mk_eq (ιm (evL x.1)), qf_mk_eq (0 : F) (1 / 2), map_zero, zero_add, ← mul_assoc, ← map_mul]
  congr 3
  field_simp

end FurioLombardo.Discharge.SelmerBasis.W7
