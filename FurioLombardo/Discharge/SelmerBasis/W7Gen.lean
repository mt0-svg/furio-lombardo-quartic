import FurioLombardo.Discharge.SelmerBasis.PlaceWGen
import FurioLombardo.Discharge.SelmerBasis.Spanning
import FurioLombardo.Discharge.SelmerBasis.Interfaces
import FurioLombardo.Discharge.SelmerSpan.Mumford

/-!
# Generic layer of the place above 7 (lane selmer-p7)

At `w7` (`e = 7`, residue field `𝔽₃₄₃`, `‖2‖ = 1`) the local algebra `K_w7[T]/(fRev 1)` is `K_w7⁴ × F5`
with `F5 = QF K_w7 A B` a ramified (Eisenstein) quadratic field. This file holds the
facts that do not depend on the data:

* odd residue characteristic: `π`, `u` (`u ^ N ≡ -1`) are independent modulo squares (`indep_pi_u`);
  a square certificate with an approximation (`isSquare_of_near`);
* the Eisenstein component `QF K A B` inherits the Fermat and Euler congruences of `K` (`qfE_fermat`,
  `qfE_euler`), `‖2‖ = 1` (`qf_norm_two`) and the non-square unit (`qf_norm_pow_add_one`); a square
  certificate read on the coordinates over `K` (`qfE_isSquare_of_cert`);
* rows over the five components: the basis `b7` of `(Fin 4 → Fˣ) × F'ˣ` modulo squares, squares and
  independence from the components (`isSquare_mul_rows7`, `indep_rows7`);
* the points: `P1 + P2 - ∞` from two points `(x_i, y_i)`, with `μ = [(T - x1)(T - x2)]` (`exists_jac_two`);
* `coordCond_range_of_imageIn`: from `CoordCond` on a subgroup containing the image to the image itself.
-/

set_option autoImplicit false

open Polynomial FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.SelmerBasis.W7

/-! ## Odd residue characteristic -/

section Odd

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

/-- **`π`, `u` are independent modulo squares** when `u` is a unit with `u ^ N ≡ -1` and every unit
satisfies `ξ ^ (2 N) ≡ 1`. -/
theorem indep_pi_u {π : F} (hπ : NormUnif π) (h2 : ‖(2 : F)‖ = 1) {N : ℕ}
    (hferm : ∀ ξ : F, ‖ξ‖ = 1 → ‖ξ ^ (2 * N) - 1‖ < 1)
    {u : F} (hu : ‖u‖ = 1) (hun : ‖u ^ N + 1‖ < 1) :
    ∀ ε : Fin 2 → ZMod 2, IsSquare (∏ l : Fin 2, ![π, u] l ^ (ε l).val) → ε = 0 := by
  intro ε h_sq
  have h_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h_cases (ε 0) with (hε0 | hε0)
  · -- ε 0 = 0
    rcases h_cases (ε 1) with (hε1 | hε1)
    · -- ε 0 = 0, ε 1 = 0: the only valid case
      ext i
      fin_cases i
      · exact hε0
      · exact hε1
    · -- ε 0 = 0, ε 1 = 1: derive contradiction
      have h_prod : (∏ l : Fin 2, ![π, u] l ^ (ε l).val) = u := by
        simp [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ZMod.val_one, hε0, hε1]
      rw [h_prod] at h_sq
      rcases h_sq.exists_mul_self with ⟨r, hr⟩
      have hr_norm : ‖r‖ = 1 := by
        have h_sq_norm : ‖r * r‖ = 1 := by rw [← hr, hu]
        rw [norm_mul] at h_sq_norm
        have h_nonneg : 0 ≤ ‖r‖ := norm_nonneg _
        nlinarith
      have h_ur : ‖r ^ (2 * N) - 1‖ < 1 := hferm r hr_norm
      have h_uN_eq : r ^ (2 * N) = u ^ N := by
        calc
          r ^ (2 * N) = (r ^ 2) ^ N := by rw [pow_mul]
          _ = (r * r) ^ N := by rw [sq]
          _ = u ^ N := by rw [hr]
      rw [h_uN_eq] at h_ur
      have h_two_norm_lt_one : ‖(2 : F)‖ < 1 := by
        calc
          ‖(2 : F)‖ = ‖(u ^ N + 1) - (u ^ N - 1)‖ := by ring
          _ ≤ max ‖u ^ N + 1‖ ‖u ^ N - 1‖ := by
            have htemp := IsUltrametricDist.norm_add_le_max (u ^ N + 1) (-(u ^ N - 1))
            rw [sub_eq_add_neg]
            exact htemp.trans (max_le_max (le_refl _) (by rw [norm_neg]))
          _ < 1 := max_lt hun h_ur
      linarith
  · -- ε 0 = 1: derive contradiction
    have h_norm_upow : ‖u ^ (ε 1).val‖ = 1 := by
      rcases h_cases (ε 1) with (hε1' | hε1')
      · rw [hε1', ZMod.val_zero, pow_zero, norm_one]
      · rw [hε1', ZMod.val_one, pow_one, hu]
    have h_prod : (∏ l : Fin 2, ![π, u] l ^ (ε l).val) = π * u ^ (ε 1).val := by
      simp [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ZMod.val_one, hε0]
    rw [h_prod] at h_sq
    rcases h_sq.exists_mul_self with ⟨r, hr⟩
    have hr_ne_zero : r ≠ 0 := by
      intro hrz
      rw [hrz, zero_mul] at hr
      have hx_ne_zero : π * u ^ (ε 1).val ≠ 0 := by
        refine mul_ne_zero hπ.ne_zero ?_
        apply pow_ne_zero _
        intro huz
        rw [huz, norm_zero] at hu
        linarith
      exact hx_ne_zero hr
    have h_norm_x : ‖π * u ^ (ε 1).val‖ = ‖π‖ := by
      rw [norm_mul, h_norm_upow, mul_one]
    have h_norm_rr : ‖r * r‖ = ‖π‖ := by
      rw [← hr, h_norm_x]
    rw [norm_mul] at h_norm_rr
    -- h_norm_rr: ‖r‖ * ‖r‖ = ‖π‖
    have h_disc : ∃ n : ℤ, ‖r‖ = ‖π‖ ^ n := hπ.disc r hr_ne_zero
    rcases h_disc with ⟨n, hn⟩
    rw [hn] at h_norm_rr
    -- (‖π‖ ^ n) * (‖π‖ ^ n) = ‖π‖
    have h_sq_eq : (‖π‖ ^ n) ^ 2 = ‖π‖ := by
      calc
        (‖π‖ ^ n) ^ 2 = ‖π‖ ^ n * ‖π‖ ^ n := by ring
        _ = ‖π‖ := h_norm_rr
    have h_norm_pos : 0 < ‖π‖ := by
      have h_nonneg := norm_nonneg π
      have h_norm_ne_zero : ‖π‖ ≠ 0 := norm_ne_zero_iff.mpr hπ.ne_zero
      exact lt_of_le_of_ne h_nonneg h_norm_ne_zero.symm
    have h_pow_eq : ‖π‖ ^ (n * (2 : ℤ)) = ‖π‖ ^ (1 : ℤ) := by
      calc
        ‖π‖ ^ (n * (2 : ℤ)) = (‖π‖ ^ n) ^ (2 : ℤ) := by rw [zpow_mul ‖π‖ n (2 : ℤ)]
        _ = (‖π‖ ^ n) ^ 2 := by norm_num
        _ = ‖π‖ := h_sq_eq
        _ = ‖π‖ ^ (1 : ℤ) := by rw [zpow_one]
    have h_norm_ne_one : ‖π‖ ≠ 1 := by linarith [hπ.norm_lt_one]
    have h_inj := zpow_right_injective₀ h_norm_pos h_norm_ne_one
    have h_exp_eq : n * (2 : ℤ) = (1 : ℤ) := h_inj h_pow_eq
    -- n * 2 = 1, impossible in ℤ
    have h_one_not_even : ¬ ∃ k : ℤ, (1 : ℤ) = 2 * k := by
      intro h
      rcases h with ⟨k, hk⟩
      omega
    exfalso
    apply h_one_not_even
    refine ⟨n, ?_⟩
    linarith

/-- **A square from an approximation**: `x` near `X` and `X` near `s²`, both closer than `‖s‖²`. -/
theorem isSquare_of_near [ProperSpace F] {π : F} (hπ : NormUnif π) (h2 : ‖(2 : F)‖ = 1) {x X s : F}
    (hs : s ≠ 0) (hxX : ‖x - X‖ < ‖s‖ ^ 2) (hXs : ‖X - s ^ 2‖ < ‖s‖ ^ 2) : IsSquare x := by
  have hxX' : ‖x - s ^ 2‖ < ‖s‖ ^ 2 := by
    calc
      ‖x - s ^ 2‖ = ‖(x - X) + (X - s ^ 2)‖ := by ring_nf
      _ ≤ max ‖x - X‖ ‖X - s ^ 2‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < ‖s‖ ^ 2 := max_lt hxX hXs
  have h4norm : ‖(4 : F)‖ = 1 := by
    calc
      ‖(4 : F)‖ = ‖(2 : F) * (2 : F)‖ := by norm_num
      _ = ‖(2 : F)‖ * ‖(2 : F)‖ := norm_mul _ _
      _ = 1 * 1 := by rw [h2]
      _ = 1 := by simp
  have hxX'' : ‖x - s ^ 2‖ < ‖(4 : F)‖ * ‖s‖ ^ 2 := by
    rw [h4norm, one_mul]
    exact hxX'
  have h2' : (2 : F) ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at h2
    linarith
  exact isSquare_of_sub_sq_lt hπ h2' hs hxX''

end Odd

/-! ## The Eisenstein component -/

section Eisen

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {π A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)]



theorem qfE_near_re_aux1 {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {π A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)]
    (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) (x y : K)
    (hz : ‖QF.mk K A B x y‖ = 1) :
    ‖y‖ * ‖QF.mk K A B 0 1‖ < 1 := by
  set Y := QF.mk K A B 0 1 with hY_def
  have hY_pos : 0 < ‖Y‖ := qfE_Y_pos hπ hA hB
  have hY_lt_one : ‖Y‖ < 1 := qfE_Y_lt_one hπ hA hB
  have hY_ne_one : ‖Y‖ ≠ 1 := by linarith
  have hnorm := qfE_norm hπ hA hB x y
  rw [hz] at hnorm
  have hmax : max ‖x‖ (‖y‖ * ‖Y‖) = 1 := hnorm.symm
  have hle : ‖y‖ * ‖Y‖ ≤ 1 := by
    have := calc
      ‖y‖ * ‖Y‖ ≤ max ‖x‖ (‖y‖ * ‖Y‖) := le_max_right _ _
      _ = 1 := hmax
    exact this
  by_contra! H
  have heq : ‖y‖ * ‖Y‖ = 1 := by linarith
  by_cases hy0 : y = 0
  · rw [hy0] at heq
    simp at heq
  · rcases hπ.disc y hy0 with ⟨n, hn⟩
    have hpow : ‖π‖ ^ n = ‖Y‖ ^ (2 * n) := qfE_pow_eq hπ hA hB n
    have hy_norm : ‖y‖ = ‖Y‖ ^ (2 * n) := by
      rw [hn, hpow]
    have hprod : ‖Y‖ ^ (2 * n + 1) = 1 := by
      calc
        ‖Y‖ ^ (2 * n + 1) = ‖Y‖ ^ (2 * n) * ‖Y‖ := by
          rw [zpow_add_one₀ (by linarith) (2 * n)]
        _ = ‖y‖ * ‖Y‖ := by rw [hy_norm]
        _ = 1 := heq
    have hzero : ‖Y‖ ^ (0 : ℤ) = 1 := by simp
    have h_eq_pow : ‖Y‖ ^ (2 * n + 1) = ‖Y‖ ^ (0 : ℤ) := by rw [hprod, hzero]
    have h_inj := (zpow_right_injective₀ (by linarith) hY_ne_one).eq_iff.mp h_eq_pow
    have h_contra : (2 : ℤ) * n + 1 ≠ 0 := by
      intro h
      have h_eq' : (2 : ℤ) * n = -1 := by linarith
      have h_even : (2 : ℤ) * n % 2 = 0 := by simp
      have h_neg_one : (-1 : ℤ) % 2 = 1 := by norm_num
      rw [h_eq'] at h_even
      norm_num at h_even
    exact h_contra h_inj

theorem qfE_near_re_aux2 {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {π A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)]
    (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) (x y : K)
    (hz : ‖QF.mk K A B x y‖ = 1) :
    ‖x‖ = 1 := by
  set Y := QF.mk K A B 0 1 with hY_def
  have hnorm := qfE_norm hπ hA hB x y
  rw [hz] at hnorm
  have hmax : max ‖x‖ (‖y‖ * ‖Y‖) = 1 := hnorm.symm
  have h_lt : ‖y‖ * ‖Y‖ < 1 := qfE_near_re_aux1 hπ hA hB x y hz
  have hx_le : ‖x‖ ≤ 1 := by
    have := calc
      ‖x‖ ≤ max ‖x‖ (‖y‖ * ‖Y‖) := le_max_left _ _
      _ = 1 := hmax
    exact this
  have hx_ge : 1 ≤ ‖x‖ := by
    by_contra! H
    have hlt' : max ‖x‖ (‖y‖ * ‖Y‖) < 1 := max_lt H h_lt
    rw [hmax] at hlt'
    linarith
  linarith

theorem qfE_near_re_aux3 {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {π A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)]
    (_hπ : NormUnif π) (_hA : ‖A‖ = ‖π‖) (_hB : ‖B‖ < 1) (x y : K)
    (_hz : ‖QF.mk K A B x y‖ = 1) :
    QF.mk K A B x y - algebraMap K (QF K A B) x = QF.mk K A B 0 y := by
  unfold QF
  apply QuadraticAlgebra.ext
  · calc
      ((QuadraticAlgebra.mk x y : QuadraticAlgebra K A B) -
        (algebraMap K (QuadraticAlgebra K A B) x : QuadraticAlgebra K A B)).re
          = ((QuadraticAlgebra.mk x y : QuadraticAlgebra K A B)).re -
            ((algebraMap K (QuadraticAlgebra K A B) x : QuadraticAlgebra K A B)).re :=
        QuadraticAlgebra.re_sub _ _
      _ = x - x := by
        rw [QuadraticAlgebra.algebraMap_re]
      _ = (0 : K) := by simp
      _ = ((QuadraticAlgebra.mk (0 : K) y : QuadraticAlgebra K A B)).re := rfl
  · calc
      ((QuadraticAlgebra.mk x y : QuadraticAlgebra K A B) -
        (algebraMap K (QuadraticAlgebra K A B) x : QuadraticAlgebra K A B)).im
          = ((QuadraticAlgebra.mk x y : QuadraticAlgebra K A B)).im -
            ((algebraMap K (QuadraticAlgebra K A B) x : QuadraticAlgebra K A B)).im :=
        QuadraticAlgebra.im_sub _ _
      _ = y - 0 := by
        rw [QuadraticAlgebra.algebraMap_im]
      _ = y := by simp
      _ = ((QuadraticAlgebra.mk (0 : K) y : QuadraticAlgebra K A B)).im := rfl

theorem qfE_near_re_aux4 {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {π A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)]
    (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) (x y : K)
    (hz : ‖QF.mk K A B x y‖ = 1) :
    ‖QF.mk K A B 0 y‖ < 1 := by
  set Y := QF.mk K A B 0 1 with hY_def
  have h_lt : ‖y‖ * ‖Y‖ < 1 := qfE_near_re_aux1 hπ hA hB x y hz
  have h_nonneg : 0 ≤ ‖y‖ * ‖Y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    ‖QF.mk K A B 0 y‖ = max ‖(0 : K)‖ (‖y‖ * ‖Y‖) := qfE_norm hπ hA hB 0 y
    _ = max 0 (‖y‖ * ‖Y‖) := by simp
    _ = ‖y‖ * ‖Y‖ := max_eq_right h_nonneg
    _ < 1 := h_lt



/-- A unit of the Eisenstein component is congruent to its coordinate on `1`. -/
theorem qfE_near_re (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) (x y : K)
    (hz : ‖QF.mk K A B x y‖ = 1) :
    ‖x‖ = 1 ∧ ‖QF.mk K A B x y - algebraMap K (QF K A B) x‖ < 1 := by
  have h1 : ‖x‖ = 1 := qfE_near_re_aux2 hπ hA hB x y hz
  have h2 : ‖QF.mk K A B x y - algebraMap K (QF K A B) x‖ < 1 := by
    rw [qfE_near_re_aux3 hπ hA hB x y hz]
    exact qfE_near_re_aux4 hπ hA hB x y hz
  exact And.intro h1 h2

/-- **Fermat's congruence at the Eisenstein component.** -/
theorem qfE_fermat (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) {N : ℕ}
    (hferm : ∀ ξ : K, ‖ξ‖ = 1 → ‖ξ ^ (2 * N) - 1‖ < 1) :
    ∀ ξ : QF K A B, ‖ξ‖ = 1 → ‖ξ ^ (2 * N) - 1‖ < 1 := by
  intro ξ hξ
  -- Decompose ξ = mk x y where x = ξ.re, y = ξ.im
  set x := (ξ : QuadraticAlgebra K A B).re with hx_def
  set y := (ξ : QuadraticAlgebra K A B).im with hy_def
  have hξ_eq : QF.mk K A B x y = ξ := by
    rw [hx_def, hy_def]
    exact (qf_mk_re_im A B ξ).symm
  rw [← hξ_eq]
  -- Let a = algebraMap x, M = 2*N
  set a := algebraMap K (QF K A B) x with ha_def
  set M := 2 * N with hM_def
  have hx_norm : ‖x‖ = 1 := by
    have h := qfE_near_re hπ hA hB x y hξ
    exact h.1
  have ha_norm : ‖a‖ = 1 := by
    rw [ha_def, QF.norm_algebraMap]
    exact hx_norm
  have hδ_lt_one : ‖QF.mk K A B x y - a‖ < 1 := by
    have h := qfE_near_re hπ hA hB x y hξ
    exact h.2
  set δ := QF.mk K A B x y - a with hδ_def
  have hδ_lt_one' : ‖δ‖ < 1 := hδ_lt_one
  have h_comm : Commute (QF.mk K A B x y) a :=
    Commute.all _ _
  -- Factorization: ξ^M - a^M = δ * sum
  have h_factor : QF.mk K A B x y ^ M - a ^ M = δ * (∑ i ∈ Finset.range M, (QF.mk K A B x y) ^ i * a ^ (M - 1 - i)) := by
    calc
      QF.mk K A B x y ^ M - a ^ M = ((∑ i ∈ Finset.range M, (QF.mk K A B x y) ^ i * a ^ (M - 1 - i)) * (QF.mk K A B x y - a)) := by
        rw [h_comm.geom_sum₂_mul M]
      _ = δ * (∑ i ∈ Finset.range M, (QF.mk K A B x y) ^ i * a ^ (M - 1 - i)) := by
        rw [hδ_def, mul_comm]
  -- The sum factor has norm ≤ 1
  have h_sum_norm_le_one : ‖∑ i ∈ Finset.range M, (QF.mk K A B x y) ^ i * a ^ (M - 1 - i)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) ?_
    intro i hi
    have hterm : ‖(QF.mk K A B x y) ^ i * a ^ (M - 1 - i)‖ ≤ 1 := by
      calc
        ‖(QF.mk K A B x y) ^ i * a ^ (M - 1 - i)‖ ≤ ‖(QF.mk K A B x y) ^ i‖ * ‖a ^ (M - 1 - i)‖ :=
          norm_mul_le _ _
        _ ≤ ‖QF.mk K A B x y‖ ^ i * ‖a‖ ^ (M - 1 - i) := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
          · exact norm_pow_le _ _
          · exact norm_pow_le _ _
        _ = 1 ^ i * 1 ^ (M - 1 - i) := by
          rw [hξ_eq, hξ, ha_norm]
        _ = 1 := by simp
    exact hterm
  -- So ‖ξ^M - a^M‖ < 1
  have h_main_lt_one : ‖QF.mk K A B x y ^ M - a ^ M‖ < 1 := by
    rw [h_factor]
    calc
      ‖δ * (∑ i ∈ Finset.range M, (QF.mk K A B x y) ^ i * a ^ (M - 1 - i))‖ ≤
          ‖δ‖ * ‖∑ i ∈ Finset.range M, (QF.mk K A B x y) ^ i * a ^ (M - 1 - i)‖ :=
        norm_mul_le _ _
      _ < 1 * 1 := by
        calc
          ‖δ‖ * ‖∑ i ∈ Finset.range M, (QF.mk K A B x y) ^ i * a ^ (M - 1 - i)‖ ≤
              ‖δ‖ * 1 := mul_le_mul_of_nonneg_left h_sum_norm_le_one (norm_nonneg _)
          _ < 1 * 1 := mul_lt_mul_of_pos_right hδ_lt_one' (by norm_num)
      _ = 1 := by norm_num
  -- Now a^M - 1 = algebraMap (x^M - 1)
  have h_aM_sub_one : a ^ M - 1 = algebraMap K (QF K A B) (x ^ M - 1) := by
    calc
      a ^ M - 1 = (algebraMap K (QF K A B) x) ^ M - algebraMap K (QF K A B) 1 := by
        simp [ha_def]
      _ = algebraMap K (QF K A B) (x ^ M) - algebraMap K (QF K A B) 1 := by
        rw [map_pow]
      _ = algebraMap K (QF K A B) (x ^ M - 1) := by
        rw [map_sub, map_one]
  have h_aM_sub_one_lt_one : ‖a ^ M - 1‖ < 1 := by
    rw [h_aM_sub_one]
    rw [QF.norm_algebraMap]
    exact hferm x hx_norm
  -- Finally, ξ^M - 1 = (ξ^M - a^M) + (a^M - 1)
  have h_final : QF.mk K A B x y ^ M - 1 = (QF.mk K A B x y ^ M - a ^ M) + (a ^ M - 1) := by
    ring
  rw [h_final]
  have h_nonarch := IsUltrametricDist.isNonarchimedean_norm (R := QF K A B)
  calc
    ‖(QF.mk K A B x y ^ M - a ^ M) + (a ^ M - 1)‖ ≤
        max ‖QF.mk K A B x y ^ M - a ^ M‖ ‖a ^ M - 1‖ :=
      h_nonarch _ _
    _ < max 1 1 :=
      max_lt_max h_main_lt_one h_aM_sub_one_lt_one
    _ = 1 := by norm_num

/-- **Euler's criterion at the Eisenstein component.** -/
theorem qfE_euler (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) {N : ℕ}
    (heuler : ∀ ξ : K, ‖ξ‖ = 1 → ‖ξ ^ N - 1‖ < 1 → ∃ s : K, ‖ξ - s ^ 2‖ < 1) :
    ∀ ξ : QF K A B, ‖ξ‖ = 1 → ‖ξ ^ N - 1‖ < 1 → ∃ s : QF K A B, ‖ξ - s ^ 2‖ < 1 := by
  intro ξ hξ_norm hξ_pow
  let x := (ξ : QuadraticAlgebra K A B).re
  have hξ_eq : QF.mk K A B x ((ξ : QuadraticAlgebra K A B).im) = ξ := qf_mk_re_im A B ξ
  have h_near := qfE_near_re hπ hA hB x ((ξ : QuadraticAlgebra K A B).im) (by
    rw [← hξ_eq]
    exact hξ_norm)
  rcases h_near with ⟨hx_norm, h_near⟩
  have h_near' : ‖ξ - algebraMap K (QF K A B) x‖ < 1 := by
    rw [← hξ_eq] at h_near
    exact h_near
  let a := algebraMap K (QF K A B) x
  have ha_norm : ‖a‖ = 1 := by
    rw [QF.norm_algebraMap K A B x, hx_norm]
  have h_a_pow_near : ‖a ^ N - 1‖ < 1 := by
    have h_sum_norm_le_one : ‖∑ i ∈ Finset.range N, ξ ^ i * a ^ (N - 1 - i)‖ ≤ 1 := by
      have h_each : ∀ i : ℕ, ‖ξ ^ i * a ^ (N - 1 - i)‖ ≤ 1 := by
        intro i
        calc
          ‖ξ ^ i * a ^ (N - 1 - i)‖ ≤ ‖ξ ^ i‖ * ‖a ^ (N - 1 - i)‖ := norm_mul_le _ _
          _ ≤ (‖ξ‖ ^ i) * (‖a‖ ^ (N - 1 - i)) := by
            refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
            · exact norm_pow_le _ _
            · exact norm_pow_le _ _
          _ = (1 : ℝ) ^ i * (1 : ℝ) ^ (N - 1 - i) := by rw [hξ_norm, ha_norm]
          _ = 1 := by simp
      refine Finset.induction_on (Finset.range N) (by simp) (fun i s hi ih => ?_)
      rw [Finset.sum_insert hi]
      have h_bound : max ‖ξ ^ i * a ^ (N - 1 - i)‖ ‖∑ j ∈ s, ξ ^ j * a ^ (N - 1 - j)‖ ≤ 1 := by
        refine le_trans (max_le (h_each i) ih) (by simp)
      exact le_trans (IsUltrametricDist.norm_add_le_max _ _) h_bound
    have h_diff_norm_lt_one : ‖ξ ^ N - a ^ N‖ < 1 := by
      have h_factor : (∑ i ∈ Finset.range N, ξ ^ i * a ^ (N - 1 - i)) * (ξ - a) = ξ ^ N - a ^ N := by
        simpa [mul_comm] using geom_sum₂_mul ξ a N
      have h_prod_norm : ‖(∑ i ∈ Finset.range N, ξ ^ i * a ^ (N - 1 - i)) * (ξ - a)‖ < 1 := by
        apply lt_of_le_of_lt (norm_mul_le _ _) ?_
        calc
          ‖∑ i ∈ Finset.range N, ξ ^ i * a ^ (N - 1 - i)‖ * ‖ξ - a‖ ≤
              1 * ‖ξ - a‖ := mul_le_mul_of_nonneg_right h_sum_norm_le_one (norm_nonneg _)
          _ < 1 * 1 := mul_lt_mul_of_pos_left h_near' (by norm_num : (0 : ℝ) < 1)
          _ = 1 := by simp
      rw [h_factor] at h_prod_norm
      exact h_prod_norm
    have h_max_eq : max ‖a ^ N - ξ ^ N‖ ‖ξ ^ N - 1‖ = max ‖ξ ^ N - a ^ N‖ ‖ξ ^ N - 1‖ := by
      have h : ‖a ^ N - ξ ^ N‖ = ‖ξ ^ N - a ^ N‖ := by
        rw [← norm_neg, neg_sub]
      rw [h]
    calc
      ‖a ^ N - 1‖ = ‖(a ^ N - ξ ^ N) + (ξ ^ N - 1)‖ := by ring
      _ ≤ max ‖a ^ N - ξ ^ N‖ ‖ξ ^ N - 1‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = max ‖ξ ^ N - a ^ N‖ ‖ξ ^ N - 1‖ := h_max_eq
      _ < max (1 : ℝ) (1 : ℝ) := by
        simpa using max_lt h_diff_norm_lt_one hξ_pow
      _ = 1 := by simp
  have hx_pow_norm_lt_one : ‖x ^ N - 1‖ < 1 := by
    calc
      ‖x ^ N - 1‖ = ‖algebraMap K (QF K A B) (x ^ N - 1)‖ := by
        rw [QF.norm_algebraMap K A B (x ^ N - 1)]
      _ = ‖(algebraMap K (QF K A B) x) ^ N - 1‖ := by simp
      _ = ‖a ^ N - 1‖ := rfl
      _ < 1 := h_a_pow_near
  obtain ⟨s, hs⟩ := heuler x hx_norm hx_pow_norm_lt_one
  refine ⟨algebraMap K (QF K A B) s, ?_⟩
  calc
    ‖ξ - (algebraMap K (QF K A B) s) ^ 2‖ = ‖(ξ - a) + (a - (algebraMap K (QF K A B) s) ^ 2)‖ := by ring
    _ = ‖(ξ - a) + algebraMap K (QF K A B) (x - s ^ 2)‖ := by
      simp [a, map_sub, map_pow]
    _ ≤ max ‖ξ - a‖ ‖algebraMap K (QF K A B) (x - s ^ 2)‖ :=
      IsUltrametricDist.norm_add_le_max _ _
    _ = max ‖ξ - a‖ ‖x - s ^ 2‖ := by rw [QF.norm_algebraMap K A B (x - s ^ 2)]
    _ < max (1 : ℝ) (1 : ℝ) := by
      simpa using max_lt h_near' hs
    _ = 1 := by simp

theorem qf_norm_two (h2 : ‖(2 : K)‖ = 1) : ‖(2 : QF K A B)‖ = 1 := by
  have h : (2 : QF K A B) = algebraMap K (QF K A B) (2 : K) := by
    simpa using (map_natCast (algebraMap K (QF K A B)) 2).symm
  rw [h]
  have hnorm : ‖algebraMap K (QF K A B) (2 : K)‖ = spectralNorm K (QF K A B) (algebraMap K (QF K A B) (2 : K)) := rfl
  rw [hnorm]
  rw [spectralNorm_extends, h2]

theorem qf_norm_pow_add_one {u : K} {N : ℕ} (hun : ‖u ^ N + 1‖ < 1) :
    ‖(algebraMap K (QF K A B) u) ^ N + 1‖ < 1 := by
  calc
    ‖(algebraMap K (QF K A B) u) ^ N + 1‖ = ‖algebraMap K (QF K A B) (u ^ N + 1)‖ := by
      simp [map_add, map_pow, map_one]
    _ = ‖u ^ N + 1‖ := by rw [QF.norm_algebraMap]
    _ < 1 := hun

/-- The distance from `x + y Y` to a scalar `t`, on the coordinates. -/
theorem qfE_norm_sub_algebraMap (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) (x y t : K) :
    ‖QF.mk K A B x y - algebraMap K (QF K A B) t‖ = max ‖x - t‖ (‖y‖ * ‖QF.mk K A B 0 1‖) := by
  have e : QF.mk K A B x y - algebraMap K (QF K A B) t = QF.mk K A B (x - t) y := by
    change (⟨x, y⟩ : QuadraticAlgebra K A B) - algebraMap K (QuadraticAlgebra K A B) t = ⟨x - t, y⟩
    ext
    · simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.algebraMap_re]
    · simp only [QuadraticAlgebra.im_sub, QuadraticAlgebra.algebraMap_im, sub_zero]
  rw [e, qfE_norm hπ hA hB]

/-- **A square certificate at the Eisenstein component**: `x + y Y` is a square when `x` is close to a
scalar `t` that is a square in the component and `y Y` is small. -/
theorem qfE_isSquare_of_cert [ProperSpace K] (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1)
    (h2 : ‖(2 : K)‖ = 1) {x y t : K} (ht0 : t ≠ 0) (ht : IsSquare (algebraMap K (QF K A B) t))
    (hx : ‖x - t‖ < ‖t‖) (hy : ‖y‖ * ‖QF.mk K A B 0 1‖ < ‖t‖) : IsSquare (QF.mk K A B x y) := by
  rcases ht with ⟨s, hs⟩
  have hs0 : s ≠ 0 := by
    intro hzero
    have hzero' : algebraMap K (QF K A B) t = 0 := by
      rw [hs, hzero, mul_zero]
    exact (map_ne_zero (algebraMap K (QF K A B))).mpr ht0 hzero'
  have hnorm_sq : ‖s‖ ^ 2 = ‖t‖ := by
    calc
      ‖s‖ ^ 2 = ‖s‖ * ‖s‖ := by ring
      _ = ‖s * s‖ := by rw [norm_mul]
      _ = ‖algebraMap K (QF K A B) t‖ := by rw [← hs]
      _ = ‖t‖ := QF.norm_algebraMap (a := A) (b := B) (x := t)
  have h_norm_four : ‖(4 : QF K A B)‖ = 1 := by
    have h4 : (4 : QF K A B) = (2 : QF K A B) * (2 : QF K A B) := by norm_num
    calc
      ‖(4 : QF K A B)‖ = ‖(2 : QF K A B) * (2 : QF K A B)‖ := by rw [h4]
      _ = ‖(2 : QF K A B)‖ * ‖(2 : QF K A B)‖ := by rw [norm_mul]
      _ = 1 * 1 := by rw [qf_norm_two h2]
      _ = 1 := by norm_num
  have h2_ne_zero : (2 : QF K A B) ≠ 0 := by
    have hnorm : ‖(2 : QF K A B)‖ = 1 := qf_norm_two h2
    intro hzero
    rw [hzero, norm_zero] at hnorm
    linarith
  have h_normUnif : NormUnif (QF.mk K A B 0 1) := qfE_normUnif hπ hA hB
  have hdist : ‖QF.mk K A B x y - s ^ 2‖ < ‖(4 : QF K A B)‖ * ‖s‖ ^ 2 := by
    have h_eq : ‖QF.mk K A B x y - s ^ 2‖ = max ‖x - t‖ (‖y‖ * ‖QF.mk K A B 0 1‖) := by
      calc
        ‖QF.mk K A B x y - s ^ 2‖ = ‖QF.mk K A B x y - (s * s)‖ := by rw [sq]
        _ = ‖QF.mk K A B x y - algebraMap K (QF K A B) t‖ := by rw [← hs]
        _ = max ‖x - t‖ (‖y‖ * ‖QF.mk K A B 0 1‖) := qfE_norm_sub_algebraMap hπ hA hB x y t
    rw [h_eq]
    rw [hnorm_sq]
    rw [h_norm_four]
    have hmax : max ‖x - t‖ (‖y‖ * ‖QF.mk K A B 0 1‖) < ‖t‖ := max_lt hx hy
    simpa [one_mul] using hmax
  exact isSquare_of_sub_sq_lt h_normUnif h2_ne_zero hs0 hdist

end Eisen

/-! ## Rows over the five components -/

section Rows

variable {F F' : Type*} [Field F] [Field F']

/-- The basis of `(Fin 4 → Fˣ) × F'ˣ` modulo squares: `b i` at component `c` (position `2 c + i`) and
`b' i` at `F'` (position `8 + i`). -/
noncomputable def b7 (b : Fin 2 → F) (b' : Fin 2 → F') (hb : ∀ i, b i ≠ 0) (hb' : ∀ i, b' i ≠ 0) :
    Fin 10 → (Fin 4 → Fˣ) × F'ˣ := fun l =>
  if h : l.val < 8 then
    (Pi.mulSingle (⟨l.val / 2, by omega⟩ : Fin 4) (Units.mk0 (b ⟨l.val % 2, by omega⟩) (hb _)), 1)
  else (1, Units.mk0 (b' ⟨l.val - 8, by omega⟩) (hb' _))

theorem b7_prod_fst (b : Fin 2 → F) (b' : Fin 2 → F') (hb : ∀ i, b i ≠ 0)
    (hb' : ∀ i, b' i ≠ 0) (A : ℕ) (c : Fin 4) :
    ((((∏ l : Fin 10, b7 b b' hb hb' l ^ (bitv 10 A l).val).1 c : Fˣ)) : F) =
      ∏ i : Fin 2, b i ^ (bitv 2 (A >>> (2 * c.val)) i).val := by
  simp only [Prod.fst_prod, Prod.pow_fst, Finset.prod_apply, Pi.pow_apply, Units.coe_prod,
    Units.val_pow_eq_pow_val]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, b7]
  fin_cases c <;> simp [bitv, Nat.testBit_shiftRight]

theorem b7_prod_snd (b : Fin 2 → F) (b' : Fin 2 → F') (hb : ∀ i, b i ≠ 0)
    (hb' : ∀ i, b' i ≠ 0) (A : ℕ) :
    ((((∏ l : Fin 10, b7 b b' hb hb' l ^ (bitv 10 A l).val).2 : F'ˣ)) : F') =
      ∏ i : Fin 2, b' i ^ (bitv 2 (A >>> 8) i).val := by
  simp only [Prod.snd_prod, Prod.pow_snd, Units.coe_prod, Units.val_pow_eq_pow_val]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, b7]
  simp [bitv, Nat.testBit_shiftRight]

/-- **Squares in `(Fin 4 → Fˣ) × F'ˣ` from squares at the five components.** -/
theorem isSquare_mul_rows7 (b : Fin 2 → F) (b' : Fin 2 → F') (hb : ∀ i, b i ≠ 0)
    (hb' : ∀ i, b' i ≠ 0) (x : (Fin 4 → Fˣ) × F'ˣ) (A : ℕ)
    (h : ∀ c : Fin 4, IsSquare ((x.1 c : F) * ∏ i : Fin 2, b i ^ (bitv 2 (A >>> (2 * c.val)) i).val))
    (h' : IsSquare ((x.2 : F') * ∏ i : Fin 2, b' i ^ (bitv 2 (A >>> 8) i).val)) :
    IsSquare (x * ∏ l : Fin 10, b7 b b' hb hb' l ^ (bitv 10 A l).val) := by
  have h1 : ∀ c, IsSquare ((x * ∏ l : Fin 10, b7 b b' hb hb' l ^ (bitv 10 A l).val).1 c) := fun c =>
    isSquare_units_of_isSquare _ (by
      rw [Prod.fst_mul, Pi.mul_apply, Units.val_mul, b7_prod_fst]; exact h c)
  have h2 : IsSquare (x * ∏ l : Fin 10, b7 b b' hb hb' l ^ (bitv 10 A l).val).2 :=
    isSquare_units_of_isSquare _ (by rw [Prod.snd_mul, Units.val_mul, b7_prod_snd]; exact h')
  choose r hr using h1
  obtain ⟨r', hr'⟩ := h2
  exact ⟨(r, r'), Prod.ext (funext hr) hr'⟩

/-- **Independence in `(Fin 4 → Fˣ) × F'ˣ` from independence at the two kinds of components.** -/
theorem indep_rows7 (b : Fin 2 → F) (b' : Fin 2 → F') (hb : ∀ i, b i ≠ 0) (hb' : ∀ i, b' i ≠ 0)
    (h1 : ∀ ε : Fin 2 → ZMod 2, IsSquare (∏ i, b i ^ (ε i).val) → ε = 0)
    (h2 : ∀ ε : Fin 2 → ZMod 2, IsSquare (∏ i, b' i ^ (ε i).val) → ε = 0) :
    ∀ ε : Fin 10 → ZMod 2, IsSquare (∏ l, b7 b b' hb hb' l ^ (ε l).val) → ε = 0 := by
  intro ε hsq
  -- projection to the c-th coordinate of the first component, mapped to F
  let π (c : Fin 4) : (Fin 4 → Fˣ) × F'ˣ →* F :=
    (Units.coeHom F).comp ((Pi.evalMonoidHom (fun _ : Fin 4 => Fˣ) c).comp (MonoidHom.fst (Fin 4 → Fˣ) F'ˣ))
  have h_sq_first (c : Fin 4) : IsSquare (π c (∏ l : Fin 10, b7 b b' hb hb' l ^ (ε l).val)) :=
    hsq.map (π c)
  -- compute the product under π c
  have h_prod_first (c : Fin 4) : π c (∏ l : Fin 10, b7 b b' hb hb' l ^ (ε l).val) =
      b 0 ^ ((ε ⟨2 * c.val, by omega⟩).val) * b 1 ^ ((ε ⟨2 * c.val + 1, by omega⟩).val) := by
    calc
      π c (∏ l : Fin 10, b7 b b' hb hb' l ^ (ε l).val)
          = ∏ l : Fin 10, π c (b7 b b' hb hb' l ^ (ε l).val) := by rw [map_prod]
      _ = ∏ l : Fin 10, (π c (b7 b b' hb hb' l)) ^ (ε l).val := by simp [map_pow]
      _ = b 0 ^ ((ε ⟨2 * c.val, by omega⟩).val) * b 1 ^ ((ε ⟨2 * c.val + 1, by omega⟩).val) := by
        fin_cases c <;>
        dsimp [π, b7] <;>
        simp [Fin.prod_univ_succ]
  have h_sq_first' (c : Fin 4) : IsSquare (b 0 ^ ((ε ⟨2 * c.val, by omega⟩).val) * b 1 ^ ((ε ⟨2 * c.val + 1, by omega⟩).val)) := by
    rw [← h_prod_first c]
    exact h_sq_first c
  -- use h1 to get ε values at even/odd positions are 0
  have h_eps_first (c : Fin 4) : ε ⟨2 * c.val, by omega⟩ = 0 ∧ ε ⟨2 * c.val + 1, by omega⟩ = 0 := by
    let ε_c : Fin 2 → ZMod 2 := fun i => ε ⟨2 * c.val + i.val, by omega⟩
    have h_sq_εc : IsSquare (∏ i : Fin 2, b i ^ (ε_c i).val) := by
      have : (∏ i : Fin 2, b i ^ (ε_c i).val) = b 0 ^ ((ε ⟨2 * c.val, by omega⟩).val) * b 1 ^ ((ε ⟨2 * c.val + 1, by omega⟩).val) := by
        simp [ε_c, Fin.prod_univ_succ]
      rw [this]
      exact h_sq_first' c
    have h_εc_zero := h1 ε_c h_sq_εc
    have h0 : ε_c 0 = 0 := by simpa [ε_c] using congrFun h_εc_zero 0
    have h1' : ε_c 1 = 0 := by simpa [ε_c] using congrFun h_εc_zero 1
    constructor
    · simpa [ε_c] using h0
    · simpa [ε_c] using h1'
  -- projection to the second component, mapped to F'
  let π' : (Fin 4 → Fˣ) × F'ˣ →* F' :=
    (Units.coeHom F').comp (MonoidHom.snd (Fin 4 → Fˣ) F'ˣ)
  have h_sq_second : IsSquare (π' (∏ l : Fin 10, b7 b b' hb hb' l ^ (ε l).val)) :=
    hsq.map π'
  have h_prod_second : π' (∏ l : Fin 10, b7 b b' hb hb' l ^ (ε l).val) =
      b' 0 ^ ((ε ⟨8, by omega⟩).val) * b' 1 ^ ((ε ⟨9, by omega⟩).val) := by
    calc
      π' (∏ l : Fin 10, b7 b b' hb hb' l ^ (ε l).val)
          = ∏ l : Fin 10, π' (b7 b b' hb hb' l ^ (ε l).val) := by rw [map_prod]
      _ = ∏ l : Fin 10, (π' (b7 b b' hb hb' l)) ^ (ε l).val := by simp [map_pow]
      _ = b' 0 ^ ((ε ⟨8, by omega⟩).val) * b' 1 ^ ((ε ⟨9, by omega⟩).val) := by
        dsimp [π', b7]
        simp [Fin.prod_univ_succ]
  have h_sq_second' : IsSquare (b' 0 ^ ((ε ⟨8, by omega⟩).val) * b' 1 ^ ((ε ⟨9, by omega⟩).val)) := by
    rw [← h_prod_second]
    exact h_sq_second
  have h_eps_second : ε ⟨8, by omega⟩ = 0 ∧ ε ⟨9, by omega⟩ = 0 := by
    let ε' : Fin 2 → ZMod 2 := fun i => ε ⟨8 + i.val, by omega⟩
    have h_sq_ε' : IsSquare (∏ i : Fin 2, b' i ^ (ε' i).val) := by
      have : (∏ i : Fin 2, b' i ^ (ε' i).val) = b' 0 ^ ((ε ⟨8, by omega⟩).val) * b' 1 ^ ((ε ⟨9, by omega⟩).val) := by
        simp [ε', Fin.prod_univ_succ]
      rw [this]
      exact h_sq_second'
    have h_ε'_zero := h2 ε' h_sq_ε'
    have h0 : ε' 0 = 0 := by simpa [ε'] using congrFun h_ε'_zero 0
    have h1' : ε' 1 = 0 := by simpa [ε'] using congrFun h_ε'_zero 1
    constructor
    · simpa [ε'] using h0
    · simpa [ε'] using h1'
  -- conclude by cases on Fin 10
  ext l
  fin_cases l
  · exact (h_eps_first 0).1
  · exact (h_eps_first 0).2
  · exact (h_eps_first 1).1
  · exact (h_eps_first 1).2
  · exact (h_eps_first 2).1
  · exact (h_eps_first 2).2
  · exact (h_eps_first 3).1
  · exact (h_eps_first 3).2
  · exact h_eps_second.1
  · exact h_eps_second.2

end Rows

/-! ## Points from two points of the curve -/

section TwoPt

variable {F : Type*} [Field F]

/-- `u = (X - x1)(X - x2)`. -/
noncomputable def uTwo (x1 x2 : F) : F[X] := (X - C x1) * (X - C x2)

/-- The line through `(x1, y1)` and `(x2, y2)`. -/
noncomputable def vTwo (x1 x2 y1 y2 : F) : F[X] := C y1 + C ((y2 - y1) / (x2 - x1)) * (X - C x1)

theorem uTwo_monic (x1 x2 : F) : (uTwo x1 x2).Monic := by
  unfold uTwo
  exact (monic_X_sub_C x1).mul (monic_X_sub_C x2)

theorem uTwo_natDegree (x1 x2 : F) : (uTwo x1 x2).natDegree = 2 := by
  unfold uTwo
  rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero x1) (Polynomial.X_sub_C_ne_zero x2),
    Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]

theorem uTwo_dvd (f : F[X]) {x1 x2 y1 y2 : F} (hx : x1 ≠ x2) (h1 : y1 ^ 2 = f.eval x1)
    (h2 : y2 ^ 2 = f.eval x2) : uTwo x1 x2 ∣ vTwo x1 x2 y1 y2 ^ 2 - f := by
  set P := vTwo x1 x2 y1 y2 ^ 2 - f with hP
  have hP_eval_x1 : P.eval x1 = 0 := by
    rw [hP]
    simp [eval_add, eval_C, eval_mul, eval_sub, eval_X, eval_pow, vTwo]
    rw [h1, sub_self]
  have hP_eval_x2 : P.eval x2 = 0 := by
    rw [hP]
    simp [eval_add, eval_C, eval_mul, eval_sub, eval_X, eval_pow, vTwo]
    field_simp [sub_ne_zero.mpr hx]
    ring_nf
    rw [h2, sub_self]
  have h_dvd1 : (X - C x1) ∣ P := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    exact hP_eval_x1
  have h_dvd2 : (X - C x2) ∣ P := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    exact hP_eval_x2
  have h_coprime : IsCoprime (X - C x1 : F[X]) (X - C x2) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hx)))
  have h_mul_dvd : (X - C x1) * (X - C x2) ∣ P :=
    IsCoprime.mul_dvd h_coprime h_dvd1 h_dvd2
  simpa [uTwo, hP] using h_mul_dvd

theorem isCoprime_uTwo_vTwo {x1 x2 y1 y2 : F} (hx : x1 ≠ x2) (h1 : y1 ≠ 0) (h2 : y2 ≠ 0) :
    IsCoprime (uTwo x1 x2) (vTwo x1 x2 y1 y2) := by
  rw [uTwo]
  apply IsCoprime.mul_left
  · -- IsCoprime (X - C x1) (vTwo x1 x2 y1 y2)
    have hirred : Irreducible (X - C (x1 : F)) := Polynomial.irreducible_X_sub_C _
    rw [hirred.coprime_iff_not_dvd]
    rw [Polynomial.dvd_iff_isRoot]
    have hv : (vTwo x1 x2 y1 y2).eval x1 = y1 := by
      dsimp [vTwo]
      simp
    rw [Polynomial.IsRoot, hv]
    exact h1
  · -- IsCoprime (X - C x2) (vTwo x1 x2 y1 y2)
    have hirred : Irreducible (X - C (x2 : F)) := Polynomial.irreducible_X_sub_C _
    rw [hirred.coprime_iff_not_dvd]
    rw [Polynomial.dvd_iff_isRoot]
    have hv : (vTwo x1 x2 y1 y2).eval x2 = y2 := by
      dsimp [vTwo]
      simp
      field_simp [sub_ne_zero.mpr hx]
      ring
    rw [Polynomial.IsRoot, hv]
    exact h2

theorem isCoprime_uTwo (f : F[X]) {x1 x2 : F} (h1 : f.eval x1 ≠ 0) (h2 : f.eval x2 ≠ 0) :
    IsCoprime (uTwo x1 x2) f := by
  have hx1 : IsCoprime (X - C x1) f := by
    have hirred : Irreducible (X - C x1) := Polynomial.irreducible_X_sub_C (r := x1)
    rw [hirred.coprime_iff_not_dvd]
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    exact h1
  have hx2 : IsCoprime (X - C x2) f := by
    have hirred : Irreducible (X - C x2) := Polynomial.irreducible_X_sub_C (r := x2)
    rw [hirred.coprime_iff_not_dvd]
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    exact h2
  have h_eq : uTwo x1 x2 = (X - C x1) * (X - C x2) := rfl
  rw [h_eq]
  exact IsCoprime.mul_left hx1 hx2

/-- **The point `P1 + P2 - ∞`** of two points `(x_i, y_i)` with `y_i ≠ 0`: its `x - T` image is the
class of `(T - x1)(T - x2)`. -/
theorem exists_jac_two (f : F[X]) [GoodSextic f] {x1 x2 y1 y2 : F} (hx : x1 ≠ x2)
    (h1 : y1 ^ 2 = f.eval x1) (h2 : y2 ^ 2 = f.eval x2) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0) :
    ∃ (D : Jac f) (hu : IsUnit (AdjoinRoot.mk f (uTwo x1 x2))),
      muJ f D = (QuotientGroup.mk hu.unit : H f) := by
  have h_dvd := uTwo_dvd f hx h1 h2
  rcases h_dvd with ⟨w, hw⟩
  have h_coprime := isCoprime_uTwo_vTwo hx hy1 hy2
  rcases h_coprime with ⟨a, b, h_ab⟩
  have hc : ∃ (a b c : F[X]), a * uTwo x1 x2 + b * vTwo x1 x2 y1 y2 + c * w = 1 := by
    refine ⟨a, b, 0, ?_⟩
    simpa using h_ab
  have h1_ne_zero : f.eval x1 ≠ 0 := by
    rw [← h1]
    exact pow_ne_zero 2 hy1
  have h2_ne_zero : f.eval x2 ≠ 0 := by
    rw [← h2]
    exact pow_ne_zero 2 hy2
  have hcop := isCoprime_uTwo f h1_ne_zero h2_ne_zero
  have h_deg : Even (uTwo x1 x2).natDegree := by
    rw [uTwo_natDegree x1 x2]
    exact even_two
  set D := mumfordJac f (uTwo_monic x1 x2) h_deg hw hc with hD
  have hu : IsUnit (AdjoinRoot.mk f (uTwo x1 x2)) :=
    FurioLombardo.Discharge.SelmerSpan.isUnit_mk_of_isCoprime hcop
  refine ⟨D, hu, ?_⟩
  rw [hD]
  exact FurioLombardo.Discharge.SelmerSpan.muJ_mumfordJac f (uTwo_monic x1 x2) h_deg hw hc hcop

end TwoPt

/-! ## From a subgroup containing the image to the image -/

/-- **`CoordCond` on the image of `μ`** from `CoordCond` on a subgroup `W` containing it. -/
theorem coordCond_range_of_imageIn {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (f : K[X])
    [GoodSextic (f.map φ)] {m c : ℕ} (g : Fin m → H f) (W : Subgroup (H (f.map φ)))
    (C : Matrix (Fin c) (Fin m) (ZMod 2)) (hI : ImageIn (f.map φ) W) (hC : CoordCond φ f g W C) :
    CoordCond φ f g (muJ (f.map φ)).range C := by
  intro a ha
  apply hC a
  rcases (MonoidHom.mem_range.1 ha) with ⟨Q, hQ⟩
  rw [← hQ]
  exact hI Q

end FurioLombardo.Discharge.SelmerBasis.W7
