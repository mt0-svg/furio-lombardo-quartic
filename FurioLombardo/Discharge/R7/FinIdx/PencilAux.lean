import Mathlib
import FurioLombardo.Discharge.R7.FinIdx.Comp
import FurioLombardo.Vendor.Toolbox.Polynomial.CoeffLimRoot
import FurioLombardo.Vendor.Toolbox.Polynomial.CoeffLimFibre
import FurioLombardo.Discharge.R7.FinIdx.PencilB0

/-!
# Helpers for PENCIL (R7)

The case analysis of `pencil` (Pencil.lean): the conclusion `PencilGoal` of the three cases
(a pair `T`, a subsequence along which `compW (D n) T → uT T.t`), its passage to subsequences, the
finishing step (`pencil_finish`: root bound, extraction, closedness of `Z`), case (A) (bounded `t`,
Lemma A at a double root), the reduction of case (B0) to `pencil_B0_false`, case (B1)
(reflection `reflect 6`, Lemma A at `α = 0`, reflection back), and the dichotomy `pencil_core`:
either `t` is bounded along a subsequence (A), or `|t| → ∞` and then either frequently
`|t1| < ε |t0|²` for every `ε` (B0) or eventually `|t1| ≥ ε |t0|²` for some `ε` (B1).
-/

open Polynomial Filter Topology
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.PolyLim

namespace FurioLombardo.Discharge.R7.FinIdx

/-! ### Algebra of the quadratics `uT` -/

section Alg

variable {L : Type*} [Field L]

theorem uT_coeff_zero (t : Fin 2 → L) : (uT t).coeff 0 = t 1 := by
  simp [uT]

theorem uT_coeff_one (t : Fin 2 → L) : (uT t).coeff 1 = t 0 := by
  simp [uT]

theorem uT_coeff_two (t : Fin 2 → L) : (uT t).coeff 2 = 1 := by
  simp [uT]

theorem uT_eval (t : Fin 2 → L) (x : L) : (uT t).eval x = x ^ 2 + t 0 * x + t 1 := by
  simp [uT]

theorem reflect_uT (t : Fin 2 → L) :
    Polynomial.reflect 2 (uT t) = C (t 1) * X ^ 2 + C (t 0) * X + 1 := by
  ext i
  rw [coeff_reflect]
  rcases i with _ | _ | _ | i
  · rw [show revAt 2 0 = 2 by decide]
    simp [uT, coeff_C, coeff_one]
  · rw [show revAt 2 1 = 1 by decide]
    simp [uT, coeff_C, coeff_one]
  · rw [show revAt 2 2 = 0 by decide]
    simp [uT, coeff_X, coeff_C, coeff_one]
  · rw [revAt_eq_self_of_lt (by omega)]
    simp [uT, coeff_one, coeff_X_pow]

/-- The reflection of `uT t`, normalized. -/
theorem reflect_uT_eq (t : Fin 2 → L) (h : t 1 ≠ 0) :
    Polynomial.reflect 2 (uT t) = C (t 1) * uT ![t 0 / t 1, (t 1)⁻¹] := by
  rw [reflect_uT]
  simp only [uT, Matrix.cons_val_zero, Matrix.cons_val_one]
  have e : C (t 1) * C (t 1)⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ h, C_1]
  rw [div_eq_mul_inv, C_mul]
  linear_combination (-C (t 0) * X - 1) * e

theorem comp_scale_uT (t : Fin 2 → L) {a : L} (ha : a ≠ 0) :
    C (a ^ 2)⁻¹ * (uT t).comp (C a * X) = uT ![t 0 / a, t 1 / a ^ 2] := by
  simp only [uT, add_comp, mul_comp, pow_comp, X_comp, C_comp, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have e : C (a ^ 2)⁻¹ * C a ^ 2 = 1 := by
    rw [← C_pow, ← C_mul, inv_mul_cancel₀ (pow_ne_zero 2 ha), C_1]
  have e1 : C (t 0 / a) = C (a ^ 2)⁻¹ * C (t 0) * C a := by
    rw [← C_mul, ← C_mul]; congr 1; field_simp
  have e2 : C (t 1 / a ^ 2) = C (a ^ 2)⁻¹ * C (t 1) := by
    rw [← C_mul]; congr 1; field_simp
  rw [e1, e2]
  linear_combination X ^ 2 * e

/-- A double root: `uT t = (X - α)²` when the discriminant vanishes. -/
theorem uT_eq_sq (h2 : (2 : L) ≠ 0) {t : Fin 2 → L} (h : t 0 ^ 2 - 4 * t 1 = 0) :
    uT t = (X - C (-(t 0) / 2)) ^ 2 := by
  set α := -(t 0) / 2 with hα
  have h0 : t 0 = -2 * α := by rw [hα]; field_simp
  have h1 : t 1 = α ^ 2 := by rw [hα]; field_simp; linear_combination -h
  rw [uT, h0, h1]
  simp only [map_mul, map_neg, map_pow, map_ofNat]
  ring

/-- Reflection of a multiple of a monic polynomial. -/
theorem reflect_dvd_reflect {u p : L[X]} (hu : u.Monic) {d m : ℕ} (hud : u.natDegree = d)
    (hp : p.natDegree ≤ d + m) (h : u ∣ p) :
    Polynomial.reflect d u ∣ Polynomial.reflect (d + m) p := by
  obtain ⟨k, rfl⟩ := h
  have hk : k.natDegree ≤ m := by
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · rw [hu.natDegree_mul' hk0, hud] at hp; omega
  rw [reflect_mul u k hud.le hk]
  exact dvd_mul_right _ _

theorem dvd_eval_eq_zero {p q : L[X]} {x : L} (h : p ∣ q) (hp : p.eval x = 0) :
    q.eval x = 0 := by
  obtain ⟨k, rfl⟩ := h
  rw [eval_mul, hp, zero_mul]

theorem qt_coeff {c : L} (hc : c ≠ 0) (Q : L[X]) :
    (C c * Polynomial.reflect 2 Q).coeff 2 = c * Q.coeff 0 ∧
      C ((C c * Polynomial.reflect 2 Q).coeff 2)⁻¹ * (C c * Polynomial.reflect 2 Q) =
        C (Q.coeff 0)⁻¹ * Polynomial.reflect 2 Q := by
  have h1 : (C c * Polynomial.reflect 2 Q).coeff 2 = c * Q.coeff 0 := by
    rw [coeff_C_mul, coeff_reflect, show revAt 2 2 = 0 by decide]
  refine ⟨h1, ?_⟩
  rw [h1, ← mul_assoc, ← C_mul, mul_inv, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc, mul_one]

end Alg

/-! ### Subsequences -/

section Seq

variable {K : Type*} [NormedField K] [ProperSpace K]

theorem strictMono_add_const (N : ℕ) : StrictMono (fun n => n + N) :=
  fun _ _ h => Nat.add_lt_add_right h N

/-- Extraction under an eventual bound. -/
theorem exists_subseq_ptendsto' {p : ℕ → K[X]} {N : ℕ} (hd : ∀ n, (p n).natDegree ≤ N) {B : ℝ}
    (hB : ∀ᶠ n in atTop, psize N (p n) ≤ B) :
    ∃ q : K[X], q.natDegree ≤ N ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ PTendsto atTop (p ∘ φ) q := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 hB
  obtain ⟨q, hq, φ, hφ, h⟩ := exists_subseq_ptendsto (p := fun n => p (n + M))
    (fun n => hd _) (B := B) (fun n => hM _ (Nat.le_add_left _ _))
  exact ⟨q, hq, fun n => φ n + M, (strictMono_add_const M).comp hφ, h⟩

/-- Extraction of pairs under an eventual bound. -/
theorem exists_subseq_dtendsto' {D : ℕ → MPair K} (hv : ∀ n, (D n).v.degree < 2) {B : ℝ}
    (hB : ∀ᶠ n in atTop, dsize (D n) ≤ B) :
    ∃ D0 : MPair K, ∃ φ : ℕ → ℕ, StrictMono φ ∧ DTendsto atTop (D ∘ φ) D0 := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 hB
  obtain ⟨D0, φ, hφ, h⟩ := exists_subseq_dtendsto (D := fun n => D (n + M))
    (fun n => hv _) (B := B) (fun n => hM _ (Nat.le_add_left _ _))
  exact ⟨D0, fun n => φ n + M, (strictMono_add_const M).comp hφ, h⟩

/-- A sequence of bounded degree with no convergent subsequence is unbounded. -/
theorem tendsto_psize_atTop {V : ℕ → K[X]} {N : ℕ} (hd : ∀ n, (V n).natDegree ≤ N)
    (h : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ V0 : K[X], PTendsto atTop (fun n => V (ψ n)) V0 → False) :
    Tendsto (fun n => psize N (V n)) atTop atTop := by
  by_contra hne
  rw [tendsto_atTop] at hne
  simp only [not_forall, Filter.not_eventually, not_le] at hne
  obtain ⟨B, hB⟩ := hne
  obtain ⟨ψ1, hψ1, hB1⟩ := extraction_of_frequently_atTop hB
  obtain ⟨V0, -, ψ2, hψ2, hlim⟩ := exists_subseq_ptendsto (p := fun n => V (ψ1 n))
    (fun n => hd _) (B := B) (fun n => (hB1 n).le)
  exact h (ψ1 ∘ ψ2) (hψ1.comp hψ2) V0 hlim

/-- If the remainders `v n = V n mod u n` are unbounded, so are the `V n`. -/
theorem tendsto_psize_of_mod {u V v : ℕ → K[X]} {u0 : K[X]} (hu : PTendsto atTop u u0)
    (hum : ∀ n, (u n).Monic ∧ (u n).natDegree = 2) (hu0m : u0.Monic) (hu0d : u0.natDegree = 2)
    (hVd : ∀ n, (V n).natDegree ≤ 3) (hvd : ∀ n, (v n).degree < 2) (hdv : ∀ n, u n ∣ V n - v n)
    (hv : Tendsto (fun n => psize 1 (v n)) atTop atTop) :
    Tendsto (fun n => psize 3 (V n)) atTop atTop := by
  refine tendsto_psize_atTop hVd fun ψ hψ V0 hV => ?_
  have hmod : ∀ n, V n %ₘ u n = v n := fun n => by
    rw [modByMonic_eq_of_dvd_sub (hum n).1 (hdv n), (modByMonic_eq_self_iff (hum n).1).2]
    rw [degree_eq_natDegree (hum n).1.ne_zero, (hum n).2]
    exact_mod_cast hvd n
  have h1 := hV.modByMonic (N := 3) (d := 2) (Eventually.of_forall fun n => hVd _)
    (hu.comp_tendsto hψ.tendsto_atTop) (Eventually.of_forall fun n => hum _) hu0m hu0d
  simp only [Function.comp_apply, hmod] at h1
  exact not_tendsto_atTop_of_tendsto_nhds (h1.psize 1) (hv.comp hψ.tendsto_atTop)

end Seq

/-! ### Estimates on sequences -/

section Leaf

theorem b1_norm_top {K : Type*} [NormedField K] {x y : ℕ → K}
    (hτ : Tendsto (fun n => ‖x n‖ + ‖y n‖) atTop atTop) {ε : ℝ} (hε : 0 < ε)
    (hB : ∀ᶠ n in atTop, ε * ‖x n‖ ^ 2 ≤ ‖y n‖) : Tendsto (fun n => ‖y n‖) atTop atTop := by
  set k := 1 + 1/ε with hk_def
  have hk_pos : 0 < k := by
    have hpos : 0 < 1/ε := div_pos (by norm_num) hε
    linarith
  rw [tendsto_atTop] at hτ ⊢
  intro b
  have hτ' := hτ (1 + b * k)
  have hx_bound (a : ℝ) : a ≤ 1 + a ^ 2 := by
    have hsq : (a - 1/2) ^ 2 ≥ 0 := sq_nonneg _
    nlinarith
  filter_upwards [hτ', hB] with n hnτ hnB
  have hx_sq : ‖x n‖ ^ 2 ≤ ‖y n‖ / ε := (le_div_iff₀ hε).mpr (by simpa [mul_comm] using hnB)
  have hx : ‖x n‖ ≤ 1 + ‖x n‖ ^ 2 := hx_bound _
  have h_comb : ‖x n‖ ≤ 1 + (‖y n‖ / ε) := by linarith
  have h_sum : ‖x n‖ + ‖y n‖ ≤ 1 + ‖y n‖ * k := by
    calc
      ‖x n‖ + ‖y n‖ ≤ (1 + (‖y n‖ / ε)) + ‖y n‖ := by linarith
      _ = 1 + ‖y n‖ * (1 + 1/ε) := by ring
      _ = 1 + ‖y n‖ * k := by rw [hk_def]
  have hb : b * k ≤ ‖y n‖ * k := by linarith
  exact le_of_mul_le_mul_right hb hk_pos

theorem b1_inv {K : Type*} [NormedField K] {y : ℕ → K}
    (hy : Tendsto (fun n => ‖y n‖) atTop atTop) : Tendsto (fun n => (y n)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  exact tendsto_inv_atTop_zero.comp hy

theorem b1_eval_ne {K : Type*} [NormedField K] {t : ℕ → Fin 2 → K}
    (hq0 : Tendsto (fun n => t n 0 / t n 1) atTop (𝓝 0))
    (hq1 : Tendsto (fun n => (t n 1)⁻¹) atTop (𝓝 0)) (h1 : ∀ᶠ n in atTop, t n 1 ≠ 0) (s : K) :
    ∀ᶠ n in atTop, (uT (t n)).eval s ≠ 0 := by
  have hlim : Tendsto (fun n : ℕ => s ^ 2 * (t n 1)⁻¹ + s * (t n 0 / t n 1) + 1) atTop (𝓝 1) := by
    have h1' : Tendsto (fun n : ℕ => s ^ 2 * (t n 1)⁻¹) atTop (𝓝 0) := by
      simpa [mul_zero] using Tendsto.const_mul (s ^ 2) hq1
    have h2' : Tendsto (fun n : ℕ => s * (t n 0 / t n 1)) atTop (𝓝 0) := by
      simpa [mul_zero] using Tendsto.const_mul s hq0
    have hsum : Tendsto (fun n : ℕ => s ^ 2 * (t n 1)⁻¹ + s * (t n 0 / t n 1)) atTop (𝓝 0) := by
      simpa [add_zero] using Tendsto.add h1' h2'
    have htotal : Tendsto (fun n : ℕ => (s ^ 2 * (t n 1)⁻¹ + s * (t n 0 / t n 1)) + 1) atTop
        (𝓝 (0 + 1)) :=
      Tendsto.add hsum tendsto_const_nhds
    simpa [add_assoc, add_zero] using htotal
  have hne : ∀ᶠ n in atTop, s ^ 2 * (t n 1)⁻¹ + s * (t n 0 / t n 1) + 1 ≠ 0 :=
    hlim.eventually_ne (by norm_num : (1 : K) ≠ 0)
  have h_eq : ∀ᶠ n in atTop, (uT (t n)).eval s * (t n 1)⁻¹ =
      s ^ 2 * (t n 1)⁻¹ + s * (t n 0 / t n 1) + 1 := by
    filter_upwards [h1] with n hn
    calc
      (uT (t n)).eval s * (t n 1)⁻¹ =
          ((X ^ 2 + C (t n 0) * X + C (t n 1)).eval s) * (t n 1)⁻¹ := rfl
      _ = (s ^ 2 + (t n 0) * s + (t n 1)) * (t n 1)⁻¹ := by simp
      _ = s ^ 2 * (t n 1)⁻¹ + s * (t n 0 / t n 1) + 1 := by
        field_simp [hn]
  filter_upwards [hne, h_eq] with n hn_ne hn_eq
  intro hzero
  apply hn_ne
  calc
    s ^ 2 * (t n 1)⁻¹ + s * (t n 0 / t n 1) + 1 = (uT (t n)).eval s * (t n 1)⁻¹ :=
        hn_eq.symm
    _ = 0 * (t n 1)⁻¹ := by rw [hzero]
    _ = 0 := by ring

theorem b1_ratio {K : Type*} [NormedField K] {x y : ℕ → K}
    (hy : Tendsto (fun n => ‖y n‖) atTop atTop) {ε : ℝ} (hε : 0 < ε)
    (hB : ∀ᶠ n in atTop, ε * ‖x n‖ ^ 2 ≤ ‖y n‖) : Tendsto (fun n => x n / y n) atTop (𝓝 0) := by
  -- Eventually, ‖y n‖ > 0
  have hy_pos : ∀ᶠ n in atTop, 0 < ‖y n‖ := by
    have h1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ ‖y n‖ := hy.eventually (eventually_ge_atTop 1)
    filter_upwards [h1] with n hn
    linarith
  -- Bound: ‖x n / y n‖ ^ 2 ≤ 1 / (ε * ‖y n‖) eventually
  have h_sq_bound : ∀ᶠ n in atTop, ‖x n / y n‖ ^ 2 ≤ (1 : ℝ) / (ε * ‖y n‖) := by
    filter_upwards [hy_pos, hB] with n hpos hBn
    have hx_sq_bound : ‖x n‖ ^ 2 ≤ ‖y n‖ / ε := by
      calc
        ‖x n‖ ^ 2 = (ε * ‖x n‖ ^ 2) / ε := by field_simp [hε.ne.symm]
        _ ≤ ‖y n‖ / ε := by
          gcongr
    calc
      ‖x n / y n‖ ^ 2 = (‖x n‖ / ‖y n‖) ^ 2 := by rw [norm_div]
      _ = ‖x n‖ ^ 2 / ‖y n‖ ^ 2 := by ring
      _ ≤ (‖y n‖ / ε) / ‖y n‖ ^ 2 := by
        gcongr
      _ = (1 : ℝ) / (ε * ‖y n‖) := by
        field_simp [hε.ne.symm, hpos.ne.symm]
  -- The upper bound tends to 0
  have h_tendsto_upper : Tendsto (fun n => (1 : ℝ) / (ε * ‖y n‖)) atTop (𝓝 0) := by
    have h_tendsto_prod : Tendsto (fun n => ε * ‖y n‖) atTop atTop :=
      Tendsto.const_mul_atTop hε hy
    have h := tendsto_inv_atTop_zero.comp h_tendsto_prod
    -- h: Tendsto ((fun r => r⁻¹) ∘ fun n => ε * ‖y n‖) atTop (𝓝 0)
    -- we need: Tendsto (fun n => (1 : ℝ) / (ε * ‖y n‖)) atTop (𝓝 0)
    have h_eq : (fun n => (1 : ℝ) / (ε * ‖y n‖)) = ((fun r => r⁻¹) ∘ fun n => ε * ‖y n‖) := by
      ext n
      simp [one_div]
    rw [h_eq]
    exact h
  -- Nonnegativity of ‖x n / y n‖ ^ 2
  have h_nonneg : ∀ᶠ n in atTop, 0 ≤ ‖x n / y n‖ ^ 2 := by
    filter_upwards with n
    positivity
  -- By squeeze theorem, ‖x n / y n‖ ^ 2 → 0
  have h_tendsto_sq : Tendsto (fun n => ‖x n / y n‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero' h_nonneg h_sq_bound h_tendsto_upper
  -- Then ‖x n / y n‖ = Real.sqrt (‖x n / y n‖ ^ 2) → Real.sqrt 0 = 0
  have h_tendsto_norm : Tendsto (fun n => ‖x n / y n‖) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp h_tendsto_sq
    -- h: Tendsto (Real.sqrt ∘ (fun n => ‖x n / y n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0))
    have h_sqrt_zero : Real.sqrt (0 : ℝ) = 0 := Real.sqrt_zero
    have h_fun_eq : (Real.sqrt ∘ (fun n => ‖x n / y n‖ ^ 2)) = (fun n => ‖x n / y n‖) := by
      ext n
      rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
    rw [h_fun_eq, h_sqrt_zero] at h
    exact h
  -- Finally, convert from norm tending to zero to the original sequence tending to zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact h_tendsto_norm

theorem b0_extract {K : Type*} [NormedField K] {t : ℕ → Fin 2 → K}
    (hτ : Tendsto (fun n => ‖t n 0‖ + ‖t n 1‖) atTop atTop)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, t n 0 ≠ 0 ∧ ‖t n 1‖ < ε * ‖t n 0‖ ^ 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, t (φ n) 0 ≠ 0) ∧
      Tendsto (fun n => ‖t (φ n) 1‖ / ‖t (φ n) 0‖ ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖t (φ n) 0‖) atTop atTop := by
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_frequently
    (P := fun k n => t n 0 ≠ 0 ∧ ‖t n 1‖ < (1 / ((k : ℝ) + 1)) * ‖t n 0‖ ^ 2)
    (fun k => hB _ (by positivity))
  refine ⟨φ, hφ, fun k => (hP k).1, ?_, ?_⟩
  · refine squeeze_zero (fun k => by positivity) (fun k => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h0 : 0 < ‖t (φ k) 0‖ ^ 2 := by have := norm_pos_iff.2 (hP k).1; positivity
    rw [div_le_iff₀ h0]
    exact (hP k).2.le
  · have hτφ := hτ.comp hφ.tendsto_atTop
    have hle : ∀ k, ‖t (φ k) 1‖ ≤ ‖t (φ k) 0‖ ^ 2 := fun k => by
      have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [k.cast_nonneg (α := ℝ)]
      have := (hP k).2
      nlinarith [sq_nonneg ‖t (φ k) 0‖]
    rw [tendsto_atTop]
    intro b
    filter_upwards [hτφ.eventually_ge_atTop (max b 0 + max b 0 ^ 2)] with k hk
    simp only [Function.comp_apply] at hk
    by_contra hlt
    rw [not_le] at hlt
    have hc : 0 ≤ max b 0 := le_max_right _ _
    have hx := norm_nonneg (t (φ k) 0)
    have hlt' : ‖t (φ k) 0‖ < max b 0 := lt_of_lt_of_le hlt (le_max_left _ _)
    have := hle k
    nlinarith [mul_self_lt_mul_self hx hlt']

theorem bounded_extract {K : Type*} [NormedField K] [ProperSpace K] {t : ℕ → Fin 2 → K} {B : ℝ}
    (hB : ∃ᶠ n in atTop, ‖t n 0‖ + ‖t n 1‖ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ t0 : Fin 2 → K, Tendsto (fun n => t (φ n)) atTop (𝓝 t0) ∧
      ∀ n, ‖t (φ n) 0‖ + ‖t (φ n) 1‖ ≤ B := by
  rcases Filter.extraction_of_frequently_atTop hB with ⟨φ1, hφ1_mono, hφ1_bound⟩
  have hB_nonneg : 0 ≤ B := by
    have h := hφ1_bound 0
    have h0 : 0 ≤ ‖t (φ1 0) 0‖ + ‖t (φ1 0) 1‖ := by
      positivity
    linarith
  have h_closedBall : ∀ n, t (φ1 n) ∈ Metric.closedBall (0 : Fin 2 → K) B := by
    intro n
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [pi_norm_le_iff_of_nonneg hB_nonneg]
    intro i
    fin_cases i <;> simp
    · have h := hφ1_bound n
      have h0 : 0 ≤ ‖t (φ1 n) 0‖ := norm_nonneg _
      have h1 : 0 ≤ ‖t (φ1 n) 1‖ := norm_nonneg _
      linarith
    · have h := hφ1_bound n
      have h0 : 0 ≤ ‖t (φ1 n) 0‖ := norm_nonneg _
      have h1 : 0 ≤ ‖t (φ1 n) 1‖ := norm_nonneg _
      linarith
  rcases tendsto_subseq_of_bounded Metric.isBounded_closedBall h_closedBall
    with ⟨t0, _, φ2, hφ2_mono, h_tendsto⟩
  refine ⟨φ1 ∘ φ2, hφ1_mono.comp hφ2_mono, t0, ?_, ?_⟩
  · simpa [Function.comp_def] using h_tendsto
  · intro n
    simpa [Function.comp_def] using hφ1_bound (φ2 n)

/-- Renormalization of a limit through `reflect 2`. -/
theorem renorm_limit {K : Type*} [NormedField K] {Q : ℕ → K[X]} {w : K[X]}
    (hQ0 : ∀ᶠ n in atTop, (Q n).coeff 0 ≠ 0) (hw : w.coeff 2 ≠ 0)
    (h : PTendsto atTop (fun n => C ((Q n).coeff 0)⁻¹ * Polynomial.reflect 2 (Q n))
      (Polynomial.reflect 2 w)) :
    PTendsto atTop (fun n => C ((Q n).coeff 2)⁻¹ * Q n) (C (w.coeff 2)⁻¹ * w) := by
  have hP : PTendsto atTop (fun n => C ((Q n).coeff 0)⁻¹ * Q n) w := by
    have := h.reflect 2
    simpa only [reflect_C_mul, reflect_reflect] using this
  refine (hP.C_mul ((hP 2).inv₀ hw)).congr' (hQ0.mono fun n hn => ?_)
  simp only [coeff_C_mul]
  rw [← mul_assoc, ← C_mul, mul_inv, inv_inv, mul_comm ((Q n).coeff 0), mul_assoc,
    mul_inv_cancel₀ hn, mul_one]

end Leaf

/-! ### The case analysis -/

variable {K : Type*} [NormedField K] [ProperSpace K] {g : K[X]} [GoodSextic g]

/-- The common conclusion of the cases: a pair `T` of nonzero discriminant and a subsequence along
which the resultants are nonzero and `compW (D n) T → uT T.t`. -/
def PencilGoal (g : K[X]) (Dn : ℕ → MPair K) : Prop :=
  ∃ T : MPair K, InZ g T ∧ T.t 0 ^ 2 - 4 * T.t 1 ≠ 0 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
    (∀ n, res2 (Dn (φ n)).t T.t ≠ 0) ∧
    PTendsto atTop (fun n => compW g (Dn (φ n)) T) (uT T.t)

omit [ProperSpace K] [GoodSextic g] in
theorem PencilGoal.of_subseq {Dn : ℕ → MPair K} {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (h : PencilGoal g (fun n => Dn (ψ n))) : PencilGoal g Dn := by
  obtain ⟨T, hT, hd, φ, hφ, hr, hW⟩ := h
  exact ⟨T, hT, hd, ψ ∘ φ, hψ.comp hφ, hr, hW⟩

omit [ProperSpace K] [GoodSextic g] in
theorem PencilGoal.of_shift {Dn : ℕ → MPair K} (N : ℕ)
    (h : PencilGoal g (fun n => Dn (n + N))) : PencilGoal g Dn :=
  PencilGoal.of_subseq (strictMono_add_const N) h

/-- **Finish**: root bound, extraction and closedness of `Z`. -/
theorem pencil_finish {Dn : ℕ → MPair K} (hZ : ∀ n, InZ g (Dn n)) (h : PencilGoal g Dn) :
    ∃ T : MPair K, InZ g T ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ n, res2 (Dn (φ n)).t T.t ≠ 0) ∧
      ∃ ys : MPair K, InZ g ys ∧ DTendsto atTop (fun n => comp g (Dn (φ n)) T) ys := by
  obtain ⟨T, hT, hd, φ, hφ, hr, hW⟩ := h
  set E : ℕ → MPair K := fun n => comp g (Dn (φ n)) T with hE
  have hEZ : ∀ n, InZ g (E n) := fun n => InZ.comp (hZ _) hT (hr n)
  obtain ⟨B, hB⟩ := rootBound (GoodSextic.two_ne_zero (f := g)) hW
    (Eventually.of_forall fun n => compW_monic (hZ _) hT (hr n)) (uT_monic _) (uT_natDegree _)
    (by rwa [uT_coeff_one, uT_coeff_zero]) (ptendsto_const g) (N := 6)
    (Eventually.of_forall fun _ => (GoodSextic.natDegree_eq (f := g)).le)
    (r := fun n => (E n).v)
    (Eventually.of_forall fun n => ⟨(hEZ n).1, by
      rw [← uT_comp (hZ _) hT (hr n)]; exact (hEZ n).2⟩)
  have h0 : ∀ᶠ n in atTop, ‖(E n).t 0‖ ≤ ‖(uT T.t).coeff 1‖ + 1 :=
    (hW 1).norm.eventually (ge_mem_nhds (lt_add_one _))
  have h1 : ∀ᶠ n in atTop, ‖(E n).t 1‖ ≤ ‖(uT T.t).coeff 0‖ + 1 :=
    (hW 0).norm.eventually (ge_mem_nhds (lt_add_one _))
  obtain ⟨ys, ψ, hψ, hlim⟩ := exists_subseq_dtendsto' (D := E) (fun n => (hEZ n).1)
    (B := ‖(uT T.t).coeff 1‖ + 1 + (‖(uT T.t).coeff 0‖ + 1) + B)
    ((h0.and (h1.and hB)).mono fun n hn => by
      simp only [dsize]
      linarith [hn.1, hn.2.1, hn.2.2])
  exact ⟨T, hT, φ ∘ ψ, hφ.comp hψ, fun n => hr _, ys,
    InZ.of_tendsto (Eventually.of_forall fun n => hEZ _) hlim, hlim⟩

omit [ProperSpace K] [GoodSextic g] in
/-- The chosen translation targets. -/
theorem pencil_target (hpts : ∀ A : Finset K, ∃ s1 s2 : K, s1 ∉ A ∧ s2 ∉ A ∧ s1 ≠ s2 ∧ s1 ≠ 0 ∧
      s2 ≠ 0 ∧ ∃ vT : K[X], InZ g ⟨![-(s1 + s2), s1 * s2], vT⟩) (A : Finset K) :
    ∃ s1 s2 : K, ∃ T : MPair K, T.t = ![-(s1 + s2), s1 * s2] ∧ InZ g T ∧
      T.t 0 ^ 2 - 4 * T.t 1 ≠ 0 ∧ T.t 1 ≠ 0 ∧ ∀ x ∈ A, (uT T.t).eval x ≠ 0 := by
  obtain ⟨s1, s2, hs1, hs2, hs12, hs10, hs20, vT, hT⟩ := hpts A
  refine ⟨s1, s2, ⟨![-(s1 + s2), s1 * s2], vT⟩, rfl, hT, ?_, ?_, fun x hx => ?_⟩
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have : (s1 - s2) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hs12)
    intro h; apply this; linear_combination h
  · simp only [Matrix.cons_val_one]
    exact mul_ne_zero hs10 hs20
  · have e : (uT ![-(s1 + s2), s1 * s2]).eval x = (x - s1) * (x - s2) := by
      rw [uT_eval]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
    change (uT ![-(s1 + s2), s1 * s2]).eval x ≠ 0
    rw [e]
    exact mul_ne_zero (sub_ne_zero.2 fun h => hs1 (h ▸ hx)) (sub_ne_zero.2 fun h => hs2 (h ▸ hx))

/-- **Case (A)**: `t` converges, `v` is unbounded. -/
theorem pencil_A {Dn : ℕ → MPair K} (hZ : ∀ n, InZ g (Dn n)) {t0 : Fin 2 → K}
    (ht : Tendsto (fun n => (Dn n).t) atTop (𝓝 t0))
    (hv : Tendsto (fun n => psize 1 (Dn n).v) atTop atTop) {T : MPair K} (hT : InZ g T)
    (hα : (uT T.t).eval (-(t0 0) / 2) ≠ 0) : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ n, res2 (Dn (φ n)).t T.t ≠ 0) ∧
      PTendsto atTop (fun n => compW g (Dn (φ n)) T) (uT T.t) := by
  have h2 : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := g)
  have hu := ptendsto_uT ht
  -- the limit quadratic has a double root, else the root bound bounds `v`
  have hdisc : t0 0 ^ 2 - 4 * t0 1 = 0 := by
    by_contra hne
    obtain ⟨B, hB⟩ := rootBound h2 hu
      (Eventually.of_forall fun n => ⟨uT_monic _, uT_natDegree _⟩) (uT_monic _) (uT_natDegree _)
      (by rwa [uT_coeff_one, uT_coeff_zero]) (ptendsto_const g) (N := 6)
      (Eventually.of_forall fun _ => (GoodSextic.natDegree_eq (f := g)).le)
      (r := fun n => (Dn n).v) (Eventually.of_forall fun n => hZ n)
    obtain ⟨n, hn1, hn2⟩ := (hB.and (hv.eventually_gt_atTop B)).exists
    linarith
  set α := -(t0 0) / 2 with hαdef
  have hsq : uT t0 = (X - C α) ^ 2 := uT_eq_sq h2 hdisc
  have ht0 : t0 = ![-(α + α), α * α] := by
    have e0 : t0 0 = -(α + α) := by rw [hαdef]; field_simp; ring
    have e1 : t0 1 = α * α := by rw [hαdef]; field_simp; linear_combination (-1 : K) * hdisc
    funext i
    fin_cases i
    · exact e0
    · exact e1
  have hres0 : res2 t0 T.t ≠ 0 := by
    rw [res2_comm, ht0, res2_eq_eval_mul]
    exact mul_ne_zero hα hα
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_res2 ht tendsto_const_nhds).eventually_ne hres0)
  have hres : ∀ n, res2 (Dn (n + N)).t T.t ≠ 0 := fun n => hN _ (Nat.le_add_left _ _)
  have huN : PTendsto atTop (fun n => uT (Dn (n + N)).t) ((X - C α) ^ 2) := by
    rw [← hsq]
    exact hu.comp_tendsto (tendsto_add_atTop_nat N)
  have hV : Tendsto (fun n => psize 3 (crtV (Dn (n + N)) T)) atTop atTop :=
    tendsto_psize_of_mod huN (fun n => ⟨uT_monic _, uT_natDegree _⟩)
      (by rw [← hsq]; exact uT_monic _) (by rw [← hsq]; exact uT_natDegree _)
      (fun n => natDegree_crtV (hZ _).1) (fun n => (hZ _).1) (fun n => dvd_crtV_sub _ _)
      (hv.comp (tendsto_add_atTop_nat N))
  obtain ⟨ψ, hψ, -, hlim⟩ := lemmaA (g := g) (q0 := uT T.t) (vT := T.v) (α := α)
    (GoodSextic.natDegree_eq (f := g)).le (uT_monic _) (uT_natDegree _) hα huN
    (fun n => ⟨uT_monic _, uT_natDegree _⟩) (fun n => natDegree_crtV (hZ _).1) hV
    (fun n => dvd_crtV_sub' (hres n)) (fun n => dvd_f_sub_crtV_sq (hZ _) hT (hres n))
  exact ⟨fun k => ψ k + N, (strictMono_add_const N).comp hψ, fun k => hres _, hlim⟩

/-- **Case (B0)**, reduction: frequently `|t1| < ε |t0|²` for every `ε` is impossible. -/
theorem pencil_B0 {Dn : ℕ → MPair K} (hZ : ∀ n, InZ g (Dn n))
    (hτ : Tendsto (fun n => ‖(Dn n).t 0‖ + ‖(Dn n).t 1‖) atTop atTop)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop, (Dn n).t 0 ≠ 0 ∧ ‖(Dn n).t 1‖ < ε * ‖(Dn n).t 0‖ ^ 2) :
    False := by
  obtain ⟨φ, -, h0, hrat, hinf⟩ := b0_extract (t := fun n => (Dn n).t) hτ hB
  exact pencil_B0_false (Dn := fun n => Dn (φ n)) (fun n => hZ _) h0 hrat hinf

/-- **Case (B1)**, core: `t0/t1 → 0`, `1/t1 → 0`. Reflect by `reflect 6`, apply Lemma A at
`α = 0` to the reflected data, and reflect the limit back. -/
theorem pencil_B1_core {Dn : ℕ → MPair K} (hZ : ∀ n, InZ g (Dn n)) {T : MPair K} (hT : InZ g T)
    (hT1 : T.t 1 ≠ 0) (h1 : ∀ n, (Dn n).t 1 ≠ 0) (hres : ∀ n, res2 (Dn n).t T.t ≠ 0)
    (hq0 : Tendsto (fun n => (Dn n).t 0 / (Dn n).t 1) atTop (𝓝 0))
    (hq1 : Tendsto (fun n => ((Dn n).t 1)⁻¹) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ PTendsto atTop (fun n => compW g (Dn (φ n)) T) (uT T.t) := by
  have hg6 : g.natDegree = 6 := GoodSextic.natDegree_eq
  set tt : ℕ → Fin 2 → K := fun n => ![(Dn n).t 0 / (Dn n).t 1, ((Dn n).t 1)⁻¹] with htt_def
  set tT : Fin 2 → K := ![T.t 0 / T.t 1, (T.t 1)⁻¹] with htT_def
  set V : ℕ → K[X] := fun n => crtV (Dn n) T with hV_def
  set Q : ℕ → K[X] := fun n => compQ g (Dn n) T with hQ_def
  have hrn : ∀ n, reflect 2 (uT (Dn n).t) = C ((Dn n).t 1) * uT (tt n) :=
    fun n => reflect_uT_eq _ (h1 n)
  have hrT : reflect 2 (uT T.t) = C (T.t 1) * uT tT := reflect_uT_eq _ hT1
  have hVd : ∀ n, (V n).natDegree ≤ 3 := fun n => natDegree_crtV (hZ n).1
  have hRVd : ∀ n, (reflect 3 (V n)).natDegree ≤ 3 :=
    fun n => natDegree_reflect_le.trans (max_le le_rfl (hVd n))
  have hf'd : (reflect 6 g).natDegree ≤ 6 := natDegree_reflect_le.trans (max_le le_rfl hg6.le)
  have hsq : ∀ n, reflect 6 (g - V n ^ 2) = reflect 6 g - reflect 3 (V n) ^ 2 := by
    intro n
    rw [reflect_sub, sq, sq]
    congr 1
    exact reflect_mul _ _ (hVd n) (hVd n)
  have hr4 : ∀ n, reflect 4 (uT (Dn n).t * uT T.t) =
      C ((Dn n).t 1 * T.t 1) * (uT (tt n) * uT tT) := by
    intro n
    have e : reflect 4 (uT (Dn n).t * uT T.t) = reflect 2 (uT (Dn n).t) * reflect 2 (uT T.t) :=
      reflect_mul _ _ (uT_natDegree _).le (uT_natDegree _).le
    rw [e, hrn, hrT, C_mul]
    ring
  -- the congruences after reflection
  have hdvT : ∀ n, uT tT ∣ reflect 3 (V n) - reflect 3 T.v := by
    intro n
    have hvT : T.v.natDegree ≤ 1 := natDegree_le_one_of_degree_lt_two hT.1
    have h' : reflect 2 (uT T.t) ∣ reflect 3 (V n - T.v) :=
      reflect_dvd_reflect (uT_monic T.t) (uT_natDegree T.t) (m := 1)
        ((natDegree_sub_le _ _).trans (max_le (hVd n) (hvT.trans (by norm_num))))
        (dvd_crtV_sub' (hres n))
    rw [reflect_sub, hrT] at h'
    exact (C_mul_dvd hT1).1 h'
  have hdv : ∀ n, uT (tt n) * uT tT ∣ reflect 6 g - reflect 3 (V n) ^ 2 := by
    intro n
    have h' : reflect 4 (uT (Dn n).t * uT T.t) ∣ reflect 6 (g - V n ^ 2) :=
      reflect_dvd_reflect (uT_mul_monic (Dn n).t T.t) (uT_mul_natDegree _ _) (m := 2)
        (natDegree_f_sub_crtV_sq (hZ n).1) (dvd_f_sub_crtV_sq (hZ n) hT (hres n))
    rw [hr4, hsq] at h'
    exact (C_mul_dvd (mul_ne_zero (h1 n) hT1)).1 h'
  -- the reflected quadratics tend to `X²`
  have htt : Tendsto tt atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    fin_cases i
    · simpa [htt_def] using hq0
    · simpa [htt_def] using hq1
  have hu0 : PTendsto atTop (fun n => uT (tt n)) (uT 0) := ptendsto_uT htt
  have hu : PTendsto atTop (fun n => uT (tt n)) ((X - C 0) ^ 2) := by
    rw [map_zero, sub_zero, ← uT_zero]
    exact hu0
  have hle : ∀ n, (reflect 6 g - reflect 3 (V n) ^ 2).natDegree ≤ 6 := fun n =>
    (natDegree_sub_le _ _).trans (max_le hf'd (natDegree_pow_le.trans (by have := hRVd n; omega)))
  -- the reflected cubics are unbounded: a limit would make the leading coefficient a square
  have hV : Tendsto (fun n => psize 3 (reflect 3 (V n))) atTop atTop := by
    refine tendsto_psize_atTop hRVd fun ψ hψ V0 hV0 => ?_
    have hd : uT 0 ∣ reflect 6 g - V0 ^ 2 :=
      ((ptendsto_const (reflect 6 g)).sub (hV0.pow 2)).dvd (N := 6) (d := 2)
        (Eventually.of_forall fun n => hle _) (hu0.comp_tendsto hψ.tendsto_atTop)
        (Eventually.of_forall fun n => ⟨uT_monic _, uT_natDegree _⟩) (uT_monic _)
        (uT_natDegree _) (Eventually.of_forall fun n => dvd_trans (dvd_mul_right _ _) (hdv _))
    have h0 := dvd_eval_eq_zero (x := 0) hd (by simp [uT_eval])
    have hl : (reflect 6 g).eval 0 = g.leadingCoeff := by
      rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero, leadingCoeff, hg6]
    rw [eval_sub, eval_pow, hl] at h0
    exact GoodSextic.not_isSquare_leadingCoeff (f := g)
      ⟨V0.eval 0, by linear_combination h0⟩
  obtain ⟨ψ, hψ, hne, hlim⟩ := lemmaA (g := reflect 6 g) (q0 := uT tT) (vT := reflect 3 T.v)
    (α := 0) hf'd (uT_monic _) (uT_natDegree _) (by simp [uT_eval, htT_def, hT1]) hu
    (fun n => ⟨uT_monic _, uT_natDegree _⟩) hRVd hV hdvT hdv
  -- the reflected quotient is `t1 τ1 · reflect 2 Q`
  have hc : ∀ n, (Dn n).t 1 * T.t 1 ≠ 0 := fun n => mul_ne_zero (h1 n) hT1
  have hq : ∀ n, (reflect 6 g - reflect 3 (V n) ^ 2) /ₘ (uT (tt n) * uT tT) =
      C ((Dn n).t 1 * T.t 1) * reflect 2 (Q n) := by
    intro n
    have e4 : reflect 6 (uT (Dn n).t * uT T.t * Q n) =
        reflect 4 (uT (Dn n).t * uT T.t) * reflect 2 (Q n) :=
      reflect_mul _ _ (uT_mul_natDegree _ _).le (natDegree_compQ (hZ n) hT (hres n))
    have e : reflect 6 g - reflect 3 (V n) ^ 2 =
        uT (tt n) * uT tT * (C ((Dn n).t 1 * T.t 1) * reflect 2 (Q n)) := by
      rw [← hsq, f_sub_crtV_sq (hZ n) hT (hres n), e4, hr4]
      ring
    rw [e, mul_divByMonic_cancel_left _ ((uT_monic _).mul (uT_monic _))]
  have hlim' : PTendsto atTop (fun k => C ((Q (ψ k)).coeff 0)⁻¹ * reflect 2 (Q (ψ k)))
      (reflect 2 (C (T.t 1)⁻¹ * uT T.t)) := by
    have e : reflect 2 (C (T.t 1)⁻¹ * uT T.t) = uT tT := by
      rw [reflect_C_mul, hrT, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hT1, C_1, one_mul]
    rw [e]
    refine hlim.congr' (Eventually.of_forall fun k => ?_)
    simp only [hq]
    exact (qt_coeff (hc _) _).2
  have hQ0 : ∀ᶠ k in atTop, (Q (ψ k)).coeff 0 ≠ 0 := hne.mono fun k hk => by
    simp only [hq, (qt_coeff (hc _) _).1] at hk
    exact right_ne_zero_of_mul hk
  have hw2 : (C (T.t 1)⁻¹ * uT T.t).coeff 2 = (T.t 1)⁻¹ := by
    rw [coeff_C_mul, uT_coeff_two, mul_one]
  have hfin := renorm_limit hQ0 (by rw [hw2]; exact inv_ne_zero hT1) hlim'
  rw [hw2, ← mul_assoc, ← C_mul, inv_inv, mul_inv_cancel₀ hT1, C_1, one_mul] at hfin
  exact ⟨ψ, hψ, hfin⟩

/-- **Case (B1)**: eventually `|t1| ≥ ε |t0|²`. -/
theorem pencil_B1 (hpts : ∀ A : Finset K, ∃ s1 s2 : K, s1 ∉ A ∧ s2 ∉ A ∧ s1 ≠ s2 ∧ s1 ≠ 0 ∧
      s2 ≠ 0 ∧ ∃ vT : K[X], InZ g ⟨![-(s1 + s2), s1 * s2], vT⟩)
    {Dn : ℕ → MPair K} (hZ : ∀ n, InZ g (Dn n))
    (hτ : Tendsto (fun n => ‖(Dn n).t 0‖ + ‖(Dn n).t 1‖) atTop atTop) {ε : ℝ} (hε : 0 < ε)
    (hB : ∀ᶠ n in atTop, ε * ‖(Dn n).t 0‖ ^ 2 ≤ ‖(Dn n).t 1‖) : PencilGoal g Dn := by
  have hy : Tendsto (fun n => ‖(Dn n).t 1‖) atTop atTop := b1_norm_top hτ hε hB
  have hq0 : Tendsto (fun n => (Dn n).t 0 / (Dn n).t 1) atTop (𝓝 0) := b1_ratio hy hε hB
  have hq1 : Tendsto (fun n => ((Dn n).t 1)⁻¹) atTop (𝓝 0) := b1_inv hy
  have h1 : ∀ᶠ n in atTop, (Dn n).t 1 ≠ 0 :=
    (hy.eventually_gt_atTop 0).mono fun n hn => norm_pos_iff.1 hn
  obtain ⟨s1, s2, T, hTt, hT, hdisc, hT1, -⟩ := pencil_target hpts ∅
  have hres : ∀ᶠ n in atTop, res2 (Dn n).t T.t ≠ 0 := by
    filter_upwards [b1_eval_ne (t := fun n => (Dn n).t) hq0 hq1 h1 s1,
      b1_eval_ne (t := fun n => (Dn n).t) hq0 hq1 h1 s2] with n hn1 hn2
    rw [hTt, res2_eq_eval_mul]
    exact mul_ne_zero hn1 hn2
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h1.and hres)
  refine PencilGoal.of_shift N ⟨T, hT, hdisc, ?_⟩
  obtain ⟨φ, hφ, hlim⟩ := pencil_B1_core (Dn := fun n => Dn (n + N)) (fun n => hZ _) hT hT1
    (fun n => (hN _ (Nat.le_add_left _ _)).1) (fun n => (hN _ (Nat.le_add_left _ _)).2)
    (hq0.comp (tendsto_add_atTop_nat N)) (hq1.comp (tendsto_add_atTop_nat N))
  exact ⟨φ, hφ, fun n => (hN _ (Nat.le_add_left _ _)).2, hlim⟩

/-- **The case analysis.** -/
theorem pencil_core (hpts : ∀ A : Finset K, ∃ s1 s2 : K, s1 ∉ A ∧ s2 ∉ A ∧ s1 ≠ s2 ∧ s1 ≠ 0 ∧
      s2 ≠ 0 ∧ ∃ vT : K[X], InZ g ⟨![-(s1 + s2), s1 * s2], vT⟩)
    {Dn : ℕ → MPair K} (hZ : ∀ n, InZ g (Dn n))
    (hinf : Tendsto (fun n => dsize (Dn n)) atTop atTop) : PencilGoal g Dn := by
  by_cases hA : ∃ B : ℝ, ∃ᶠ n in atTop, ‖(Dn n).t 0‖ + ‖(Dn n).t 1‖ ≤ B
  · -- (A): `t` bounded along a subsequence
    obtain ⟨B, hB⟩ := hA
    obtain ⟨φ, hφ, t0, ht, hBφ⟩ := bounded_extract (t := fun n => (Dn n).t) hB
    refine PencilGoal.of_subseq hφ ?_
    have hv : Tendsto (fun n => psize 1 (Dn (φ n)).v) atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_)
        (tendsto_atTop_add_const_right _ (-B) (hinf.comp hφ.tendsto_atTop))
      have := hBφ n
      simp only [Function.comp_apply, dsize]
      linarith
    obtain ⟨s1, s2, T, -, hT, hdisc, -, hTα⟩ := pencil_target hpts {-(t0 0) / 2}
    obtain ⟨ψ, hψ, hr, hW⟩ := pencil_A (Dn := fun n => Dn (φ n)) (fun n => hZ _) ht hv hT
      (hTα _ (Finset.mem_singleton_self _))
    exact ⟨T, hT, hdisc, ψ, hψ, hr, hW⟩
  · simp only [not_exists, Filter.not_frequently, not_le] at hA
    have hτ : Tendsto (fun n => ‖(Dn n).t 0‖ + ‖(Dn n).t 1‖) atTop atTop :=
      tendsto_atTop.2 fun b => (hA b).mono fun n hn => hn.le
    by_cases hB0 : ∀ ε : ℝ, 0 < ε →
        ∃ᶠ n in atTop, (Dn n).t 0 ≠ 0 ∧ ‖(Dn n).t 1‖ < ε * ‖(Dn n).t 0‖ ^ 2
    · exact (pencil_B0 hZ hτ hB0).elim
    · simp only [not_forall, Filter.not_frequently, not_and, not_lt] at hB0
      obtain ⟨ε, hε, hev⟩ := hB0
      refine pencil_B1 hpts hZ hτ hε (hev.mono fun n hn => ?_)
      by_cases h0 : (Dn n).t 0 = 0
      · rw [h0, norm_zero]
        simp
      · exact hn h0

end FurioLombardo.Discharge.R7.FinIdx
