import Mathlib
import FurioLombardo.Vendor.Toolbox.Polynomial.CoeffLim

/-!
# The root bound for square roots modulo converging quadratics

If monic quadratics `w n` tend to a monic quadratic `w0` of nonzero discriminant, `F n` tend to
`F0` in bounded degree, and `r n` (degree `< 2`) are square roots of `F n` modulo `w n`, then the
`r n` are eventually bounded. Only the triangle inequality is used: with `w = X² + aX + b`,
`r = r1 X + r0`, `ρ = 2 r0 - a r1`, `δ = a² - 4b`, one has `ρ r1 = G1`, `ρ² + δ r1² = G0` with
`G0, G1` explicit in the remainder of `F` mod `w`, hence `(ρ² - δ r1²)² = G0² - 4δ G1²`.

Origin: written for this formalization (finite index of the chart ball of a genus 2 Jacobian over
a 2-adic field, `FurioLombardo.Discharge.R7.FinIdx`).
-/

open Polynomial Filter Topology

namespace FurioLombardo.Vendor.Toolbox.PolyLim

variable {K : Type*} [NormedField K] {ι : Type*} {l : Filter ι}

/-- A monic polynomial of degree 2 is `X ^ 2 + C a * X + C b`. -/
theorem eq_quad_of_monic {w : K[X]} (hm : w.Monic) (hd : w.natDegree = 2) :
    w = X ^ 2 + C (w.coeff 1) * X + C (w.coeff 0) := by
  have h2 : w.coeff 2 = 1 := by rw [← hd]; exact hm.coeff_natDegree
  ext i
  rcases i with _ | _ | _ | i
  · simp
  · simp
  · simp [h2]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : w.natDegree < i + 3)]
    simp [coeff_X_pow]

/-- Remainder of a square modulo a monic quadratic. -/
theorem sq_mod_quad (a b r0 r1 : K) (F : K[X])
    (h : (X ^ 2 + C a * X + C b) ∣ F - (C r1 * X + C r0) ^ 2) :
    2 * r0 * r1 - a * r1 ^ 2 = (F %ₘ (X ^ 2 + C a * X + C b)).coeff 1 ∧
      r0 ^ 2 - b * r1 ^ 2 = (F %ₘ (X ^ 2 + C a * X + C b)).coeff 0 := by
  set w : K[X] := X ^ 2 + C a * X + C b with hw
  have hwm : w.Monic := by rw [hw]; monicity!
  have hwd : w.degree = 2 := by rw [hw]; compute_degree!
  have hR : (C (2 * r0 * r1 - a * r1 ^ 2) * X + C (r0 ^ 2 - b * r1 ^ 2)).degree < w.degree := by
    rw [hwd]
    exact (degree_linear_le).trans_lt (by decide)
  have hid : (C r1 * X + C r0) ^ 2 =
      C (2 * r0 * r1 - a * r1 ^ 2) * X + C (r0 ^ 2 - b * r1 ^ 2) + w * C (r1 ^ 2) := by
    rw [hw]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring
  have hsq : (C r1 * X + C r0) ^ 2 %ₘ w =
      C (2 * r0 * r1 - a * r1 ^ 2) * X + C (r0 ^ 2 - b * r1 ^ 2) :=
    (div_modByMonic_unique (C (r1 ^ 2)) _ hwm ⟨hid.symm, hR⟩).2
  have hF : F %ₘ w = (C r1 * X + C r0) ^ 2 %ₘ w := by
    have := add_modByMonic (F - (C r1 * X + C r0) ^ 2) ((C r1 * X + C r0) ^ 2) (q := w)
    rw [sub_add_cancel, (modByMonic_eq_zero_iff_dvd hwm).2 h, zero_add] at this
    exact this
  rw [hF, hsq]
  refine ⟨?_, ?_⟩ <;> simp only [coeff_add, coeff_C_mul, coeff_X_one, coeff_X_zero,
    coeff_C, one_ne_zero, ite_false, ite_true, mul_one, mul_zero, add_zero, zero_add]

/-- Norm bounds from `ρ r = G1` and `ρ ^ 2 + δ r ^ 2 = G0`, through
`(ρ ^ 2 - δ r ^ 2) ^ 2 = G0 ^ 2 - 4 δ G1 ^ 2`. -/
theorem norm_root_bound {ρ r δ G0 G1 : K} (h1 : ρ * r = G1) (h0 : ρ ^ 2 + δ * r ^ 2 = G0) :
    ‖(2 : K)‖ * ‖ρ‖ ^ 2 ≤ 2 * ‖G0‖ + (1 + 4 * ‖δ‖) * ‖G1‖ ∧
      ‖(2 : K)‖ * ‖δ‖ * ‖r‖ ^ 2 ≤ 2 * ‖G0‖ + (1 + 4 * ‖δ‖) * ‖G1‖ := by
  set S := ρ ^ 2 - δ * r ^ 2
  have hS : S ^ 2 = G0 ^ 2 - 4 * δ * G1 ^ 2 := by
    linear_combination (ρ ^ 2 + δ * r ^ 2 + G0) * h0 - 4 * δ * (ρ * r + G1) * h1
  have h4 : ‖(4 : K)‖ ≤ 4 := by
    have := Nat.norm_cast_le (α := K) 4
    simpa using this
  have hS2 : ‖S‖ ^ 2 ≤ ‖G0‖ ^ 2 + 4 * ‖δ‖ * ‖G1‖ ^ 2 := by
    rw [← norm_pow, hS]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_mul, norm_mul, norm_pow]
    gcongr
  have hSle : ‖S‖ ≤ ‖G0‖ + (1 + 4 * ‖δ‖) * ‖G1‖ := by
    have hd := norm_nonneg δ
    have hg0 := norm_nonneg G0
    have hg1 := norm_nonneg G1
    have hs := norm_nonneg S
    nlinarith [mul_nonneg hd hg1, mul_nonneg (mul_nonneg hd hd) (mul_nonneg hg1 hg1),
      mul_nonneg hg0 hg1, mul_nonneg (mul_nonneg hg0 hg1) hd]
  constructor
  · have : (2 : K) * ρ ^ 2 = G0 + S := by rw [← h0]; ring
    calc ‖(2 : K)‖ * ‖ρ‖ ^ 2 = ‖(2 : K) * ρ ^ 2‖ := by rw [norm_mul, norm_pow]
      _ = ‖G0 + S‖ := by rw [this]
      _ ≤ ‖G0‖ + ‖S‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  · have : (2 : K) * δ * r ^ 2 = G0 - S := by rw [← h0]; ring
    calc ‖(2 : K)‖ * ‖δ‖ * ‖r‖ ^ 2 = ‖(2 : K) * δ * r ^ 2‖ := by rw [norm_mul, norm_mul, norm_pow]
      _ = ‖G0 - S‖ := by rw [this]
      _ ≤ ‖G0‖ + ‖S‖ := norm_sub_le _ _
      _ ≤ _ := by linarith

/-- **Root bound**: if monic quadratics `w n` tend to a monic quadratic `w0` of nonzero
discriminant, `F n` tend to `F0` in bounded degree, and `r n` of degree `< 2` satisfy
`w n ∣ F n - r n ^ 2` eventually, then `psize 1 (r n)` is eventually bounded. -/
theorem rootBound (h2 : (2 : K) ≠ 0) {w F r : ι → K[X]} {w0 F0 : K[X]} {N : ℕ}
    (hw : PTendsto l w w0) (hwm : ∀ᶠ n in l, (w n).Monic ∧ (w n).natDegree = 2)
    (hw0m : w0.Monic) (hw0d : w0.natDegree = 2)
    (hdisc : w0.coeff 1 ^ 2 - 4 * w0.coeff 0 ≠ 0)
    (hF : PTendsto l F F0) (hFd : ∀ᶠ n in l, (F n).natDegree ≤ N)
    (hr : ∀ᶠ n in l, (r n).degree < 2 ∧ w n ∣ F n - r n ^ 2) :
    ∃ B : ℝ, ∀ᶠ n in l, psize 1 (r n) ≤ B := by
  have hmod := hF.modByMonic hFd hw hwm hw0m hw0d
  set a : ι → K := fun n => (w n).coeff 1 with ha_def
  set b : ι → K := fun n => (w n).coeff 0 with hb_def
  set F1 : ι → K := fun n => (F n %ₘ w n).coeff 1 with hF1_def
  set F0' : ι → K := fun n => (F n %ₘ w n).coeff 0 with hF0_def
  set δ : ι → K := fun n => a n ^ 2 - 4 * b n with hδ_def
  set G0 : ι → K := fun n => 4 * F0' n - 2 * a n * F1 n with hG0_def
  have ha : Tendsto a l (𝓝 (w0.coeff 1)) := hw 1
  have hb : Tendsto b l (𝓝 (w0.coeff 0)) := hw 0
  have hF1 : Tendsto F1 l (𝓝 ((F0 %ₘ w0).coeff 1)) := hmod 1
  have hF0 : Tendsto F0' l (𝓝 ((F0 %ₘ w0).coeff 0)) := hmod 0
  have hδ : Tendsto δ l (𝓝 (w0.coeff 1 ^ 2 - 4 * w0.coeff 0)) :=
    (ha.pow 2).sub (hb.const_mul 4)
  have hG0 : Tendsto G0 l
      (𝓝 (4 * (F0 %ₘ w0).coeff 0 - 2 * w0.coeff 1 * (F0 %ₘ w0).coeff 1)) :=
    (hF0.const_mul 4).sub ((ha.const_mul 2).mul hF1)
  set A := ‖w0.coeff 1‖ + 1
  set g0 := ‖4 * (F0 %ₘ w0).coeff 0 - 2 * w0.coeff 1 * (F0 %ₘ w0).coeff 1‖ + 1
  set g1 := ‖(F0 %ₘ w0).coeff 1‖ + 1
  set dd := ‖w0.coeff 1 ^ 2 - 4 * w0.coeff 0‖ + 1
  set e := ‖w0.coeff 1 ^ 2 - 4 * w0.coeff 0‖ / 2
  have hdpos : 0 < ‖w0.coeff 1 ^ 2 - 4 * w0.coeff 0‖ := norm_pos_iff.2 hdisc
  have he : 0 < e := by positivity
  have h2pos : 0 < ‖(2 : K)‖ := norm_pos_iff.2 h2
  set c := 2 * g0 + (1 + 4 * dd) * g1
  set R := 1 + c / ‖(2 : K)‖
  set R1 := 1 + c / (‖(2 : K)‖ * e)
  refine ⟨(R + A * R1) / ‖(2 : K)‖ + R1, ?_⟩
  have eA : ∀ᶠ n in l, ‖a n‖ < A := ha.norm.eventually_lt_const (lt_add_one _)
  have eG0 : ∀ᶠ n in l, ‖G0 n‖ < g0 := hG0.norm.eventually_lt_const (lt_add_one _)
  have eG1 : ∀ᶠ n in l, ‖F1 n‖ < g1 := hF1.norm.eventually_lt_const (lt_add_one _)
  have eδ : ∀ᶠ n in l, ‖δ n‖ < dd := hδ.norm.eventually_lt_const (lt_add_one _)
  have eδ' : ∀ᶠ n in l, e < ‖δ n‖ := hδ.norm.eventually_const_lt (half_lt_self hdpos)
  filter_upwards [hr, hwm, eA, eG0, eG1, eδ, eδ'] with n hrn hwn hAn hG0n hG1n hδn hδn'
  have hwq := eq_quad_of_monic hwn.1 hwn.2
  have hrq : r n = C ((r n).coeff 1) * X + C ((r n).coeff 0) :=
    eq_X_add_C_of_degree_le_one (Order.le_of_lt_succ hrn.1)
  obtain ⟨e1, e0⟩ := sq_mod_quad (a n) (b n) ((r n).coeff 0) ((r n).coeff 1) (F n)
    (by rw [ha_def, hb_def]; dsimp only; rw [← hwq, ← hrq]; exact hrn.2)
  rw [ha_def, hb_def] at e1 e0
  dsimp only at e1 e0
  rw [← hwq] at e1 e0
  set r0 := (r n).coeff 0
  set r1 := (r n).coeff 1
  obtain ⟨hρ, hr1⟩ := norm_root_bound (ρ := 2 * r0 - a n * r1) (r := r1) (δ := δ n) (G0 := G0 n)
    (G1 := F1 n) (by rw [hF1_def]; linear_combination e1)
    (by rw [hδ_def, hG0_def, hF1_def, hF0_def]; linear_combination 4 * e0 - 2 * a n * e1)
  have hc : 2 * ‖G0 n‖ + (1 + 4 * ‖δ n‖) * ‖F1 n‖ ≤ c := by
    have := norm_nonneg (F1 n)
    have := norm_nonneg (δ n)
    have : (1 + 4 * ‖δ n‖) * ‖F1 n‖ ≤ (1 + 4 * dd) * g1 := by
      apply mul_le_mul <;> nlinarith
    linarith
  have hρ' : ‖2 * r0 - a n * r1‖ ≤ R := by
    have h := hρ.trans hc
    have : ‖2 * r0 - a n * r1‖ ^ 2 ≤ c / ‖(2 : K)‖ := by
      rw [le_div_iff₀ h2pos]; linarith
    nlinarith [norm_nonneg (2 * r0 - a n * r1)]
  have hr1' : ‖r1‖ ≤ R1 := by
    have h := hr1.trans hc
    have : ‖r1‖ ^ 2 ≤ c / (‖(2 : K)‖ * e) := by
      rw [le_div_iff₀ (mul_pos h2pos he)]
      have : ‖(2 : K)‖ * e * ‖r1‖ ^ 2 ≤ ‖(2 : K)‖ * ‖δ n‖ * ‖r1‖ ^ 2 := by
        gcongr
      linarith
    nlinarith [norm_nonneg r1]
  have hr0' : ‖r0‖ ≤ (R + A * R1) / ‖(2 : K)‖ := by
    rw [le_div_iff₀ h2pos]
    have h : (2 : K) * r0 = (2 * r0 - a n * r1) + a n * r1 := by ring
    calc ‖r0‖ * ‖(2 : K)‖ = ‖(2 * r0 - a n * r1) + a n * r1‖ := by rw [← h, norm_mul, mul_comm]
      _ ≤ ‖2 * r0 - a n * r1‖ + ‖a n‖ * ‖r1‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ R + A * R1 := by gcongr
  have hps : psize 1 (r n) = ‖r0‖ + ‖r1‖ := by
    simp [psize, Finset.sum_range_succ, r0, r1]
  rw [hps]
  linarith

end FurioLombardo.Vendor.Toolbox.PolyLim
