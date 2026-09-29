import Mathlib
import FurioLombardo.Vendor.LeanPool.RectangleIntegral

/-!
# Shifting a vertical line integral past finitely many simple poles (lane M2)

`H = Σ_{p ∈ P} Φ_p(s)/(s - p)` with every `Φ_p` holomorphic on an open set containing the closed
strip `σL ≤ Re s ≤ σR`, the poles real and strictly inside the strip. If `H` is integrable on
both boundary lines and small on horizontal segments far up and down, then

  `∫ H(σR + it) dt - ∫ H(σL + it) dt = 2π Σ_p Φ_p(p)`.

Rectangle Cauchy theorem from Mathlib (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`)
for the regular parts `dslope Φ_p p`, and `NumberField.Odlyzko.rectangleIntegral_principal`
(Lean Pool, adapted from PNT+) for the principal parts `Φ_p(p)/(s - p)`.
-/

namespace FurioLombardo.M2.Zimmert

open Complex MeasureTheory Filter Topology Set
open NumberField.Odlyzko

open scoped Interval

/-- A function continuous on the closed rectangle is integrable on its border. -/
lemma rectangleBorderIntegrable_of_continuousOn {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    RectangleBorderIntegrable f z w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ContinuousOn.intervalIntegrable ?_
    refine hf.comp (by fun_prop) ?_
    intro x hx
    refine ⟨by simpa using hx, by simp [left_mem_uIcc]⟩
  · refine ContinuousOn.intervalIntegrable ?_
    refine hf.comp (by fun_prop) ?_
    intro x hx
    refine ⟨by simpa using hx, by simp [right_mem_uIcc]⟩
  · refine ContinuousOn.intervalIntegrable ?_
    refine hf.comp (by fun_prop) ?_
    intro y hy
    refine ⟨by simp [right_mem_uIcc], by simpa using hy⟩
  · refine ContinuousOn.intervalIntegrable ?_
    refine hf.comp (by fun_prop) ?_
    intro y hy
    refine ⟨by simp [left_mem_uIcc], by simpa using hy⟩

/-- Cauchy's theorem for rectangles in the notation `rectangleIntegral`. -/
lemma rectangleIntegral_eq_zero {f : ℂ → ℂ} {z w : ℂ}
    (hf : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectangleIntegral f z w = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf
  simpa [rectangleIntegral, horizontalIntegral, verticalSegmentIntegral] using h

/-- The points of the border of a rectangle are not strictly inside it. -/
lemma border_ne_of_inside {z w p : ℂ} (hP : z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im)
    {s : ℂ} (hs : s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im) : s ≠ p := by
  rintro rfl
  rcases hs with h | h | h | h <;> linarith [hP.1, hP.2.1, hP.2.2.1, hP.2.2.2]

/-- The rectangle integral of `Σ_p Φ_p(s)/(s - p)` is `2πi Σ_p Φ_p(p)`. -/
theorem rectangleIntegral_sum_poles {U : Set ℂ} (hU : IsOpen U) (P : Finset ℂ)
    (Φ : ℂ → ℂ → ℂ) (hΦ : ∀ p ∈ P, DifferentiableOn ℂ (Φ p) U) {z w : ℂ}
    (hzw : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U)
    (hP : ∀ p ∈ P, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im) :
    rectangleIntegral (fun s => ∑ p ∈ P, Φ p s / (s - p)) z w
      = 2 * Real.pi * I * ∑ p ∈ P, Φ p p := by
  set Rect := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hRect
  have hpU : ∀ p ∈ P, p ∈ U := fun p hp => hzw ⟨by
      simp only [mem_preimage]
      exact ⟨le_trans (min_le_left _ _) (hP p hp).1.le,
        le_trans (hP p hp).2.1.le (le_max_right _ _)⟩, by
      simp only [mem_preimage]
      exact ⟨le_trans (min_le_left _ _) (hP p hp).2.2.1.le,
        le_trans (hP p hp).2.2.2.le (le_max_right _ _)⟩⟩
  have hdsl : ∀ p ∈ P, DifferentiableOn ℂ (dslope (Φ p) p) U := fun p hp =>
    (differentiableOn_dslope (hU.mem_nhds (hpU p hp))).mpr (hΦ p hp)
  -- on the border, split each term into principal part and regular part
  have hsplit : ∀ p ∈ P, ∀ s : ℂ, s ≠ p →
      Φ p s / (s - p) = Φ p p / (s - p) + dslope (Φ p) p s := by
    intro p _ s hs
    rw [dslope_of_ne _ hs, slope_def_field]
    have : s - p ≠ 0 := sub_ne_zero.mpr hs
    field_simp
    ring
  have hcongr : rectangleIntegral (fun s => ∑ p ∈ P, Φ p s / (s - p)) z w
      = rectangleIntegral (fun s => ∑ p ∈ P, (Φ p p / (s - p) + dslope (Φ p) p s)) z w := by
    apply rectangleIntegral_congr
    · intro x _
      refine Finset.sum_congr rfl (fun p hp => hsplit p hp _ ?_)
      exact border_ne_of_inside (hP p hp) (Or.inr (Or.inr (Or.inl (by simp))))
    · intro x _
      refine Finset.sum_congr rfl (fun p hp => hsplit p hp _ ?_)
      exact border_ne_of_inside (hP p hp) (Or.inr (Or.inr (Or.inr (by simp))))
    · intro y _
      refine Finset.sum_congr rfl (fun p hp => hsplit p hp _ ?_)
      exact border_ne_of_inside (hP p hp) (Or.inr (Or.inl (by simp)))
    · intro y _
      refine Finset.sum_congr rfl (fun p hp => hsplit p hp _ ?_)
      exact border_ne_of_inside (hP p hp) (Or.inl (by simp))
  rw [hcongr]
  -- border integrability of the two kinds of terms
  have hprin_int : ∀ p ∈ P, RectangleBorderIntegrable (fun s => Φ p p / (s - p)) z w := by
    intro p hp
    have hne : ∀ s : ℂ, (s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im) →
        s - p ≠ 0 := fun s hs => sub_ne_zero.mpr (border_ne_of_inside (hP p hp) hs)
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro x _
      exact hne _ (Or.inr (Or.inr (Or.inl (by simp))))
    · refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro x _
      exact hne _ (Or.inr (Or.inr (Or.inr (by simp))))
    · refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro y _
      exact hne _ (Or.inr (Or.inl (by simp)))
    · refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro y _
      exact hne _ (Or.inl (by simp))
  have hreg_int : ∀ p ∈ P, RectangleBorderIntegrable (dslope (Φ p) p) z w := fun p hp =>
    rectangleBorderIntegrable_of_continuousOn ((hdsl p hp).continuousOn.mono hzw)
  have hterm_int : ∀ p ∈ P,
      RectangleBorderIntegrable (fun s => Φ p p / (s - p) + dslope (Φ p) p s) z w :=
    fun p hp => (hprin_int p hp).add_integrable (hreg_int p hp)
  rw [rectangleIntegral_fun_sum (f := fun p s => Φ p p / (s - p) + dslope (Φ p) p s) hterm_int,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [(hprin_int p hp).add (hreg_int p hp),
    rectangleIntegral_eq_zero ((hdsl p hp).mono hzw), add_zero]
  exact rectangleIntegral_principal (hP p hp).1 (hP p hp).2.1 (hP p hp).2.2.1 (hP p hp).2.2.2

/-- **Contour shift.** Let `H` agree off `P` with `Σ_{p ∈ P} Φ_p(s)/(s - p)`, the `Φ_p` holomorphic
on an open set containing the closed strip `σL ≤ Re s ≤ σR`, the poles real and strictly inside.
If `H` is integrable on both boundary lines and uniformly small on horizontal segments far up and
down, then `∫ H(σR + it) dt - ∫ H(σL + it) dt = 2π Σ_p Φ_p(p)`. -/
theorem contour_shift {σL σR : ℝ} (hLR : σL < σR) {U : Set ℂ} (hU : IsOpen U)
    (hstrip : ∀ s : ℂ, σL ≤ s.re → s.re ≤ σR → s ∈ U) (P : Finset ℂ) (Φ : ℂ → ℂ → ℂ)
    (hΦ : ∀ p ∈ P, DifferentiableOn ℂ (Φ p) U)
    (hP : ∀ p ∈ P, σL < p.re ∧ p.re < σR ∧ p.im = 0) (H : ℂ → ℂ)
    (hH : ∀ s : ℂ, s ∉ P → H s = ∑ p ∈ P, Φ p s / (s - p))
    (hR : Integrable fun t : ℝ => H (σR + t * I))
    (hL : Integrable fun t : ℝ => H (σL + t * I))
    (hhor : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ x : ℝ, σL ≤ x → x ≤ σR →
      ‖H (x + T * I)‖ ≤ ε ∧ ‖H (x + (-T) * I)‖ ≤ ε) :
    (∫ t : ℝ, H (σR + t * I)) - ∫ t : ℝ, H (σL + t * I) = 2 * Real.pi * ∑ p ∈ P, Φ p p := by
  set S := ∑ p ∈ P, Φ p p with hS
  -- the rectangle identity for every height T > 0
  have hrect : ∀ T : ℝ, 0 < T →
      (∫ x in σL..σR, H (x + (-T) * I)) - (∫ x in σL..σR, H (x + T * I))
        + I * (∫ y in (-T)..T, H (σR + y * I)) - I * (∫ y in (-T)..T, H (σL + y * I))
        = 2 * Real.pi * I * S := by
    intro T hT
    set z : ℂ := σL + (-T) * I with hz
    set w : ℂ := σR + T * I with hw
    have hzre : z.re = σL := by simp [hz]
    have hzim : z.im = -T := by simp [hz]
    have hwre : w.re = σR := by simp [hw]
    have hwim : w.im = T := by simp [hw]
    have hsub : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U := by
      intro s hs
      have h1 := hs.1
      simp only [mem_preimage, hzre, hwre, uIcc_of_le hLR.le] at h1
      exact hstrip s h1.1 h1.2
    have hPin : ∀ p ∈ P, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im := by
      intro p hp
      obtain ⟨h1, h2, h3⟩ := hP p hp
      rw [hzre, hwre, hzim, hwim, h3]
      exact ⟨h1, h2, by linarith, hT⟩
    have hmain := rectangleIntegral_sum_poles hU P Φ hΦ hsub hPin
    have hcongr : rectangleIntegral H z w
        = rectangleIntegral (fun s => ∑ p ∈ P, Φ p s / (s - p)) z w := by
      have hoff : ∀ s : ℂ, (s.re = z.re ∨ s.re = w.re ∨ s.im = z.im ∨ s.im = w.im) → s ∉ P :=
        fun s hs hsP => border_ne_of_inside (hPin s hsP) hs rfl
      apply rectangleIntegral_congr
      · intro x _
        exact hH _ (hoff _ (Or.inr (Or.inr (Or.inl (by simp)))))
      · intro x _
        exact hH _ (hoff _ (Or.inr (Or.inr (Or.inr (by simp)))))
      · intro y _
        exact hH _ (hoff _ (Or.inr (Or.inl (by simp))))
      · intro y _
        exact hH _ (hoff _ (Or.inl (by simp)))
    rw [← hcongr] at hmain
    simpa [rectangleIntegral, horizontalIntegral, verticalSegmentIntegral, hzre, hzim, hwre,
      hwim, smul_eq_mul] using hmain
  -- the horizontal integrals tend to zero
  have hhor_tend : ∀ F : ℝ → ℝ → ℂ,
      (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ x : ℝ, σL ≤ x → x ≤ σR → ‖F T x‖ ≤ ε) →
      Tendsto (fun T : ℝ => ∫ x in σL..σR, F T x) atTop (𝓝 0) := by
    intro F hF
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := hF (ε / (2 * (σR - σL))) (by
      have : 0 < σR - σL := by linarith
      positivity)
    refine ⟨T₀, fun T hT => ?_⟩
    rw [dist_zero_right]
    have hbound : ∀ x ∈ Ι σL σR, ‖F T x‖ ≤ ε / (2 * (σR - σL)) := by
      intro x hx
      rw [uIoc_of_le hLR.le] at hx
      exact hT₀ T hT x hx.1.le hx.2
    calc ‖∫ x in σL..σR, F T x‖
        ≤ ε / (2 * (σR - σL)) * |σR - σL| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ = ε / 2 := by
          have hpos : 0 < σR - σL := by linarith
          rw [abs_of_pos hpos]
          field_simp
      _ < ε := by linarith
  have htop := hhor_tend (fun T x => H (x + T * I)) (fun ε hε => by
    obtain ⟨T₀, h⟩ := hhor ε hε
    exact ⟨T₀, fun T hT x h1 h2 => (h T hT x h1 h2).1⟩)
  have hbot := hhor_tend (fun T x => H (x + (-T) * I)) (fun ε hε => by
    obtain ⟨T₀, h⟩ := hhor ε hε
    exact ⟨T₀, fun T hT x h1 h2 => (h T hT x h1 h2).2⟩)
  -- the vertical integrals tend to the line integrals
  have hvR : Tendsto (fun T : ℝ => ∫ y in (-T)..T, H (σR + y * I)) atTop
      (𝓝 (∫ t : ℝ, H (σR + t * I))) :=
    intervalIntegral_tendsto_integral hR tendsto_neg_atTop_atBot tendsto_id
  have hvL : Tendsto (fun T : ℝ => ∫ y in (-T)..T, H (σL + y * I)) atTop
      (𝓝 (∫ t : ℝ, H (σL + t * I))) :=
    intervalIntegral_tendsto_integral hL tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ =>
      (∫ x in σL..σR, H (x + (-T) * I)) - (∫ x in σL..σR, H (x + T * I))
        + I * (∫ y in (-T)..T, H (σR + y * I)) - I * (∫ y in (-T)..T, H (σL + y * I)))
      atTop (𝓝 (0 - 0 + I * (∫ t : ℝ, H (σR + t * I)) - I * (∫ t : ℝ, H (σL + t * I)))) :=
    ((hbot.sub htop).add (hvR.const_mul I)).sub (hvL.const_mul I)
  have hconst : Tendsto (fun T : ℝ =>
      (∫ x in σL..σR, H (x + (-T) * I)) - (∫ x in σL..σR, H (x + T * I))
        + I * (∫ y in (-T)..T, H (σR + y * I)) - I * (∫ y in (-T)..T, H (σL + y * I)))
      atTop (𝓝 (2 * Real.pi * I * S)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (hrect T hT).symm
  have heq := tendsto_nhds_unique hlim hconst
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have : I * ((∫ t : ℝ, H (σR + t * I)) - ∫ t : ℝ, H (σL + t * I))
      = I * (2 * Real.pi * S) := by
    rw [mul_sub]
    linear_combination heq
  exact mul_left_cancel₀ hI this

end FurioLombardo.M2.Zimmert
