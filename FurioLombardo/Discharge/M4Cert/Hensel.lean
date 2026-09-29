import Mathlib

/-!
# Hensel's lemma in a complete ultrametric normed field

For a polynomial `f` with coefficients of norm at most 1 and a point `a` of norm at most 1 with
`‖f(a)‖ < ‖f'(a)‖²`, `f` has a root `z` with `‖z - a‖ ≤ ‖f(a)‖ / ‖f'(a)‖`. Proof: the map
`z ↦ z - f(z) / f'(a)` is a contraction of the closed ball of radius `‖f(a)‖ / ‖f'(a)‖` around `a`
(Banach's fixed point theorem, `ContractingWith.exists_fixedPoint'`). Mathlib's `hensels_lemma` is
the case of `ℤ_[p]`.
-/

namespace FurioLombardo.Discharge.M4Cert

open Polynomial

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable (K) in
/-- The closed unit ball of an ultrametric normed field, as a subring. -/
def unitBallSubring : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {x y} hx hy := by
    have hx' : ‖x‖ ≤ 1 := hx
    have hy' : ‖y‖ ≤ 1 := hy
    show ‖x * y‖ ≤ 1
    rw [norm_mul]
    nlinarith [norm_nonneg x, norm_nonneg y]
  one_mem' := by simp
  add_mem' {x y} hx hy := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by simp
  neg_mem' {x} hx := by simpa using hx

omit [CompleteSpace K] in
/-- Membership in `unitBallSubring K` is having norm at most 1. -/
lemma mem_unitBallSubring {x : K} : x ∈ unitBallSubring K ↔ ‖x‖ ≤ 1 := Iff.rfl

omit [CompleteSpace K] in
/-- In an ultrametric normed field, `‖x - y‖ ≤ max ‖x‖ ‖y‖`. -/
lemma norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max x (-y)

omit [CompleteSpace K] in
/-- A polynomial with coefficients of norm at most 1 is the image of a polynomial over the closed
unit ball. -/
lemma exists_lift_unitBall (f : K[X]) (hf : ∀ i, ‖f.coeff i‖ ≤ 1) :
    ∃ g : (unitBallSubring K)[X], g.map (unitBallSubring K).subtype = f := by
  have hsub : (↑f.coeffs : Set K) ⊆ unitBallSubring K := by
    intro c hc
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.mp hc
    exact hf n
  exact ⟨f.toSubring _ hsub, map_toSubring _ _ _⟩

omit [CompleteSpace K] in
/-- The derivative of a polynomial with coefficients of norm at most 1 has norm at most 1 on the
closed unit ball. -/
lemma norm_derivative_eval_le_one (f : K[X]) (hf : ∀ i, ‖f.coeff i‖ ≤ 1) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖f.derivative.eval x‖ ≤ 1 := by
  obtain ⟨g, rfl⟩ := exists_lift_unitBall f hf
  set x' : unitBallSubring K := ⟨x, hx⟩
  have : x = (unitBallSubring K).subtype x' := rfl
  rw [derivative_map, this, eval_map_apply]
  exact (g.derivative.eval x').2

omit [CompleteSpace K] in
/-- Key estimate: for `a, z, w` in the closed unit ball,
`‖f(z) - f(w) - f'(a) (z - w)‖ ≤ ‖z - w‖ * max ‖z - a‖ ‖w - a‖`. -/
lemma norm_eval_sub_eval_sub_le (f : K[X]) (hf : ∀ i, ‖f.coeff i‖ ≤ 1) {a z w : K}
    (ha : ‖a‖ ≤ 1) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖f.eval z - f.eval w - f.derivative.eval a * (z - w)‖ ≤ ‖z - w‖ * max ‖z - a‖ ‖w - a‖ := by
  obtain ⟨g, rfl⟩ := exists_lift_unitBall f hf
  lift a to unitBallSubring K using ha
  lift z to unitBallSubring K using hz
  lift w to unitBallSubring K using hw
  obtain ⟨k, hk⟩ := binomExpansion g w (z - w)
  obtain ⟨c, hc⟩ := evalSubFactor (derivative g) w a
  rw [show w + (z - w) = z by ring] at hk
  have key : g.eval z - g.eval w - g.derivative.eval a * (z - w) =
      (z - w) * (k * (z - w) + c * (w - a)) := by
    linear_combination hk + (z - w) * hc
  have e := congrArg (fun t : unitBallSubring K => (t : K)) key
  push_cast at e
  have hmap : ∀ x : unitBallSubring K,
      (g.map (unitBallSubring K).subtype).eval (x : K) = ((g.eval x : unitBallSubring K) : K) :=
    fun x => eval_map_apply (p := g) (f := (unitBallSubring K).subtype) x
  have hmap' : ∀ x : unitBallSubring K,
      (g.map (unitBallSubring K).subtype).derivative.eval (x : K) =
        ((g.derivative.eval x : unitBallSubring K) : K) := fun x => by
    rw [derivative_map]
    exact eval_map_apply (p := g.derivative) (f := (unitBallSubring K).subtype) x
  rw [hmap z, hmap w, hmap' a, e, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hk1 : ‖(k : K)‖ ≤ 1 := mem_unitBallSubring.mp k.2
  have hc1 : ‖(c : K)‖ ≤ 1 := mem_unitBallSubring.mp c.2
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(k : K)‖ * ‖(z : K) - w‖ ≤ 1 * ‖(z : K) - w‖ :=
          mul_le_mul_of_nonneg_right hk1 (norm_nonneg _)
      _ = ‖((z : K) - a) - ((w : K) - a)‖ := by rw [one_mul]; congr 1; ring
      _ ≤ max ‖(z : K) - a‖ ‖(w : K) - a‖ := norm_sub_le_max' _ _
  · rw [norm_mul]
    calc ‖(c : K)‖ * ‖(w : K) - a‖ ≤ 1 * ‖(w : K) - a‖ :=
          mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)
      _ ≤ max ‖(z : K) - a‖ ‖(w : K) - a‖ := by rw [one_mul]; exact le_max_right _ _

/-- **Hensel's lemma** in a complete ultrametric normed field. -/
theorem hensel_of_norm_lt (f : K[X]) (hf : ∀ i, ‖f.coeff i‖ ≤ 1) (a : K) (ha : ‖a‖ ≤ 1)
    (h : ‖f.eval a‖ < ‖f.derivative.eval a‖ ^ 2) :
    ∃ z : K, f.eval z = 0 ∧ ‖z - a‖ ≤ ‖f.eval a‖ / ‖f.derivative.eval a‖ := by
  have hd1 : ‖f.derivative.eval a‖ ≤ 1 := norm_derivative_eval_le_one f hf ha
  have hdpos : 0 < ‖f.derivative.eval a‖ := by
    rcases (norm_nonneg (f.derivative.eval a)).lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq] at h; nlinarith [norm_nonneg (f.eval a)]
  have hd0 : f.derivative.eval a ≠ 0 := norm_pos_iff.mp hdpos
  set d := f.derivative.eval a with hd_def
  set ρ := ‖f.eval a‖ / ‖d‖ with hρ_def
  have hρ0 : 0 ≤ ρ := div_nonneg (norm_nonneg _) hdpos.le
  have hρd : ρ < ‖d‖ := by rw [hρ_def, div_lt_iff₀ hdpos]; nlinarith
  have hρ1 : ρ ≤ 1 := hρd.le.trans hd1
  have hfa : ‖f.eval a‖ = ρ * ‖d‖ := by rw [hρ_def, div_mul_cancel₀ _ hdpos.ne']
  set B := Metric.closedBall a ρ with hB_def
  set g : K → K := fun z => z - f.eval z / d with hg_def
  have hB1 : ∀ z ∈ B, ‖z‖ ≤ 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have := IsUltrametricDist.norm_add_le_max (z - a) a
    rw [sub_add_cancel] at this
    exact this.trans (max_le (hz.trans hρ1) ha)
  have hmaps : Set.MapsTo g B B := by
    intro z hz
    have hz1 := hB1 z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    have key := norm_eval_sub_eval_sub_le f hf ha hz1 ha
    have hga : g z - a = -((f.eval z - f.eval a - d * (z - a)) + f.eval a) / d := by
      simp only [hg_def]; field_simp; ring
    rw [hga, norm_div, norm_neg, div_le_iff₀ hdpos]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hfa.le)
    calc _ ≤ ‖z - a‖ * max ‖z - a‖ ‖a - a‖ := key
      _ ≤ ρ * ρ := by
          rw [sub_self, norm_zero, max_eq_left (norm_nonneg _)]
          exact mul_le_mul hz hz (norm_nonneg _) hρ0
      _ ≤ ρ * ‖d‖ := mul_le_mul_of_nonneg_left hρd.le hρ0
  have hlip : ∀ z ∈ B, ∀ w ∈ B, ‖g z - g w‖ ≤ (ρ / ‖d‖) * ‖z - w‖ := by
    intro z hz w hw
    have key := norm_eval_sub_eval_sub_le f hf ha (hB1 z hz) (hB1 w hw)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz hw
    have hgzw : g z - g w = -(f.eval z - f.eval w - d * (z - w)) / d := by
      simp only [hg_def]; field_simp; ring
    rw [hgzw, norm_div, norm_neg, div_le_iff₀ hdpos]
    calc _ ≤ ‖z - w‖ * max ‖z - a‖ ‖w - a‖ := key
      _ ≤ ‖z - w‖ * ρ := mul_le_mul_of_nonneg_left (max_le hz hw) (norm_nonneg _)
      _ = ρ / ‖d‖ * ‖z - w‖ * ‖d‖ := by field_simp
  obtain ⟨Kc, hKc⟩ : ∃ Kc : NNReal, (Kc : ℝ) = ρ / ‖d‖ := ⟨⟨_, div_nonneg hρ0 hdpos.le⟩, rfl⟩
  have hK : Kc < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_one, hKc, div_lt_one hdpos]
    exact hρd
  have hcontr : ContractingWith Kc (hmaps.restrict g B B) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [Subtype.dist_eq, Set.MapsTo.val_restrict_apply, dist_eq_norm, hKc]
    exact hlip x x.2 y y.2
  have haB : a ∈ B := Metric.mem_closedBall_self hρ0
  obtain ⟨y, hyB, hfix, -⟩ :=
    hcontr.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps haB (edist_ne_top _ _)
  refine ⟨y, ?_, ?_⟩
  · have hy : g y = y := hfix
    simp only [hg_def, sub_eq_self, div_eq_zero_iff] at hy
    exact hy.resolve_right hd0
  · rw [Metric.mem_closedBall, dist_eq_norm] at hyB
    exact hyB

end FurioLombardo.Discharge.M4Cert
