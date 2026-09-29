import Mathlib
import FurioLombardo.Vendor.Toolbox.Polynomial.CoeffLimRoot
import FurioLombardo.Discharge.R7.FinIdx.ZSet

/-!
# PENCIL, case (B0) (R7)

Pairs `D n = (t n, v n)` of `Z` with `‖t₀‖ → ∞` and `‖t₁‖ / ‖t₀‖² → 0` do not exist. Scaling by
`a = -t₀`: `a⁻² u(aX) = X² - X + t₁/t₀² → X² - X`, `a⁻⁶ g(aX) → ℓ X⁶` (`ptendsto_scale`), and
`v̂ = a⁻³ v(aX)` is a square root of the scaled sextic modulo the scaled quadratic. The root bound
bounds `v̂`, a limit `v̂*` satisfies `X² - X ∣ ℓ X⁶ - v̂*²`, and evaluation at `1` makes the leading
coefficient `ℓ` a square, against `GoodSextic`.
-/
open Polynomial Filter Topology
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.PolyLim

namespace FurioLombardo.Discharge.R7.FinIdx

variable {K : Type*} [NormedField K]

/-- Scaling `X ↦ -t₀ X` turns `uT t` into `t₀² (X² - X + t₁/t₀²)`. -/
theorem uT_comp_neg_mul_X (t : Fin 2 → K) (h : t 0 ≠ 0) :
    (uT t).comp (C (-t 0) * X) = C (t 0 ^ 2) * uT ![-1, t 1 / t 0 ^ 2] := by
  have e : C (t 1) = C (t 0 ^ 2) * C (t 1 / t 0 ^ 2) := by
    rw [← C_mul, mul_div_cancel₀ _ (pow_ne_zero 2 h)]
  simp only [uT, add_comp, mul_comp, pow_comp, X_comp, C_comp, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [e]
  simp only [map_neg, map_pow, map_one]
  ring

/-- Coefficients of `c⁻ᵈ g(c X)` for `‖c‖ → ∞`: the limit is the leading term. -/
theorem ptendsto_scale {ι : Type*} {l : Filter ι} {g : K[X]} {d : ℕ} (hg : g.natDegree ≤ d)
    {c : ι → K} (hc : Tendsto (fun n => ‖c n‖) l atTop) :
    PTendsto l (fun n => C ((c n ^ d)⁻¹) * g.comp (C (c n) * X)) (C (g.coeff d) * X ^ d) := by
  intro i
  simp only [coeff_C_mul, comp_C_mul_X_coeff, coeff_X_pow]
  have hc0 : ∀ᶠ n in l, c n ≠ 0 := by
    filter_upwards [hc.eventually_gt_atTop 0] with n hn
    exact norm_pos_iff.mp hn
  rcases lt_trichotomy i d with hi | rfl | hi
  · simp only [hi.ne, ite_false, mul_zero]
    have hk : Tendsto (fun n => ‖c n‖ ^ (d - i)) l atTop :=
      Tendsto.comp (tendsto_pow_atTop (by omega)) hc
    have h0 : Tendsto (fun n => ((c n) ^ (d - i))⁻¹) l (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv, norm_pow]
      exact hk.inv_tendsto_atTop
    have := h0.mul_const (g.coeff i)
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [hc0] with n hn
    have e : c n ^ d = c n ^ (d - i) * c n ^ i := by rw [← pow_add, Nat.sub_add_cancel hi.le]
    rw [e, mul_inv, mul_comm (g.coeff i), ← mul_assoc, mul_assoc _ (c n ^ i)⁻¹,
      inv_mul_cancel₀ (pow_ne_zero _ hn), mul_one]
  · simp only [ite_true, mul_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hc0] with n hn
    rw [mul_comm (g.coeff i), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hn), one_mul]
  · simp only [hi.ne', ite_false, mul_zero, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hg hi),
      zero_mul]
    exact tendsto_const_nhds

/-- **Case (B0) of PENCIL is impossible**: pairs of `Z` with `‖t₀‖ → ∞` and `‖t₁‖ / ‖t₀‖² → 0`
would give, after scaling by `-t₀`, a square root of the leading coefficient modulo `X² - X`. -/
theorem pencil_B0_false [ProperSpace K] {g : K[X]} [GoodSextic g] {Dn : ℕ → MPair K}
    (hZ : ∀ n, InZ g (Dn n)) (h0 : ∀ n, (Dn n).t 0 ≠ 0)
    (hrat : Tendsto (fun n => ‖(Dn n).t 1‖ / ‖(Dn n).t 0‖ ^ 2) atTop (𝓝 0))
    (hinf : Tendsto (fun n => ‖(Dn n).t 0‖) atTop atTop) : False := by
  set a : ℕ → K := fun n => -(Dn n).t 0 with ha
  have ha0 : ∀ n, a n ≠ 0 := fun n => neg_ne_zero.mpr (h0 n)
  have hainf : Tendsto (fun n => ‖a n‖) atTop atTop := by simpa [ha] using hinf
  -- the scaled data
  set tu : ℕ → Fin 2 → K := fun n => ![-1, (Dn n).t 1 / (Dn n).t 0 ^ 2] with htu
  set fh : ℕ → K[X] := fun n => C ((a n ^ 6)⁻¹) * g.comp (C (a n) * X) with hfh
  set vh : ℕ → K[X] := fun n => C ((a n ^ 3)⁻¹) * (Dn n).v.comp (C (a n) * X) with hvh
  have hg6 : g.natDegree ≤ 6 := GoodSextic.natDegree_eq.le
  have htu0 : Tendsto tu atTop (𝓝 ![-1, 0]) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    fin_cases i
    · exact tendsto_const_nhds
    · change Tendsto (fun n => (Dn n).t 1 / (Dn n).t 0 ^ 2) atTop (𝓝 0)
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [norm_div, norm_pow] using hrat
  have hu := ptendsto_uT htu0
  have hf := ptendsto_scale hg6 hainf
  have hdvd : ∀ n, uT (tu n) ∣ fh n - vh n ^ 2 := by
    intro n
    obtain ⟨q, hq⟩ := (hZ n).2
    have hc := congrArg (fun p => p.comp (C (a n) * X)) hq
    simp only [sub_comp, pow_comp, mul_comp] at hc
    rw [ha, uT_comp_neg_mul_X _ (h0 n)] at hc
    refine ⟨C ((a n ^ 6)⁻¹) * C ((Dn n).t 0 ^ 2) * q.comp (C (a n) * X), ?_⟩
    have e : fh n - vh n ^ 2 = C ((a n ^ 6)⁻¹) *
        (g.comp (C (a n) * X) - (Dn n).v.comp (C (a n) * X) ^ 2) := by
      simp only [hfh, hvh, mul_pow, ← C_pow, inv_pow, ← pow_mul]
      ring
    rw [e]
    simp only [ha] at hc ⊢
    rw [hc]
    ring
  have hvd : ∀ n, (vh n).degree < 2 := by
    intro n
    refine lt_of_le_of_lt (degree_le_of_natDegree_le (n := 1) ?_) (by norm_num)
    refine natDegree_C_mul_le _ _ |>.trans ?_
    refine natDegree_comp_le.trans ?_
    have h1 := natDegree_le_one_of_degree_lt_two (hZ n).1
    have h2 : (C (a n) * X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
    nlinarith
  obtain ⟨B, hB⟩ := rootBound (GoodSextic.two_ne_zero (f := g)) hu
    (Eventually.of_forall fun n => ⟨uT_monic _, uT_natDegree _⟩) (uT_monic _) (uT_natDegree _)
    (by simp [uT, coeff_X]) hf
    (Eventually.of_forall fun n => (natDegree_C_mul_le _ _).trans
      (natDegree_comp_le.trans (by
        have h2 : (C (a n) * X).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
        nlinarith)))
    (Eventually.of_forall fun n => ⟨hvd n, hdvd n⟩)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hB
  obtain ⟨q, -, φ, hφ, hq⟩ := exists_subseq_ptendsto (p := fun k => vh (k + N0)) (N := 1)
    (fun k => natDegree_le_one_of_degree_lt_two (hvd _)) (B := B) (fun k => hN0 _ (by omega))
  have hshift : Tendsto (fun k => φ k + N0) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_right _ _) hφ.tendsto_atTop
  have hlim := ((hf.comp_tendsto hshift).sub (hq.pow 2)).dvd (N := 6) (d := 2)
    (Eventually.of_forall fun k => by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans (by
          have h2 : (C (a (φ k + N0)) * X).natDegree ≤ 1 :=
            (natDegree_C_mul_le _ _).trans natDegree_X_le
          nlinarith))
      · refine natDegree_pow_le.trans ?_
        have := natDegree_le_one_of_degree_lt_two (hvd (φ k + N0))
        simp only [Function.comp_apply]
        omega)
    (hu.comp_tendsto hshift) (Eventually.of_forall fun k => ⟨uT_monic _, uT_natDegree _⟩)
    (uT_monic _) (uT_natDegree _) (Eventually.of_forall fun k => hdvd _)
  have hev := eval_eq_zero_of_dvd_of_eval_eq_zero (x := (1 : K)) hlim (by simp [uT])
  apply GoodSextic.not_isSquare_leadingCoeff (f := g)
  refine ⟨q.eval 1, ?_⟩
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one] at hev
  rw [leadingCoeff, GoodSextic.natDegree_eq]
  linear_combination hev

end FurioLombardo.Discharge.R7.FinIdx
