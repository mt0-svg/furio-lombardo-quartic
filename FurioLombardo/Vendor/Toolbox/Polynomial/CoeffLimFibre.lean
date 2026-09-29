import Mathlib
import FurioLombardo.Vendor.Toolbox.Polynomial.CoeffLim

/-!
# Leading order of quotients along a fibre (Lemma A)

Let `u n → (X - α)²` (monic quadratics), `u_T` monic quadratic with `u_T(α) ≠ 0`, and `V n` of
degree `≤ 3` with `|V n| → ∞`, `u_T ∣ V n - v_T` and `u n * u_T ∣ g - (V n)²` (`deg g ≤ 6`). Then
along a subsequence the quotient `q n = (g - (V n)²) /ₘ (u n * u_T)` has nonzero `X²` coefficient
and its monic normalization tends to `u_T`.

Proof: normalize `V n` by a coefficient of largest norm, extract a limit `V̂ ≠ 0`; the limit
divisibilities give `u_T ∣ V̂` and `(X - α)² u_T ∣ V̂²`, hence `V̂ = μ (X - α) u_T` with
`μ ≠ 0`, and `λ⁻² q n → -μ² u_T`.

Origin: written for this formalization (finite index of the chart ball of a genus 2 Jacobian over
a 2-adic field, `FurioLombardo.Discharge.R7.FinIdx`).
-/

open Polynomial Filter Topology

namespace FurioLombardo.Vendor.Toolbox.PolyLim

variable {K : Type*} [NormedField K]

/-- A polynomial of degree `≤ 3` that is a multiple of a monic quadratic `q0` and vanishes at a
point `α` with `q0(α) ≠ 0` is `μ (X - α) q0`. -/
theorem eq_C_mul_X_sub_C_mul {q0 W : K[X]} {α : K} (hq0m : q0.Monic) (hq0d : q0.natDegree = 2)
    (hα : q0.eval α ≠ 0) (hW : W.natDegree ≤ 3) (hq : q0 ∣ W) (hWα : W.eval α = 0) :
    ∃ μ : K, W = C μ * (X - C α) * q0 := by
  obtain ⟨m, rfl⟩ := hq
  rcases eq_or_ne m 0 with hm0 | hm0
  · exact ⟨0, by simp [hm0]⟩
  have hmd : m.natDegree ≤ 1 := by
    rw [hq0m.natDegree_mul' hm0, hq0d] at hW
    omega
  have hmα : m.eval α = 0 := by
    rw [eval_mul] at hWα
    exact (mul_eq_zero.1 hWα).resolve_left hα
  have hm := eq_X_add_C_of_natDegree_le_one hmd
  have h0 : m.coeff 0 = -(m.coeff 1 * α) := by
    rw [hm] at hmα
    simp only [eval_add, eval_mul, eval_C, eval_X] at hmα
    linear_combination hmα
  have hm' : m = C (m.coeff 1) * (X - C α) := by
    conv_lhs => rw [hm]
    rw [h0, C_neg, C_mul]
    ring
  refine ⟨m.coeff 1, ?_⟩
  conv_lhs => rw [hm']
  ring

/-- **Lemma A**: for `u n → (X - α)²` (monic quadratics), `q0` monic quadratic with
`q0(α) ≠ 0`, `V n` of degree `≤ 3` with `psize 3 (V n) → ∞`, `q0 ∣ V n - vT` and
`u n * q0 ∣ g - V n ^ 2` (`deg g ≤ 6`), along a subsequence the quotients
`(g - V n ^ 2) /ₘ (u n * q0)` have a nonzero `X²` coefficient and, normalized by it, tend
to `q0`. -/
theorem lemmaA [ProperSpace K] {g q0 vT : K[X]} {α : K} (hg : g.natDegree ≤ 6)
    (hq0m : q0.Monic) (hq0d : q0.natDegree = 2) (hα : q0.eval α ≠ 0)
    {u V : ℕ → K[X]} (hu : PTendsto atTop u ((X - C α) ^ 2))
    (hum : ∀ n, (u n).Monic ∧ (u n).natDegree = 2)
    (hVd : ∀ n, (V n).natDegree ≤ 3) (hV : Tendsto (fun n => psize 3 (V n)) atTop atTop)
    (hVT : ∀ n, q0 ∣ V n - vT) (hdvd : ∀ n, u n * q0 ∣ g - V n ^ 2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ᶠ k in atTop, ((g - V (φ k) ^ 2) /ₘ (u (φ k) * q0)).coeff 2 ≠ 0) ∧
      PTendsto atTop (fun k => C (((g - V (φ k) ^ 2) /ₘ (u (φ k) * q0)).coeff 2)⁻¹ *
        ((g - V (φ k) ^ 2) /ₘ (u (φ k) * q0))) q0 := by
  -- a coefficient of largest norm
  choose j hj hjmax using fun n =>
    Finset.exists_max_image (Finset.range 4) (fun i => ‖(V n).coeff i‖) ⟨0, by simp⟩
  set L : ℕ → K := fun n => (V n).coeff (j n) with hL_def
  have hL4 : ∀ n, psize 3 (V n) ≤ 4 * ‖L n‖ := by
    intro n
    calc psize 3 (V n) = ∑ i ∈ Finset.range 4, ‖(V n).coeff i‖ := rfl
      _ ≤ ∑ _i ∈ Finset.range 4, ‖L n‖ := Finset.sum_le_sum fun i hi => hjmax n i hi
      _ = 4 * ‖L n‖ := by simp
  have hLtop : Tendsto (fun n => ‖L n‖) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (hV.atTop_div_const (by norm_num : (0 : ℝ) < 4))
    have := hL4 n
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hLinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := tendsto_inv_atTop_zero.comp hLtop
    simpa only [norm_inv, Function.comp_def] using this
  have hLne : ∀ᶠ n in atTop, L n ≠ 0 :=
    (hLtop.eventually_gt_atTop 0).mono fun n hn => norm_pos_iff.1 hn
  -- the normalized sequence
  set W : ℕ → K[X] := fun n => C (L n)⁻¹ * V n with hW_def
  have hWd : ∀ n, (W n).natDegree ≤ 3 := fun n => (natDegree_C_mul_le _ _).trans (hVd n)
  have hWc : ∀ n, ∀ i ∈ Finset.range 4, ‖(W n).coeff i‖ ≤ 1 := by
    intro n i hi
    rw [hW_def]
    dsimp only
    rw [coeff_C_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hjmax n i hi) (norm_nonneg _)
  have hWB : ∀ n, psize 3 (W n) ≤ 4 := by
    intro n
    calc psize 3 (W n) = ∑ i ∈ Finset.range 4, ‖(W n).coeff i‖ := rfl
      _ ≤ ∑ _i ∈ Finset.range 4, (1 : ℝ) := Finset.sum_le_sum fun i hi => hWc n i hi
      _ = 4 := by simp
  have hW1 : ∀ n, L n ≠ 0 → 1 ≤ psize 3 (W n) := by
    intro n hn
    have h1 : ‖(W n).coeff (j n)‖ = 1 := by
      rw [hW_def]
      dsimp only
      rw [coeff_C_mul]
      change ‖(L n)⁻¹ * L n‖ = 1
      rw [inv_mul_cancel₀ hn, norm_one]
    calc (1 : ℝ) = ‖(W n).coeff (j n)‖ := h1.symm
      _ ≤ psize 3 (W n) := Finset.single_le_sum (f := fun i => ‖(W n).coeff i‖)
          (fun i _ => norm_nonneg _) (hj n)
  -- extraction
  obtain ⟨Ws, hWsd, φ, hφ, hWs⟩ := exists_subseq_ptendsto hWd hWB
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hLneφ : ∀ᶠ k in atTop, L (φ k) ≠ 0 := hφt.eventually hLne
  have hLinvφ : Tendsto (fun k => (L (φ k))⁻¹) atTop (𝓝 0) := hLinv.comp hφt
  have hWs0 : Ws ≠ 0 := by
    intro h0
    have h1 : 1 ≤ psize 3 Ws :=
      ge_of_tendsto (hWs.psize 3) (hLneφ.mono fun k hk => hW1 (φ k) hk)
    rw [h0] at h1
    simp [psize] at h1
    linarith
  -- `q0` divides the limit
  have hq0Ws : q0 ∣ Ws := by
    have hp : PTendsto atTop (fun k => W (φ k) - C (L (φ k))⁻¹ * vT) (Ws - C 0 * vT) :=
      hWs.sub ((ptendsto_C hLinvφ).mul (ptendsto_const vT))
    rw [map_zero, zero_mul, sub_zero] at hp
    refine hp.dvd (N := max 3 vT.natDegree) (d := 2) (Eventually.of_forall fun k => ?_)
      (ptendsto_const q0) (Eventually.of_forall fun _ => ⟨hq0m, hq0d⟩) hq0m hq0d
      (Eventually.of_forall fun k => ?_)
    · exact (natDegree_sub_le _ _).trans (max_le_max (hWd _) (natDegree_C_mul_le _ _))
    · have := dvd_mul_of_dvd_right (hVT (φ k)) (C (L (φ k))⁻¹)
      rw [mul_sub] at this
      exact this
  -- `(X - α) ^ 2 q0` divides `-Ws ^ 2`
  have hlim_m : ((X - C α) ^ 2 * q0).Monic := ((monic_X_sub_C α).pow 2).mul hq0m
  have hlim_d : ((X - C α) ^ 2 * q0).natDegree = 4 := by
    rw [((monic_X_sub_C α).pow 2).natDegree_mul hq0m, (monic_X_sub_C α).natDegree_pow,
      natDegree_X_sub_C, hq0d]
  have huq : PTendsto atTop (fun k => u (φ k) * q0) ((X - C α) ^ 2 * q0) :=
    (hu.comp_tendsto hφt).mul (ptendsto_const q0)
  have huqm : ∀ᶠ k in atTop, (u (φ k) * q0).Monic ∧ (u (φ k) * q0).natDegree = 4 :=
    Eventually.of_forall fun k => ⟨(hum _).1.mul hq0m, by
      rw [(hum _).1.natDegree_mul hq0m, (hum _).2, hq0d]⟩
  have hP : PTendsto atTop (fun k => C ((L (φ k))⁻¹ ^ 2) * g - W (φ k) ^ 2)
      (C (0 ^ 2) * g - Ws ^ 2) :=
    ((ptendsto_C (hLinvφ.pow 2)).mul (ptendsto_const g)).sub (hWs.pow 2)
  rw [zero_pow two_ne_zero, map_zero, zero_mul, zero_sub] at hP
  have hPd : ∀ᶠ k in atTop, (C ((L (φ k))⁻¹ ^ 2) * g - W (φ k) ^ 2).natDegree ≤ 6 :=
    Eventually.of_forall fun k => (natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans hg) (natDegree_pow_le.trans (by nlinarith [hWd (φ k)])))
  have hPeq : ∀ k, C ((L (φ k))⁻¹ ^ 2) * g - W (φ k) ^ 2 =
      C ((L (φ k))⁻¹ ^ 2) * (g - V (φ k) ^ 2) := by
    intro k
    rw [hW_def]
    simp only [C_pow]
    ring
  have hdiv4 : (X - C α) ^ 2 * q0 ∣ -Ws ^ 2 :=
    hP.dvd hPd huq huqm hlim_m hlim_d (Eventually.of_forall fun k => by
      rw [hPeq]; exact dvd_mul_of_dvd_right (hdvd _) _)
  -- `Ws` vanishes at `α`
  have hWsα : Ws.eval α = 0 := by
    have h1 : X - C α ∣ -Ws ^ 2 :=
      (dvd_mul_of_dvd_left (dvd_pow_self _ two_ne_zero) q0).trans hdiv4
    rw [dvd_iff_isRoot, IsRoot, eval_neg, eval_pow, neg_eq_zero] at h1
    exact (pow_eq_zero_iff two_ne_zero).1 h1
  obtain ⟨μ, hμ⟩ := eq_C_mul_X_sub_C_mul hq0m hq0d hα hWsd hq0Ws hWsα
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hWs0
    rw [hμ]
    simp
  -- the limit of the scaled quotients
  have hQlim : PTendsto atTop (fun k => C ((L (φ k))⁻¹ ^ 2) *
      ((g - V (φ k) ^ 2) /ₘ (u (φ k) * q0))) (-C (μ ^ 2) * q0) := by
    have h := hP.divByMonic hPd huq huqm hlim_m hlim_d
    have hval : -Ws ^ 2 /ₘ ((X - C α) ^ 2 * q0) = -C (μ ^ 2) * q0 := by
      rw [show -Ws ^ 2 = ((X - C α) ^ 2 * q0) * (-C (μ ^ 2) * q0) by rw [hμ, C_pow]; ring]
      exact mul_divByMonic_cancel_left _ hlim_m
    rw [hval] at h
    refine h.congr' (Eventually.of_forall fun k => ?_)
    rw [hPeq, ← smul_eq_C_mul, smul_divByMonic, smul_eq_C_mul]
  have hq2 : q0.coeff 2 = 1 := by rw [← hq0d]; exact hq0m.coeff_natDegree
  have hc2 : Tendsto (fun k => (L (φ k))⁻¹ ^ 2 *
      ((g - V (φ k) ^ 2) /ₘ (u (φ k) * q0)).coeff 2) atTop (𝓝 (-μ ^ 2)) := by
    have h := hQlim 2
    rw [neg_mul, coeff_neg, coeff_C_mul, hq2, mul_one] at h
    simpa only [coeff_C_mul] using h
  have hne : -μ ^ 2 ≠ 0 := neg_ne_zero.2 (pow_ne_zero 2 hμ0)
  have hev := hc2.eventually_ne hne
  refine ⟨φ, hφ, hev.mono fun k hk => right_ne_zero_of_mul hk, ?_⟩
  have hfin := hQlim.C_mul (hc2.inv₀ hne)
  rw [← C_neg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hne, C_1, one_mul] at hfin
  refine hfin.congr' (hLneφ.mono fun k hk => ?_)
  have ha : (L (φ k))⁻¹ ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero hk)
  rw [← mul_assoc, ← C_mul, mul_inv, mul_comm ((L (φ k))⁻¹ ^ 2)⁻¹, mul_assoc,
    inv_mul_cancel₀ ha, mul_one]

end FurioLombardo.Vendor.Toolbox.PolyLim
