import Mathlib
import FurioLombardo.Discharge.M4Log.Defs

/-!
# The chart logarithm is its linear part up to a quadratic error (lane lean-m4box, D7)

R7's scaled logarithm `logVal Φ f c` (Toolbox/FormalGroup/ScaledLog.lean) has linear part the
identity and coefficients of degree `d ≥ 2` in `𝔪^(d-1)` (`coeff_logC_mem`). Hence, for `y` with
coordinates in an ideal `I`, `logVal y - y` lies in every closed ideal `J` containing
`𝔪^(n-1) I^n` for all `n ≥ 2` (`logVal_sub_self_mem`); over `OKv` with `I = (pv^m)`:
`‖logVal y - y‖ ≤ ‖pv‖^(1 + 2m)` (`norm_logK_sub_le`).

With lane lean-m4log's chart formula `lamK (ψ z) = pv^(M0+4) Amat logVal(y)`, `z = pv⁴ y`
(M4Log/Defs.lean `lamK_chart`), and the chart coordinates `t = pv^M0 z` (R7's `tPt`): if
`‖tᵢ‖ ≤ ‖pv‖^D` with `D ≥ M0 + 4`, then `z ∈ B1` (`mem_B1_of_norm_tPt`) and, when the entries of
`Amat k` are integral,
`‖lamK (ψ z) - Amat t‖ ≤ ‖pv‖^(2D - M0 - 3)` (`norm_lamK_chart_sub_le`).
-/

open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv
open FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Vendor.Toolbox.FormalGroup FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman IsLocalRing
open scoped Matrix

namespace FurioLombardo.Discharge.M4Box

/-! ## The scaled logarithm near the origin, generic -/

section Generic

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [CharZero K]

/-- **The scaled logarithm minus its linear part**: for `y` with coordinates in `I`, `logVal y - y`
lies in every closed ideal `J` with `𝔪^(n-1) I^n ≤ J` for `n ≥ 2`. -/
theorem logVal_sub_self_mem {p : ℕ} {c : O} (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O)
    (hc : ScalingHyp p c) {f : O →+* K} (hf : Function.Injective f) (Φ : FormalGroupLaw O ι)
    {I J : Ideal O} (hJ : IsClosed (J : Set O))
    (hIJ : ∀ n : ℕ, 2 ≤ n → maximalIdeal O ^ (n - 1) * I ^ n ≤ J)
    {y : ι → O} (hy : ∀ j, y j ∈ I) (i : ι) :
    logVal Φ f c y i - y i ∈ J := by
  classical
  have h3 := (MvPSeries.hasSum_evalT y (decay_logC hp hpm hc hf Φ i)).sub
    (MvPSeries.hasSum_evalT y (decay_X (O := O) i))
  rw [MvPSeries.evalT_X] at h3
  change MvPSeries.evalT y (logC Φ f c i) - y i ∈ J
  rw [← h3.tsum_eq]
  refine tsum_mem hJ fun d => ?_
  rw [← sub_mul]
  rcases le_or_gt d.degree 1 with hd | hd
  · have hcoeff : MvPowerSeries.coeff d (logC Φ f c i) =
        MvPowerSeries.coeff d (MvPowerSeries.X i : MvPowerSeries ι O) := by
      apply hf
      rw [map_coeff_logC hp hpm hc f Φ i d]
      have h0 := (Φ.map f).log_sub_X_order i d hd
      rw [map_sub, sub_eq_zero] at h0
      rw [h0, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
      split_ifs with hdi
      · subst hdi
        simp [Finsupp.degree_single]
      · simp
    rw [hcoeff, sub_self, zero_mul]
    exact J.zero_mem
  · have hX : MvPowerSeries.coeff d (MvPowerSeries.X i : MvPowerSeries ι O) = 0 := by
      rw [MvPowerSeries.coeff_X]
      split_ifs with hdi
      · rw [hdi, Finsupp.degree_single] at hd
        omega
      · rfl
    rw [hX, sub_zero]
    have hL := coeff_logC_mem hp hpm hc hf Φ i d
    have hP : d.prod (fun s e => y s ^ e) ∈ I ^ d.degree := by
      rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      exact Ideal.prod_mem_prod fun s _ => Ideal.pow_mem_pow (hy s) _
    exact hIJ d.degree hd (Ideal.mul_mem_mul hL hP)

end Generic

/-! ## Over `OKv` -/

/-- An ideal `(pv^n)` of `OKv` is closed. -/
theorem isClosed_span_pvO_pow (n : ℕ) : IsClosed ((Ideal.span {pvO ^ n} : Ideal OKv) : Set OKv) := by
  have e : ((Ideal.span {pvO ^ n} : Ideal OKv) : Set OKv) = {x : OKv | ‖(x : Kv)‖ ≤ ‖pv‖ ^ n} := by
    ext x
    exact mem_span_pvO_pow_iff n
  rw [e]
  exact isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const

/-- `𝔪^(n-1) (pv^m)^n ≤ (pv^(1+2m))` for `n ≥ 2`. -/
theorem maximalIdeal_pow_mul_span_le (m n : ℕ) (hn : 2 ≤ n) :
    maximalIdeal OKv ^ (n - 1) * (Ideal.span {pvO ^ m}) ^ n ≤ Ideal.span {pvO ^ (1 + 2 * m)} := by
  rw [maximalIdeal_OKv, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_le_span_singleton, ← pow_mul,
    ← pow_add]
  have : 2 * m ≤ m * n := by nlinarith
  exact pow_dvd_pow _ (by omega)

/-- R7's scaling `pv⁴` satisfies the scaling hypothesis at `p = 2`. -/
theorem scalingHyp_cB : ScalingHyp 2 cB :=
  scalingHyp_uniformizer natCast_two_mem_maximalIdeal isUnit_u2 natCast_two_eq

/-- **The chart logarithm near the origin**: for `‖yⱼ‖ ≤ ‖pv‖^m`,
`‖logK y - y‖ ≤ ‖pv‖^(1 + 2m)`. -/
theorem norm_logK_sub_le (k : Fin 2) (h : AdmM0 k) {m : ℕ} {y : Fin 2 → OKv}
    (hy : ∀ j, ‖(y j : Kv)‖ ≤ ‖pv‖ ^ m) (i : Fin 2) :
    ‖logK k h y i - (y i : Kv)‖ ≤ ‖pv‖ ^ (1 + 2 * m) := by
  have hmem := logVal_sub_self_mem Nat.prime_two natCast_two_mem_maximalIdeal scalingHyp_cB
    subtype_injective (fgl k h) (isClosed_span_pvO_pow (1 + 2 * m))
    (fun n hn => maximalIdeal_pow_mul_span_le m n hn)
    (fun j => (mem_span_pvO_pow_iff m).mpr (hy j)) i
  rw [mem_span_pvO_pow_iff] at hmem
  simpa [logK] using hmem

/-! ## The chart point and the linear part -/

/-- The chart coordinates of `z`: `t = pv^M0 z`. -/
noncomputable abbrev tK (k : Fin 2) (h : AdmM0 k) (z : (fgl k h).Points) : Fin 2 → Kv :=
  (baseKv k).toSetup.tPt (M0 k) z

theorem tK_apply (k : Fin 2) (h : AdmM0 k) (z : (fgl k h).Points) (i : Fin 2) :
    tK k h z i = pv ^ M0 k * ((z i : OKv) : Kv) := rfl

/-- A point whose chart coordinates have norm at most `‖pv‖^(M0+4)` lies in `B1`. -/
theorem mem_B1_of_norm_tPt (k : Fin 2) (h : AdmM0 k) (z : (fgl k h).Points)
    (hz : ∀ i, ‖tK k h z i‖ ≤ ‖pv‖ ^ (M0 k + 4)) : z ∈ B1 (fgl k h) cB := by
  intro j
  rw [cB, mem_span_pvO_pow_iff]
  have h1 := hz j
  rw [tK_apply, norm_mul, norm_pow, pow_add] at h1
  exact le_of_mul_le_mul_left h1 (pow_pos norm_pv_pos _)

/-- An integral `2 × 2` matrix does not increase the sup norm (ultrametric). -/
theorem norm_mulVec_le {A : Matrix (Fin 2) (Fin 2) Kv} (hA : ∀ i j, ‖A i j‖ ≤ 1)
    {w : Fin 2 → Kv} {r : ℝ} (hw : ∀ j, ‖w j‖ ≤ r) (i : Fin 2) : ‖(A *ᵥ w) i‖ ≤ r := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i _)).trans (hw _)

/-- **D7: the chart logarithm is its linear part up to a quadratic error.** If the chart
coordinates `t` of `z` satisfy `‖tᵢ‖ ≤ ‖pv‖^D`, `D ≥ M0 + 4`, and `Amat k` is integral, then
`‖lamK (ψ z) - Amat t‖ ≤ ‖pv‖^(2D - M0 - 3)`. -/
theorem norm_lamK_chart_sub_le (k : Fin 2) (h : AdmM0 k) (hA : ∀ i j, ‖Amat k i j‖ ≤ 1)
    (z : (fgl k h).Points) {D : ℕ} (hD : M0 k + 4 ≤ D) (ht : ∀ i, ‖tK k h z i‖ ≤ ‖pv‖ ^ D)
    (i : Fin 2) :
    ‖lamK k (chart k h z) i - (Amat k *ᵥ tK k h z) i‖ ≤ ‖pv‖ ^ (2 * D - M0 k - 3) := by
  have hB1 := mem_B1_of_norm_tPt k h z fun i =>
    (ht i).trans (pow_le_pow_of_le_one (norm_nonneg _) norm_pv_lt_one.le hD)
  set y : Fin 2 → OKv := fun j => divC cB (z j : OKv) with hydef
  have hy : ∀ j, (z j : OKv) = cB * y j := fun j => (mul_divC (hB1 j)).symm
  rw [lamK_chart k h z hB1 y hy]
  have htj : ∀ j, tK k h z j = pv ^ (M0 k + 4) * (y j : Kv) := by
    intro j
    rw [tK_apply, hy j, Subring.coe_mul, Subring.coe_pow, coe_pvO]
    ring
  have hyn : ∀ j, ‖(y j : Kv)‖ ≤ ‖pv‖ ^ (D - (M0 k + 4)) := by
    intro j
    have h1 := ht j
    have h2 : ‖pv‖ ^ D = ‖pv‖ ^ (M0 k + 4) * ‖pv‖ ^ (D - (M0 k + 4)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [htj, norm_mul, norm_pow, h2] at h1
    exact le_of_mul_le_mul_left h1 (pow_pos norm_pv_pos _)
  have e : ((pv ^ (M0 k + 4) • Amat k) *ᵥ logK k h y) i - (Amat k *ᵥ tK k h z) i =
      (Amat k *ᵥ (fun j => pv ^ (M0 k + 4) * (logK k h y j - (y j : Kv)))) i := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, htj]
    ring
  rw [e]
  refine norm_mulVec_le hA (fun j => ?_) i
  rw [norm_mul, norm_pow]
  calc ‖pv‖ ^ (M0 k + 4) * ‖logK k h y j - (y j : Kv)‖
      ≤ ‖pv‖ ^ (M0 k + 4) * ‖pv‖ ^ (1 + 2 * (D - (M0 k + 4))) := by
        gcongr
        exact norm_logK_sub_le k h hyn j
    _ = ‖pv‖ ^ (2 * D - M0 k - 3) := by
        rw [← pow_add]
        congr 1
        omega

end FurioLombardo.Discharge.M4Box
