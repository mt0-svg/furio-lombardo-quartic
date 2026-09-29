import Mathlib
import FurioLombardo.Discharge.SelmerBasis.Count.Setup
import FurioLombardo.Discharge.R7.FinIdx.ZSet
import FurioLombardo.Vendor.Toolbox.PowerSeries.EvalLip

/-!
# The chart lemma (R7)

* `tendsto_evO`: evaluation of a fixed `(unitBall K)`-series is continuous in the point (through
  `FurioLombardo.Vendor.Toolbox.EvalLip.eval_sub_mem`: evaluation is Lipschitz for closed ideals);
* `ptendsto_vPt`: `z ↦ vPt z` is continuous (coefficientwise, in `K`);
* `inZ_chart`: chart pairs `(π^M z, vPt z)` lie in `Z`;
* `chart_lemma`: pairs of `Z` close to the chart pair of `z_T ∈ B1 Φ c` are chart pairs of points
  of `B1 Φ c`.
* `zPair`: the points `z(s1, s2)` with `uT (π^M z) = (X - s1)(X - s2)`, `s_i = π^(M+4+j_i)`.
-/

set_option autoImplicit false

open Polynomial Filter Topology
open FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Vendor.Toolbox.PolyLim
open FurioLombardo.Discharge.R7 FurioLombardo.Discharge.R7.FinIdx

namespace FurioLombardo.Discharge.SelmerBasis.Count

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {π : K} (hπ : IsUniformizer π)

/-- The ideals `π ^ m (unitBall K)` are closed. -/
theorem isClosed_span_pi_pow (m : ℕ) : IsClosed ((Ideal.span {hπ.toBall ^ m} : Ideal (unitBall K)) : Set (unitBall K)) := by
  have : ((Ideal.span {hπ.toBall ^ m} : Ideal (unitBall K)) : Set (unitBall K)) = {x : (unitBall K) | ‖(x : K)‖ ≤ ‖π‖ ^ m} := by
    ext x; exact hπ.mem_span_pow_iff m
  rw [this]
  exact isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const

include hπ in
/-- Evaluation of a fixed `(unitBall K)`-series is continuous (in the `K` topology on coordinates). -/
theorem tendsto_evO [CompleteSpace K] {ι σ : Type*} [Finite σ] {l : Filter ι} (H : MvPowerSeries σ (unitBall K))
    {z : ι → σ → IsLocalRing.maximalIdeal (unitBall K)} {z0 : σ → IsLocalRing.maximalIdeal (unitBall K)}
    (h : ∀ j, Tendsto (fun n => (((z n j : (unitBall K))) : K)) l (𝓝 ((z0 j : (unitBall K)) : K))) :
    Tendsto (fun n => ((FurioLombardo.Vendor.Toolbox.Bounded.evO (z n) H : (unitBall K)) : K)) l
      (𝓝 ((FurioLombardo.Vendor.Toolbox.Bounded.evO z0 H : (unitBall K)) : K)) := by
  haveI := hπ.hasUniformizer
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hπ.norm_lt_one
  have hj : ∀ j, ∀ᶠ n in l, dist (((z n j : (unitBall K))) : K) ((z0 j : (unitBall K)) : K) < ‖π‖ ^ m :=
    fun j => Metric.tendsto_nhds.mp (h j) _ (pow_pos hπ.norm_pos m)
  have hall : ∀ᶠ n in l, ∀ j, dist (((z n j : (unitBall K))) : K) ((z0 j : (unitBall K)) : K) < ‖π‖ ^ m := by
    exact Filter.eventually_all.mpr hj
  filter_upwards [hall] with n hn
  have hmem : ∀ j, ((z n j : (unitBall K))) - ((z0 j : (unitBall K))) ∈ Ideal.span {hπ.toBall ^ m} := fun j => by
    rw [hπ.mem_span_pow_iff, AddSubgroupClass.coe_sub]
    have := hn j
    rw [dist_eq_norm] at this
    exact this.le
  have := FurioLombardo.Vendor.Toolbox.EvalLip.eval_sub_mem H (fun j => (z n j).2) (fun j => (z0 j).2)
    (isClosed_span_pi_pow hπ m) hmem
  rw [hπ.mem_span_pow_iff, AddSubgroupClass.coe_sub] at this
  rw [dist_eq_norm]
  exact lt_of_le_of_lt this hm

/-- Continuity of the resultant `resQ` in both arguments. -/
theorem tendsto_resQ {K : Type*} [NormedField K] {ι : Type*} {l : Filter ι} {t : ι → Fin 2 → K}
    {t0 : Fin 2 → K} {v : ι → K[X]} {v0 : K[X]} (ht : Tendsto t l (𝓝 t0))
    (hv : PTendsto l v v0) : Tendsto (fun n => resQ (t n) (v n)) l (𝓝 (resQ t0 v0)) := by
  have h0 := tendsto_pi_nhds.mp ht 0
  have h1 := tendsto_pi_nhds.mp ht 1
  simp only [resQ]
  exact (((hv 0).pow 2).sub ((h0.mul (hv 0)).mul (hv 1))).add (h1.mul ((hv 1).pow 2))

/-- The candidate abscissas `π ^ (M + (e + 1) + j)`. -/
noncomputable def sK (π : K) (e M j : ℕ) : K := π ^ (M + (e + 1) + j)

variable (e : ℕ)

include hπ in
theorem sK_injective (M : ℕ) : Function.Injective (sK π e M) := by
  intro j1 j2 h
  have h' := congrArg norm h
  simp only [sK, norm_pow] at h'
  have := pow_right_injective₀ hπ.norm_pos hπ.norm_lt_one.ne h'
  omega

include hπ in
theorem sK_ne_zero (M j : ℕ) : sK π e M j ≠ 0 := pow_ne_zero _ hπ.ne_zero

theorem pi_mem_maximalIdeal : hπ.toBall ∈ IsLocalRing.maximalIdeal (unitBall K) := by
  rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self _

theorem pi_pow_mem_maximalIdeal {k : ℕ} (hk : k ≠ 0) :
    hπ.toBall ^ k ∈ IsLocalRing.maximalIdeal (unitBall K) :=
  Ideal.pow_mem_of_mem _ (pi_mem_maximalIdeal hπ) k (Nat.pos_of_ne_zero hk)

/-- The point `z(s1, s2)` of the chart with `uT (π^M z) = (X - s1)(X - s2)`,
`s_i = sK M j_i`. -/
noncomputable def zPair (M j1 j2 : ℕ) : Fin 2 → IsLocalRing.maximalIdeal (unitBall K) :=
  ![⟨-(hπ.toBall ^ (e + 1 + j1) + hπ.toBall ^ (e + 1 + j2)), neg_mem (Ideal.add_mem _
      (pi_pow_mem_maximalIdeal hπ (by omega)) (pi_pow_mem_maximalIdeal hπ (by omega)))⟩,
    ⟨hπ.toBall ^ (M + (e + 1) + (e + 1) + j1 + j2), pi_pow_mem_maximalIdeal hπ (by omega)⟩]

variable [CompleteSpace K] [CharZero K] [HasUniformizer K] (D : LSetup K)

/-- Chart pairs lie in `Z`. -/
theorem inZ_chart [GoodSextic D.f] {M : ℕ} (hM : (D.toSetup hπ).Adm M)
    (z : Fin 2 → IsLocalRing.maximalIdeal (unitBall K)) :
    InZ D.f ⟨(D.toSetup hπ).tPt M z, (D.toSetup hπ).vPt hM z⟩ :=
  ⟨(D.toSetup hπ).vPt_degree hM z, (D.toSetup hπ).dvd_pt hM z⟩

/-- **Continuity of the chart branch.** -/
theorem ptendsto_vPt {M : ℕ} (hM : (D.toSetup hπ).Adm M) {ι : Type*} {l : Filter ι}
    {z : ι → Fin 2 → IsLocalRing.maximalIdeal (unitBall K)} {z0 : Fin 2 → IsLocalRing.maximalIdeal (unitBall K)}
    (h : ∀ j, Tendsto (fun n => (((z n j : (unitBall K))) : K)) l (𝓝 ((z0 j : (unitBall K)) : K))) :
    PTendsto l (fun n => (D.toSetup hπ).vPt hM (z n)) ((D.toSetup hπ).vPt hM z0) := by
  intro i
  have hG := FurioLombardo.Vendor.Toolbox.SubPoly.mem_LR.mp hM.v i
  obtain ⟨N, hN⟩ := (FurioLombardo.Vendor.Toolbox.Bounded.mem_bddR.mp hG)
  have key : ∀ w, ((D.toSetup hπ).vPt hM w).coeff i = ((π : K) ^ N)⁻¹ *
      ((FurioLombardo.Vendor.Toolbox.Bounded.evO w (FurioLombardo.Vendor.Toolbox.Bounded.scaled hπ.toBall N _ hN) : (unitBall K)) : K) := by
    intro w
    rw [Setup.vPt, FurioLombardo.Vendor.Toolbox.SubPoly.coeff_evR, FurioLombardo.Vendor.Toolbox.Bounded.evS_apply,
      FurioLombardo.Vendor.Toolbox.Bounded.evB_eq _ _ _ N hN]
    rfl
  simp only [key]
  exact (tendsto_evO hπ _ h).const_mul _

/-- **The chart lemma.** -/
theorem chart_lemma [GoodSextic D.f] {M : ℕ} (hM : (D.toSetup hπ).Adm M)
    (zT : ((D.toSetup hπ).fglO hM.good).Points)
    (hzT : zT ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((D.toSetup hπ).fglO hM.good) (hπ.toBall ^ (e + 1)))
    {ι : Type*} {l : Filter ι} {Dn : ι → MPair K} (hZ : ∀ᶠ n in l, InZ D.f (Dn n))
    (hlim : DTendsto l Dn ⟨(D.toSetup hπ).tPt M zT, (D.toSetup hπ).vPt hM zT⟩) :
    ∀ᶠ n in l, ∃ z : ((D.toSetup hπ).fglO hM.good).Points,
      z ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((D.toSetup hπ).fglO hM.good) (hπ.toBall ^ (e + 1)) ∧
      Dn n = ⟨(D.toSetup hπ).tPt M z, (D.toSetup hπ).vPt hM z⟩ := by
  have hpM : (π : K) ^ M ≠ 0 := pow_ne_zero M hπ.ne_zero
  -- the rescaled coordinates
  set zr : ι → Fin 2 → K := fun n j => ((π : K) ^ M)⁻¹ * (Dn n).t j with hzr
  have hzT' : ∀ j, (((zT j : (unitBall K))) : K) = ((π : K) ^ M)⁻¹ * (D.toSetup hπ).tPt M zT j := by
    intro j
    simp only [Setup.tPt]
    rw [← mul_assoc, hπ.coe_toBall, inv_mul_cancel₀ hpM, one_mul]
  have hzlim : ∀ j, Tendsto (fun n => zr n j) l (𝓝 (((zT j : (unitBall K))) : K)) := by
    intro j
    rw [hzT']
    exact (tendsto_pi_nhds.mp hlim.1 j).const_mul _
  have hsmall : ∀ᶠ n in l, ∀ j, ‖zr n j‖ ≤ ‖π‖ ^ (e + 1) := by
    refine Filter.eventually_all.mpr fun j => ?_
    have hT := (hπ.mem_span_pow_iff (e + 1)).mp (hzT j)
    filter_upwards [Metric.tendsto_nhds.mp (hzlim j) _ (pow_pos hπ.norm_pos (e + 1))] with n hn
    rw [dist_eq_norm] at hn
    have := IsUltrametricDist.norm_add_le_max (zr n j - ((zT j : (unitBall K)) : K)) ((zT j : (unitBall K)) : K)
    rw [sub_add_cancel] at this
    exact this.trans (max_le hn.le hT)
  have hpv4 : ‖π‖ ^ (e + 1) < 1 := pow_lt_one₀ hπ.norm_pos.le hπ.norm_lt_one (by norm_num)
  -- the points
  let mk : ∀ n, (∀ j, ‖zr n j‖ ≤ ‖π‖ ^ (e + 1)) → ((D.toSetup hπ).fglO hM.good).Points :=
    fun n h j => ⟨⟨zr n j, ((h j).trans hpv4.le : _)⟩,
      mem_maximalIdeal_iff.mpr (lt_of_le_of_lt (h j) hpv4)⟩
  classical
  let z : ι → ((D.toSetup hπ).fglO hM.good).Points := fun n =>
    if h : ∀ j, ‖zr n j‖ ≤ ‖π‖ ^ (e + 1) then mk n h else zT
  have hz : ∀ n (h : ∀ j, ‖zr n j‖ ≤ ‖π‖ ^ (e + 1)), z n = mk n h := fun n h => dite_eq_left h
  have hzval : ∀ᶠ n in l, ∀ j, (((z n j : (unitBall K))) : K) = zr n j := by
    filter_upwards [hsmall] with n hn j
    rw [hz n hn]
  have hzt : ∀ j, Tendsto (fun n => (((z n j : (unitBall K))) : K)) l (𝓝 (((zT j : (unitBall K))) : K)) :=
    fun j => (hzlim j).congr' (hzval.mono fun n hn => (hn j).symm)
  have hvlim := ptendsto_vPt hπ D hM hzt
  have hres2 : resQ ((D.toSetup hπ).tPt M zT) ((D.toSetup hπ).vPt hM zT + (D.toSetup hπ).vPt hM zT) ≠ 0 := by
    have e : resQ ((D.toSetup hπ).tPt M zT) ((D.toSetup hπ).vPt hM zT + (D.toSetup hπ).vPt hM zT) =
        4 * resQ ((D.toSetup hπ).tPt M zT) ((D.toSetup hπ).vPt hM zT) := by
      simp only [resQ, coeff_add]; ring
    rw [e]
    exact mul_ne_zero (by norm_num) ((D.toSetup hπ).resQ_pt_ne hM zT)
  have hreslim := tendsto_resQ hlim.1 (hvlim.add hlim.2)
  filter_upwards [hsmall, hZ, hreslim.eventually_ne hres2] with n hn hZn hrn
  have htn : (D.toSetup hπ).tPt M (z n) = (Dn n).t := by
    funext j
    simp only [Setup.tPt, hz n hn, mk, zr, hπ.coe_toBall]
    rw [← mul_assoc, mul_inv_cancel₀ hpM, one_mul]
  refine ⟨z n, fun j => ?_, ?_⟩
  · rw [hz n hn]
    exact (hπ.mem_span_pow_iff _).mpr (hn j)
  have hdeg : ((D.toSetup hπ).vPt hM (z n) + (Dn n).v).degree < 2 :=
    lt_of_le_of_lt (degree_add_le _ _) (max_lt ((D.toSetup hπ).vPt_degree hM (z n)) hZn.1)
  have hcop := isCoprime_uT (Dn n).t hdeg hrn
  have hd1 := (D.toSetup hπ).dvd_pt hM (z n)
  rw [htn] at hd1
  have hd2 : uT (Dn n).t ∣ ((D.toSetup hπ).vPt hM (z n) - (Dn n).v) *
      ((D.toSetup hπ).vPt hM (z n) + (Dn n).v) := by
    have := dvd_sub hZn.2 hd1
    have e : D.f - (Dn n).v ^ 2 - (D.f - (D.toSetup hπ).vPt hM (z n) ^ 2) =
        ((D.toSetup hπ).vPt hM (z n) - (Dn n).v) * ((D.toSetup hπ).vPt hM (z n) + (Dn n).v) := by ring
    rwa [e] at this
  have hd3 := hcop.dvd_of_dvd_mul_right hd2
  have hdeg' : ((D.toSetup hπ).vPt hM (z n) - (Dn n).v).degree < (uT (Dn n).t).degree := by
    rw [degree_eq_natDegree (uT_monic _).ne_zero, uT_natDegree]
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt ((D.toSetup hπ).vPt_degree hM (z n)) hZn.1)
  have hv := eq_zero_of_dvd_of_degree_lt hd3 hdeg'
  rw [sub_eq_zero] at hv
  rw [htn, hv]

theorem tPt_zPair (M j1 j2 : ℕ) :
    (D.toSetup hπ).tPt M (zPair hπ e M j1 j2) = ![-(sK π e M j1 + sK π e M j2), sK π e M j1 * sK π e M j2] := by
  funext i
  fin_cases i
  · simp [Setup.tPt, zPair, sK]
    ring
  · simp [Setup.tPt, zPair, sK]
    ring

theorem zPair_mem_B1 [GoodSextic D.f] {M : ℕ} (hM : (D.toSetup hπ).Adm M) (j1 j2 : ℕ) :
    (zPair hπ e M j1 j2 : ((D.toSetup hπ).fglO hM.good).Points) ∈
      FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((D.toSetup hπ).fglO hM.good) (hπ.toBall ^ (e + 1)) := by
  intro j
  rw [Ideal.mem_span_singleton]
  fin_cases j
  · simp only [zPair]
    exact dvd_neg.mpr (dvd_add (pow_dvd_pow _ (by omega)) (pow_dvd_pow _ (by omega)))
  · simp only [zPair]
    exact pow_dvd_pow _ (by omega)

end FurioLombardo.Discharge.SelmerBasis.Count
