import Mathlib
import FurioLombardo.Discharge.R7.ChartKv
import FurioLombardo.Discharge.R7.FinIdx.ZSet
import FurioLombardo.Vendor.Toolbox.PowerSeries.EvalLip

/-!
# The chart lemma (R7)

* `tendsto_evO`: evaluation of a fixed `OKv`-series is continuous in the point (through
  `FurioLombardo.Vendor.Toolbox.EvalLip.eval_sub_mem`: evaluation is Lipschitz for closed ideals);
* `ptendsto_vPt`: `z ↦ vPt z` is continuous (coefficientwise, in `Kv`);
* `inZ_chart`: chart pairs `(π^M z, vPt z)` lie in `Z`;
* `chart_lemma`: pairs of `Z` close to the chart pair of `z_T ∈ B1 Φ c` are chart pairs of points
  of `B1 Φ c`.
* `zPair`: the points `z(s1, s2)` with `uT (π^M z) = (X - s1)(X - s2)`, `s_i = pv^(M+4+j_i)`.
-/

open Polynomial Filter Topology
open FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Vendor.Toolbox.PolyLim
open FurioLombardo.Discharge.M4Cert

namespace FurioLombardo.Discharge.R7.FinIdx

/-- The ideals `pv ^ m OKv` are closed. -/
theorem isClosed_span_pvO_pow (m : ℕ) : IsClosed ((Ideal.span {pvO ^ m} : Ideal OKv) : Set OKv) := by
  have : ((Ideal.span {pvO ^ m} : Ideal OKv) : Set OKv) = {x : OKv | ‖(x : Kv)‖ ≤ ‖pv‖ ^ m} := by
    ext x; exact mem_span_pvO_pow_iff m
  rw [this]
  exact isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const

/-- Evaluation of a fixed `OKv`-series is continuous (in the `Kv` topology on coordinates). -/
theorem tendsto_evO {ι σ : Type*} [Finite σ] {l : Filter ι} (H : MvPowerSeries σ OKv)
    {z : ι → σ → IsLocalRing.maximalIdeal OKv} {z0 : σ → IsLocalRing.maximalIdeal OKv}
    (h : ∀ j, Tendsto (fun n => (((z n j : OKv)) : Kv)) l (𝓝 ((z0 j : OKv) : Kv))) :
    Tendsto (fun n => ((FurioLombardo.Vendor.Toolbox.Bounded.evO (z n) H : OKv) : Kv)) l
      (𝓝 ((FurioLombardo.Vendor.Toolbox.Bounded.evO z0 H : OKv) : Kv)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε norm_pv_lt_one
  have hj : ∀ j, ∀ᶠ n in l, dist (((z n j : OKv)) : Kv) ((z0 j : OKv) : Kv) < ‖pv‖ ^ m :=
    fun j => Metric.tendsto_nhds.mp (h j) _ (pow_pos norm_pv_pos m)
  have hall : ∀ᶠ n in l, ∀ j, dist (((z n j : OKv)) : Kv) ((z0 j : OKv) : Kv) < ‖pv‖ ^ m := by
    exact Filter.eventually_all.mpr hj
  filter_upwards [hall] with n hn
  have hmem : ∀ j, ((z n j : OKv)) - ((z0 j : OKv)) ∈ Ideal.span {pvO ^ m} := fun j => by
    rw [mem_span_pvO_pow_iff, AddSubgroupClass.coe_sub]
    have := hn j
    rw [dist_eq_norm] at this
    exact this.le
  have := FurioLombardo.Vendor.Toolbox.EvalLip.eval_sub_mem H (fun j => (z n j).2) (fun j => (z0 j).2)
    (isClosed_span_pvO_pow m) hmem
  rw [mem_span_pvO_pow_iff, AddSubgroupClass.coe_sub] at this
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

variable (D : SetupKv)

/-- Chart pairs lie in `Z`. -/
theorem inZ_chart [GoodSextic D.f] {M : ℕ} (hM : D.toSetup.Adm M)
    (z : Fin 2 → IsLocalRing.maximalIdeal OKv) :
    InZ D.f ⟨D.toSetup.tPt M z, D.toSetup.vPt hM z⟩ :=
  ⟨D.toSetup.vPt_degree hM z, D.toSetup.dvd_pt hM z⟩

/-- **Continuity of the chart branch.** -/
theorem ptendsto_vPt {M : ℕ} (hM : D.toSetup.Adm M) {ι : Type*} {l : Filter ι}
    {z : ι → Fin 2 → IsLocalRing.maximalIdeal OKv} {z0 : Fin 2 → IsLocalRing.maximalIdeal OKv}
    (h : ∀ j, Tendsto (fun n => (((z n j : OKv)) : Kv)) l (𝓝 ((z0 j : OKv) : Kv))) :
    PTendsto l (fun n => D.toSetup.vPt hM (z n)) (D.toSetup.vPt hM z0) := by
  intro i
  have hG := FurioLombardo.Vendor.Toolbox.SubPoly.mem_LR.mp hM.v i
  obtain ⟨N, hN⟩ := (FurioLombardo.Vendor.Toolbox.Bounded.mem_bddR.mp hG)
  have key : ∀ w, (D.toSetup.vPt hM w).coeff i = ((pv : Kv) ^ N)⁻¹ *
      ((FurioLombardo.Vendor.Toolbox.Bounded.evO w (FurioLombardo.Vendor.Toolbox.Bounded.scaled pvO N _ hN) : OKv) : Kv) := by
    intro w
    rw [Setup.vPt, FurioLombardo.Vendor.Toolbox.SubPoly.coeff_evR, FurioLombardo.Vendor.Toolbox.Bounded.evS_apply,
      FurioLombardo.Vendor.Toolbox.Bounded.evB_eq _ _ _ N hN]
    rfl
  simp only [key]
  exact (tendsto_evO _ h).const_mul _

/-- **The chart lemma.** -/
theorem chart_lemma [GoodSextic D.f] {M : ℕ} (hM : D.toSetup.Adm M)
    (zT : (D.toSetup.fglO hM.good).Points)
    (hzT : zT ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 (D.toSetup.fglO hM.good) (pvO ^ (3 + 1)))
    {ι : Type*} {l : Filter ι} {Dn : ι → MPair Kv} (hZ : ∀ᶠ n in l, InZ D.f (Dn n))
    (hlim : DTendsto l Dn ⟨D.toSetup.tPt M zT, D.toSetup.vPt hM zT⟩) :
    ∀ᶠ n in l, ∃ z : (D.toSetup.fglO hM.good).Points,
      z ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 (D.toSetup.fglO hM.good) (pvO ^ (3 + 1)) ∧
      Dn n = ⟨D.toSetup.tPt M z, D.toSetup.vPt hM z⟩ := by
  have hpM : (pv : Kv) ^ M ≠ 0 := pow_ne_zero M isUniformizer_pv.ne_zero
  -- the rescaled coordinates
  set zr : ι → Fin 2 → Kv := fun n j => ((pv : Kv) ^ M)⁻¹ * (Dn n).t j with hzr
  have hzT' : ∀ j, (((zT j : OKv)) : Kv) = ((pv : Kv) ^ M)⁻¹ * D.toSetup.tPt M zT j := by
    intro j
    simp only [Setup.tPt]
    rw [← mul_assoc, coe_pvO, inv_mul_cancel₀ hpM, one_mul]
  have hzlim : ∀ j, Tendsto (fun n => zr n j) l (𝓝 (((zT j : OKv)) : Kv)) := by
    intro j
    rw [hzT']
    exact (tendsto_pi_nhds.mp hlim.1 j).const_mul _
  have hsmall : ∀ᶠ n in l, ∀ j, ‖zr n j‖ ≤ ‖pv‖ ^ (3 + 1) := by
    refine Filter.eventually_all.mpr fun j => ?_
    have hT := (mem_span_pvO_pow_iff (3 + 1)).mp (hzT j)
    filter_upwards [Metric.tendsto_nhds.mp (hzlim j) _ (pow_pos norm_pv_pos (3 + 1))] with n hn
    rw [dist_eq_norm] at hn
    have := IsUltrametricDist.norm_add_le_max (zr n j - ((zT j : OKv) : Kv)) ((zT j : OKv) : Kv)
    rw [sub_add_cancel] at this
    exact this.trans (max_le hn.le hT)
  have hpv4 : ‖pv‖ ^ (3 + 1) < 1 := pow_lt_one₀ norm_pv_pos.le norm_pv_lt_one (by norm_num)
  -- the points
  let mk : ∀ n, (∀ j, ‖zr n j‖ ≤ ‖pv‖ ^ (3 + 1)) → (D.toSetup.fglO hM.good).Points :=
    fun n h j => ⟨⟨zr n j, ((h j).trans hpv4.le : _)⟩,
      mem_maximalIdeal_iff.mpr (lt_of_le_of_lt (h j) hpv4)⟩
  classical
  let z : ι → (D.toSetup.fglO hM.good).Points := fun n =>
    if h : ∀ j, ‖zr n j‖ ≤ ‖pv‖ ^ (3 + 1) then mk n h else zT
  have hz : ∀ n (h : ∀ j, ‖zr n j‖ ≤ ‖pv‖ ^ (3 + 1)), z n = mk n h := fun n h => dite_eq_left h
  have hzval : ∀ᶠ n in l, ∀ j, (((z n j : OKv)) : Kv) = zr n j := by
    filter_upwards [hsmall] with n hn j
    rw [hz n hn]
  have hzt : ∀ j, Tendsto (fun n => (((z n j : OKv)) : Kv)) l (𝓝 (((zT j : OKv)) : Kv)) :=
    fun j => (hzlim j).congr' (hzval.mono fun n hn => (hn j).symm)
  have hvlim := ptendsto_vPt D hM hzt
  have hres2 : resQ (D.toSetup.tPt M zT) (D.toSetup.vPt hM zT + D.toSetup.vPt hM zT) ≠ 0 := by
    have e : resQ (D.toSetup.tPt M zT) (D.toSetup.vPt hM zT + D.toSetup.vPt hM zT) =
        4 * resQ (D.toSetup.tPt M zT) (D.toSetup.vPt hM zT) := by
      simp only [resQ, coeff_add]; ring
    rw [e]
    exact mul_ne_zero (by norm_num) (D.toSetup.resQ_pt_ne hM zT)
  have hreslim := tendsto_resQ hlim.1 (hvlim.add hlim.2)
  filter_upwards [hsmall, hZ, hreslim.eventually_ne hres2] with n hn hZn hrn
  have htn : D.toSetup.tPt M (z n) = (Dn n).t := by
    funext j
    simp only [Setup.tPt, hz n hn, mk, zr, coe_pvO]
    rw [← mul_assoc, mul_inv_cancel₀ hpM, one_mul]
  refine ⟨z n, fun j => ?_, ?_⟩
  · rw [hz n hn]
    exact (mem_span_pvO_pow_iff _).mpr (hn j)
  have hdeg : (D.toSetup.vPt hM (z n) + (Dn n).v).degree < 2 :=
    lt_of_le_of_lt (degree_add_le _ _) (max_lt (D.toSetup.vPt_degree hM (z n)) hZn.1)
  have hcop := isCoprime_uT (Dn n).t hdeg hrn
  have hd1 := D.toSetup.dvd_pt hM (z n)
  rw [htn] at hd1
  have hd2 : uT (Dn n).t ∣ (D.toSetup.vPt hM (z n) - (Dn n).v) *
      (D.toSetup.vPt hM (z n) + (Dn n).v) := by
    have := dvd_sub hZn.2 hd1
    have e : D.f - (Dn n).v ^ 2 - (D.f - D.toSetup.vPt hM (z n) ^ 2) =
        (D.toSetup.vPt hM (z n) - (Dn n).v) * (D.toSetup.vPt hM (z n) + (Dn n).v) := by ring
    rwa [e] at this
  have hd3 := hcop.dvd_of_dvd_mul_right hd2
  have hdeg' : (D.toSetup.vPt hM (z n) - (Dn n).v).degree < (uT (Dn n).t).degree := by
    rw [degree_eq_natDegree (uT_monic _).ne_zero, uT_natDegree]
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (D.toSetup.vPt_degree hM (z n)) hZn.1)
  have hv := eq_zero_of_dvd_of_degree_lt hd3 hdeg'
  rw [sub_eq_zero] at hv
  rw [htn, hv]

/-- The candidate abscissas `pv ^ (M + 4 + j)`. -/
noncomputable def sK (M j : ℕ) : Kv := pv ^ (M + 4 + j)

theorem sK_injective (M : ℕ) : Function.Injective (sK M) := by
  intro j1 j2 h
  have h' := congrArg norm h
  simp only [sK, norm_pow] at h'
  have := pow_right_injective₀ norm_pv_pos norm_pv_lt_one.ne h'
  omega

theorem sK_ne_zero (M j : ℕ) : sK M j ≠ 0 := pow_ne_zero _ isUniformizer_pv.ne_zero

theorem pvO_mem_maximalIdeal : pvO ∈ IsLocalRing.maximalIdeal OKv := by
  rw [maximalIdeal_OKv]; exact Ideal.mem_span_singleton_self _

theorem pvO_pow_mem_maximalIdeal {k : ℕ} (hk : k ≠ 0) :
    pvO ^ k ∈ IsLocalRing.maximalIdeal OKv :=
  Ideal.pow_mem_of_mem _ pvO_mem_maximalIdeal k (Nat.pos_of_ne_zero hk)

/-- The point `z(s1, s2)` of the chart with `uT (π^M z) = (X - s1)(X - s2)`,
`s_i = sK M j_i`. -/
noncomputable def zPair (M j1 j2 : ℕ) : Fin 2 → IsLocalRing.maximalIdeal OKv :=
  ![⟨-(pvO ^ (4 + j1) + pvO ^ (4 + j2)), neg_mem (Ideal.add_mem _
      (pvO_pow_mem_maximalIdeal (by omega)) (pvO_pow_mem_maximalIdeal (by omega)))⟩,
    ⟨pvO ^ (M + 8 + j1 + j2), pvO_pow_mem_maximalIdeal (by omega)⟩]

theorem tPt_zPair (M j1 j2 : ℕ) :
    D.toSetup.tPt M (zPair M j1 j2) = ![-(sK M j1 + sK M j2), sK M j1 * sK M j2] := by
  funext i
  fin_cases i
  · simp [Setup.tPt, zPair, sK]
    ring
  · simp [Setup.tPt, zPair, sK]
    ring

theorem zPair_mem_B1 [GoodSextic D.f] {M : ℕ} (hM : D.toSetup.Adm M) (j1 j2 : ℕ) :
    (zPair M j1 j2 : (D.toSetup.fglO hM.good).Points) ∈
      FurioLombardo.Vendor.Toolbox.FormalGroup.B1 (D.toSetup.fglO hM.good) (pvO ^ (3 + 1)) := by
  intro j
  rw [Ideal.mem_span_singleton]
  fin_cases j
  · simp only [zPair]
    exact dvd_neg.mpr (dvd_add (pow_dvd_pow _ (by omega)) (pow_dvd_pow _ (by omega)))
  · simp only [zPair]
    exact pow_dvd_pow _ (by omega)

end FurioLombardo.Discharge.R7.FinIdx
