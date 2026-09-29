import Mathlib
import FurioLombardo.Discharge.KvArith.Chart
import FurioLombardo.Discharge.M4Log.Model

/-!
# The chart branch near the base point (lane lean-kv-arith, N1)

`clsA_eq_chartCls` and `psi_chartPt` need `resQ t (w + vPt z) ≠ 0`, which holds when `w` is the chart
branch: `w ≡ vPt z (mod uT t)`. Here the input for the norm criterion `resQ_ne_zero_of_norm`: the
coefficients of `vPt z` stay near those of `v0`.

For an integral model `H : IntModel S a` (`p = π^a`, `b = V0(0)`), lane lean-m4log's transport gives
`p^n v_n(p t₀, p² t₁) = b ṽ_n(t)` with `ṽ` integral (`IntModel.tw_v`). At the chart point `t = π^(4a) z`
this reads `p^n (vPt z)_n = b ṽ_n(π^(3a) z₀, π^(2a) z₁)`, and at `t = 0` it reads `p^n (v0)_n = b ṽ_n(0)`.
An integral series moves by at most the size of its argument from its constant term
(`evO_sub_constantCoeff_mem`), so `‖(vPt z)_n - (v0)_n‖ ‖pv‖^(n a) ≤ ‖b‖ ‖pv‖^m` as soon as
`‖π^(3a) z₀‖, ‖π^(2a) z₁‖ ≤ ‖pv‖^m` (`norm_vPt_coeff_sub_le`).
-/

open Polynomial IsLocalRing
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7
open FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Vendor.Toolbox.Bounded
open FurioLombardo.Discharge.M4Log.Model
open FurioLombardo.Vendor.Toolbox.Conv (rescale_C' constantCoeff_rescale')

namespace FurioLombardo.Discharge.KvArith

/-! ## An integral series near its constant term -/

section Generic

variable {K : Type*} [Field K] {O : Subring K} [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {σ : Type*} [Finite σ]

/-- The value of an integral series minus its constant term lies in every closed ideal that
contains the terms of positive degree. -/
theorem evO_sub_constantCoeff_mem (z : σ → maximalIdeal O) (G : MvPowerSeries σ O) {I : Ideal O}
    (hI : IsClosed (I : Set O))
    (hG : ∀ d : σ →₀ ℕ, d ≠ 0 → MvPowerSeries.coeff d G * d.prod (fun s e => (z s : O) ^ e) ∈ I) :
    evO z G - MvPowerSeries.constantCoeff G ∈ I := by
  classical
  have h := (FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.hasSum_eval (hasEval_coe z) G).sub
    (hasSum_ite_eq (0 : σ →₀ ℕ) (MvPowerSeries.constantCoeff G))
  change FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.eval (fun i => (z i : O)) G -
    MvPowerSeries.constantCoeff G ∈ I
  rw [← h.tsum_eq]
  refine tsum_mem hI fun d => ?_
  by_cases hd : d = 0
  · subst hd
    simp
  · simp only [hd, ite_false, sub_zero]
    exact hG d hd

end Generic

/-! ## Over `K_v` -/

/-- An ideal `(pv^n)` of `OKv` is closed. -/
theorem isClosed_span_pvO_pow' (n : ℕ) :
    IsClosed ((Ideal.span {pvO ^ n} : Ideal OKv) : Set OKv) := by
  have e : ((Ideal.span {pvO ^ n} : Ideal OKv) : Set OKv) = {x : OKv | ‖(x : Kv)‖ ≤ ‖pv‖ ^ n} := by
    ext x
    exact mem_span_pvO_pow_iff n
  rw [e]
  exact isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const

/-- The weights `(π^(3a), π^(2a))` that take `(p t₀, p² t₁)` to `π^(4a) t`. -/
noncomputable def wtB (a : ℕ) : Fin 2 → Kv := ![pv ^ (3 * a), pv ^ (2 * a)]

theorem wtB_mul_wt1 (a : ℕ) : wtB a * wt1 (pv ^ a) = fun _ => pv ^ (4 * a) := by
  funext i
  fin_cases i
  · simp only [wtB, wt1, Pi.mul_apply, Fin.zero_eta, Matrix.cons_val_zero]
    rw [← pow_add]
    ring_nf
  · simp only [wtB, wt1, Pi.mul_apply, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← pow_mul, ← pow_add]
    ring_nf

theorem norm_wtB_le_one (a : ℕ) (i : Fin 2) : ‖wtB a i‖ ≤ 1 := by
  fin_cases i <;>
  · simp only [wtB, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) norm_pv_lt_one.le

theorem wtB_mem (a : ℕ) (i : Fin 2) : wtB a i ∈ unitBall Kv :=
  mem_unitBall_iff.mpr (norm_wtB_le_one a i)

/-- The rescaled integral branch `ṽ_n(π^(3a) t₀, π^(2a) t₁)` is integral. -/
theorem rescale_wtB_mem {G : MvPowerSeries (Fin 2) Kv} (hG : G ∈ intSeries (unitBall Kv) (Fin 2))
    (a : ℕ) : MvPowerSeries.rescale (wtB a) G ∈ intSeries (unitBall Kv) (Fin 2) := by
  rw [mem_intSeries] at hG ⊢
  intro d
  rw [MvPowerSeries.coeff_rescale]
  refine Subring.mul_mem _ ?_ (hG d)
  exact Subring.prod_mem _ fun s _ => Subring.pow_mem _ (wtB_mem a s) _

/-- A term of positive degree of the rescaled integral branch at `z`. -/
theorem norm_term_le {G : MvPowerSeries (Fin 2) Kv} (hG : G ∈ intSeries (unitBall Kv) (Fin 2))
    (a : ℕ) (z : Fin 2 → maximalIdeal OKv) {m : ℕ} (hz : ∀ i, ‖wtB a i * ((z i : OKv) : Kv)‖ ≤ ‖pv‖ ^ m)
    {d : Fin 2 →₀ ℕ} (hd : d ≠ 0) :
    ‖MvPowerSeries.coeff d (MvPowerSeries.rescale (wtB a) G) *
      d.prod (fun s e => ((z s : OKv) : Kv) ^ e)‖ ≤ ‖pv‖ ^ m := by
  have hc : ‖MvPowerSeries.coeff d G‖ ≤ 1 := mem_unitBall_iff.mp (mem_intSeries.mp hG d)
  rw [MvPowerSeries.coeff_rescale, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two, Fin.prod_univ_two]
  have e : (wtB a 0 ^ d 0 * wtB a 1 ^ d 1) * MvPowerSeries.coeff d G *
      (((z 0 : OKv) : Kv) ^ d 0 * ((z 1 : OKv) : Kv) ^ d 1) =
      MvPowerSeries.coeff d G * ((wtB a 0 * ((z 0 : OKv) : Kv)) ^ d 0 *
        (wtB a 1 * ((z 1 : OKv) : Kv)) ^ d 1) := by ring
  rw [e, norm_mul, norm_mul, norm_pow, norm_pow]
  have h0 := hz 0
  have h1 := hz 1
  have hm1 : ‖pv‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) norm_pv_lt_one.le
  have hp0 : 0 ≤ ‖pv‖ ^ m := by positivity
  have hA : ‖wtB a 0 * ((z 0 : OKv) : Kv)‖ ^ d 0 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (h0.trans hm1)
  have hB : ‖wtB a 1 * ((z 1 : OKv) : Kv)‖ ^ d 1 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (h1.trans hm1)
  have hdd : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
    by_contra hc'
    push Not at hc'
    apply hd
    ext i
    fin_cases i
    · exact hc'.1
    · exact hc'.2
  have key : ‖wtB a 0 * ((z 0 : OKv) : Kv)‖ ^ d 0 * ‖wtB a 1 * ((z 1 : OKv) : Kv)‖ ^ d 1 ≤
      ‖pv‖ ^ m := by
    rcases hdd with h | h
    · have : ‖wtB a 0 * ((z 0 : OKv) : Kv)‖ ^ d 0 ≤ ‖pv‖ ^ m :=
        (pow_le_of_le_one (norm_nonneg _) (h0.trans hm1) h).trans h0
      calc _ ≤ ‖pv‖ ^ m * 1 := mul_le_mul this hB (by positivity) hp0
        _ = _ := mul_one _
    · have : ‖wtB a 1 * ((z 1 : OKv) : Kv)‖ ^ d 1 ≤ ‖pv‖ ^ m :=
        (pow_le_of_le_one (norm_nonneg _) (h1.trans hm1) h).trans h1
      calc _ ≤ 1 * ‖pv‖ ^ m := mul_le_mul hA this (by positivity) zero_le_one
        _ = _ := one_mul _
  calc _ ≤ 1 * (‖wtB a 0 * ((z 0 : OKv) : Kv)‖ ^ d 0 * ‖wtB a 1 * ((z 1 : OKv) : Kv)‖ ^ d 1) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := by rw [one_mul]; exact key

/-- **N1: the chart branch near the base point.** For an integral model at the scale `p = π^a`
and a chart point `z` with `‖π^(3a) z₀‖, ‖π^(2a) z₁‖ ≤ ‖pv‖^m`,
`‖(vPt z)_n - (v0)_n‖ ‖pv‖^(n a) ≤ ‖b‖ ‖pv‖^m`. -/
theorem norm_vPt_coeff_sub_le (Dk : SetupKv) [M3a.Genus2.GoodSextic Dk.f] {a : ℕ}
    (H : IntModel Dk.toSetup a)
    (z : Fin 2 → maximalIdeal OKv) {m : ℕ}
    (hz : ∀ i, ‖wtB a i * ((z i : OKv) : Kv)‖ ≤ ‖pv‖ ^ m) (n : ℕ) :
    ‖(Dk.toSetup.vPt (adm_of_intModel H) z).coeff n - Dk.toSetup.v0.coeff n‖ * ‖pv‖ ^ (n * a) ≤
      ‖H.b‖ * ‖pv‖ ^ m := by
  set vn := Dk.toSetup.v.coeff n with hvn
  set vt := H.vt.coeff n with hvt
  have hvtI : vt ∈ intSeries (unitBall Kv) (Fin 2) := coeff_mem_intSeries_of_liftsRing H.vt_mem n
  set G := MvPowerSeries.rescale (wtB a) vt with hG
  have hGI : G ∈ intSeries (unitBall Kv) (Fin 2) := rescale_wtB_mem hvtI a
  -- the transport identity at degree `n`
  have htw : MvPowerSeries.C ((pv ^ a) ^ n) * MvPowerSeries.rescale (wt1 (pv ^ a)) vn =
      MvPowerSeries.C H.b * vt := by
    have := congrArg (fun P => P.coeff n) H.tw_v
    simp only [coeff_tw, Polynomial.coeff_C_mul] at this
    exact this
  -- at the chart point
  have hR : MvPowerSeries.C ((pv ^ a) ^ n) *
      MvPowerSeries.rescale (fun _ => pv ^ (4 * a)) vn = MvPowerSeries.C H.b * G := by
    rw [← wtB_mul_wt1, mul_comm (wtB a), ← MvPowerSeries.rescale_rescale,
      ← rescale_C' (wtB a) ((pv ^ a) ^ n), ← map_mul, htw, map_mul, rescale_C']
  -- the value at `z`
  have hvn_mem : vn ∈ bddR (Fin 2) Dk.toSetup.π ((Dk.toSetup.π : Kv) ^ (4 * a)) := FurioLombardo.Vendor.Toolbox.SubPoly.mem_LR.mp (adm_of_intModel H).v n
  have hC : MvPowerSeries.C ((pv ^ a) ^ n) ∈ bdd Dk.toSetup.O (Fin 2) Dk.toSetup.π := C_mem_bdd Dk.toSetup.hπ0 Dk.toSetup.hbd _
  have hCb : MvPowerSeries.C H.b ∈ bdd Dk.toSetup.O (Fin 2) Dk.toSetup.π := C_mem_bdd Dk.toSetup.hπ0 Dk.toSetup.hbd _
  have hGb : G ∈ bdd Dk.toSetup.O (Fin 2) Dk.toSetup.π := intSeries_le_bdd _ hGI
  have hval : (pv ^ a) ^ n * (Dk.toSetup.vPt (adm_of_intModel H) z).coeff n =
      H.b * ((evO z (toO hGI) : OKv) : Kv) := by
    rw [Setup.coeff_vPt, evS_apply]
    have key : (⟨_, hC⟩ * ⟨_, hvn_mem⟩ : bdd Dk.toSetup.O (Fin 2) Dk.toSetup.π) = ⟨_, hCb⟩ * ⟨_, hGb⟩ :=
      Subtype.ext hR
    have := congrArg (evB Dk.toSetup.hπ0 z) key
    rw [map_mul, map_mul, evB_C, evB_C] at this
    rw [this, ← evB_of_mem_intSeries Dk.toSetup.hπ0 z hGI]
  -- the value at `0`
  have hv0 : Dk.toSetup.v0.coeff n = MvPowerSeries.constantCoeff vn := by
    have := congrArg (fun P => P.coeff n) Dk.toSetup.v_map
    simp only [Polynomial.coeff_map] at this
    exact this.symm
  have hcst : (pv ^ a) ^ n * Dk.toSetup.v0.coeff n =
      H.b * ((MvPowerSeries.constantCoeff (toO hGI) : OKv) : Kv) := by
    have := congrArg MvPowerSeries.constantCoeff htw
    rw [map_mul, map_mul, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_C,
      constantCoeff_rescale'] at this
    have hc0 : ((MvPowerSeries.constantCoeff (toO hGI) : OKv) : Kv) = MvPowerSeries.constantCoeff G := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_toO,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [hv0, this, hc0, hG, constantCoeff_rescale']
  -- the difference
  have hmem := evO_sub_constantCoeff_mem z (toO hGI) (isClosed_span_pvO_pow' m) (fun d hd => by
    rw [mem_span_pvO_pow_iff]
    have e : ((MvPowerSeries.coeff d (toO hGI) * d.prod (fun s e => ((z s : OKv)) ^ e) : OKv) : Kv) =
        MvPowerSeries.coeff d G * d.prod (fun s e => ((z s : OKv) : Kv) ^ e) := by
      rw [Subring.coe_mul, coeff_toO, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      push_cast
      rfl
    rw [e]
    exact norm_term_le hvtI a z hz hd)
  rw [mem_span_pvO_pow_iff] at hmem
  have hdiff : (pv ^ a) ^ n * ((Dk.toSetup.vPt (adm_of_intModel H) z).coeff n - Dk.toSetup.v0.coeff n) =
      H.b * (((evO z (toO hGI) - MvPowerSeries.constantCoeff (toO hGI) : OKv)) : Kv) := by
    rw [mul_sub, hval, hcst, AddSubgroupClass.coe_sub, mul_sub]
  have hn := congrArg norm hdiff
  rw [norm_mul, norm_mul, norm_pow, norm_pow, ← pow_mul, mul_comm a n] at hn
  rw [mul_comm, hn]
  exact mul_le_mul_of_nonneg_left hmem (norm_nonneg _)

/-! ## `resQ ≠ 0` on the chart branch -/

theorem v0_coeff_zero (Dk : SetupKv) {a : ℕ} (H : IntModel Dk.toSetup a) :
    Dk.toSetup.v0.coeff 0 = H.b := by
  rw [Setup.v0, coeff_modByMonic_X_pow _ two_pos, H.hV00]

theorem norm_v0_coeff_one_le (Dk : SetupKv) {a : ℕ} (H : IntModel Dk.toSetup a) :
    ‖Dk.toSetup.v0.coeff 1‖ * ‖pv‖ ^ a ≤ ‖H.b‖ := by
  have h := congrArg (fun P => P.coeff 1) H.v0_comp
  simp only [Polynomial.coeff_C_mul] at h
  rw [coeff_modByMonic_X_pow _ one_lt_two] at h
  have hc : (Dk.toSetup.v0.comp (C (pw Dk.toSetup a) * X)).coeff 1 =
      Dk.toSetup.v0.coeff 1 * pw Dk.toSetup a := by
    rw [comp_C_mul_X_coeff, pow_one]
  rw [hc] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_mul] at hn
  have hp : ‖pw Dk.toSetup a‖ = ‖pv‖ ^ a := norm_pow _ _
  rw [← hp, hn]
  exact mul_le_of_le_one_right (norm_nonneg _) (mem_unitBall_iff.mp (H.Vt_mem 1))

/-- The chart point `t / π^(4a)` in the weights of N1. -/
theorem chartPt_wtB_le {a m : ℕ} {t : Fin 2 → Kv} (ht : ∀ i, ‖t i‖ ≤ ‖pv‖ ^ (4 * a + 4))
    (ht0 : ‖t 0‖ ≤ ‖pv‖ ^ (m + a)) (ht1 : ‖t 1‖ ≤ ‖pv‖ ^ (m + 2 * a)) (i : Fin 2) :
    ‖wtB a i * (((chartPt (4 * a) t ht) i : OKv) : Kv)‖ ≤ ‖pv‖ ^ m := by
  have hq := norm_pv_pos
  change ‖wtB a i * (t i / pv ^ (4 * a))‖ ≤ _
  fin_cases i
  · simp only [wtB, Fin.zero_eta, Matrix.cons_val_zero]
    rw [norm_mul, norm_div, norm_pow, norm_pow, mul_div_assoc', div_le_iff₀ (by positivity),
      show 4 * a = 3 * a + a by ring, pow_add, ← mul_assoc, mul_comm (‖pv‖ ^ m), mul_assoc,
      ← pow_add]
    exact mul_le_mul_of_nonneg_left ht0 (by positivity)
  · simp only [wtB, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [norm_mul, norm_div, norm_pow, norm_pow, mul_div_assoc', div_le_iff₀ (by positivity),
      show 4 * a = 2 * a + 2 * a by ring, pow_add, ← mul_assoc, mul_comm (‖pv‖ ^ m), mul_assoc,
      ← pow_add]
    exact mul_le_mul_of_nonneg_left ht1 (by positivity)

/-- **`resQ ≠ 0` on the chart branch.** For an integral model at the scale `π^a`, chart
coordinates `t` with `‖t₀‖ ≤ ‖pv‖^(m+a)`, `‖t₁‖ ≤ ‖pv‖^(m+2a)`, `m ≥ 7`, and a `w` on the branch
of `v0` (`‖w₀ - b‖ < ‖2b‖`, `‖w₁‖ ‖pv‖^a ≤ ‖b‖`), `w + vPt z` is coprime to `uT t`. -/
theorem resQ_branch_ne_zero (Dk : SetupKv) [M3a.Genus2.GoodSextic Dk.f] {a : ℕ}
    (H : IntModel Dk.toSetup a) {t : Fin 2 → Kv} (ht : ∀ i, ‖t i‖ ≤ ‖pv‖ ^ (4 * a + 4))
    {m : ℕ} (hm : 7 ≤ m) (ht0 : ‖t 0‖ ≤ ‖pv‖ ^ (m + a)) (ht1 : ‖t 1‖ ≤ ‖pv‖ ^ (m + 2 * a))
    {w : Kv[X]} (hw0 : ‖w.coeff 0 - H.b‖ < ‖2 * H.b‖) (hw1 : ‖w.coeff 1‖ * ‖pv‖ ^ a ≤ ‖H.b‖) :
    resQ t (w + Dk.toSetup.vPt (adm_of_intModel H) (chartPt (4 * a) t ht)) ≠ 0 := by
  set vP := Dk.toSetup.vPt (adm_of_intModel H) (chartPt (4 * a) t ht) with hvP
  have hz := chartPt_wtB_le ht ht0 ht1
  have hN0 := norm_vPt_coeff_sub_le Dk H _ hz 0
  have hN1 := norm_vPt_coeff_sub_le Dk H _ hz 1
  rw [← hvP, zero_mul, pow_zero, mul_one, v0_coeff_zero Dk H] at hN0
  rw [← hvP, one_mul] at hN1
  set q := ‖pv‖ with hq
  set B := ‖H.b‖ with hB
  have hq0 : 0 < q := norm_pv_pos
  have hq1 : q < 1 := norm_pv_lt_one
  have hB0 : 0 < B := norm_pos_iff.mpr H.hb
  have h2b : ‖2 * H.b‖ = q ^ 3 * B := by rw [norm_mul, norm_two_Kv, hq, norm_pv_pow_three]
  have hqm : q ^ m ≤ q ^ 7 := pow_le_pow_of_le_one hq0.le hq1.le hm
  have hq73 : q ^ 7 < q ^ 3 := pow_lt_pow_right_of_lt_one₀ hq0 hq1 (by norm_num)
  have hq76 : q ^ 7 < q ^ 6 := pow_lt_pow_right_of_lt_one₀ hq0 hq1 (by norm_num)
  have hqa : 0 < q ^ a := pow_pos hq0 a
  -- the constant coefficient: `y₀ = 2b + (w₀ - b) + (vP₀ - b)`, of norm `‖2b‖`
  have hy0 : ‖(w + vP).coeff 0‖ = q ^ 3 * B := by
    have e : (w + vP).coeff 0 = 2 * H.b + ((w.coeff 0 - H.b) + (vP.coeff 0 - H.b)) := by
      rw [coeff_add]; ring
    have hs : ‖(w.coeff 0 - H.b) + (vP.coeff 0 - H.b)‖ < ‖2 * H.b‖ := by
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hw0 ?_)
      rw [h2b]
      calc ‖vP.coeff 0 - H.b‖ ≤ B * q ^ m := hN0
        _ ≤ B * q ^ 7 := mul_le_mul_of_nonneg_left hqm hB0.le
        _ < q ^ 3 * B := by rw [mul_comm]; exact mul_lt_mul_of_pos_right hq73 hB0
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hs), max_eq_left hs.le, h2b]
  -- the linear coefficient: `‖y₁‖ q^a ≤ B`
  have hy1 : ‖(w + vP).coeff 1‖ * q ^ a ≤ B := by
    have e : (w + vP).coeff 1 = w.coeff 1 + (Dk.toSetup.v0.coeff 1 +
        (vP.coeff 1 - Dk.toSetup.v0.coeff 1)) := by
      rw [coeff_add]; ring
    have hv1 := norm_v0_coeff_one_le Dk H
    have hd1 : ‖vP.coeff 1 - Dk.toSetup.v0.coeff 1‖ * q ^ a ≤ B :=
      hN1.trans (mul_le_of_le_one_right hB0.le (pow_le_one₀ hq0.le hq1.le))
    rw [e]
    have h1 := IsUltrametricDist.norm_add_le_max (w.coeff 1)
      (Dk.toSetup.v0.coeff 1 + (vP.coeff 1 - Dk.toSetup.v0.coeff 1))
    have h2 := IsUltrametricDist.norm_add_le_max (Dk.toSetup.v0.coeff 1)
      (vP.coeff 1 - Dk.toSetup.v0.coeff 1)
    calc _ ≤ max ‖w.coeff 1‖ (max ‖Dk.toSetup.v0.coeff 1‖
          ‖vP.coeff 1 - Dk.toSetup.v0.coeff 1‖) * q ^ a :=
          mul_le_mul_of_nonneg_right (h1.trans (max_le_max le_rfl h2)) hqa.le
      _ ≤ B := by
        rw [max_mul_of_nonneg _ _ hqa.le, max_mul_of_nonneg _ _ hqa.le]
        exact max_le hw1 (max_le hv1 hd1)
  have hy1' : 0 ≤ ‖(w + vP).coeff 1‖ := norm_nonneg _
  refine resQ_ne_zero_of_norm ?_ ?_ ?_
  · intro h0
    have : ‖(w + vP).coeff 0‖ = 0 := by rw [h0, norm_zero]
    rw [hy0] at this
    exact (ne_of_gt (mul_pos (pow_pos hq0 3) hB0)) this
  · -- `‖t₀‖ y₀ y₁ < y₀²`
    rw [norm_mul, norm_mul, hy0]
    have ht0' : ‖t 0‖ * ‖(w + vP).coeff 1‖ ≤ q ^ m * B := by
      calc ‖t 0‖ * ‖(w + vP).coeff 1‖ ≤ q ^ (m + a) * ‖(w + vP).coeff 1‖ :=
            mul_le_mul_of_nonneg_right ht0 hy1'
        _ = q ^ m * (‖(w + vP).coeff 1‖ * q ^ a) := by rw [pow_add]; ring
        _ ≤ q ^ m * B := mul_le_mul_of_nonneg_left hy1 (by positivity)
    have hlt : ‖t 0‖ * ‖(w + vP).coeff 1‖ < q ^ 3 * B :=
      ht0'.trans_lt (mul_lt_mul_of_pos_right (hqm.trans_lt hq73) hB0)
    have hpos : 0 < q ^ 3 * B := mul_pos (pow_pos hq0 3) hB0
    calc ‖t 0‖ * (q ^ 3 * B) * ‖(w + vP).coeff 1‖ = (‖t 0‖ * ‖(w + vP).coeff 1‖) * (q ^ 3 * B) := by ring
      _ < (q ^ 3 * B) * (q ^ 3 * B) := mul_lt_mul_of_pos_right hlt hpos
      _ = (q ^ 3 * B) ^ 2 := by ring
  · -- `‖t₁‖ y₁² < y₀²`
    rw [norm_mul, norm_pow, hy0]
    calc ‖t 1‖ * ‖(w + vP).coeff 1‖ ^ 2 ≤ q ^ (m + 2 * a) * ‖(w + vP).coeff 1‖ ^ 2 := mul_le_mul_of_nonneg_right ht1 (by positivity)
      _ = q ^ m * (‖(w + vP).coeff 1‖ * q ^ a) ^ 2 := by rw [pow_add, pow_mul]; ring
      _ ≤ q ^ m * B ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_left₀ (by positivity) hy1 2
      _ < q ^ 6 * B ^ 2 := mul_lt_mul_of_pos_right (hqm.trans_lt hq76) (by positivity)
      _ = (q ^ 3 * B) ^ 2 := by ring

end FurioLombardo.Discharge.KvArith
