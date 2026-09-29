import Mathlib
import FurioLombardo.Discharge.SelmerBasis.Count.Chart
import FurioLombardo.Discharge.R7.FinIdx.BadSet

/-!
# KEY (R7)

For every `D* ∈ Z` and every family `D n → D*` in `Z`, eventually `cls (D n) · (cls D*)⁻¹` lies in
any subgroup `G` of `Pic F` containing the chart image `ψ(B1 Φ c)`. Proof: a good chart pair
`T = D(z_T)` (BadSet.lean), `D' = comp T (-D*)`, continuity of `comp (·) D'` at `D*`, uniqueness of
reduced pairs (`comp D* D' = T`), and the chart lemma.
-/

set_option autoImplicit false

open Polynomial Filter Topology
open FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Vendor.Toolbox.PolyLim
open FurioLombardo.Discharge.R7 FurioLombardo.Discharge.R7.FinIdx

namespace FurioLombardo.Discharge.SelmerBasis.Count

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [HasUniformizer K] {π : K} (hπ : IsUniformizer π) (e : ℕ)
  (D : LSetup K) [GoodSextic D.f] {F : K[X]} [GoodSextic F] {a : K}

include hπ in
/-- Infinitely many `j` avoid a finite set of values of `sK π e M`. -/
theorem exists_sK_not_mem (M : ℕ) {B : Set K} (hB : B.Finite) : ∃ j, sK π e M j ∉ B :=
  (hB.preimage (sK_injective hπ e M).injOn).infinite_compl.nonempty

/-- **KEY.** -/
theorem key (hF : D.f.comp (X - C a) = F) {M : ℕ} (hM : (D.toSetup hπ).Adm M) (G : Subgroup (Pic F))
    (hG : ∀ z ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((D.toSetup hπ).fglO hM.good) (hπ.toBall ^ (e + 1)),
      ((Additive.toMul ((D.toSetup hπ).psi hF hM z) : Jac F) : Pic F) ∈ G)
    {Ds : MPair K} (hDs : InZ D.f Ds) {ι : Type*} {l : Filter ι} {Dn : ι → MPair K}
    (hZ : ∀ᶠ n in l, InZ D.f (Dn n)) (hlim : DTendsto l Dn Ds) :
    ∀ᶠ n in l, cls F a (Dn n) * (cls F a Ds)⁻¹ ∈ G := by
  have hu0 : uT Ds.t ≠ 0 := (uT_monic _).ne_zero
  have hroots : {x : K | (uT Ds.t).IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hu0
  -- the first abscissa
  obtain ⟨j1, hj1⟩ := exists_sK_not_mem hπ e M hroots
  set s1 := sK π e M j1
  have hs1 : (uT Ds.t).eval s1 ≠ 0 := hj1
  -- the second abscissa
  have hbad := finite_bad hDs hs1
  obtain ⟨j2, hj2⟩ := exists_sK_not_mem hπ e M ((hbad.union hroots).union (Set.finite_singleton s1))
  set s2 := sK π e M j2
  simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hj2
  obtain ⟨⟨hnb, hs2⟩, hne⟩ := hj2
  have hs2 : (uT Ds.t).eval s2 ≠ 0 := hs2
  -- the target chart pair
  set zT : ((D.toSetup hπ).fglO hM.good).Points := zPair hπ e M j1 j2
  have hzT : zT ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((D.toSetup hπ).fglO hM.good) (hπ.toBall ^ (e + 1)) :=
    zPair_mem_B1 hπ e D hM j1 j2
  set T : MPair K := ⟨(D.toSetup hπ).tPt M zT, (D.toSetup hπ).vPt hM zT⟩ with hTdef
  have hT : InZ D.f T := inZ_chart hπ D hM zT
  have hTt : T.t = ![-(s1 + s2), s1 * s2] := tPt_zPair hπ e D M j1 j2
  have hTeq : T = ⟨![-(s1 + s2), s1 * s2], (D.toSetup hπ).vPt hM zT⟩ := by
    rw [← hTt]
  have hG1 : res2 T.t Ds.neg.t ≠ 0 := by
    change res2 T.t Ds.t ≠ 0
    rw [res2_comm, hTt, res2_eq_eval_mul]
    exact mul_ne_zero hs1 hs2
  set D' := comp D.f T Ds.neg
  have hD' : InZ D.f D' := InZ.comp hT hDs.neg hG1
  have hG2 : res2 Ds.t D'.t ≠ 0 := by
    intro h
    apply hnb
    refine ⟨(D.toSetup hπ).vPt hM zT, hTeq ▸ hT, hne, hs2, ?_⟩
    rw [← hTeq]
    exact h
  -- continuity of `comp (·) D'` at `Ds`
  have hcont : DTendsto l (fun n => comp D.f (Dn n) D') (comp D.f Ds D') :=
    hlim.comp ⟨tendsto_const_nhds, ptendsto_const _⟩ (hZ.mono fun n hn => ⟨hn, hD'⟩) hDs hD' hG2
  -- `comp Ds D' = T`
  have hcompT : comp D.f Ds D' = T := by
    refine eq_of_cls_eq hF (InZ.comp hDs hD' hG2) hT ?_
    rw [cls_comp hF hDs hD' hG2, cls_comp hF hT hDs.neg hG1, cls_neg hF hDs, mul_comm (cls F a T),
      ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hcompT] at hcont
  have hres : ∀ᶠ n in l, res2 (Dn n).t D'.t ≠ 0 :=
    (tendsto_res2 hlim.1 tendsto_const_nhds).eventually_ne hG2
  have hZc : ∀ᶠ n in l, InZ D.f (comp D.f (Dn n) D') := by
    filter_upwards [hZ, hres] with n hn hr
    exact InZ.comp hn hD' hr
  have hch := chart_lemma hπ e D hM zT hzT hZc hcont
  filter_upwards [hch, hZ, hres] with n ⟨z, hz, heq⟩ hZn hrn
  have e1 : cls F a (Dn n) * cls F a D' = (D.toSetup hπ).chartCls F a hM z := by
    rw [← cls_comp hF hZn hD' hrn, heq]
    rfl
  have e2 : cls F a Ds * cls F a D' = (D.toSetup hπ).chartCls F a hM zT := by
    rw [← cls_comp hF hDs hD' hG2, hcompT]
    rfl
  have hmem := G.mul_mem (hG z hz) (G.inv_mem (hG zT hzT))
  rw [(D.toSetup hπ).psi_apply hF hM, (D.toSetup hπ).psi_apply hF hM, ← e1, ← e2] at hmem
  have e3 : cls F a (Dn n) * cls F a D' * (clsA F a 0 (D.toSetup hπ).v0)⁻¹ *
      (cls F a Ds * cls F a D' * (clsA F a 0 (D.toSetup hπ).v0)⁻¹)⁻¹ =
      cls F a (Dn n) * (cls F a Ds)⁻¹ := by group
  rwa [e3] at hmem

end FurioLombardo.Discharge.SelmerBasis.Count
