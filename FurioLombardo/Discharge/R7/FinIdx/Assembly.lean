import Mathlib
import FurioLombardo.Discharge.R7.FinIdx.Key
import FurioLombardo.Discharge.R7.FinIdx.Pencil
import FurioLombardo.Discharge.R7.ConcreteKv
import FurioLombardo.Vendor.Toolbox.GroupTheory.FiniteIndexSeq

/-!
# `HFinIdx` for every base point over `Kv`, and `LogChartFin` for both twists (R7)

* `hFinIdx_of_setupKv`: for a `SetupKv` with `GoodSextic` model and any admissible exponent, the
  image of the ball `B1 Φ (pv⁴)` under the chart contains a subgroup of finite index of `Jac F`
  (the named hypothesis `HFinIdx` is a theorem);
* `logChartFin_fRev_uncond`: `LogChartFin` for `Jac ((fRev k).map σ)`, `k = 0, 1`, without
  hypothesis, with the explicit logarithm on the image of the ball.
-/

open Polynomial Filter Topology
open FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Vendor.Toolbox.PolyLim
open FurioLombardo.Discharge.M4Cert
open FurioLombardo.Discharge.M3a.Bruin (fRev)
open FurioLombardo.Discharge.R7.ConcreteKv

namespace FurioLombardo.Discharge.R7.FinIdx

/-- Two distinct indices in an `atTop`-eventual set. -/
theorem exists_two_of_eventually {p : ℕ → Prop} (h : ∀ᶠ n in atTop, p n) :
    ∃ n m, n ≠ m ∧ p n ∧ p m := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  exact ⟨N, N + 1, by omega, hN N le_rfl, hN (N + 1) (by omega)⟩

variable (D : SetupKv) [GoodSextic D.f] {F : Kv[X]} [GoodSextic F] {a : Kv}

/-- The chart supplies pairs over split quadratics with abscissas outside any finite set. -/
theorem hpts_chart {M : ℕ} (hM : D.toSetup.Adm M) (A : Finset Kv) :
    ∃ s1 s2 : Kv, s1 ∉ A ∧ s2 ∉ A ∧ s1 ≠ s2 ∧ s1 ≠ 0 ∧ s2 ≠ 0 ∧
      ∃ vT : Kv[X], InZ D.f ⟨![-(s1 + s2), s1 * s2], vT⟩ := by
  obtain ⟨j1, hj1⟩ := exists_sK_not_mem M A.finite_toSet
  obtain ⟨j2, hj2⟩ := exists_sK_not_mem M (A.finite_toSet.union (Set.finite_singleton (sK M j1)))
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_singleton_iff, not_or] at hj2
  refine ⟨sK M j1, sK M j2, hj1, hj2.1, Ne.symm hj2.2, sK_ne_zero M j1, sK_ne_zero M j2,
    D.toSetup.vPt hM (zPair M j1 j2), ?_⟩
  have h := inZ_chart D hM (zPair M j1 j2)
  rwa [tPt_zPair] at h

/-- **Property (T)**: every sequence of `Jac F` has two distinct terms whose quotient lies in
any subgroup `G` of `Pic F` containing the chart image of the ball. -/
theorem propT (hF : D.f.comp (X - C a) = F) {M : ℕ} (hM : D.toSetup.Adm M) (G : Subgroup (Pic F))
    (hG : ∀ z ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 (D.toSetup.fglO hM.good) (pvO ^ (3 + 1)),
      ((Additive.toMul (D.toSetup.psi hF hM z) : Jac F) : Pic F) ∈ G)
    (x : ℕ → Jac F) : ∃ n m, n ≠ m ∧ (x n : Pic F) / (x m : Pic F) ∈ G := by
  by_cases h1 : ∃ᶠ n in atTop, x n = 1
  · obtain ⟨n, hn, m, hm, hnm⟩ := (Nat.frequently_atTop_iff_infinite.mp h1).nontrivial
    refine ⟨n, m, hnm, ?_⟩
    simp only [Set.mem_ofPred_eq] at hn hm
    rw [hn, hm, OneMemClass.coe_one, div_one]
    exact G.one_mem
  obtain ⟨N, hN⟩ := eventually_atTop.mp (not_frequently.mp h1)
  have hD : ∀ k, ∃ E : MPair Kv, InZ D.f E ∧ (x (N + k) : Pic F) = cls F a E := by
    intro k
    rcases jac_eq_one_or_cls hF (x (N + k)) with h | h
    · exact absurd h (hN (N + k) (by omega))
    · exact h
  choose Dn hZ hcls using hD
  suffices hs : ∃ k k', k ≠ k' ∧ cls F a (Dn k) / cls F a (Dn k') ∈ G by
    obtain ⟨k, k', hkk, hk⟩ := hs
    refine ⟨N + k, N + k', by omega, ?_⟩
    rwa [hcls k, hcls k']
  by_cases h2 : Tendsto (fun k => dsize (Dn k)) atTop atTop
  · -- unbounded: PENCIL, then KEY at the limit
    obtain ⟨T, hT, φ, hφ, hres, ys, hys, hlim⟩ := pencil (hpts_chart D hM) hZ h2
    have hE : ∀ᶠ k in atTop, InZ D.f (comp D.f (Dn (φ k)) T) :=
      Eventually.of_forall fun k => InZ.comp (hZ _) hT (hres k)
    have hk := key D hF hM G hG hys hE hlim
    obtain ⟨k, k', hkk, hk1, hk2⟩ := exists_two_of_eventually hk
    refine ⟨φ k, φ k', hφ.injective.ne hkk, ?_⟩
    have hm := G.mul_mem hk1 (G.inv_mem hk2)
    rw [cls_comp hF (hZ _) hT (hres k), cls_comp hF (hZ _) hT (hres k')] at hm
    have e : cls F a (Dn (φ k)) * cls F a T * (cls F a ys)⁻¹ *
        (cls F a (Dn (φ k')) * cls F a T * (cls F a ys)⁻¹)⁻¹ =
        cls F a (Dn (φ k)) / cls F a (Dn (φ k')) := by
      simp only [← div_eq_mul_inv]
      rw [div_div_div_cancel_right, mul_div_mul_right_eq_div]
    rwa [e] at hm
  · -- bounded along a subsequence: extraction, then KEY at the limit
    rw [tendsto_atTop] at h2
    push Not at h2
    obtain ⟨B, hB⟩ := h2
    obtain ⟨ψ, hψ, hψB⟩ := extraction_of_frequently_atTop hB
    obtain ⟨Ds, φ, hφ, hlim⟩ := exists_subseq_dtendsto (D := Dn ∘ ψ) (fun n => (hZ _).1)
      (B := B) (fun n => (hψB n).le)
    have hZs : ∀ᶠ k in atTop, InZ D.f ((Dn ∘ ψ ∘ φ) k) := Eventually.of_forall fun k => hZ _
    have hDs : InZ D.f Ds := InZ.of_tendsto hZs hlim
    have hk := key D hF hM G hG hDs hZs hlim
    obtain ⟨k, k', hkk, hk1, hk2⟩ := exists_two_of_eventually hk
    refine ⟨ψ (φ k), ψ (φ k'), (hψ.comp hφ).injective.ne hkk, ?_⟩
    have hm := G.mul_mem hk1 (G.inv_mem hk2)
    have e : cls F a ((Dn ∘ ψ ∘ φ) k) * (cls F a Ds)⁻¹ *
        (cls F a ((Dn ∘ ψ ∘ φ) k') * (cls F a Ds)⁻¹)⁻¹ =
        cls F a (Dn (ψ (φ k))) / cls F a (Dn (ψ (φ k'))) := by
      simp only [Function.comp_apply, ← div_eq_mul_inv]
      exact div_div_div_cancel_right _ _ _
    rwa [e] at hm

/-- **Finite index of the chart ball.** -/
theorem hFinIdx_of_setupKv (D : SetupKv) [GoodSextic D.f] (F : Kv[X]) [GoodSextic F] (a : Kv)
    (hF : D.f.comp (X - C a) = F) {M : ℕ} (hM : D.toSetup.Adm M) :
    HFinIdx (D.toSetup.fglO hM.good) (D.toSetup.psi hF hM) (pvO ^ (3 + 1)) := by
  obtain ⟨L, hLbij, -, -⟩ := log_chart_OKv (D.toSetup.fglO hM.good)
  obtain ⟨H', e, -, hH'1, hH'2⟩ :=
    exists_addSubgroup_of_bijective (FurioLombardo.Vendor.Toolbox.FormalGroup.B1 (D.toSetup.fglO hM.good) (pvO ^ (3 + 1)))
      (D.toSetup.psi hF hM) (D.toSetup.psi_injective hF hM) L hLbij
  refine ⟨H', ?_, fun b hb => ?_⟩
  swap
  · obtain ⟨⟨z, hz⟩, rfl⟩ := hH'1 b hb
    exact ⟨z, hz, rfl⟩
  let G : Subgroup (Pic F) := (AddSubgroup.toSubgroup H').map (Jac F).subtype
  have hGmem : ∀ y : Additive (Jac F), ((Additive.toMul y : Jac F) : Pic F) ∈ G → y ∈ H' := by
    intro y hy
    obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp hy
    have : y' = Additive.toMul y := Subtype.ext hyy
    rw [this] at hy'
    exact hy'
  have hG : ∀ z ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 (D.toSetup.fglO hM.good) (pvO ^ (3 + 1)),
      ((Additive.toMul (D.toSetup.psi hF hM z) : Jac F) : Pic F) ∈ G :=
    fun z hz => Subgroup.mem_map_of_mem (Jac F).subtype
      (x := Additive.toMul (D.toSetup.psi hF hM z)) (hH'2 ⟨z, hz⟩).1
  refine FurioLombardo.Vendor.Toolbox.GroupTheory.finiteIndex_of_seq H' fun x => ?_
  obtain ⟨n, m, hnm, h⟩ := propT D hF hM G hG fun n => Additive.toMul (x n)
  refine ⟨n, m, hnm, hGmem _ ?_⟩
  rw [toMul_sub]
  exact h

/-- **`LogChartFin` for `Jac F_k`, `k = 0, 1`**, unconditionally, with the explicit logarithm on
the image of the ball. -/
theorem logChartFin_fRev_uncond (k : Fin 2) :
    ∃ M, ∃ hM : (baseKv k).toSetup.Adm M,
      ∃ lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2]), Analytic.LogChartFin lam ∧
        ∃ H' : AddSubgroup (Additive (Jac ((fRev k).map σ))),
          (H' : Set (Additive (Jac ((fRev k).map σ)))) = (baseKv k).toSetup.psi (hF k) hM ''
            (FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((baseKv k).toSetup.fglO hM.good) (pvO ^ (3 + 1)) :
              Set ((baseKv k).toSetup.fglO hM.good).Points) ∧
          H'.FiniteIndex ∧
          ∀ z ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((baseKv k).toSetup.fglO hM.good) (pvO ^ (3 + 1)),
            ∀ y : Fin 2 → OKv, (∀ j, (z j : OKv) = pvO ^ (3 + 1) * y j) →
              lam ((baseKv k).toSetup.psi (hF k) hM z) = H'.index • coordEquiv
                (FurioLombardo.Vendor.Toolbox.FormalGroup.logVal ((baseKv k).toSetup.fglO hM.good)
                  (unitBall Kv).subtype (pvO ^ (3 + 1)) y) := by
  obtain ⟨M, hM, h⟩ := logChartFin_fRev k
  exact ⟨M, hM, h (hFinIdx_of_setupKv (baseKv k) _ (aK k) (hF k) hM)⟩

end FurioLombardo.Discharge.R7.FinIdx
