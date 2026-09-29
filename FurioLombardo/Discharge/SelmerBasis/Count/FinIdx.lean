import Mathlib
import FurioLombardo.Discharge.SelmerBasis.Count.Key
import FurioLombardo.Discharge.R7.FinIdx.Pencil
import FurioLombardo.Vendor.Toolbox.GroupTheory.FiniteIndexSeq

/-!
# Count lane: finite index of the chart ball over a local field

The port of R7's `hFinIdx_of_setupKv` (R7/FinIdx/Assembly.lean) from `M4Cert.Kv` to any complete,
proper, ultrametric, nontrivially normed field `K` of characteristic zero with a uniformizer `π`
and a prime `p` with `p = π ^ e u` (`u` a unit of the ball):

* `propT`: every sequence of `Jac F` has two distinct terms whose quotient lies in any subgroup
  containing the chart image of the ball `B1 Φ (π ^ (e + 1))`;
* `exists_finiteIndex_chart`: that image is a subgroup `H` of finite index of `Additive (Jac F)`,
  with an additive bijection `H → (unitBall K)²` (the scaled logarithm).
-/

set_option autoImplicit false

open Polynomial Filter Topology
open FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Vendor.Toolbox.PolyLim
open FurioLombardo.Discharge.R7 FurioLombardo.Discharge.R7.FinIdx

namespace FurioLombardo.Discharge.SelmerBasis.Count

/-- The image under an injective `ψ` of a submonoid `S` carrying an additive bijection `L` onto a
group is a subgroup `H`, with an additive bijection `e : H → V` transporting `L` (copy of R7's
`exists_addSubgroup_of_bijective`, LogChart.lean, which imports `M4Cert.Kv`). -/
theorem exists_addSubgroup_of_bijective {M G V : Type*} [AddCommMonoid M] [AddCommGroup G]
    [AddCommGroup V] (S : AddSubmonoid M) (ψ : M →+ G) (hψ : Function.Injective ψ)
    (L : S →+ V) (hL : Function.Bijective L) :
    ∃ (H : AddSubgroup G) (e : H →+ V), Function.Bijective e ∧
      (∀ g ∈ H, ∃ z : S, ψ z = g) ∧ ∀ z : S, ∃ h : ψ z ∈ H, e ⟨ψ z, h⟩ = L z := by
  have hL_inj : Function.Injective L := hL.injective
  have hL_surj : Function.Surjective L := hL.surjective
  have h_neg : ∀ z : S, ∃ z' : S, z + z' = 0 := by
    intro z
    obtain ⟨z', hz'⟩ := hL_surj (-L z)
    refine ⟨z', ?_⟩
    apply hL_inj
    simp [hz']
  let H : AddSubgroup G :=
    { carrier := Set.image ψ (S : Set M)
      zero_mem' := by
        refine ⟨0, S.zero_mem, ?_⟩
        simp
      add_mem' := by
        rintro a b ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
        refine ⟨z + w, S.add_mem hz hw, ?_⟩
        simp
      neg_mem' := by
        rintro a ⟨z, hz, rfl⟩
        obtain ⟨z', hz'⟩ := h_neg ⟨z, hz⟩
        refine ⟨z', z'.2, ?_⟩
        have h_eq : ψ z + ψ (z' : M) = 0 := by
          have h := congrArg (λ (x : S) => ψ (x : M)) hz'
          simpa [map_add, map_zero] using h
        calc
          ψ (z' : M) = (ψ z + ψ (z' : M)) - ψ z := by abel
          _ = 0 - ψ z := by rw [h_eq]
          _ = -ψ z := by simp
    }
  let j : S →+ H :=
    { toFun := λ z => Subtype.mk (ψ z) ⟨z, z.2, rfl⟩
      map_add' := by
        intro x y
        ext
        simp
      map_zero' := by
        ext
        simp
    }
  have hj_inj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply hψ
    have hval := congrArg (λ (t : H) => (t : G)) h
    simpa [j] using hval
  have hj_surj : Function.Surjective j := by
    intro h
    have hmem : (h : G) ∈ (H : Set G) := h.property
    rcases hmem with ⟨z, hz, hz_eq⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    simpa [j] using hz_eq
  have hj_bijective : Function.Bijective j := ⟨hj_inj, hj_surj⟩
  let j_equiv : S ≃+ H := AddEquiv.ofBijective j hj_bijective
  let e : H →+ V := L.comp j_equiv.symm.toAddMonoidHom
  have he_bijective : Function.Bijective e := by
    have h_symm_bijective : Function.Bijective j_equiv.symm :=
      ⟨j_equiv.symm.injective, j_equiv.symm.surjective⟩
    simpa [e] using Function.Bijective.comp hL h_symm_bijective
  have h_forall_g : ∀ g ∈ H, ∃ z : S, ψ z = g := by
    intro g hg
    rcases hg with ⟨z, hz, hz_eq⟩
    exact ⟨⟨z, hz⟩, hz_eq⟩
  have h_forall_z : ∀ z : S, ∃ h : ψ z ∈ H, e ⟨ψ z, h⟩ = L z := by
    intro z
    have hmem : ψ (z : M) ∈ (H : Set G) := by
      refine ⟨z, z.2, rfl⟩
    have h_j_symm : j_equiv.symm ⟨ψ z, hmem⟩ = z := by
      apply j_equiv.injective
      rw [AddEquiv.apply_symm_apply]
      dsimp [j_equiv, j]
      apply Subtype.ext
      rfl
    refine ⟨hmem, ?_⟩
    calc
      e ⟨ψ z, hmem⟩ = (L.comp j_equiv.symm.toAddMonoidHom) ⟨ψ z, hmem⟩ := rfl
      _ = L (j_equiv.symm ⟨ψ z, hmem⟩) := rfl
      _ = L z := by rw [h_j_symm]
  exact ⟨H, e, he_bijective, h_forall_g, h_forall_z⟩

/-- Two distinct indices in an `atTop`-eventual set. -/
theorem exists_two_of_eventually {p : ℕ → Prop} (h : ∀ᶠ n in atTop, p n) :
    ∃ n m, n ≠ m ∧ p n ∧ p m := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  exact ⟨N, N + 1, by omega, hN N le_rfl, hN (N + 1) (by omega)⟩

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ProperSpace K] [CharZero K] [HasUniformizer K] {π : K} (hπ : IsUniformizer π) (e : ℕ)
  (D : LSetup K) [GoodSextic D.f] {F : K[X]} [GoodSextic F] {a : K}

include e in
/-- The chart supplies pairs over split quadratics with abscissas outside any finite set. -/
theorem hpts_chart {M : ℕ} (hM : (D.toSetup hπ).Adm M) (A : Finset K) :
    ∃ s1 s2 : K, s1 ∉ A ∧ s2 ∉ A ∧ s1 ≠ s2 ∧ s1 ≠ 0 ∧ s2 ≠ 0 ∧
      ∃ vT : K[X], InZ D.f ⟨![-(s1 + s2), s1 * s2], vT⟩ := by
  obtain ⟨j1, hj1⟩ := exists_sK_not_mem hπ e M A.finite_toSet
  obtain ⟨j2, hj2⟩ := exists_sK_not_mem hπ e M (A.finite_toSet.union (Set.finite_singleton (sK π e M j1)))
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_singleton_iff, not_or] at hj2
  refine ⟨sK π e M j1, sK π e M j2, hj1, hj2.1, Ne.symm hj2.2, sK_ne_zero hπ e M j1, sK_ne_zero hπ e M j2,
    (D.toSetup hπ).vPt hM (zPair hπ e M j1 j2), ?_⟩
  have h := inZ_chart hπ D hM (zPair hπ e M j1 j2)
  rwa [tPt_zPair hπ e D M] at h

/-- **Property (T)**: every sequence of `Jac F` has two distinct terms whose quotient lies in
any subgroup `G` of `Pic F` containing the chart image of the ball. -/
theorem propT (hF : D.f.comp (X - C a) = F) {M : ℕ} (hM : (D.toSetup hπ).Adm M) (G : Subgroup (Pic F))
    (hG : ∀ z ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((D.toSetup hπ).fglO hM.good) (hπ.toBall ^ (e + 1)),
      ((Additive.toMul ((D.toSetup hπ).psi hF hM z) : Jac F) : Pic F) ∈ G)
    (x : ℕ → Jac F) : ∃ n m, n ≠ m ∧ (x n : Pic F) / (x m : Pic F) ∈ G := by
  by_cases h1 : ∃ᶠ n in atTop, x n = 1
  · obtain ⟨n, hn, m, hm, hnm⟩ := (Nat.frequently_atTop_iff_infinite.mp h1).nontrivial
    refine ⟨n, m, hnm, ?_⟩
    simp only [Set.mem_ofPred_eq] at hn hm
    rw [hn, hm, OneMemClass.coe_one, div_one]
    exact G.one_mem
  obtain ⟨N, hN⟩ := eventually_atTop.mp (not_frequently.mp h1)
  have hD : ∀ k, ∃ E : MPair K, InZ D.f E ∧ (x (N + k) : Pic F) = cls F a E := by
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
    obtain ⟨T, hT, φ, hφ, hres, ys, hys, hlim⟩ := pencil (hpts_chart hπ e D hM) hZ h2
    have hE : ∀ᶠ k in atTop, InZ D.f (comp D.f (Dn (φ k)) T) :=
      Eventually.of_forall fun k => InZ.comp (hZ _) hT (hres k)
    have hk := key hπ e D hF hM G hG hys hE hlim
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
    have hk := key hπ e D hF hM G hG hDs hZs hlim
    obtain ⟨k, k', hkk, hk1, hk2⟩ := exists_two_of_eventually hk
    refine ⟨ψ (φ k), ψ (φ k'), (hψ.comp hφ).injective.ne hkk, ?_⟩
    have hm := G.mul_mem hk1 (G.inv_mem hk2)
    have e : cls F a ((Dn ∘ ψ ∘ φ) k) * (cls F a Ds)⁻¹ *
        (cls F a ((Dn ∘ ψ ∘ φ) k') * (cls F a Ds)⁻¹)⁻¹ =
        cls F a (Dn (ψ (φ k))) / cls F a (Dn (ψ (φ k'))) := by
      simp only [Function.comp_apply, ← div_eq_mul_inv]
      exact div_div_div_cancel_right _ _ _
    rwa [e] at hm

/-- **Finite index of the chart ball** over `K`: the chart image of `B1 Φ (π ^ (e + 1))` is a
subgroup of finite index of `Additive (Jac F)`, additively in bijection with `(unitBall K)²`. -/
theorem exists_finiteIndex_chart (hF : D.f.comp (X - C a) = F) {M : ℕ}
    (hM : (D.toSetup hπ).Adm M) {p : ℕ} (hp : p.Prime)
    (hpm : (p : unitBall K) ∈ IsLocalRing.maximalIdeal (unitBall K)) {u : unitBall K}
    (hu : IsUnit u) (hpe : (p : unitBall K) = hπ.toBall ^ e * u) :
    ∃ (H : AddSubgroup (Additive (Jac F))) (L : H →+ (Fin 2 → unitBall K)),
      Function.Bijective L ∧ H.FiniteIndex := by
  obtain ⟨L, hLbij, -, -⟩ := FurioLombardo.Vendor.Toolbox.FormalGroup.log_chart_uniformizer hp hpm
    hπ.maximalIdeal_eq hπ.toBall_ne_zero hu hpe subtype_injective ((D.toSetup hπ).fglO hM.good)
  obtain ⟨H', e', he', hH'1, hH'2⟩ :=
    exists_addSubgroup_of_bijective
      (FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((D.toSetup hπ).fglO hM.good) (hπ.toBall ^ (e + 1)))
      ((D.toSetup hπ).psi hF hM) ((D.toSetup hπ).psi_injective hF hM) L hLbij
  refine ⟨H', e', he', ?_⟩
  let G : Subgroup (Pic F) := (AddSubgroup.toSubgroup H').map (Jac F).subtype
  have hGmem : ∀ y : Additive (Jac F), ((Additive.toMul y : Jac F) : Pic F) ∈ G → y ∈ H' := by
    intro y hy
    obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp hy
    have : y' = Additive.toMul y := Subtype.ext hyy
    rw [this] at hy'
    exact hy'
  have hG : ∀ z ∈ FurioLombardo.Vendor.Toolbox.FormalGroup.B1 ((D.toSetup hπ).fglO hM.good) (hπ.toBall ^ (e + 1)),
      ((Additive.toMul ((D.toSetup hπ).psi hF hM z) : Jac F) : Pic F) ∈ G :=
    fun z hz => Subgroup.mem_map_of_mem (Jac F).subtype
      (x := Additive.toMul ((D.toSetup hπ).psi hF hM z)) (hH'2 ⟨z, hz⟩).1
  refine FurioLombardo.Vendor.Toolbox.GroupTheory.finiteIndex_of_seq H' fun x => ?_
  obtain ⟨n, m, hnm, h⟩ := propT hπ e D hF hM G hG fun n => Additive.toMul (x n)
  refine ⟨n, m, hnm, hGmem _ ?_⟩
  rw [toMul_sub]
  exact h

end FurioLombardo.Discharge.SelmerBasis.Count
