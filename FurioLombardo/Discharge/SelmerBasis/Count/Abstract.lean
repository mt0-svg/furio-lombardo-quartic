import Mathlib
import FurioLombardo.Vendor.Toolbox.GroupTheory.NsmulIndex
import FurioLombardo.Vendor.Toolbox.Padic.UnitBall

/-!
# Count lane: the abstract count and the representatives of `V / 2V`

For a group `J` with a subgroup `H` of finite index of `Additive J` and a bijective additive map
`L : H → V` onto a group `V` without `2`-torsion, `[J : J²] ≤ #(V / 2V) · #J[2]`; a homomorphism `μ` from
`J` to a group of exponent `2` then has at most that many values (`cnt_count_of_chart`). The
representatives of `V / 2V` for `V = O²`: residue field `𝔽₂` and `2 = ϖ^e u` (`cnt_reps_pow`,
`cnt_reps_two_of_pow`, `cnt_reps_pi`), `2` a unit (`cnt_reps_unit`), transport along an additive
equivalence (`cnt_reps_equiv`) and `ℤ_[2]` (`cnt_reps_padic`).
-/

set_option autoImplicit false

open FurioLombardo.Vendor.Toolbox.UnitBall

namespace FurioLombardo.Discharge.SelmerBasis.Count

theorem cnt_index_le_of_reps {V : Type*} [AddCommGroup V] (t : Finset V)
    (ht : ∀ v : V, ∃ r ∈ t, ∃ w : V, v = r + 2 • w) :
    (nsmulAddMonoidHom 2 : V →+ V).range.FiniteIndex ∧
      (nsmulAddMonoidHom 2 : V →+ V).range.index ≤ t.card := by
  classical
  set G := (nsmulAddMonoidHom 2 : V →+ V).range
  have hsurj : Function.Surjective (fun r : t => (QuotientAddGroup.mk (r : V) : V ⧸ G)) := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H v =>
      obtain ⟨r, hr, w, rfl⟩ := ht v
      refine ⟨⟨r, hr⟩, ?_⟩
      show (QuotientAddGroup.mk r : V ⧸ G) = QuotientAddGroup.mk (r + 2 • w)
      rw [QuotientAddGroup.eq]
      exact ⟨w, by simp⟩
  have : Finite (V ⧸ G) := Finite.of_surjective _ hsurj
  have hle : Nat.card (V ⧸ G) ≤ t.card :=
    (Nat.card_le_card_of_surjective _ hsurj).trans_eq (by simp)
  have hpos : Nat.card (V ⧸ G) ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, this⟩
  exact ⟨⟨hpos⟩, hle⟩

theorem cnt_exists_reps {A : Type*} [AddCommGroup A] (G : AddSubgroup A) (hG : G.FiniteIndex) :
    ∃ R : Finset A, R.card = G.index ∧ ∀ x : A, ∃ r ∈ R, x - r ∈ G := by
  classical
  have := hG
  have : Finite (A ⧸ G) := AddSubgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (A ⧸ G) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : A ⧸ G => q.out), ?_, fun x => ?_⟩
  · rw [Finset.card_image_of_injective _ (fun a b h => by
        simpa using congrArg (QuotientAddGroup.mk (s := G)) h), Finset.card_univ,
      AddSubgroup.index, Nat.card_eq_fintype_card]
  · refine ⟨(QuotientAddGroup.mk x : A ⧸ G).out, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h := QuotientAddGroup.eq.mp (Quotient.out_eq' (QuotientAddGroup.mk x : A ⧸ G))
    rw [sub_eq_neg_add]
    exact h

theorem cnt_card_ker_le {A : Type*} [AddCommGroup A] (t : Finset A)
    (ht : ∀ x : A, 2 • x = 0 → x ∈ t) :
    Nat.card (nsmulAddMonoidHom 2 : A →+ A).ker ≤ t.card := by
  classical
  have hinj : Function.Injective (fun x : (nsmulAddMonoidHom 2 : A →+ A).ker =>
      (⟨x.1, ht x.1 x.2⟩ : t)) := fun a b h => Subtype.ext (congrArg (fun z : t => (z : A)) h)
  exact (Nat.card_le_card_of_injective _ hinj).trans (by simp)

theorem cnt_index_nsmul_of_bijective {B V : Type*} [AddCommGroup B] [AddCommGroup V] (L : B →+ V)
    (hL : Function.Bijective L) (n : ℕ) :
    (nsmulAddMonoidHom n : B →+ B).range.index = (nsmulAddMonoidHom n : V →+ V).range.index := by
  have hc : (nsmulAddMonoidHom n : V →+ V).range.comap L = (nsmulAddMonoidHom n : B →+ B).range := by
    ext b
    simp only [AddSubgroup.mem_comap, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨b', rfl⟩ := hL.2 v
      exact ⟨b', hL.1 (by rw [map_nsmul, hv])⟩
    · rintro ⟨b', rfl⟩
      exact ⟨L b', by rw [map_nsmul]⟩
  rw [← hc, AddSubgroup.index_comap_of_surjective _ hL.2]

theorem cnt_inf_ker_eq_bot {A V : Type*} [AddCommGroup A] [AddCommGroup V] (H : AddSubgroup A)
    (L : H →+ V) (hL : Function.Injective L) (hV : ∀ v : V, 2 • v = 0 → v = 0) :
    H ⊓ (nsmulAddMonoidHom 2 : A →+ A).ker = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hk⟩
  have h2 : (2 • x : A) = 0 := hk
  have h0 : (2 • (⟨x, hx⟩ : H)) = 0 := Subtype.ext (by simpa using h2)
  have hL0 : L ⟨x, hx⟩ = 0 := hV _ (by rw [← map_nsmul, h0, map_zero])
  have : (⟨x, hx⟩ : H) = 0 := hL (by rw [hL0, map_zero])
  exact (AddSubgroup.mem_bot).mpr (congrArg Subtype.val this)

theorem cnt_index_two_le {A V : Type*} [AddCommGroup A] [AddCommGroup V] (H : AddSubgroup A)
    (hH : H.FiniteIndex) (L : H →+ V) (hL : Function.Bijective L)
    (hV : ∀ v : V, 2 • v = 0 → v = 0) (tV : Finset V)
    (htV : ∀ v : V, ∃ r ∈ tV, ∃ w : V, v = r + 2 • w)
    (tT : Finset A) (htT : ∀ x : A, 2 • x = 0 → x ∈ tT) :
    (nsmulAddMonoidHom 2 : A →+ A).range.FiniteIndex ∧
      (nsmulAddMonoidHom 2 : A →+ A).range.index ≤ tV.card * tT.card := by
  have := hH
  have e1 := FurioLombardo.Vendor.Toolbox.GroupTheory.index_range_nsmul_eq_relIndex_mul_card 2 H
    (cnt_inf_ker_eq_bot H L hL.1 hV)
  rw [FurioLombardo.Vendor.Toolbox.GroupTheory.relIndex_map_nsmul_eq_index, cnt_index_nsmul_of_bijective L hL 2] at e1
  obtain ⟨hfi, hle⟩ := cnt_index_le_of_reps tV htV
  have hk := cnt_card_ker_le tT htT
  have hfin : Finite (nsmulAddMonoidHom 2 : A →+ A).ker :=
    Finite.of_injective (fun x : (nsmulAddMonoidHom 2 : A →+ A).ker => (⟨x.1, htT x.1 x.2⟩ : tT))
      (fun a b h => Subtype.ext (congrArg (fun z : tT => (z : A)) h))
  have hk0 : Nat.card (nsmulAddMonoidHom 2 : A →+ A).ker ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩
  refine ⟨⟨by rw [e1]; exact mul_ne_zero hfi.index_ne_zero hk0⟩, ?_⟩
  rw [e1]
  exact Nat.mul_le_mul hle hk

theorem cnt_count_of_index {J Q : Type*} [CommGroup J] [CommGroup Q] (μ : J →* Q)
    (hQ : ∀ q : Q, q ^ 2 = 1) {N : ℕ}
    (hfi : (nsmulAddMonoidHom 2 : Additive J →+ Additive J).range.FiniteIndex)
    (hN : (nsmulAddMonoidHom 2 : Additive J →+ Additive J).range.index ≤ N) :
    ∃ s : Finset Q, (∀ x : J, μ x ∈ s) ∧ s.card ≤ N := by
  classical
  obtain ⟨R, hRc, hR⟩ := cnt_exists_reps _ hfi
  refine ⟨R.image (fun r => μ (Additive.toMul r)), fun x => ?_, ?_⟩
  · obtain ⟨r, hr, y, hy⟩ := hR (Additive.ofMul x)
    refine Finset.mem_image.mpr ⟨r, hr, ?_⟩
    have hx : Additive.ofMul x = r + 2 • y := by
      rw [show (2 • y : Additive J) = nsmulAddMonoidHom 2 y from rfl, hy]; abel
    have : x = Additive.toMul r * Additive.toMul y ^ 2 := by
      rw [← toMul_nsmul, ← toMul_add, ← hx, toMul_ofMul]
    rw [this, map_mul, map_pow, hQ, mul_one]
  · exact Finset.card_image_le.trans (hRc ▸ hN)

theorem cnt_count_of_chart {J Q V : Type*} [CommGroup J] [CommGroup Q] [AddCommGroup V]
    (μ : J →* Q) (hQ : ∀ q : Q, q ^ 2 = 1)
    (H : AddSubgroup (Additive J)) (hH : H.FiniteIndex) (L : H →+ V) (hL : Function.Bijective L)
    (hV : ∀ v : V, 2 • v = 0 → v = 0) {a b : ℕ}
    (tV : Finset V) (htV : tV.card ≤ 2 ^ a) (htV' : ∀ v : V, ∃ r ∈ tV, ∃ w : V, v = r + 2 • w)
    (tT : Finset J) (htT : tT.card ≤ 2 ^ b) (htT' : ∀ x : J, x ^ 2 = 1 → x ∈ tT) :
    ∃ s : Finset Q, (∀ x : J, μ x ∈ s) ∧ s.card ≤ 2 ^ (a + b) := by
  have htT'' : ∀ x : Additive J, 2 • x = 0 → x ∈ tT.map Additive.ofMul.toEmbedding := by
    intro x hx
    refine Finset.mem_map.mpr ⟨Additive.toMul x, htT' _ ?_, rfl⟩
    rw [← toMul_nsmul, hx, toMul_zero]
  obtain ⟨hfi, hle⟩ := cnt_index_two_le H hH L hL hV tV htV' _ htT''
  refine cnt_count_of_index μ hQ hfi (hle.trans ?_)
  rw [Finset.card_map, pow_add]
  exact Nat.mul_le_mul htV htT

theorem cnt_res_ball {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {π : K}
    (hπ : IsUniformizer π) (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) :
    ∀ x : unitBall K, (∃ y : unitBall K, x = hπ.toBall * y) ∨
      (∃ y : unitBall K, x = 1 + hπ.toBall * y) := by
  have key : ∀ z : unitBall K, ‖(z : K)‖ < 1 → ∃ y : unitBall K, z = hπ.toBall * y := by
    intro z hz
    have hm : z ∈ Ideal.span {hπ.toBall} := by
      rw [← hπ.maximalIdeal_eq]; exact mem_maximalIdeal_iff.mpr hz
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨y, by rw [← hy, mul_comm]⟩
  intro x
  rcases hres (x : K) (norm_coe_le_one x) with h | h
  · exact Or.inl (key x h)
  · obtain ⟨y, hy⟩ := key (x - 1) (by simpa using h)
    exact Or.inr ⟨y, by rw [← hy]; ring⟩

theorem cnt_reps_pow {O : Type*} [CommRing O] (ϖ : O)
    (hres : ∀ x : O, (∃ y : O, x = ϖ * y) ∨ (∃ y : O, x = 1 + ϖ * y)) (n : ℕ) :
    ∃ t : Finset O, t.card ≤ 2 ^ n ∧ ∀ x : O, ∃ r ∈ t, ∃ y : O, x = r + ϖ ^ n * y := by
  classical
  induction n with
  | zero => exact ⟨{0}, by simp, fun x => ⟨0, Finset.mem_singleton_self _, x, by ring⟩⟩
  | succ n ih =>
    obtain ⟨t, htc, ht⟩ := ih
    refine ⟨t ∪ t.image (fun r => r + ϖ ^ n), ?_, fun x => ?_⟩
    · calc (t ∪ t.image (fun r => r + ϖ ^ n)).card ≤ t.card + (t.image (fun r => r + ϖ ^ n)).card :=
            Finset.card_union_le _ _
        _ ≤ t.card + t.card := Nat.add_le_add_left Finset.card_image_le _
        _ ≤ 2 ^ (n + 1) := by rw [pow_succ]; omega
    · obtain ⟨r, hr, y, rfl⟩ := ht x
      rcases hres y with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact ⟨r, Finset.mem_union_left _ hr, z, by ring⟩
      · exact ⟨r + ϖ ^ n, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr), z, by ring⟩

theorem cnt_reps_two_of_pow {O : Type*} [CommRing O] (ϖ u : O) (e : ℕ) (hu : IsUnit u)
    (h2 : (2 : O) = ϖ ^ e * u) (t : Finset O)
    (ht : ∀ x : O, ∃ r ∈ t, ∃ y : O, x = r + ϖ ^ e * y) :
    ∀ x : O, ∃ r ∈ t, ∃ y : O, x = r + 2 • y := by
  intro x
  obtain ⟨r, hr, y, rfl⟩ := ht x
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨r, hr, v * y, ?_⟩
  rw [two_nsmul, ← two_mul, h2]
  linear_combination (-(ϖ ^ e * y)) * hv

theorem cnt_reps_pi {O : Type*} [AddCommGroup O] (m : ℕ) (t : Finset O)
    (ht : ∀ x : O, ∃ r ∈ t, ∃ y : O, x = r + 2 • y) :
    ∃ T : Finset (Fin m → O), T.card ≤ t.card ^ m ∧
      ∀ v : Fin m → O, ∃ r ∈ T, ∃ w : Fin m → O, v = r + 2 • w := by
  classical
  refine ⟨Fintype.piFinset (fun _ : Fin m => t), by simp [Fintype.card_piFinset], fun v => ?_⟩
  choose r hr y hy using fun i => ht (v i)
  refine ⟨r, Fintype.mem_piFinset.mpr hr, y, ?_⟩
  funext i
  simpa using hy i

theorem cnt_reps_unit {O : Type*} [CommRing O] (h2 : IsUnit (2 : O)) (m : ℕ) :
    ∀ v : Fin m → O, ∃ r ∈ ({0} : Finset (Fin m → O)), ∃ w : Fin m → O, v = r + 2 • w := by
  intro v
  obtain ⟨c, hc⟩ := h2.exists_left_inv
  refine ⟨0, Finset.mem_singleton_self _, fun i => c * v i, ?_⟩
  funext i
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, two_nsmul]
  linear_combination (-(v i)) * hc

theorem cnt_reps_equiv {V W : Type*} [AddCommGroup V] [AddCommGroup W] (e : V ≃+ W) (t : Finset W)
    (ht : ∀ x : W, ∃ r ∈ t, ∃ y : W, x = r + 2 • y) :
    ∃ T : Finset V, T.card ≤ t.card ∧ ∀ v : V, ∃ r ∈ T, ∃ w : V, v = r + 2 • w := by
  classical
  refine ⟨t.image e.symm, Finset.card_image_le, fun v => ?_⟩
  obtain ⟨r, hr, y, hy⟩ := ht (e v)
  refine ⟨e.symm r, Finset.mem_image_of_mem _ hr, e.symm y, ?_⟩
  apply e.injective
  rw [hy, map_add, map_nsmul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem cnt_reps_padic :
    ∃ t : Finset ℤ_[2], t.card ≤ 2 ∧ ∀ x : ℤ_[2], ∃ r ∈ t, ∃ y : ℤ_[2], x = r + 2 • y := by
  classical
  refine ⟨{0, 1}, Finset.card_le_two, fun x => ?_⟩
  obtain ⟨n, hn, hx⟩ := PadicInt.exists_mem_range (p := 2) (x := x)
  rw [PadicInt.maximalIdeal_eq_span_p] at hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hx
  refine ⟨(n : ℤ_[2]), ?_, y, ?_⟩
  · interval_cases n <;> simp
  · rw [two_nsmul, ← two_mul]
    push_cast at hy ⊢
    linear_combination -hy

end FurioLombardo.Discharge.SelmerBasis.Count
