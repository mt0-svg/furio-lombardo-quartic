import Mathlib

/-!
# Lane M3b: ranks and indices of powers in finitely generated abelian groups

Generic group theory for Chevalley's formula (Toolbox candidates). For a commutative group `A`
the rank is `Module.finrank ℤ (Additive A)`.

* `index_range_nsmul_eq`, `index_range_pow_eq`: in a finitely generated abelian group,
  `[A : A^n] = n ^ rank A * |A[n]|` for `n ≠ 0` (from the structure theorem
  `AddCommGroup.equiv_free_prod_directSum_zmod` and Mathlib's `AddSubgroup.index_range_nsmul`).
* `finrank_additive_eq_ker_add_range`: rank-nullity for homomorphisms of commutative groups.
* `finrank_additive_eq_of_sq_mem`: `H ≤ K` with `K^2 ≤ H` have the same rank.
-/

namespace FurioLombardo.M3b

open Module

section Generic

variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

theorem index_range_nsmul_congr (e : M ≃+ M') (n : ℕ) :
    (nsmulAddMonoidHom n : M' →+ M').range.index = (nsmulAddMonoidHom n : M →+ M).range.index := by
  rw [← AddSubgroup.index_map_equiv (nsmulAddMonoidHom n : M →+ M).range e,
    AddEquiv.map_range_nsmulAddMonoidHom]

theorem card_ker_nsmul_congr (e : M ≃+ M') (n : ℕ) :
    Nat.card (nsmulAddMonoidHom n : M' →+ M').ker = Nat.card (nsmulAddMonoidHom n : M →+ M).ker := by
  have h : (nsmulAddMonoidHom n : M' →+ M').ker =
      (nsmulAddMonoidHom n : M →+ M).ker.map (e : M →+ M') := by
    ext x
    simp only [AddSubgroup.mem_map, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
    constructor
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [← map_nsmul, hx, map_zero]
    · rintro ⟨y, hy, rfl⟩
      rw [← map_nsmul, hy, map_zero]
  rw [h]
  exact Nat.card_congr (e.addSubgroupMap _).toEquiv.symm

theorem index_range_nsmul_prod (n : ℕ) :
    (nsmulAddMonoidHom n : M × M' →+ M × M').range.index =
      (nsmulAddMonoidHom n : M →+ M).range.index * (nsmulAddMonoidHom n : M' →+ M').range.index := by
  have : (nsmulAddMonoidHom n : M × M' →+ M × M') =
      (nsmulAddMonoidHom n : M →+ M).prodMap (nsmulAddMonoidHom n : M' →+ M') := by
    ext <;> simp
  rw [this, AddMonoidHom.range_prodMap, AddSubgroup.index_prod]

theorem card_ker_nsmul_prod (n : ℕ) :
    Nat.card (nsmulAddMonoidHom n : M × M' →+ M × M').ker =
      Nat.card (nsmulAddMonoidHom n : M →+ M).ker * Nat.card (nsmulAddMonoidHom n : M' →+ M').ker := by
  have : (nsmulAddMonoidHom n : M × M' →+ M × M') =
      (nsmulAddMonoidHom n : M →+ M).prodMap (nsmulAddMonoidHom n : M' →+ M') := by
    ext <;> simp
  rw [this, AddMonoidHom.ker_prodMap, ← Nat.card_prod]
  exact Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv

/-- The `ℤ`-rank of `F × T` with `T` finite is the rank of `F`. -/
theorem finrank_prod_finite [Module.Finite ℤ M] [Finite M'] :
    finrank ℤ (M × M') = finrank ℤ M := by
  have : Module.Finite ℤ M' := Module.Finite.of_finite
  have hT : finrank ℤ M' = 0 := by
    rw [Module.finrank_eq_zero_iff_isTorsion]
    intro x
    refine ⟨⟨(Nat.card M' : ℤ), ?_⟩, ?_⟩
    · exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast Nat.card_pos.ne')
    · simp [natCast_zsmul]
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.ker (LinearMap.fst ℤ M M'))
  rw [(LinearMap.quotKerEquivOfSurjective _ LinearMap.fst_surjective).finrank_eq] at h
  have hN : finrank ℤ (LinearMap.ker (LinearMap.fst ℤ M M')) = 0 := by
    rw [LinearMap.ker_fst, (LinearEquiv.ofInjective _ LinearMap.inr_injective).symm.finrank_eq, hT]
  omega

/-- **Index of `n`-multiples in a finitely generated abelian group**:
`[M : nM] = n ^ rank M * |M[n]|`. -/
theorem index_range_nsmul_eq [Module.Finite ℤ M] (n : ℕ) (hn : n ≠ 0) :
    (nsmulAddMonoidHom n : M →+ M).range.index =
      n ^ finrank ℤ M * Nat.card (nsmulAddMonoidHom n : M →+ M).ker := by
  have : AddGroup.FG M := Module.Finite.iff_addGroup_fg.mp inferInstance
  obtain ⟨k, ι, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  rw [← index_range_nsmul_congr f, ← card_ker_nsmul_congr f, f.toIntLinearEquiv.finrank_eq,
    index_range_nsmul_prod, card_ker_nsmul_prod, finrank_prod_finite,
    AddSubgroup.index_range_nsmul, AddSubgroup.index_range]
  have h1 : Nat.card (nsmulAddMonoidHom n : (Fin k →₀ ℤ) →+ (Fin k →₀ ℤ)).ker = 1 := by
    rw [(AddMonoidHom.ker_eq_bot_iff _).2 (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn)]
    exact AddSubgroup.card_bot
  rw [h1, one_mul]

/-- **Index of `n`-th powers in a finitely generated abelian group**:
`[A : A^n] = n ^ rank A * |A[n]|`. -/
theorem index_range_pow_eq {A : Type*} [CommGroup A] [Module.Finite ℤ (Additive A)] (n : ℕ)
    (hn : n ≠ 0) :
    (powMonoidHom n : A →* A).range.index =
      n ^ finrank ℤ (Additive A) * Nat.card (powMonoidHom n : A →* A).ker := by
  have h1 : (powMonoidHom n : A →* A).range.index =
      (nsmulAddMonoidHom n : Additive A →+ Additive A).range.index := by
    rw [← Subgroup.index_toAddSubgroup]
    congr 1
  have h2 : Nat.card (powMonoidHom n : A →* A).ker =
      Nat.card (nsmulAddMonoidHom n : Additive A →+ Additive A).ker := by
    refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun x => ?_)
    simp only [MonoidHom.mem_ker, AddMonoidHom.mem_ker, powMonoidHom_apply,
      nsmulAddMonoidHom_apply]
    rfl
  rw [h1, h2]
  exact index_range_nsmul_eq n hn

end Generic

section Rank

variable {A B : Type*} [CommGroup A] [CommGroup B]

/-- Subgroups of a finitely generated abelian group are finitely generated. -/
theorem finite_additive_subgroup [Module.Finite ℤ (Additive A)] (H : Subgroup A) :
    Module.Finite ℤ (Additive H) :=
  Module.Finite.of_injective (MonoidHom.toAdditive H.subtype).toIntLinearMap
    (fun x y h => by
      have : ((Additive.toMul x : H) : A) = ((Additive.toMul y : H) : A) := h
      exact Additive.toMul.injective (Subtype.ext this))

/-- The image of a finitely generated abelian group is finitely generated. -/
theorem finite_additive_range [Module.Finite ℤ (Additive A)] (f : A →* B) :
    Module.Finite ℤ (Additive f.range) :=
  Module.Finite.of_surjective (MonoidHom.toAdditive f.rangeRestrict).toIntLinearMap
    (fun y => by
      obtain ⟨x, hx⟩ := f.rangeRestrict_surjective (Additive.toMul y)
      exact ⟨Additive.ofMul x, by
        change Additive.ofMul (f.rangeRestrict x) = y
        rw [hx]; rfl⟩)

/-- Isomorphic groups have the same rank. -/
theorem finrank_additive_congr (e : A ≃* B) :
    finrank ℤ (Additive A) = finrank ℤ (Additive B) :=
  (MulEquiv.toAdditive e).toIntLinearEquiv.finrank_eq

/-- A torsion group has rank zero. -/
theorem finrank_additive_eq_zero [Module.Finite ℤ (Additive A)]
    (h : ∀ a : A, ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1) : finrank ℤ (Additive A) = 0 := by
  rw [Module.finrank_eq_zero_iff_isTorsion]
  intro x
  obtain ⟨n, hn, hx⟩ := h (Additive.toMul x)
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩, ?_⟩
  change (n : ℤ) • x = 0
  rw [natCast_zsmul]
  change Additive.ofMul (Additive.toMul x ^ n) = 0
  rw [hx]; rfl

/-- **Rank-nullity** for homomorphisms of commutative groups. -/
theorem finrank_additive_eq_ker_add_range [Module.Finite ℤ (Additive A)] (f : A →* B) :
    finrank ℤ (Additive A) = finrank ℤ (Additive f.ker) + finrank ℤ (Additive f.range) := by
  set g : Additive A →ₗ[ℤ] Additive B := (MonoidHom.toAdditive f).toIntLinearMap
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.ker g)
  rw [(LinearMap.quotKerEquivRange g).finrank_eq] at h
  have eK : Additive f.ker ≃+ LinearMap.ker g :=
    { toFun := fun x => ⟨Additive.ofMul ((Additive.toMul x : f.ker) : A), (Additive.toMul x).2⟩
      invFun := fun y => Additive.ofMul ⟨Additive.toMul (y : Additive A), y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl }
  have eR : Additive f.range ≃+ LinearMap.range g :=
    { toFun := fun x => ⟨Additive.ofMul ((Additive.toMul x : f.range) : B), by
        obtain ⟨a, ha⟩ := (Additive.toMul x).2
        exact ⟨Additive.ofMul a, by
          change Additive.ofMul (f a) = _
          rw [ha]⟩⟩
      invFun := fun y => Additive.ofMul ⟨Additive.toMul (y : Additive B), by
        obtain ⟨a, ha⟩ := y.2
        exact ⟨Additive.toMul a, by
          rw [← ha]; rfl⟩⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl }
  rw [eK.toIntLinearEquiv.finrank_eq, eR.toIntLinearEquiv.finrank_eq]
  omega

/-- Equal subgroups have equal ranks. -/
theorem finrank_additive_subgroup_congr {H K : Subgroup A} (h : H = K) :
    finrank ℤ (Additive H) = finrank ℤ (Additive K) :=
  finrank_additive_congr (MulEquiv.subgroupCongr h)

/-- If `H ≤ K` and `K / H` is killed by `2`, then `H` and `K` have the same rank. -/
theorem finrank_additive_eq_of_sq_mem {H K : Subgroup A} [Module.Finite ℤ (Additive K)]
    (hHK : H ≤ K) (hsq : ∀ k ∈ K, k ^ 2 ∈ H) :
    finrank ℤ (Additive H) = finrank ℤ (Additive K) := by
  have h := finrank_additive_eq_ker_add_range (QuotientGroup.mk' (H.subgroupOf K))
  rw [QuotientGroup.ker_mk'] at h
  have := finite_additive_range (QuotientGroup.mk' (H.subgroupOf K))
  have h0 : finrank ℤ (Additive (QuotientGroup.mk' (H.subgroupOf K)).range) = 0 := by
    refine finrank_additive_eq_zero fun q => ⟨2, two_ne_zero, ?_⟩
    obtain ⟨⟨k, hk⟩, hq⟩ := q.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hq, ← map_pow, Subgroup.coe_one, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hsq k hk
  rw [h0, add_zero, finrank_additive_congr (Subgroup.subgroupOfEquivOfLe hHK)] at h
  exact h.symm

/-- A subgroup of a finitely generated subgroup is finitely generated. -/
theorem finite_additive_of_le {H K : Subgroup A} [Module.Finite ℤ (Additive K)] (hHK : H ≤ K) :
    Module.Finite ℤ (Additive H) :=
  Module.Finite.of_injective (MonoidHom.toAdditive (Subgroup.inclusion hHK)).toIntLinearMap
    (fun _ _ h => Additive.toMul.injective (Subgroup.inclusion_injective hHK h))

/-- The relative index of the `n`-th powers of a subgroup. -/
theorem relIndex_map_pow (H : Subgroup A) (n : ℕ) :
    (H.map (powMonoidHom n)).relIndex H = (powMonoidHom n : H →* H).range.index := by
  rw [Subgroup.relIndex]
  congr 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by rw [Subgroup.coe_pow]; exact hyx)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, rfl⟩

/-- In the units of a domain of characteristic not two, a subgroup containing `-1` has exactly two
elements of square one. -/
theorem card_ker_sq_eq_two {R : Type*} [CommRing R] [IsDomain R] (h2 : (2 : R) ≠ 0)
    (H : Subgroup Rˣ) (hH : -1 ∈ H) : Nat.card (powMonoidHom 2 : H →* H).ker = 2 := by
  have hne : (⟨⟨-1, hH⟩, by ext; simp [powMonoidHom_apply]⟩ : (powMonoidHom 2 : H →* H).ker) ≠ 1 := by
    intro h
    have := congrArg (fun x : (powMonoidHom 2 : H →* H).ker => (((x : H) : Rˣ) : R)) h
    simp only [Units.val_neg, Units.val_one, OneMemClass.coe_one] at this
    apply h2
    linear_combination -this
  rw [Nat.card_eq_two_iff' 1]
  refine ⟨_, hne, fun y hy => ?_⟩
  have hy2 : (((y : H) : Rˣ) : R) ^ 2 = 1 := by
    have := congrArg (fun x : H => ((x : Rˣ) : R)) y.2
    simpa [powMonoidHom_apply] using this
  rcases mul_self_eq_one_iff.1 ((pow_two _).symm.trans hy2) with h | h
  · exact absurd (Subtype.ext (Subtype.ext (Units.ext h))) hy
  · exact Subtype.ext (Subtype.ext (Units.ext (by simpa using h)))

end Rank

end FurioLombardo.M3b
