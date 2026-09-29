import FurioLombardo.M1.Vendor.Stoll.SelmerGroup

/-!
# The Selmer group K(S,2) of a number field with odd class number

For a number field `F` with `Cl(F)[2] = 0` and a finite set `S` of primes:

* `card_selmerGroup_two_le`: `#K(S,2) ≤ 2 ^ (rank F + #S + 1)`. The class group of the
  `S`-integers is a quotient of `Cl(F)` (`SInteger.extendedHom_surjective`), so it has no
  2-torsion; the exact sequence `O_S^× / 2 → K(S,2) → Cl(O_S)[2]` (`ker_toSClassGroup`,
  `range_toSClassGroup`) and Dirichlet's S-unit theorem (`finrank_sUnit_of_numberField`,
  `CommGroup.card_modPow`) bound the order.
* `mk_mem_selmerGroup_two`: a criterion for membership in `K(S,2)`: at every prime `v ∉ S`,
  `u a = b ^ 2` with `a` integral and prime to `v`.
* `exists_isSquare_mul_prod`: if `m ≥ rank F + #S + 1` elements of `K(S,2)` are independent
  (no nonempty subproduct is a square), every element of `K(S,2)` is one of their subproducts
  modulo squares.
-/

namespace FurioLombardo.M1

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F]

/-- The square class group `F^× / F^×2`. -/
abbrev SqClass (F : Type*) [Field F] := Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range

/-- The subproduct of `g` selected by `e`. -/
def subprod {M : Type*} [CommMonoid M] {m : ℕ} (g : Fin m → M) (e : Fin m → Bool) : M :=
  ∏ i, if e i then g i else 1

/-- In a finite commutative group without 2-torsion, squaring is bijective; this passes to
quotients. -/
theorem sq_eq_one_of_surjective {G H : Type*} [CommGroup G] [CommGroup H] [Finite G] [Finite H]
    (φ : G →* H) (hφ : Function.Surjective φ) (hG : ∀ c : G, c ^ 2 = 1 → c = 1) (c : H)
    (hc : c ^ 2 = 1) : c = 1 := by
  have hinjG : Function.Injective (fun c : G => c ^ 2) := by
    intro a b hab
    have : (a * b⁻¹) ^ 2 = 1 := by
      simp only at hab; rw [mul_pow, hab, inv_pow, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hG _ this)
  have hsurjG : Function.Surjective (fun c : G => c ^ 2) := Finite.surjective_of_injective hinjG
  have hsurjH : Function.Surjective (fun c : H => c ^ 2) := by
    intro c
    obtain ⟨d, rfl⟩ := hφ c
    obtain ⟨e, rfl⟩ := hsurjG d
    exact ⟨φ e, by simp [map_pow]⟩
  have hinjH : Function.Injective (fun c : H => c ^ 2) := Finite.injective_iff_surjective.mpr hsurjH
  exact hinjH (by simp only; rw [hc, one_pow])

/-- **Selmer bound.** -/
theorem card_selmerGroup_two_le (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hCl : ∀ c : ClassGroup (𝓞 F), c ^ 2 = 1 → c = 1) :
    Nat.card (selmerGroup (K := F) (S := S) (n := 2)) ≤ 2 ^ (Units.rank F + S.ncard + 1) := by
  -- the class group of the S-integers has no 2-torsion
  have hClS : ∀ c : ClassGroup (S.integer F), c ^ 2 = 1 → c = 1 :=
    sq_eq_one_of_surjective (ClassGroup.extendedHom (𝓞 F) (S.integer F))
      (SInteger.extendedHom_surjective F S) hCl
  -- every Selmer class comes from an S-unit
  have hsurj : Function.Surjective (sUnitToSelmer F S 2) := by
    intro x
    have hx : x ∈ (sUnitToSelmer F S 2).range := by
      rw [← ker_toSClassGroup, MonoidHom.mem_ker]
      have hr : toSClassGroup F S 2 x ∈ (toSClassGroup F S 2).range := ⟨x, rfl⟩
      rw [range_toSClassGroup, MonoidHom.mem_ker, powMonoidHom_apply] at hr
      exact hClS _ hr
    exact hx
  have hfg := fg_sUnit F S hS
  have : Finite (S.unit F ⧸ (powMonoidHom 2 : S.unit F →* S.unit F).range) :=
    CommGroup.finite_modPow 2
  have hle : Nat.card (selmerGroup (K := F) (S := S) (n := 2)) ≤
      Nat.card (S.unit F ⧸ (powMonoidHom 2 : S.unit F →* S.unit F).range) := by
    refine Nat.card_le_card_of_surjective (sUnitModPowToSelmer F S 2) fun x ↦ ?_
    obtain ⟨u, hu⟩ := hsurj x
    exact ⟨QuotientGroup.mk u, hu⟩
  refine hle.trans ?_
  rw [CommGroup.card_modPow _ two_ne_zero, finrank_sUnit_of_numberField F S hS]
  -- the 2-torsion of the S-units injects into that of F^×, which has order 2
  have hker : Nat.card (powMonoidHom 2 : S.unit F →* S.unit F).ker ≤ 2 := by
    have h2 : ringChar F ≠ 2 := by rw [ringChar.eq F 0]; norm_num
    have : Finite (powMonoidHom 2 : Fˣ →* Fˣ).ker :=
      Nat.finite_of_card_ne_zero (by rw [Units.card_ker_powMonoidHom_two F h2]; norm_num)
    let ι : (powMonoidHom 2 : S.unit F →* S.unit F).ker → (powMonoidHom 2 : Fˣ →* Fˣ).ker :=
      fun x => ⟨((x : S.unit F) : Fˣ), by
        have hx := x.2
        rw [MonoidHom.mem_ker, powMonoidHom_apply] at hx ⊢
        exact congrArg Subtype.val hx⟩
    have hι : Function.Injective ι := by
      intro x y hxy
      apply Subtype.ext; apply Subtype.ext
      have h := congrArg Subtype.val hxy
      exact h
    exact (Nat.card_le_card_of_injective ι hι).trans_eq (Units.card_ker_powMonoidHom_two F h2)
  calc 2 ^ (Units.rank F + S.ncard) * Nat.card (powMonoidHom 2 : S.unit F →* S.unit F).ker
      ≤ 2 ^ (Units.rank F + S.ncard) * 2 := Nat.mul_le_mul_left _ hker
    _ = 2 ^ (Units.rank F + S.ncard + 1) := by rw [pow_succ]

/-- **Membership criterion for `K(S,2)`.** -/
theorem mk_mem_selmerGroup_two (S : Set (HeightOneSpectrum (𝓞 F))) (u : Fˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ∃ a b : 𝓞 F, a ∉ v.asIdeal ∧ (u : F) * (a : F) = (b : F) ^ 2) :
    (QuotientGroup.mk u : SqClass F) ∈ selmerGroup (K := F) (S := S) (n := 2) := by
  intro v hv
  obtain ⟨a, b, ha, hab⟩ := h v hv
  have hb0 : (b : F) ≠ 0 := by
    intro hb
    rw [hb, zero_pow two_ne_zero, mul_eq_zero] at hab
    rcases hab with h0 | h0
    · exact u.ne_zero h0
    · apply ha
      have : a = 0 := by exact_mod_cast h0
      rw [this]; exact v.asIdeal.zero_mem
  rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
  refine HeightOneSpectrum.dvd_toAdd_valuationOfNeZero v (z := Units.mk0 _ hb0) ?_
  have hva : v.valuation F (a : F) = 1 := by
    have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (v := v) (r := a)).mpr ha
    exact this
  have := congrArg (v.valuation F) hab
  rw [map_mul, hva, mul_one, map_pow] at this
  simpa using this

/-- An injective map from `Fin m → Bool` into a finite subgroup of order at most `2 ^ m` hits
every element. -/
theorem exists_eq_of_injective {G : Type*} [Group G] (H : Subgroup G) {m : ℕ}
    (hfin : Finite H) (hcard : Nat.card H ≤ 2 ^ m) (φ : (Fin m → Bool) → G) (hφ : ∀ e, φ e ∈ H)
    (hinj : Function.Injective φ) (x : G) (hx : x ∈ H) : ∃ e, φ e = x := by
  let ψ : (Fin m → Bool) → H := fun e => ⟨φ e, hφ e⟩
  have hψ_inj : Function.Injective ψ := fun e e' h => hinj (congrArg Subtype.val h)
  have : Fintype H := Fintype.ofFinite H
  have hcard_eq : Fintype.card (Fin m → Bool) = Fintype.card H := by
    refine le_antisymm (Fintype.card_le_of_injective ψ hψ_inj) ?_
    rw [← Nat.card_eq_fintype_card]
    simpa [Fintype.card_bool, Fintype.card_fin] using hcard
  have hψ_surj : Function.Surjective ψ :=
    ((Fintype.bijective_iff_injective_and_card ψ).mpr ⟨hψ_inj, hcard_eq⟩).surjective
  obtain ⟨e, he⟩ := hψ_surj ⟨x, hx⟩
  exact ⟨e, congrArg Subtype.val he⟩

theorem subprod_map {M N : Type*} [CommMonoid M] [CommMonoid N] (f : M →* N) {m : ℕ}
    (g : Fin m → M) (e : Fin m → Bool) : f (subprod g e) = subprod (fun i => f (g i)) e := by
  simp only [subprod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  split <;> simp

/-- The product of two subproducts is the subproduct of the symmetric difference times a
square. -/
theorem subprod_mul_subprod {M : Type*} [CommMonoid M] {m : ℕ} (g : Fin m → M)
    (e e' : Fin m → Bool) :
    subprod g e * subprod g e' =
      subprod g (fun i => xor (e i) (e' i)) * (subprod g (fun i => e i && e' i)) ^ 2 := by
  simp only [subprod, ← Finset.prod_mul_distrib, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h1 : e i <;> by_cases h2 : e' i <;> simp [h1, h2, sq]

/-- Two units have the same square class iff their quotient is a square. -/
theorem sqClass_mk_eq_mk_iff (a b : Fˣ) :
    (QuotientGroup.mk a : SqClass F) = QuotientGroup.mk b ↔ ∃ y : Fˣ, (b : F) = a * y ^ 2 := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have : (b : F) = a * ((a⁻¹ * b : Fˣ) : F) := by simp
    rw [this, ← hy]; simp
  · rintro ⟨y, hy⟩
    refine ⟨y, Units.ext ?_⟩
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, hy]
    field_simp [a.ne_zero]
    exact (Units.inv_mul a).symm

/-- **Spanning from independence.** -/
theorem exists_isSquare_mul_prod (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hCl : ∀ c : ClassGroup (𝓞 F), c ^ 2 = 1 → c = 1) {m : ℕ}
    (hm : Units.rank F + S.ncard + 1 ≤ m) (g : Fin m → Fˣ)
    (hg : ∀ i, (QuotientGroup.mk (g i) : SqClass F) ∈ selmerGroup (K := F) (S := S) (n := 2))
    (hind : ∀ e : Fin m → Bool, IsSquare (subprod (fun i => (g i : F)) e) → ∀ i, e i = false)
    (u : Fˣ) (hu : (QuotientGroup.mk u : SqClass F) ∈ selmerGroup (K := F) (S := S) (n := 2)) :
    ∃ e : Fin m → Bool, IsSquare ((u : F) * subprod (fun i => (g i : F)) e) := by
  have hfin : Finite (selmerGroup (K := F) (S := S) (n := 2)) :=
    finite_selmerGroup_of_numberField F S 2 hS
  have hcard : Nat.card (selmerGroup (K := F) (S := S) (n := 2)) ≤ 2 ^ m :=
    (card_selmerGroup_two_le S hS hCl).trans (Nat.pow_le_pow_right (by norm_num) hm)
  have hcoe : ∀ e, ((subprod g e : Fˣ) : F) = subprod (fun i => (g i : F)) e := fun e =>
    subprod_map (Units.coeHom F) g e
  -- the preimage of the Selmer group in `Fˣ`
  let H' : Subgroup Fˣ := (selmerGroup (K := F) (S := S) (n := 2)).comap (QuotientGroup.mk' _)
  have hmem : ∀ e, subprod g e ∈ H' := fun e =>
    Subgroup.prod_mem H' fun i _ => by
      split
      · exact hg i
      · exact H'.one_mem
  let φ : (Fin m → Bool) → SqClass F := fun e => QuotientGroup.mk (subprod g e)
  have hinj : Function.Injective φ := by
    intro e e' hee
    obtain ⟨y, hy⟩ := (sqClass_mk_eq_mk_iff (subprod g e) (subprod g e')).mp hee
    have hx := congrArg (fun w : Fˣ => (w : F)) (subprod_mul_subprod g e e')
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hx
    have hC : ((subprod g (fun i => e i && e' i) : Fˣ) : F) ≠ 0 := Units.ne_zero _
    have h2 : IsSquare ((subprod g (fun i => xor (e i) (e' i)) : Fˣ) : F) := by
      rw [hy] at hx
      generalize ((subprod g (fun i => xor (e i) (e' i)) : Fˣ) : F) = X at hx ⊢
      generalize ((subprod g (fun i => e i && e' i) : Fˣ) : F) = C at hx hC ⊢
      generalize ((subprod g e : Fˣ) : F) = A at hx ⊢
      refine ⟨A * y / C, ?_⟩
      field_simp
      linear_combination -hx
    rw [hcoe] at h2
    have h3 := hind _ h2
    funext i
    have h4 := h3 i
    by_cases he : e i <;> by_cases he' : e' i <;> simp only [he, he'] at h4 ⊢ <;> simp at h4
  obtain ⟨e, he⟩ := exists_eq_of_injective (m := m) (selmerGroup (K := F) (S := S) (n := 2))
    hfin hcard φ (fun e => hmem e) hinj (QuotientGroup.mk u⁻¹)
    (Subgroup.inv_mem _ hu)
  refine ⟨e, ?_⟩
  obtain ⟨y, hy⟩ := (sqClass_mk_eq_mk_iff (subprod g e) u⁻¹).mp he
  rw [← hcoe]
  refine ⟨y⁻¹, ?_⟩
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  have hy0 : (y : F) ≠ 0 := y.ne_zero
  simp only [Units.val_inv_eq_inv_val] at hy ⊢
  have hA : ((subprod g e : Fˣ) : F) = (u : F)⁻¹ / (y : F) ^ 2 := by
    field_simp at hy ⊢; linear_combination -hy
  rw [hA]; field_simp

end FurioLombardo.M1
