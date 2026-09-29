import Mathlib

/-!
# The index of `2B` from a torsion-free subgroup of finite index

For an abelian group `B` with a subgroup `B1` of finite index without 2-torsion,
`[B : 2B] = [B1 : 2B1] · #B[2]` (`index_twoB_eq`). For `B = A(k_v)` and `B1` the points of the formal group with
coordinates in `4 O_v`, `B1 ≅ O_v²` gives `[B1 : 2B1] = 2^6` (`relIndex_two_of_embedding`: any subgroup `M` of
`V = Fin 6 → ℤ_[2]` of finite index has `[M : 2M] = [V : 2V] = 2^6`), so `[A(k_v) : 2A(k_v)] = 2^6 · #A(k_v)[2]`,
the count behind "the seven local points `D_i` are a basis of `A(k_v)/2A(k_v)`".
-/

namespace FurioLombardo.Discharge.Analytic

open AddSubgroup

section General

variable {B : Type*} [AddCommGroup B]

/-- Doubling `b ↦ 2 b`. -/
abbrev dbl (B : Type*) [AddCommGroup B] : B →+ B := nsmulAddMonoidHom 2

/-- `2B`, the image of doubling. -/
abbrev twoB (B : Type*) [AddCommGroup B] : AddSubgroup B := (dbl B).range

/-- `B[2]`, the kernel of doubling. -/
abbrev tors2 (B : Type*) [AddCommGroup B] : AddSubgroup B := (dbl B).ker

theorem mem_tors2 {b : B} : b ∈ tors2 B ↔ (2 : ℕ) • b = 0 := Iff.rfl

theorem mem_twoB {b : B} : b ∈ twoB B ↔ ∃ c : B, (2 : ℕ) • c = b := Iff.rfl

/-- The preimage under doubling of `2 B1` is `B1 + B[2]`. -/
theorem comap_dbl_map_dbl (B1 : AddSubgroup B) : (B1.map (dbl B)).comap (dbl B) = B1 ⊔ tors2 B := by
  ext b
  constructor
  · rintro ⟨b1, hb1, h⟩
    have h' : (2 : ℕ) • b1 = (2 : ℕ) • b := h
    have hk : b - b1 ∈ tors2 B := by
      rw [mem_tors2, nsmul_sub, h', sub_self]
    have : b = b1 + (b - b1) := by abel
    rw [this]
    exact add_mem_sup hb1 hk
  · intro hb
    have h1 : B1 ≤ (B1.map (dbl B)).comap (dbl B) := fun x hx => ⟨x, hx, rfl⟩
    have h2 : tors2 B ≤ (B1.map (dbl B)).comap (dbl B) := by
      intro x hx
      refine ⟨0, B1.zero_mem, ?_⟩
      have : (2 : ℕ) • x = 0 := hx
      simp only [map_zero]
      exact this.symm
    exact (sup_le h1 h2) hb

/-- **The index of `2B`.** If `B1 ≤ B` has finite index and no 2-torsion, `[B : 2B] = [B1 : 2B1] · #B[2]`. -/
theorem index_twoB_eq (B1 : AddSubgroup B) [hfi : B1.FiniteIndex] (hB1 : B1 ⊓ tors2 B = ⊥) :
    (twoB B).index = (B1.map (dbl B)).relIndex B1 * Nat.card (tors2 B) := by
  set H1 := B1.map (dbl B) with hH1def
  set K := tors2 B with hKdef
  have hH1B1 : H1 ≤ B1 := by
    rintro _ ⟨b, hb, rfl⟩
    exact B1.nsmul_mem hb 2
  have hH1H : H1 ≤ twoB B := by
    rintro _ ⟨b, -, rfl⟩
    exact ⟨b, rfl⟩
  have e1 := relIndex_mul_index hH1B1
  have e2 := relIndex_mul_index hH1H
  have e5 : H1.relIndex (twoB B) = (B1 ⊔ K).index := by
    rw [← comap_dbl_map_dbl, ← relIndex_top_right, relIndex_comap, ← AddMonoidHom.range_eq_map]
  have e3 := relIndex_mul_index (le_sup_left : B1 ≤ B1 ⊔ K)
  have e8 : B1.relIndex (B1 ⊔ K) = Nat.card K := by
    rw [relIndex_sup_left, ← inf_relIndex_right, hB1, relIndex_bot_left]
  have hi : B1.index ≠ 0 := hfi.index_ne_zero
  have hj : (B1 ⊔ K).index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e3
    exact hi e3.symm
  rw [e5] at e2
  rw [e8] at e3
  -- a · i = j · x and t · j = i give x = a · t
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hj)
  calc (B1 ⊔ K).index * (twoB B).index = H1.index := e2
    _ = H1.relIndex B1 * B1.index := e1.symm
    _ = H1.relIndex B1 * (Nat.card K * (B1 ⊔ K).index) := by rw [e3]
    _ = (B1 ⊔ K).index * (H1.relIndex B1 * Nat.card K) := by ring

/-- For a subgroup `M` of finite index of a group `V` on which doubling is injective, `[M : 2M] = [V : 2V]`. -/
theorem relIndex_two_eq_index_twoB {V : Type*} [AddCommGroup V] (hinj : Function.Injective (dbl V))
    (M : AddSubgroup V) [hfi : M.FiniteIndex] : (M.map (dbl V)).relIndex M = (twoB V).index := by
  have hle : M.map (dbl V) ≤ M := by
    rintro _ ⟨b, hb, rfl⟩
    exact M.nsmul_mem hb 2
  have hle2 : M.map (dbl V) ≤ twoB V := by
    rintro _ ⟨b, -, rfl⟩
    exact ⟨b, rfl⟩
  have e1 := relIndex_mul_index hle
  have e2 := relIndex_mul_index hle2
  have e3 : (M.map (dbl V)).relIndex (twoB V) = M.index := by
    show (M.map (dbl V)).relIndex (dbl V).range = M.index
    rw [AddMonoidHom.range_eq_map, relIndex_map_map_of_injective _ _ hinj, relIndex_top_right]
  rw [e3] at e2
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfi.index_ne_zero)
  rw [e1, ← e2, mul_comm]

/-- `[B1 : 2B1]`, computed in `B`, is the index of `2 B1` in the group `B1`. -/
theorem relIndex_map_dbl_eq (B1 : AddSubgroup B) : (B1.map (dbl B)).relIndex B1 = (twoB B1).index := by
  unfold relIndex
  congr 1
  ext x
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    simpa using h
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2, by simp⟩

/-- `[B1 : 2B1]` is invariant under a homomorphism injective on `B1`: it equals `[g(B1) : 2 g(B1)]`. -/
theorem relIndex_two_map {V : Type*} [AddCommGroup V] (g : B →+ V) (B1 : AddSubgroup B)
    (hg : ∀ b ∈ B1, g b = 0 → b = 0) :
    (B1.map (dbl B)).relIndex B1 = ((B1.map g).map (dbl V)).relIndex (B1.map g) := by
  set g1 : B1 →+ V := g.comp B1.subtype with hg1
  have hinj : Function.Injective g1 := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Subtype.ext (hg x x.2 hx)
  have hM : (⊤ : AddSubgroup B1).map g1 = B1.map g := by
    ext v
    constructor
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, trivial, rfl⟩
  have h2M : (twoB B1).map g1 = (B1.map g).map (dbl V) := by
    ext v
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      refine ⟨g c, ⟨c, c.2, rfl⟩, ?_⟩
      simp [hg1]
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      refine ⟨(2 : ℕ) • ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, ?_⟩
      simp [hg1]
  rw [relIndex_map_dbl_eq, ← relIndex_top_right, ← relIndex_map_map_of_injective _ _ hinj, hM, h2M]

end General

end FurioLombardo.Discharge.Analytic
