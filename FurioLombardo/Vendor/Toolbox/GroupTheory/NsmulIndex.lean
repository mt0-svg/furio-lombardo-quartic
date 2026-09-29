/-
Generalized from 2 to any n from `FurioLombardo.Discharge.Analytic.TwoIndex` (discharge of the analytic
hypotheses). Namespace FurioLombardo.Vendor.Toolbox.GroupTheory.
-/
import Mathlib

/-!
# The index of `nB` from a subgroup of finite index without `n`-torsion

For an abelian group `B` (not necessarily finitely generated) with a subgroup `B1` of finite index meeting `B[n]`
trivially, `[B : nB] = [B1 : nB1] · #B[n]` (`index_range_nsmul_eq_relIndex_mul_card`). When `B1` embeds as a
subgroup of finite index in a group `V` without `n`-torsion (for instance `ℤ_p^d`), `[B1 : nB1] = [V : nV]`
(`relIndex_map_nsmul_eq_index_range`, `relIndex_map_nsmul_map`). Use: `[A(k_v) : 2A(k_v)] = 2^(d [k_v : ℚ_2]) · #A(k_v)[2]`
for an abelian variety of dimension d over a 2-adic field, from the points of its formal group with coordinates in
`4 O_v` (a subgroup of finite index, isomorphic to `O_v^d` through the formal logarithm).

* `comap_nsmul_map_nsmul`: the preimage of `n B1` under `b ↦ n b` is `B1 ⊔ B[n]`.
* `index_range_nsmul_eq_relIndex_mul_card`: `[B : nB] = [B1 : nB1] · #B[n]` if `B1` has finite index and
  `B1 ⊓ B[n] = ⊥`.
* `relIndex_map_nsmul_eq_index_range`: `[M : nM] = [V : nV]` for `M` of finite index in `V` when `b ↦ n b` is
  injective on `V`.
* `relIndex_map_nsmul_eq_index`: `[B1 : nB1]` computed in `B` is the index of `n B1` in the group `B1`.
* `relIndex_map_nsmul_map`: `[B1 : nB1] = [g(B1) : n g(B1)]` for a homomorphism `g` injective on `B1`.
-/

namespace FurioLombardo.Vendor.Toolbox.GroupTheory

open AddSubgroup

variable {B : Type*} [AddCommGroup B]

/-- The preimage of `n B1` under `b ↦ n b` is `B1 + B[n]`. -/
theorem comap_nsmul_map_nsmul (n : ℕ) (B1 : AddSubgroup B) :
    (B1.map (nsmulAddMonoidHom n)).comap (nsmulAddMonoidHom n) = B1 ⊔ (nsmulAddMonoidHom n : B →+ B).ker := by
  ext b
  constructor
  · rintro ⟨b1, hb1, h⟩
    have h' : n • b1 = n • b := h
    have hk : b - b1 ∈ (nsmulAddMonoidHom n : B →+ B).ker := by
      show n • (b - b1) = 0
      rw [nsmul_sub, h', sub_self]
    have : b = b1 + (b - b1) := by abel
    rw [this]
    exact add_mem_sup hb1 hk
  · intro hb
    have h1 : B1 ≤ (B1.map (nsmulAddMonoidHom n)).comap (nsmulAddMonoidHom n) := fun x hx => ⟨x, hx, rfl⟩
    have h2 : (nsmulAddMonoidHom n : B →+ B).ker ≤ (B1.map (nsmulAddMonoidHom n)).comap (nsmulAddMonoidHom n) := by
      intro x hx
      refine ⟨0, B1.zero_mem, ?_⟩
      have : n • x = 0 := hx
      simp only [map_zero]
      exact this.symm
    exact (sup_le h1 h2) hb

/-- **The index of `nB`.** If `B1 ≤ B` has finite index and meets `B[n]` trivially, `[B : nB] = [B1 : nB1] · #B[n]`. -/
theorem index_range_nsmul_eq_relIndex_mul_card (n : ℕ) (B1 : AddSubgroup B) [hfi : B1.FiniteIndex]
    (hB1 : B1 ⊓ (nsmulAddMonoidHom n : B →+ B).ker = ⊥) :
    (nsmulAddMonoidHom n : B →+ B).range.index =
      (B1.map (nsmulAddMonoidHom n)).relIndex B1 * Nat.card (nsmulAddMonoidHom n : B →+ B).ker := by
  set H1 := B1.map (nsmulAddMonoidHom n) with hH1def
  set K := (nsmulAddMonoidHom n : B →+ B).ker with hKdef
  have hH1B1 : H1 ≤ B1 := by
    rintro _ ⟨b, hb, rfl⟩
    exact B1.nsmul_mem hb n
  have hH1H : H1 ≤ (nsmulAddMonoidHom n : B →+ B).range := by
    rintro _ ⟨b, -, rfl⟩
    exact ⟨b, rfl⟩
  have e1 := relIndex_mul_index hH1B1
  have e2 := relIndex_mul_index hH1H
  have e5 : H1.relIndex (nsmulAddMonoidHom n : B →+ B).range = (B1 ⊔ K).index := by
    rw [← comap_nsmul_map_nsmul, ← relIndex_top_right, relIndex_comap, ← AddMonoidHom.range_eq_map]
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
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hj)
  calc (B1 ⊔ K).index * (nsmulAddMonoidHom n : B →+ B).range.index = H1.index := e2
    _ = H1.relIndex B1 * B1.index := e1.symm
    _ = H1.relIndex B1 * (Nat.card K * (B1 ⊔ K).index) := by rw [e3]
    _ = (B1 ⊔ K).index * (H1.relIndex B1 * Nat.card K) := by ring

/-- For a subgroup `M` of finite index of a group `V` on which `b ↦ n b` is injective, `[M : nM] = [V : nV]`. -/
theorem relIndex_map_nsmul_eq_index_range {V : Type*} [AddCommGroup V] (n : ℕ)
    (hinj : Function.Injective (nsmulAddMonoidHom n : V →+ V)) (M : AddSubgroup V) [hfi : M.FiniteIndex] :
    (M.map (nsmulAddMonoidHom n)).relIndex M = (nsmulAddMonoidHom n : V →+ V).range.index := by
  have hle : M.map (nsmulAddMonoidHom n) ≤ M := by
    rintro _ ⟨b, hb, rfl⟩
    exact M.nsmul_mem hb n
  have hle2 : M.map (nsmulAddMonoidHom n) ≤ (nsmulAddMonoidHom n : V →+ V).range := by
    rintro _ ⟨b, -, rfl⟩
    exact ⟨b, rfl⟩
  have e1 := relIndex_mul_index hle
  have e2 := relIndex_mul_index hle2
  have e3 : (M.map (nsmulAddMonoidHom n)).relIndex (nsmulAddMonoidHom n : V →+ V).range = M.index := by
    rw [AddMonoidHom.range_eq_map, relIndex_map_map_of_injective _ _ hinj, relIndex_top_right]
  rw [e3] at e2
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfi.index_ne_zero)
  rw [e1, ← e2, mul_comm]

/-- `[B1 : nB1]`, computed in `B`, is the index of `n B1` in the group `B1`. -/
theorem relIndex_map_nsmul_eq_index (n : ℕ) (B1 : AddSubgroup B) :
    (B1.map (nsmulAddMonoidHom n)).relIndex B1 = (nsmulAddMonoidHom n : B1 →+ B1).range.index := by
  unfold relIndex
  congr 1
  ext x
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    simpa using h
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2, by simp⟩

/-- `[B1 : nB1]` is invariant under a homomorphism injective on `B1`: it equals `[g(B1) : n g(B1)]`. -/
theorem relIndex_map_nsmul_map {V : Type*} [AddCommGroup V] (n : ℕ) (g : B →+ V) (B1 : AddSubgroup B)
    (hg : ∀ b ∈ B1, g b = 0 → b = 0) :
    (B1.map (nsmulAddMonoidHom n)).relIndex B1 =
      ((B1.map g).map (nsmulAddMonoidHom n)).relIndex (B1.map g) := by
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
  have h2M : (nsmulAddMonoidHom n : B1 →+ B1).range.map g1 = (B1.map g).map (nsmulAddMonoidHom n) := by
    ext v
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      refine ⟨g c, ⟨c, c.2, rfl⟩, ?_⟩
      simp [hg1]
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      refine ⟨n • ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, ?_⟩
      simp [hg1]
  rw [relIndex_map_nsmul_eq_index, ← relIndex_top_right, ← relIndex_map_map_of_injective _ _ hinj, hM, h2M]

end FurioLombardo.Vendor.Toolbox.GroupTheory
