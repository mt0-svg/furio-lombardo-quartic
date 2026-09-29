import FurioLombardo.M1.Norms
import FurioLombardo.Discharge.M3b.K21Real

/-!
# Signature of `K21`: at most three real places, unit rank at most 11

The real embeddings of `K21` are the three `realEmb k` of the M3b discharge lane
(`FurioLombardo.Discharge.M3b.exists_eq_realEmb`: every real root of `f` is one of three roots
isolated by kernel-checked Moebius sign certificates). Then `r1 ≤ 3`, `r1 + 2 r2 = 21`, so the
unit rank `r1 + r2 - 1` is at most `11`.
-/

namespace FurioLombardo.M1

open NumberField

theorem nrRealPlaces_le : InfinitePlace.nrRealPlaces K21 ≤ 3 := by
  classical
  let g : {φ : K21 →+* ℂ // ComplexEmbedding.IsReal φ} → Fin 3 := fun φ =>
    (Discharge.M3b.exists_eq_realEmb φ.2.embedding).choose
  have hg : ∀ φ, φ.2.embedding = Discharge.M3b.realEmb (g φ) := fun φ =>
    (Discharge.M3b.exists_eq_realEmb _).choose_spec
  have hinj : Function.Injective g := by
    intro φ ψ h
    apply Subtype.ext
    refine RingHom.ext fun x => ?_
    rw [← ComplexEmbedding.IsReal.coe_embedding_apply φ.2 x,
      ← ComplexEmbedding.IsReal.coe_embedding_apply ψ.2 x, hg φ, hg ψ, h]
  have h1 := Fintype.card_le_of_injective g hinj
  rw [Fintype.card_fin] at h1
  rw [← InfinitePlace.card_real_embeddings]
  convert h1

theorem rank_le : Units.rank K21 ≤ 11 := by
  have h := nrRealPlaces_le
  have h_card_eq : InfinitePlace.nrRealPlaces K21 + 2 * InfinitePlace.nrComplexPlaces K21 = 21 := by
    rw [← finrank_K21]
    exact InfinitePlace.card_add_two_mul_card_eq_rank K21
  have h_rank_def : Units.rank K21 = Fintype.card (InfinitePlace K21) - 1 := rfl
  rw [h_rank_def, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K21]
  omega

end FurioLombardo.M1
