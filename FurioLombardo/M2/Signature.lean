import FurioLombardo.M1.Signature
import FurioLombardo.M2.Field

/-!
# Signature of K21: three real places, nine complex places (lane M2)

Lane M1 proves `r₁ ≤ 3` (`FurioLombardo.M1.nrRealPlaces_le`); the three real embeddings
`FurioLombardo.Discharge.M3b.realEmb k` of the M3b discharge are distinct, which gives `r₁ ≥ 3`.
Then `r₁ + 2 r₂ = 21` gives `r₂ = 9`. `FurioLombardo.M1.K21` and `FurioLombardo.M2.K21` are the
same type (`FurioLombardo.M2.k21_eq`).
-/

namespace FurioLombardo.M2

open NumberField

theorem nrRealPlaces_M1K21 : InfinitePlace.nrRealPlaces FurioLombardo.M1.K21 = 3 := by
  classical
  apply le_antisymm FurioLombardo.M1.nrRealPlaces_le
  rw [← InfinitePlace.card_real_embeddings]
  let g : Fin 3 → {φ : FurioLombardo.M1.K21 →+* ℂ // ComplexEmbedding.IsReal φ} := fun k =>
    ⟨Complex.ofRealHom.comp (Discharge.M3b.realEmb k), by
      rw [ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun x => ?_
      simp [ComplexEmbedding.conjugate]⟩
  have hg : Function.Injective g := by
    intro a b h
    apply Discharge.M3b.realEmb_injective
    refine RingHom.ext fun x => ?_
    have := congrArg (fun φ : {φ : FurioLombardo.M1.K21 →+* ℂ // ComplexEmbedding.IsReal φ} =>
      (φ.1 x)) h
    simpa [g] using this
  simpa using Fintype.card_le_of_injective g hg

/-- K21 has three real places. -/
theorem nrRealPlaces_K21 : InfinitePlace.nrRealPlaces K21 = 3 := nrRealPlaces_M1K21

/-- K21 has nine complex places. -/
theorem nrComplexPlaces_K21 : InfinitePlace.nrComplexPlaces K21 = 9 := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank FurioLombardo.M1.K21
  rw [FurioLombardo.M1.finrank_K21, nrRealPlaces_M1K21] at h
  change InfinitePlace.nrComplexPlaces FurioLombardo.M1.K21 = 9
  omega

end FurioLombardo.M2
