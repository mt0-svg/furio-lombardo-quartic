import Mathlib
import FurioLombardo.M2.Zimmert.Limit
import FurioLombardo.M2.Zimmert.ClassZeta

/-!
# Zimmert's Satz 2 at `γ = 1/2` for every number field (lane M2)

`zimmert_satz2_half`: for every number field `K`, every ideal class `C` and every
`0 < α < 1/2`, the class `C` contains a nonzero integral ideal `I` with
`zimmertS2 r₁ r₂ (1/2) α ≤ log (√|d_K| / N I)`.

This is R. Zimmert, Invent. Math. 62 (1981), Satz 2, at `γ = 1/2`. Proof: the per class data of
`exists_zdata` (AINTLIB's class theta functions), Satz 1 at `γ = 1/2` in the limit `β → 1/2`
(`ZData.satz1_half`) with `m` the least norm of an integral ideal of `C`, and the conversion
`satz2_of_bound`.
-/

namespace FurioLombardo.M2.Zimmert

open NumberField NumberField.InfinitePlace

open scoped nonZeroDivisors

universe u

/-- **Zimmert's Satz 2 at `γ = 1/2`.** -/
theorem zimmert_satz2_half {K : Type u} [Field K] [NumberField K] (C : ClassGroup (𝓞 K))
    {α : ℝ} (hα : 0 < α) (hα2 : α < 1 / 2) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      zimmertS2 (nrRealPlaces K) (nrComplexPlaces K) (1 / 2) α
        ≤ Real.log (Real.sqrt |(discr K : ℝ)| / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)) := by
  classical
  obtain ⟨ιf, D, hA, hμ⟩ := exists_zdata C
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C
  have : Nonempty (classIdeals K C) := ⟨⟨J, hJ⟩⟩
  have hex : ∃ n : ℕ, ∃ J : classIdeals K C, Ideal.absNorm (J.1 : Ideal (𝓞 K)) = n :=
    ⟨_, ⟨J, hJ⟩, rfl⟩
  obtain ⟨J₀, hJ₀⟩ := Nat.find_spec hex
  have hmμ : ∀ j, ((Nat.find hex : ℕ) : ℝ) ≤ D.μ j := by
    intro j
    rw [hμ j]
    exact_mod_cast Nat.find_min' hex ⟨j, rfl⟩
  have hm : 0 < ((Nat.find hex : ℕ) : ℝ) := by
    have h1 := D.hμ J₀
    rw [hμ J₀, hJ₀] at h1
    linarith
  have ha : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    have h := card_add_two_mul_card_eq_rank K
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hs := D.satz1_half ha hα hα2 hm hmμ
  have hrank : ((Module.finrank ℚ K : ℕ) : ℝ)
      = ((nrRealPlaces K + 2 * nrComplexPlaces K : ℕ) : ℝ) := by
    rw [card_add_two_mul_card_eq_rank]
  have hd : 0 < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
  refine ⟨J₀.1, J₀.2, ?_⟩
  rw [hJ₀]
  refine satz2_of_bound _ _ hα hα2 hd hm ?_
  rw [hA, hrank] at hs
  exact hs

end FurioLombardo.M2.Zimmert
