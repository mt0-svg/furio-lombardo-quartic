import FurioLombardo.M3b.Glue
import FurioLombardo.M3b.AbstractUnits

/-!
# Lane M3b: the unit indices of a quadratic extension

For `L/K` quadratic with `σ ≠ 1` and `D = galData`: `[E⁺ : (E⁺)²] = 2 ^ (r_K + 1)`,
`[E⁻ : (E⁻)²] = 2 ^ (r_L - r_K + 1)`, `[E⁺ : E ∩ N(Lˣ)] = [E_K : E_K ∩ N(Lˣ)]`, and the count of
infinite places `r_L + t_∞ = 2 r_K + 1`.
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.M3b

open NumberField Module
open scoped nonZeroDivisors

section UnitsIndex

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem finite_additive_of_mulEquiv {A B : Type*} [CommGroup A] [CommGroup B]
    [Module.Finite ℤ (Additive A)] (e : A ≃* B) : Module.Finite ℤ (Additive B) :=
  Module.Finite.equiv (MulEquiv.toAdditive e).toIntLinearEquiv

theorem galData_finite_E (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) :
    Module.Finite ℤ (Additive (galData h2 σ).E) :=
  finite_additive_of_mulEquiv ((MonoidHom.ofInjective iotaL_injective).trans
    (MulEquiv.subgroupCongr (galData_E h2 σ).symm))

theorem galData_finrank_E (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) :
    finrank ℤ (Additive (galData h2 σ).E) = Units.rank L := by
  rw [← Units.finrank_eq, finrank_additive_congr ((MonoidHom.ofInjective iotaL_injective).trans
    (MulEquiv.subgroupCongr (galData_E h2 σ).symm))]

theorem galData_finrank_Eplus (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) :
    finrank ℤ (Additive (galData h2 σ).Eplus) = Units.rank K := by
  rw [← Units.finrank_eq, finrank_additive_congr ((MonoidHom.ofInjective iotaK_injective).trans
    (MulEquiv.subgroupCongr (galData_Eplus h2 σ hσ1).symm))]

theorem galData_finrank_Eminus (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) :
    finrank ℤ (Additive (galData h2 σ).Eminus) + Units.rank K = Units.rank L := by
  have := galData_finite_E h2 σ
  have h := (galData h2 σ).finrank_Eplus_add_Eminus
  rw [galData_finrank_Eplus h2 σ hσ1, galData_finrank_E] at h
  omega

theorem neg_one_mem_Eplus (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) :
    (-1 : Lˣ) ∈ (galData h2 σ).Eplus := by
  rw [galData_Eplus h2 σ hσ1]
  exact ⟨-1, Units.ext (by simp [coe_iotaK])⟩

theorem neg_one_mem_Eminus (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) :
    (-1 : Lˣ) ∈ (galData h2 σ).Eminus := by
  refine ⟨?_, ?_⟩
  · rw [galData_E]
    exact ⟨-1, Units.ext (by simp [iotaL])⟩
  · show (-1 : Lˣ) * sigmaX σ (-1) = 1
    have : sigmaX σ (-1) = -1 := Units.ext (by rw [coe_sigmaX]; simp)
    rw [this, neg_one_mul, neg_neg]

theorem two_ne_zero_L : (2 : L) ≠ 0 := two_ne_zero

theorem galData_index_sq_Eplus (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) :
    ((galData h2 σ).Eplus.map (powMonoidHom 2)).relIndex (galData h2 σ).Eplus =
      2 ^ (Units.rank K + 1) := by
  have := galData_finite_E h2 σ
  have := finite_additive_of_le (galData h2 σ).Eplus_le_E
  rw [relIndex_map_pow, index_range_pow_eq 2 two_ne_zero, galData_finrank_Eplus h2 σ hσ1,
    card_ker_sq_eq_two two_ne_zero_L _ (neg_one_mem_Eplus h2 σ hσ1), pow_succ]

theorem galData_index_sq_Eminus (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) :
    ((galData h2 σ).Eminus.map (powMonoidHom 2)).relIndex (galData h2 σ).Eminus =
      2 ^ (finrank ℤ (Additive (galData h2 σ).Eminus) + 1) := by
  have := galData_finite_E h2 σ
  have := finite_additive_of_le (galData h2 σ).Eminus_le_E
  rw [relIndex_map_pow, index_range_pow_eq 2 two_ne_zero,
    card_ker_sq_eq_two two_ne_zero_L _ (neg_one_mem_Eminus h2 σ), pow_succ]

theorem galData_relIndex_NXE (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ1 : σ ≠ 1) :
    (galData h2 σ).NXE.relIndex (galData h2 σ).Eplus = (normUnits K L).index := by
  rw [galData_NXE h2 σ hσ1, galData_Eplus h2 σ hσ1, MonoidHom.range_eq_map, relIndex_map_map,
    (MonoidHom.ker_eq_bot_iff _).2 iotaK_injective, sup_bot_eq, Subgroup.relIndex_top_right]

theorem mem_ramifiedRealPlaces_iff (v : InfinitePlace K) :
    v ∈ ramifiedRealPlaces K L ↔ ¬ v.IsUnramifiedIn L := by
  constructor
  · rintro ⟨hv, w, hw, hwc⟩ h
    have := h w hw
    exact (InfinitePlace.not_isUnramified_iff.2 ⟨hwc, hw ▸ hv⟩) this
  · intro h
    simp only [InfinitePlace.IsUnramifiedIn, not_forall] at h
    obtain ⟨w, hw, hwu⟩ := h
    obtain ⟨hwc, hwr⟩ := InfinitePlace.not_isUnramified_iff.1 hwu
    exact ⟨hw ▸ hwr, w, hw, hwc⟩

open scoped Classical in
/-- **Infinite places of a quadratic extension**: `r_L + t_∞ = 2 r_K + 1`. -/
theorem rank_add_ncard_ramifiedRealPlaces (h2 : Module.finrank K L = 2) :
    Units.rank L + (ramifiedRealPlaces K L).ncard = 2 * Units.rank K + 1 := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  have hc := InfinitePlace.card_eq_card_isUnramifiedIn K L
  rw [h2] at hc
  set U : Finset (InfinitePlace K) := Finset.univ.filter fun w => w.IsUnramifiedIn L
  have hU : U.card + Uᶜ.card = Fintype.card (InfinitePlace K) := by
    rw [Finset.card_add_card_compl]
  have hR : (ramifiedRealPlaces K L).ncard = Uᶜ.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp [U, mem_ramifiedRealPlaces_iff]
  have hK : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  have hL : 0 < Fintype.card (InfinitePlace L) := Fintype.card_pos
  simp only [Units.rank]
  rw [hR]
  omega

end UnitsIndex

end FurioLombardo.M3b
