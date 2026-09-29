import FurioLombardo.M3b.Abstract
import FurioLombardo.M3b.GroupRank

/-!
# Lane M3b: ranks of the units in the abstract setting

For `D : InvData X I` with `E = ker φ` finitely generated: `rank E⁺ + rank E⁻ = rank E`, from the
homomorphism `e ↦ sX e / e` on `E` (kernel `E⁺`, image `DE`, and `(E⁻)² ≤ DE ≤ E⁻`).
-/

namespace FurioLombardo.M3b

open Module

namespace InvData

variable {X I : Type*} [CommGroup X] [CommGroup I] (D : InvData X I)

theorem Eplus_le_E : D.Eplus ≤ D.E := inf_le_left

theorem Eminus_le_E : D.Eminus ≤ D.E := inf_le_left

theorem finrank_Eplus_add_Eminus [Module.Finite ℤ (Additive D.E)] :
    finrank ℤ (Additive D.Eplus) + finrank ℤ (Additive D.Eminus) = finrank ℤ (Additive D.E) := by
  set ψ : D.E →* X := D.difX.comp D.E.subtype
  have h := finrank_additive_eq_ker_add_range ψ
  have hker : ψ.ker = D.Eplus.subgroupOf D.E := by
    ext e
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ψ, MonoidHom.coe_comp,
      Function.comp_apply, Subgroup.coe_subtype, InvData.Eplus, Subgroup.mem_inf]
    rw [D.difX_apply, div_eq_one, D.mem_fixX]
    exact ⟨fun h => ⟨e.2, h⟩, fun h => h.2⟩
  have hrange : ψ.range = D.DE := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]; rfl
  have := finite_additive_of_le D.Eminus_le_E
  have hDE : finrank ℤ (Additive D.DE) = finrank ℤ (Additive D.Eminus) := by
    refine finrank_additive_eq_of_sq_mem D.DE_le_Eminus fun k hk => ?_
    have : k ^ 2 ∈ D.Eminus.map (powMonoidHom 2) := ⟨k, hk, rfl⟩
    rw [D.map_sq_Eminus] at this
    exact Subgroup.map_mono D.Eminus_le_E this
  rw [finrank_additive_subgroup_congr hker, finrank_additive_subgroup_congr hrange, hDE,
    finrank_additive_congr (Subgroup.subgroupOfEquivOfLe D.Eplus_le_E)] at h
  exact h.symm

end InvData

end FurioLombardo.M3b
