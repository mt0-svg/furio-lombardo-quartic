import Mathlib
import FurioLombardo.Vendor.Toolbox.TauCeti.NumberTheory.LocalField.Squares
import FurioLombardo.Vendor.Toolbox.TauCeti.NumberTheory.LocalField.NormalizedValuation
import FurioLombardo.Vendor.Toolbox.TauCeti.NumberTheory.LocalField.Uniformizer
import FurioLombardo.Discharge.M4Cert.Kv
import FurioLombardo.Discharge.SelmerBasis.SquareLemmas
import FurioLombardo.M1.Vendor.Stoll.Basic

/-!
# From ultrametric proper normed fields to `IsNonarchimedeanLocalField`

For a nontrivially normed field `F` with an ultrametric, proper norm, `normValuativeRel F` is the
valuative relation `x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖` (Mathlib's `ValuativeRel.ofValuation` of
`NormedField.valuation`), and with the norm topology `F` is a nonarchimedean local field
(`isNonarchimedeanLocalField`). The relation is a named definition, installed by
`open scoped FurioLombardo.Discharge.SelmerBasis.NormedLocal`, so no other valuative relation is
disturbed.

The compatibility lemmas translate the valuation, the ring of integers, the residue map, uniformizers
and `v_K(2)` of the TauCeti local field API into norms: `valuation_le_valuation_iff`,
`valuation_lt_valuation_iff`, `mem_integer_iff`, `residue_eq_zero_iff`, `isUniformizer_of_norm`,
`toAdd_normalizedValuation_of_norm`, `natCastValuation_two_of_norm`.

Tests: `M4Cert.Kv` and the quadratic extension `QuadraticAlgebra Kv δ 0` with the spectral norm over
`Kv` are local fields, and `‖z‖ ^ 2 = ‖QuadraticAlgebra.norm z‖` in the latter (`norm_sq_eq_norm_norm`).
-/

namespace FurioLombardo.Discharge.SelmerBasis

open ValuativeRel FurioLombardo.Vendor.Toolbox.TauCeti

noncomputable section

/-! ## The valuative relation of a norm -/

section NormedField

variable (F : Type*) [NormedField F] [IsUltrametricDist F]

/-- The valuative relation of an ultrametric normed field: `x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖`. -/
@[instance_reducible]
def normValuativeRel : ValuativeRel F :=
  ValuativeRel.ofValuation (NormedField.valuation (K := F))

/-- `NormedField.valuation` is compatible with `normValuativeRel`. -/
theorem normValuation_compatible :
    @Valuation.Compatible F _ _ _ (NormedField.valuation (K := F)) (normValuativeRel F) :=
  Valuation.Compatible.ofValuation _

namespace NormedLocal

attribute [scoped instance] normValuativeRel normValuation_compatible

end NormedLocal

open scoped NormedLocal

variable {F}

theorem vle_iff_norm_le (x y : F) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := NNReal.coe_le_coe

theorem valuation_le_valuation_iff (x y : F) : valuation F x ≤ valuation F y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [← (valuation F).vle_iff_le, vle_iff_norm_le]

theorem valuation_lt_valuation_iff (x y : F) : valuation F x < valuation F y ↔ ‖x‖ < ‖y‖ := by
  rw [← not_le, valuation_le_valuation_iff, not_le]

theorem valuation_eq_valuation_iff (x y : F) : valuation F x = valuation F y ↔ ‖x‖ = ‖y‖ := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_le_valuation_iff, valuation_le_valuation_iff]

theorem valuation_le_one_iff (x : F) : valuation F x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  simpa using valuation_le_valuation_iff x 1

theorem valuation_lt_one_iff (x : F) : valuation F x < 1 ↔ ‖x‖ < 1 := by
  simpa using valuation_lt_valuation_iff x 1

theorem valuation_eq_one_iff (x : F) : valuation F x = 1 ↔ ‖x‖ = 1 := by
  simpa using valuation_eq_valuation_iff x 1

theorem mem_integer_iff (x : F) : x ∈ 𝒪[F] ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, valuation_le_one_iff]

/-- The residue of an integral element vanishes iff its norm is `< 1`. -/
theorem residue_eq_zero_iff (x : 𝒪[F]) : IsLocalRing.residue 𝒪[F] x = 0 ↔ ‖(x : F)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _),
    ← valuation_lt_one_iff, lt_iff_le_and_ne]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

/-- Two integral elements have the same residue iff their difference has norm `< 1`. -/
theorem residue_eq_residue_iff (x y : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x = IsLocalRing.residue 𝒪[F] y ↔ ‖(x : F) - y‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  rfl

end NormedField

/-! ## The local field structure -/

section Local

variable (F : Type*) [NontriviallyNormedField F] [IsUltrametricDist F]

open scoped NormedLocal

/-- The norm topology is the valuative topology of `normValuativeRel`. -/
theorem isValuativeTopology : IsValuativeTopology F :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle NormedField.valuation
    fun {s} => NormedField.toValued.is_topological_valuation s

theorem isNontrivial : ValuativeRel.IsNontrivial F := by
  refine (isNontrivial_iff_isNontrivial (NormedField.valuation (K := F))).2 ?_
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one F
  refine ⟨⟨x, ?_, ?_⟩⟩
  · simpa [← NNReal.coe_inj] using hx0.ne'
  · intro h
    have : ‖x‖ = 1 := by simpa [← NNReal.coe_inj] using h
    exact hx1.ne this

/-- A nontrivially normed field with an ultrametric locally compact norm is a nonarchimedean local
field for `normValuativeRel` and the norm topology. -/
theorem isNonarchimedeanLocalField [LocallyCompactSpace F] : IsNonarchimedeanLocalField F :=
  have := isValuativeTopology F
  have := isNontrivial F
  { }

namespace NormedLocal

attribute [scoped instance] isNonarchimedeanLocalField

end NormedLocal

end Local

/-! ## The local square theorem in norms -/

section Squares

/-- **Local square theorem**, in norms: in a proper ultrametric normed field with a norm uniformizer,
`1 + 4 m` is a square when `m` is integral, congruent to `t ^ 2 + t` modulo `𝔪` with `t` integral,
and `1 + 4 m` is a unit (automatic in residue characteristic `2`). Proof: TauCeti's
`isSquare_of_eq_one_add_four_mul` for `normValuativeRel`. -/
theorem isSquare_one_add_four_mul {F : Type*} [NormedField F] [IsUltrametricDist F] [ProperSpace F]
    {π : F} (hπ : NormUnif π) (h2 : (2 : F) ≠ 0) {m t : F} (hm : ‖m‖ ≤ 1) (ht : ‖t‖ ≤ 1)
    (hmt : ‖m - (t ^ 2 + t)‖ < 1) (h1 : ‖1 + 4 * m‖ = 1) : IsSquare (1 + 4 * m) := by
  let _ : NontriviallyNormedField F :=
    { ‹NormedField F› with
      non_trivial := ⟨π⁻¹, by
        rw [norm_inv]
        exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr hπ.ne_zero, hπ.norm_lt_one⟩⟩ }
  open scoped NormedLocal in
  have : IsNonarchimedeanLocalField F := isNonarchimedeanLocalField F
  open scoped NormedLocal in
  have hw0 : (1 + 4 * m : F) ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  open scoped NormedLocal in
  have key : IsSquare (Units.mk0 (1 + 4 * m) hw0) := by
    refine isSquare_of_eq_one_add_four_mul (K := F) h2 (m := ⟨m, (mem_integer_iff m).2 hm⟩) rfl
      ((valuation_eq_one_iff _).2 h1) ?_
    refine ⟨IsLocalRing.residue _ ⟨t, (mem_integer_iff t).2 ht⟩, ?_⟩
    simp only
    rw [← map_pow, ← map_add, residue_eq_residue_iff]
    simpa using (show ‖(t ^ 2 + t) - m‖ < 1 by rwa [norm_sub_rev])
  obtain ⟨r, hr⟩ := key
  exact ⟨r, by simpa using congrArg Units.val hr⟩

/-- An element within `‖4‖` of `1` is a square. -/
theorem isSquare_of_norm_sub_one_lt {F : Type*} [NormedField F] [IsUltrametricDist F]
    [ProperSpace F] {π : F} (hπ : NormUnif π) (h2 : (2 : F) ≠ 0) {z : F}
    (hz : ‖z - 1‖ < ‖(4 : F)‖) : IsSquare z := by
  have h4 : (4 : F) ≠ 0 := by
    intro hzero
    apply h2
    have : (4 : F) = (2 : F) * (2 : F) := by norm_num
    rw [this, mul_eq_zero] at hzero
    rcases hzero with h | h
    · exact h
    · exact h
  set m := (z - 1) / (4 : F) with hm_def
  have hz_eq : z = 1 + 4 * m := by
    dsimp [m]
    field_simp [h4]
    ring
  have hnorm_m_lt_one : ‖m‖ < 1 := by
    rw [hm_def, norm_div]
    exact (div_lt_one (norm_pos_iff.mpr h4)).mpr hz
  have hnorm_4_le_one : ‖(4 : F)‖ ≤ 1 :=
    IsUltrametricDist.norm_natCast_le_one (R := F) 4
  have hnorm_z_sub_one_lt_one : ‖z - 1‖ < 1 :=
    lt_of_lt_of_le hz hnorm_4_le_one
  have hnorm_z_eq_one : ‖z‖ = 1 := by
    have hz' : z = (z - 1) + 1 := by ring
    rw [hz']
    have hne : ‖z - 1‖ ≠ ‖(1 : F)‖ := by
      rw [norm_one]
      exact ne_of_lt hnorm_z_sub_one_lt_one
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, max_eq_right]
    exact le_of_lt hnorm_z_sub_one_lt_one
  have hm_le_one : ‖m‖ ≤ 1 := le_of_lt hnorm_m_lt_one
  have ht_le_one : ‖(0 : F)‖ ≤ 1 := by
    simpa using norm_nonneg (0 : F)
  have hmt : ‖m - ((0 : F) ^ 2 + (0 : F))‖ < 1 := by
    simp [hnorm_m_lt_one]
  have h1 : ‖1 + 4 * m‖ = 1 := by
    rw [← hz_eq, hnorm_z_eq_one]
  rw [hz_eq]
  exact isSquare_one_add_four_mul hπ h2 hm_le_one ht_le_one hmt h1

/-- **Square certificate**: `x` is a square when `x / s ^ 2` is within `‖4‖` of `1`. -/
theorem isSquare_of_norm_div_sq_sub_one_lt {F : Type*} [NormedField F] [IsUltrametricDist F]
    [ProperSpace F] {π : F} (hπ : NormUnif π) (h2 : (2 : F) ≠ 0) {x s : F} (hs : s ≠ 0)
    (hx : ‖x / s ^ 2 - 1‖ < ‖(4 : F)‖) : IsSquare x := by
  have h_sq_div : IsSquare (x / s ^ 2) :=
    isSquare_of_norm_sub_one_lt hπ h2 hx
  rcases h_sq_div with ⟨r, hr⟩
  refine ⟨s * r, ?_⟩
  calc
    x = (x / s ^ 2) * s ^ 2 := by field_simp [hs]
    _ = (r * r) * s ^ 2 := by rw [hr]
    _ = (s * r) * (s * r) := by ring

end Squares

/-! ## Residue fields of a valuation subring given by the norm -/

section Residue

theorem vs_mem_maximalIdeal_iff {F : Type*} [NormedField F] [IsUltrametricDist F] (O : ValuationSubring F) (hO : ∀ x : F, x ∈ O ↔ ‖x‖ ≤ 1)
    (x : O) : x ∈ IsLocalRing.maximalIdeal O ↔ ‖(x : F)‖ < 1 := by
  have hx_mem : (x : F) ∈ O := Subtype.mem x
  have hx_norm_le_one : ‖(x : F)‖ ≤ 1 := by
    rw [← hO]
    exact hx_mem
  have hx_norm_nonneg : 0 ≤ ‖(x : F)‖ := norm_nonneg _
  have h_zero_ne_one : (0 : O) ≠ 1 := by
    intro h
    have : (0 : F) = (1 : F) := by simpa using congr_arg Subtype.val h
    exact zero_ne_one this
  -- Key equivalence: IsUnit x ↔ ‖x‖ = 1
  have h_isUnit_iff_norm_eq_one : IsUnit x ↔ ‖(x : F)‖ = 1 := by
    constructor
    · intro h
      have hinv_mem : (x : F)⁻¹ ∈ O := by
        have h_mul : (x : F) * ((h.unit⁻¹ : Oˣ) : F) = 1 := by
          have hx : (x : F) = ((h.unit : O) : F) := by rw [h.unit_spec]
          rw [hx]
          have htemp := Units.val_inv h.unit
          exact congr_arg (fun (z : O) => (z : F)) htemp
        have h_inv_eq : (x : F)⁻¹ = ((h.unit⁻¹ : Oˣ) : F) :=
          inv_eq_of_mul_eq_one_right h_mul
        rw [h_inv_eq]
        exact ((h.unit⁻¹ : Oˣ) : O).property
      have hinv_norm_le_one : ‖(x : F)⁻¹‖ ≤ 1 := ((hO ((x : F)⁻¹)).mp hinv_mem)
      have h_norm_inv : ‖(x : F)⁻¹‖ = ‖(x : F)‖⁻¹ := norm_inv _
      rw [h_norm_inv] at hinv_norm_le_one
      have h_one_le_norm : 1 ≤ ‖(x : F)‖ := by
        rcases (inv_le_one_iff₀.mp hinv_norm_le_one) with (h0 | h1)
        · have hx_norm_zero : ‖(x : F)‖ = 0 := by linarith
          have hx_zero : (x : F) = 0 := norm_eq_zero.mp hx_norm_zero
          have hx_zero_O : x = 0 := Subtype.ext hx_zero
          rw [hx_zero_O] at h
          have : ¬ IsUnit (0 : O) := by
            rw [isUnit_zero_iff]
            exact h_zero_ne_one
          exact absurd h this
        · exact h1
      exact le_antisymm hx_norm_le_one h_one_le_norm
    · intro h
      have hx_ne_zero : (x : F) ≠ 0 := by
        intro hzero
        rw [hzero] at h
        have : ‖(0 : F)‖ = 0 := norm_zero
        rw [this] at h
        norm_num at h
      have h_norm_inv : ‖(x : F)⁻¹‖ = ‖(x : F)‖⁻¹ := norm_inv _
      rw [h] at h_norm_inv
      have h_norm_inv_one : ‖(x : F)⁻¹‖ = 1 := by
        rw [h_norm_inv]
        norm_num
      have hinv_mem : (x : F)⁻¹ ∈ O := (hO ((x : F)⁻¹)).mpr (by rw [h_norm_inv_one])
      let y : O := ⟨(x : F)⁻¹, hinv_mem⟩
      have h_mul : x * y = 1 := by
        ext
        simp [y, hx_ne_zero]
      have h_mul' : y * x = 1 := by
        ext
        simp [y, hx_ne_zero]
      exact ⟨Units.mk x y h_mul h_mul', rfl⟩
  -- Now use valuation_lt_one_iff to connect maximal ideal membership to valuation < 1
  rw [ValuationSubring.valuation_lt_one_iff]
  -- Goal: O.valuation (x : F) < 1 ↔ ‖(x : F)‖ < 1
  -- We know O.valuation (x : F) ≤ 1 ↔ ‖(x : F)‖ ≤ 1
  have h_val_le_one_iff : O.valuation (x : F) ≤ 1 ↔ ‖(x : F)‖ ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff, hO]
  -- And O.valuation (x : F) = 1 ↔ IsUnit x
  have h_val_eq_one_iff : O.valuation (x : F) = 1 ↔ ‖(x : F)‖ = 1 := by
    rw [← ValuationSubring.valuation_eq_one_iff, h_isUnit_iff_norm_eq_one]
  -- Now use the trichotomy: both sides are ≤ 1, so they're either < 1 or = 1
  rcases lt_or_eq_of_le (ValuationSubring.valuation_le_one O (x : O)) with (hlt | heq)
  · -- O.valuation < 1
    have h_norm_lt_one : ‖(x : F)‖ < 1 := by
      rcases (lt_or_eq_of_le hx_norm_le_one) with (hlt' | heq')
      · exact hlt'
      · -- ‖x‖ = 1, then O.valuation = 1 by h_val_eq_one_iff, contradiction
        have : O.valuation (x : F) = 1 := h_val_eq_one_iff.mpr heq'
        rw [this] at hlt
        exfalso; exact lt_irrefl _ hlt
    exact ⟨fun _ => h_norm_lt_one, fun _ => hlt⟩
  · -- O.valuation = 1
    have h_norm_eq_one : ‖(x : F)‖ = 1 := h_val_eq_one_iff.mp heq
    have h_not_lt_val : ¬ (O.valuation (x : F) < 1) := by rw [heq]; exact lt_irrefl _
    have h_not_lt_norm : ¬ (‖(x : F)‖ < 1) := by rw [h_norm_eq_one]; exact lt_irrefl _
    exact ⟨fun h => (h_not_lt_val h).elim, fun h => (h_not_lt_norm h).elim⟩

theorem vs_residue_eq_iff {F : Type*} [NormedField F] [IsUltrametricDist F] (O : ValuationSubring F) (hO : ∀ x : F, x ∈ O ↔ ‖x‖ ≤ 1) (x y : O) :
    IsLocalRing.residue O x = IsLocalRing.residue O y ↔ ‖(x : F) - y‖ < 1 := by
  have h_val_le_one_iff_norm_le_one (z : F) : O.valuation z ≤ 1 ↔ ‖z‖ ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff, hO]
  have h_val_lt_one_iff_norm_lt_one (a : O) : O.valuation (a : F) < 1 ↔ ‖(a : F)‖ < 1 := by
    constructor
    · -- O.valuation a < 1 → ‖(a : F)‖ < 1
      intro hval
      have hle_val : O.valuation (a : F) ≤ 1 := le_of_lt hval
      have hle_norm : ‖(a : F)‖ ≤ 1 := ((h_val_le_one_iff_norm_le_one (a : F)).mp hle_val)
      by_cases ha0 : (a : F) = 0
      · rw [ha0, norm_zero]; exact zero_lt_one
      · have ha_inv_not_mem : (a : F)⁻¹ ∉ O := by
          intro hinv
          have hunit : IsUnit a := by
            have h1 : (a : O) * (⟨(a : F)⁻¹, hinv⟩ : O) = 1 := by
              ext; dsimp; field_simp [ha0]
            have h2 : (⟨(a : F)⁻¹, hinv⟩ : O) * (a : O) = 1 := by
              ext; dsimp; field_simp [ha0]
            exact ⟨⟨a, ⟨(a : F)⁻¹, hinv⟩, h1, h2⟩, rfl⟩
          have ha_mem_max : a ∈ IsLocalRing.maximalIdeal O := by
            rwa [ValuationSubring.valuation_lt_one_iff]
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha_mem_max
          exact ha_mem_max hunit
        have hnorm_inv_gt_one : 1 < ‖(a : F)⁻¹‖ := by
          have : ¬ ‖(a : F)⁻¹‖ ≤ 1 := by rwa [← hO]
          exact by linarith
        have h_mul : (a : F) * (a : F)⁻¹ = 1 := by field_simp [ha0]
        have h_norm_mul : ‖(a : F) * (a : F)⁻¹‖ = ‖(a : F)‖ * ‖(a : F)⁻¹‖ := norm_mul _ _
        rw [h_mul, norm_one] at h_norm_mul
        by_contra! hge
        have heq : ‖(a : F)‖ = 1 := by linarith
        rw [heq] at h_norm_mul
        have : ‖(a : F)⁻¹‖ = 1 := by nlinarith
        linarith
    · -- ‖(a : F)‖ < 1 → O.valuation a < 1
      intro hnorm
      have hle_norm : ‖(a : F)‖ ≤ 1 := le_of_lt hnorm
      have hle_val : O.valuation (a : F) ≤ 1 := ((h_val_le_one_iff_norm_le_one (a : F)).mpr hle_norm)
      by_contra! hge
      have heq : O.valuation (a : F) = 1 := le_antisymm hle_val hge
      have hunit : IsUnit a := ((ValuationSubring.valuation_eq_one_iff O) a).mpr heq
      have ha_ne_zero : (a : F) ≠ 0 := by
        intro hzero
        have hzero_val : O.valuation (a : F) = 0 := by simpa [hzero] using ValuationSubring.valuation.map_zero
        rw [heq] at hzero_val
        exact zero_ne_one hzero_val.symm
      have ha_inv_mem : (a : F)⁻¹ ∈ O := by
        rcases hunit.exists_right_inv with ⟨b, hb⟩
        have h_mul_F : (a : F) * (b : F) = 1 := by
          simpa using congrArg (fun x : O => (x : F)) hb
        have hb_eq : (b : F) = (a : F)⁻¹ := by
          apply eq_inv_of_mul_eq_one_right h_mul_F
        simpa [hb_eq] using Subtype.coe_prop b
      have hnorm_inv_le_one : ‖(a : F)⁻¹‖ ≤ 1 :=
        (hO ((a : F)⁻¹)).mp ha_inv_mem
      have h_mul : (a : F) * (a : F)⁻¹ = 1 := by field_simp [ha_ne_zero]
      have h_norm_mul : ‖(a : F) * (a : F)⁻¹‖ = ‖(a : F)‖ * ‖(a : F)⁻¹‖ := norm_mul _ _
      rw [h_mul, norm_one] at h_norm_mul
      have h_lt : ‖(a : F)‖ * ‖(a : F)⁻¹‖ < 1 := by
        have hpos : 0 < ‖(a : F)⁻¹‖ := by
          by_contra! h
          have h_nonneg : 0 ≤ ‖(a : F)⁻¹‖ := norm_nonneg _
          have hzero : ‖(a : F)⁻¹‖ = 0 := by linarith
          have h_inv_zero : (a : F)⁻¹ = 0 := norm_eq_zero.mp hzero
          have h_contra : (a : F) = 0 := inv_eq_zero.mp h_inv_zero
          exact ha_ne_zero h_contra
        calc
          ‖(a : F)‖ * ‖(a : F)⁻¹‖ < 1 * ‖(a : F)⁻¹‖ :=
            mul_lt_mul_of_pos_right hnorm hpos
          _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hnorm_inv_le_one (by norm_num)
          _ = 1 := by norm_num
      have : (1 : ℝ) < (1 : ℝ) := by
        calc
          (1 : ℝ) = ‖(a : F)‖ * ‖(a : F)⁻¹‖ := h_norm_mul
          _ < (1 : ℝ) := h_lt
      exact lt_irrefl _ this
  constructor
  · intro h
    have hsub : IsLocalRing.residue O (x - y) = 0 := by
      rw [map_sub, h, sub_self]
    rw [IsLocalRing.residue_eq_zero_iff] at hsub
    rw [ValuationSubring.valuation_lt_one_iff] at hsub
    exact (h_val_lt_one_iff_norm_lt_one (x - y)).mp hsub
  · intro h
    have h_norm_lt_one : ‖((x - y : O) : F)‖ < 1 := by simpa using h
    have hval : O.valuation ((x - y : O) : F) < 1 :=
      (h_val_lt_one_iff_norm_lt_one (x - y)).mpr h_norm_lt_one
    have hmem : (x - y : O) ∈ IsLocalRing.maximalIdeal O := by
      rwa [← ValuationSubring.valuation_lt_one_iff O (x - y)] at hval
    have hzero : IsLocalRing.residue O (x - y) = 0 := by
      rwa [IsLocalRing.residue_eq_zero_iff]
    have h_eq : IsLocalRing.residue O x - IsLocalRing.residue O y = 0 := by
      rw [← map_sub (IsLocalRing.residue O) x y, hzero]
    exact sub_eq_zero.mp h_eq

/-- Residue field `𝔽₂`: every integral element is `0` or `1` modulo `𝔪`. -/
theorem res_F2 {F : Type*} [NormedField F] [IsUltrametricDist F] (O : ValuationSubring F) (hO : ∀ x : F, x ∈ O ↔ ‖x‖ ≤ 1)
    (hcard : Nat.card (IsLocalRing.ResidueField O) = 2) :
    ∀ y : F, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1 := by
  classical
  intro y hy
  have hyO : y ∈ O := (hO y).mpr hy
  -- The residue field has exactly 2 elements, so it's finite
  have hfinite : Finite (IsLocalRing.ResidueField O) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype (IsLocalRing.ResidueField O) := Fintype.ofFinite _
  have hcard' : Fintype.card (IsLocalRing.ResidueField O) ≤ 2 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  -- In a ring with at most 2 elements, the universal set is {0, 1}
  have huniv : (Finset.univ : Finset (IsLocalRing.ResidueField O)) = {0, 1} :=
    Finset.univ_of_card_le_two hcard'
  -- The residue of y is in the universal set
  have hmem : IsLocalRing.residue O ⟨y, hyO⟩ ∈ (Finset.univ : Finset (IsLocalRing.ResidueField O)) := by
    simp
  rw [huniv] at hmem
  have hcases : IsLocalRing.residue O ⟨y, hyO⟩ = (0 : IsLocalRing.ResidueField O) ∨
      IsLocalRing.residue O ⟨y, hyO⟩ = (1 : IsLocalRing.ResidueField O) := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hcases with (h | h)
  · -- residue = 0, so ‖y - 0‖ < 1
    left
    have := (vs_residue_eq_iff O hO ⟨y, hyO⟩ 0).mp ?_
    · simpa [sub_zero] using this
    · simpa using h
  · -- residue = 1, so ‖y - 1‖ < 1
    right
    have := (vs_residue_eq_iff O hO ⟨y, hyO⟩ 1).mp ?_
    · simpa using this
    · simpa using h

/-- Residue field `𝔽₄` with `ω̄ ^ 2 + ω̄ + 1 = 0`: every integral element is `a + b ω` modulo `𝔪`. -/
theorem res_F4 {F : Type*} [NormedField F] [IsUltrametricDist F] (O : ValuationSubring F) (hO : ∀ x : F, x ∈ O ↔ ‖x‖ ≤ 1)
    (hcard : Nat.card (IsLocalRing.ResidueField O) = 4) {ω : F} (hω : ‖ω‖ ≤ 1)
    (hω2 : ‖ω ^ 2 + ω + 1‖ < 1) :
    ∀ y : F, ‖y‖ ≤ 1 → ∃ a b : ZMod 2, ‖y - ((a.val : F) + (b.val : F) * ω)‖ < 1 := by
  classical
  let k := IsLocalRing.ResidueField O
  -- k is finite with cardinality 4
  have hfinite : Finite k := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hfintype : Fintype k := Fintype.ofFinite k
  have hcard_fin : Fintype.card k = 4 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  -- In k, 4 = 0 (by FiniteField.cast_card_eq_zero)
  have h4zero : (4 : k) = 0 := by
    have := FiniteField.cast_card_eq_zero k
    rw [hcard_fin] at this
    exact this
  -- Hence 2 = 0 in k (since 2*2 = 4 = 0 in a field)
  have h2zero : (2 : k) = 0 := by
    have hsq : (2 : k) * (2 : k) = (4 : k) := by norm_num
    have hzero : (2 : k) * (2 : k) = 0 := by rw [hsq, h4zero]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hzero with h | h
    · exact h
    · exact h
  -- Hence 1 + 1 = 0 in k
  have h_one_add_one : (1 : k) + 1 = 0 := by
    have : (2 : k) = (1 : k) + 1 := by norm_num
    rw [this] at h2zero
    exact h2zero
  -- Let o = residue of ω in k
  have hωO : ω ∈ O := (hO ω).mpr hω
  let o := IsLocalRing.residue O (⟨ω, hωO⟩ : O)
  -- o satisfies o^2 + o + 1 = 0
  have ho_eq : o ^ 2 + o + 1 = 0 := by
    have hmem : ω ^ 2 + ω + 1 ∈ O := (hO (ω ^ 2 + ω + 1)).mpr (by linarith)
    let x : O := ⟨ω ^ 2 + ω + 1, hmem⟩
    have hx_norm_lt_one : ‖(x : F)‖ < 1 := by simpa using hω2
    have hx_mem_max : x ∈ IsLocalRing.maximalIdeal O :=
      ((vs_mem_maximalIdeal_iff O hO x).mpr hx_norm_lt_one)
    have hx_res_zero : IsLocalRing.residue O x = 0 :=
      (IsLocalRing.residue_eq_zero_iff x).mpr hx_mem_max
    -- Now compute: residue O x = (residue O ω)^2 + residue O ω + 1 = o^2 + o + 1
    let a : O := ⟨ω, hωO⟩
    have hx_eq : x = a ^ 2 + a + 1 := by
      dsimp [x, a]
      ext
      simp
    rw [hx_eq] at hx_res_zero
    simp at hx_res_zero
    dsimp [o, a] at *
    exact hx_res_zero
  -- Distinctness lemmas
  have ho_ne_zero : o ≠ 0 := by
    intro h
    have hcalc : o ^ 2 + o + 1 = 1 := by simp [h]
    rw [ho_eq] at hcalc
    norm_num at hcalc
  have ho_ne_one : o ≠ 1 := by
    intro h
    have hcalc : o ^ 2 + o + 1 = 1 + 1 + 1 := by simp [h]
    rw [hcalc] at ho_eq
    rw [h_one_add_one] at ho_eq
    -- ho_eq: 0 + 1 = 0 → 1 = 0
    have : (1 : k) ≠ 0 := by norm_num
    apply this
    -- simplify 0 + 1 = 0 to 1 = 0
    simpa using ho_eq
  have ho_add_one_ne_zero : o + 1 ≠ 0 := by
    intro h
    have ho_eq_one : o = 1 := by
      have h_one_eq_neg_one : (1 : k) = -1 :=
        eq_neg_of_add_eq_zero_left h_one_add_one
      have h_one_eq_neg_o : (1 : k) = -o :=
        eq_neg_of_add_eq_zero_right h
      have h_neg_o_eq_neg_one : -o = -1 :=
        calc
          -o = (1 : k) := Eq.symm h_one_eq_neg_o
          _ = -1 := h_one_eq_neg_one
      exact (neg_inj (a := o) (b := 1)).mp h_neg_o_eq_neg_one
    exact ho_ne_one ho_eq_one
  have ho_add_one_ne_one : o + 1 ≠ 1 := by
    intro h
    have ho_eq_zero : o = 0 := by
      -- o + 1 = 1 → o = 0 (subtract 1 from both sides)
      -- Using add_right_cancel: a + b = c + b → a = c
      -- We have o + 1 = 1, and 1 = 0 + 1
      -- So o + 1 = 0 + 1 → o = 0
      have : o + 1 = 0 + 1 := by
        rw [h, zero_add]
      exact add_right_cancel this
    exact ho_ne_zero ho_eq_zero
  have ho_add_one_ne_o : o + 1 ≠ o := by
    intro h
    have : (1 : k) = 0 := by
      -- o + 1 = o → 1 = 0 (subtract o from both sides)
      -- Using add_left_cancel: a + b = a + c → b = c
      -- We have o + 1 = o, and o = o + 0
      -- So o + 1 = o + 0 → 1 = 0
      have : o + 1 = o + 0 := by
        rw [h, add_zero]
      exact add_left_cancel this
    norm_num at this
  -- The set {0, 1, o, o+1} has cardinality 4
  let s : Finset k := {0, 1, o, o + 1}
  have hs_card : s.card = 4 := by
    have h0_not_mem : (0 : k) ∉ ({1, o, o + 1} : Finset k) := by
      simp [ho_ne_zero.symm, ho_add_one_ne_zero.symm, show (0 : k) ≠ 1 from by norm_num]
    have h1_not_mem : (1 : k) ∉ ({o, o + 1} : Finset k) := by
      simp [ho_ne_one.symm, ho_add_one_ne_one.symm]
    have ho_not_mem : o ∉ ({o + 1} : Finset k) := by
      simp
    have hcard0 : ({0, 1, o, o + 1} : Finset k).card = ({1, o, o + 1} : Finset k).card + 1 :=
      Finset.card_insert_of_notMem h0_not_mem
    have hcard1 : ({1, o, o + 1} : Finset k).card = ({o, o + 1} : Finset k).card + 1 :=
      Finset.card_insert_of_notMem h1_not_mem
    have hcard2 : ({o, o + 1} : Finset k).card = ({o + 1} : Finset k).card + 1 :=
      Finset.card_insert_of_notMem ho_not_mem
    have hcard3 : ({o + 1} : Finset k).card = 1 := by simp
    dsimp [s]
    calc
      ({0, 1, o, o + 1} : Finset k).card = ({1, o, o + 1} : Finset k).card + 1 := hcard0
      _ = ({o, o + 1} : Finset k).card + 2 := by rw [hcard1]
      _ = ({o + 1} : Finset k).card + 3 := by rw [hcard2]
      _ = 1 + 3 := by rw [hcard3]
      _ = 4 := by norm_num
  have huniv : s = Finset.univ :=
    Finset.eq_univ_of_card s (by rw [hs_card, hcard_fin])
  -- Now prove the main statement
  intro y hy
  have hyO : y ∈ O := (hO y).mpr hy
  let y' : O := ⟨y, hyO⟩
  -- The residue of y is in s = univ
  have hmem : IsLocalRing.residue O y' ∈ s := by
    rw [huniv]
    exact Finset.mem_univ _
  -- Case analysis on which element of s the residue equals
  rcases Finset.mem_insert.mp hmem with (h | h)
  · -- residue y = 0
    have hres : IsLocalRing.residue O y' = 0 := by simpa using h
    have hy_mem_max : y' ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      exact hres
    have hy_norm_lt_one : ‖(y' : F)‖ < 1 :=
      ((vs_mem_maximalIdeal_iff O hO y').mp hy_mem_max)
    refine ⟨0, 0, ?_⟩
    simpa [ZMod.val_zero] using hy_norm_lt_one
  · rcases Finset.mem_insert.mp h with (h | h)
    · -- residue y = 1
      have hres : IsLocalRing.residue O y' = 1 := by simpa using h
      have h1O : (1 : F) ∈ O := by
        rw [hO]
        norm_num
      let z : O := ⟨1, h1O⟩
      have hz_eq : z = (1 : O) := by ext; rfl
      have hz_res : IsLocalRing.residue O z = 1 := by
        rw [hz_eq]
        simp
      have h_eq : IsLocalRing.residue O y' = IsLocalRing.residue O z := by rw [hres, hz_res]
      have h_norm : ‖(y' : F) - (z : F)‖ < 1 :=
        ((vs_residue_eq_iff O hO y' z).mp h_eq)
      refine ⟨1, 0, ?_⟩
      simpa [z, ZMod.val_one, ZMod.val_zero] using h_norm
    · rcases Finset.mem_insert.mp h with (h | h)
      · -- residue y = o
        have hres : IsLocalRing.residue O y' = o := by simpa using h
        let z : O := ⟨ω, hωO⟩
        have hz_res : IsLocalRing.residue O z = o := rfl
        have h_eq : IsLocalRing.residue O y' = IsLocalRing.residue O z := by rw [hres, hz_res]
        have h_norm : ‖(y' : F) - (z : F)‖ < 1 :=
          ((vs_residue_eq_iff O hO y' z).mp h_eq)
        refine ⟨0, 1, ?_⟩
        simpa [z, ZMod.val_one, ZMod.val_zero] using h_norm
      · -- residue y = o + 1
        have hres : IsLocalRing.residue O y' = o + 1 := by simpa using h
        have hzO : (1 : F) + ω ∈ O := by
          rw [hO]
          calc
            ‖(1 : F) + ω‖ ≤ max ‖(1 : F)‖ ‖ω‖ := IsUltrametricDist.norm_add_le_max _ _
            _ ≤ max 1 1 := by
              refine max_le_max ?_ hω
              norm_num
            _ = 1 := by norm_num
        let z : O := ⟨(1 : F) + ω, hzO⟩
        let a : O := ⟨ω, hωO⟩
        have hz_eq : z = (1 : O) + a := by
          dsimp [z, a]
          ext
          simp
        -- residue of (1 + ω) = residue 1 + residue ω = 1 + o = o + 1
        have hz_res : IsLocalRing.residue O z = o + 1 := by
          rw [hz_eq]
          -- IsLocalRing.residue is a ring homomorphism
          -- residue (1 + a) = residue 1 + residue a = 1 + residue a
          -- And residue a = o, and 1 + o = o + 1 by add_comm
          dsimp [a, o]
          simp [add_comm]
        have h_eq : IsLocalRing.residue O y' = IsLocalRing.residue O z := by rw [hres, hz_res]
        have h_norm : ‖(y' : F) - (z : F)‖ < 1 :=
          ((vs_residue_eq_iff O hO y' z).mp h_eq)
        refine ⟨1, 1, ?_⟩
        simpa [z, ZMod.val_one, ZMod.val_zero] using h_norm

/-- Fermat congruence for a residue field of cardinality `2 N + 1`. -/
theorem res_fermat {F : Type*} [NormedField F] [IsUltrametricDist F] (O : ValuationSubring F) (hO : ∀ x : F, x ∈ O ↔ ‖x‖ ≤ 1) {N : ℕ}
    (hcard : Nat.card (IsLocalRing.ResidueField O) = 2 * N + 1) :
    ∀ ξ : F, ‖ξ‖ = 1 → ‖ξ ^ (2 * N) - 1‖ < 1 := by
  intro ξ hξ
  have hξ_le : ‖ξ‖ ≤ 1 := by
    rw [hξ]
  have hξ_mem_O : ξ ∈ O := ((hO ξ).mpr hξ_le)
  have hξ_not_maximal : (⟨ξ, hξ_mem_O⟩ : O) ∉ IsLocalRing.maximalIdeal O := by
    intro h
    have hlt := ((vs_mem_maximalIdeal_iff O hO ⟨ξ, hξ_mem_O⟩).mp h)
    rw [hξ] at hlt
    exact lt_irrefl _ hlt
  have h_residue_ne_zero : (IsLocalRing.residue O) (⟨ξ, hξ_mem_O⟩ : O) ≠ 0 :=
    mt (IsLocalRing.residue_eq_zero_iff _).mp hξ_not_maximal
  have h_fin : Finite (IsLocalRing.ResidueField O) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    omega
  haveI : Fintype (IsLocalRing.ResidueField O) := Fintype.ofFinite _
  have h_card : Fintype.card (IsLocalRing.ResidueField O) = 2 * N + 1 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  have h_card_sub_one : Fintype.card (IsLocalRing.ResidueField O) - 1 = 2 * N := by
    rw [h_card]
    omega
  have h_pow_card_sub_one : (IsLocalRing.residue O) (⟨ξ, hξ_mem_O⟩ : O) ^ (Fintype.card (IsLocalRing.ResidueField O) - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ h_residue_ne_zero
  have h_pow_eq_one : (IsLocalRing.residue O) (⟨ξ, hξ_mem_O⟩ : O) ^ (2 * N) = 1 := by
    rw [← h_card_sub_one, h_pow_card_sub_one]
  have h_residue_pow_eq_one : (IsLocalRing.residue O) ((⟨ξ, hξ_mem_O⟩ : O) ^ (2 * N)) = (IsLocalRing.residue O) 1 := by
    calc
      (IsLocalRing.residue O) ((⟨ξ, hξ_mem_O⟩ : O) ^ (2 * N))
          = ((IsLocalRing.residue O) (⟨ξ, hξ_mem_O⟩ : O)) ^ (2 * N) := by rw [map_pow]
      _ = 1 := h_pow_eq_one
      _ = (IsLocalRing.residue O) 1 := by rw [map_one]
  have h_result := ((vs_residue_eq_iff O hO ((⟨ξ, hξ_mem_O⟩ : O) ^ (2 * N)) 1).mp h_residue_pow_eq_one)
  simpa using h_result

/-- Euler's criterion for a residue field of odd cardinality `2 N + 1`. -/
theorem res_euler {F : Type*} [NormedField F] [IsUltrametricDist F] (O : ValuationSubring F) (hO : ∀ x : F, x ∈ O ↔ ‖x‖ ≤ 1) {N : ℕ}
    (hcard : Nat.card (IsLocalRing.ResidueField O) = 2 * N + 1) :
    ∀ ξ : F, ‖ξ‖ = 1 → ‖ξ ^ N - 1‖ < 1 → ∃ s : F, ‖ξ - s ^ 2‖ < 1 := by
  let k := IsLocalRing.ResidueField O
  -- The residue field is finite since Nat.card k = 2*N+1 ≠ 0
  have hk_finite : Finite k := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    omega
  have hk_fintype : Fintype k := Fintype.ofFinite k
  -- From hcard, Fintype.card k = 2*N+1
  have hcard_fin : Fintype.card k = 2 * N + 1 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  -- Since 2*N+1 is odd, ringChar k ≠ 2
  have hchar_ne_two : ringChar k ≠ 2 := by
    intro hchar_eq_two
    have h_even : Fintype.card k % 2 = 0 := FiniteField.even_card_of_char_two hchar_eq_two
    rw [hcard_fin] at h_even
    have h_mod : (2 * N + 1) % 2 = 1 := by omega
    rw [h_mod] at h_even
    omega
  -- Also compute Fintype.card k / 2 = N
  have hcard_div_two : Fintype.card k / 2 = N := by
    rw [hcard_fin]
    omega
  intro ξ hξ_norm hξ_pow
  -- ξ ∈ O since ‖ξ‖ = 1 ≤ 1
  have hξO : ξ ∈ O := by
    rw [hO]
    exact le_of_eq hξ_norm
  let x : O := ⟨ξ, hξO⟩
  -- The residue of x is nonzero
  have hres_ne_zero : IsLocalRing.residue O x ≠ 0 := by
    intro hzero
    have hmem := (IsLocalRing.residue_eq_zero_iff _).mp hzero
    have hmem' := (vs_mem_maximalIdeal_iff O hO x).mp hmem
    -- hmem' : ‖(x : F)‖ < 1, but ‖(x : F)‖ = ‖ξ‖ = 1
    rw [hξ_norm] at hmem'
    exact lt_irrefl _ hmem'
  -- ξ^N - 1 ∈ O since ‖ξ^N - 1‖ < 1 ≤ 1
  have h_pow_sub_one_O : ξ ^ N - 1 ∈ O := by
    rw [hO]
    exact le_of_lt hξ_pow
  let y : O := ⟨ξ ^ N - 1, h_pow_sub_one_O⟩
  -- residue(y) = 0, i.e., residue(x)^N = 1
  have hres_pow_eq_one : (IsLocalRing.residue O x) ^ N = 1 := by
    have hy_res_zero : IsLocalRing.residue O y = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]
      rw [vs_mem_maximalIdeal_iff O hO y]
      simpa [y] using hξ_pow
    -- Compute residue(y) in terms of residue(x)
    -- y = x^N - 1 in O (they have the same image in F)
    have hy_eq : (y : F) = (x : F) ^ N - 1 := by
      simp [y, x]
    -- Since residue is a ring homomorphism and y = x^N - 1 in O:
    have hy_res_eq : IsLocalRing.residue O y = (IsLocalRing.residue O x) ^ N - 1 := by
      -- First show equality in O, then apply residue
      have hy_eq_O : y = x ^ N - 1 := by
        ext; simpa [y, x] using rfl
      simpa [hy_eq_O, map_sub, map_pow, map_one]
    rw [hy_res_eq] at hy_res_zero
    -- Now hy_res_zero: (residue x)^N - 1 = 0, so (residue x)^N = 1
    exact sub_eq_zero.mp hy_res_zero
  -- By Euler's criterion, residue(x) is a square
  have h_square : IsSquare (IsLocalRing.residue O x) := by
    rw [FiniteField.isSquare_iff hchar_ne_two hres_ne_zero, hcard_div_two]
    exact hres_pow_eq_one
  -- So there exists t : k such that t * t = residue(x)
  rcases h_square with ⟨t, ht⟩
  -- residue is surjective, so lift t to s' : O
  have h_surj : Function.Surjective (IsLocalRing.residue O) := IsLocalRing.residue_surjective
  rcases h_surj t with ⟨s', hs'⟩
  -- Let s be the coercion of s' to F
  let s : F := (s' : F)
  use s
  -- Need to show ‖ξ - s^2‖ < 1
  -- Using vs_residue_eq_iff, it suffices to show residue(x) = residue(s'^2)
  have h_eq_res : IsLocalRing.residue O x = IsLocalRing.residue O (s' ^ 2) := by
    calc
      IsLocalRing.residue O x = t * t := ht
      _ = (IsLocalRing.residue O s') * (IsLocalRing.residue O s') := by rw [hs']
      _ = IsLocalRing.residue O (s' * s') := by rw [map_mul]
      _ = IsLocalRing.residue O (s' ^ 2) := by ring
  -- Now apply vs_residue_eq_iff
  simpa [x, s] using ((vs_residue_eq_iff O hO x (s' ^ 2)).mp h_eq_res)


/-- A unit with nonsquare residue, for a residue field of odd cardinality `2 N + 1`. -/
theorem res_nonsq {F : Type*} [NormedField F] [IsUltrametricDist F] (O : ValuationSubring F) (hO : ∀ x : F, x ∈ O ↔ ‖x‖ ≤ 1) {N : ℕ}
    (hcard : Nat.card (IsLocalRing.ResidueField O) = 2 * N + 1) :
    ∃ u : F, ‖u‖ = 1 ∧ ‖u ^ N + 1‖ < 1 := by
  set k := IsLocalRing.ResidueField O
  have hcard_pos : Nat.card k ≠ 0 := by
    rw [hcard]
    omega
  have hfinite : Finite k := Nat.finite_of_card_ne_zero hcard_pos
  have hfintype : Fintype k := Fintype.ofFinite k
  have hcard_fintype : Fintype.card k = 2 * N + 1 := by
    rw [← Nat.card_eq_fintype_card, hcard]
  have hchar_ne_two : ringChar k ≠ 2 := by
    intro hchar
    have h_even : Fintype.card k % 2 = 0 := FiniteField.even_card_of_char_two hchar
    rw [hcard_fintype] at h_even
    omega
  rcases FiniteField.exists_nonsquare hchar_ne_two with ⟨r, hr_nonsq⟩
  have hr_ne_zero : r ≠ 0 := by
    intro hzero
    apply hr_nonsq
    rw [hzero]
    exact ⟨0, by simp⟩
  have hcard_div_two : Fintype.card k / 2 = N := by
    rw [hcard_fintype]
    omega
  have h_pow_N_ne_one : r ^ N ≠ 1 := by
    rw [← hcard_div_two]
    have h_sq_iff := FiniteField.isSquare_iff hchar_ne_two hr_ne_zero
    rcases h_sq_iff with ⟨h_forward, h_backward⟩
    intro h_eq
    apply hr_nonsq
    apply h_backward
    exact h_eq
  have h_pow_card_sub_one : r ^ (Fintype.card k - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one r hr_ne_zero
  have h_pow_two_N : r ^ (2 * N) = 1 := by
    have : Fintype.card k - 1 = 2 * N := by
      rw [hcard_fintype]
      omega
    rw [this] at h_pow_card_sub_one
    exact h_pow_card_sub_one
  have h_pow_N_sq : (r ^ N) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, h_pow_two_N]
  have h_pow_N_eq_neg_one : r ^ N = -1 := by
    have h_sq_eq_one : (r ^ N) ^ 2 = 1 ^ 2 := by
      rw [h_pow_N_sq, one_pow]
    have h_eq_or : r ^ N = 1 ∨ r ^ N = -1 := by
      apply eq_or_eq_neg_of_sq_eq_sq _ _ h_sq_eq_one
    rcases h_eq_or with (h | h)
    · exact absurd h h_pow_N_ne_one
    · exact h
  -- Lift r to O
  have h_surj : Function.Surjective (IsLocalRing.residue O) := IsLocalRing.residue_surjective
  rcases h_surj r with ⟨u', hu'⟩
  set u := (u' : F) with hu_def
  have h_residue_u : IsLocalRing.residue O u' = r := hu'
  have hu_ne_zero : u ≠ 0 := by
    intro hzero
    apply hr_ne_zero
    have hzero_res : IsLocalRing.residue O (0 : O) = 0 := by simp
    have hu'_zero : u' = (0 : O) := Subtype.ext hzero
    rw [hu'_zero, hzero_res] at h_residue_u
    exact h_residue_u.symm
  have h_isUnit : IsUnit u' := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    rw [h_residue_u]
    exact hr_ne_zero
  have hu_norm_eq_one : ‖u‖ = 1 := by
    have h_mem_O : u ∈ (O : Set F) := by
      rw [hu_def]
      exact SetLike.coe_mem u'
    have h_norm_le_one : ‖u‖ ≤ 1 := by
      rw [← hO u]
      exact h_mem_O
    -- Since u' is a unit in O, its inverse is also in O
    rcases h_isUnit.exists_right_inv with ⟨v, hv⟩
    -- hv : u' * v = 1 in O
    have hv_mem_O : (v : F) ∈ (O : Set F) := SetLike.coe_mem v
    have hv_eq_inv : (v : F) = u⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      calc
        (v : F) * u = (v : F) * (u' : F) := rfl
        _ = ((v * u' : O) : F) := by simp
        _ = ((u' * v : O) : F) := by simp [mul_comm]
        _ = ((1 : O) : F) := by rw [hv]
        _ = 1 := by simp
    rw [hv_eq_inv] at hv_mem_O
    have h_norm_inv_le_one : ‖u⁻¹‖ ≤ 1 := by
      rw [← hO (u⁻¹)]
      exact hv_mem_O
    have h_norm_inv_eq : ‖u⁻¹‖ = ‖u‖⁻¹ := norm_inv u
    rw [h_norm_inv_eq] at h_norm_inv_le_one
    have hu_norm_pos : 0 < ‖u‖ :=
      (norm_pos_iff.mpr hu_ne_zero)
    have h_one_le_norm : 1 ≤ ‖u‖ :=
      ((inv_le_one₀ hu_norm_pos).mp h_norm_inv_le_one)
    exact le_antisymm h_norm_le_one h_one_le_norm
  have hu_pow_N_add_one_residue_eq_zero : IsLocalRing.residue O (u' ^ N + 1) = 0 := by
    calc
      IsLocalRing.residue O (u' ^ N + 1) = (IsLocalRing.residue O u') ^ N + IsLocalRing.residue O 1 := by
        simp [map_add, map_pow]
      _ = r ^ N + 1 := by
        simp [h_residue_u]
      _ = (-1) + 1 := by rw [h_pow_N_eq_neg_one]
      _ = 0 := by simp
  have hu_pow_N_add_one_mem_maximalIdeal : (u' ^ N + 1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact hu_pow_N_add_one_residue_eq_zero
  have h_norm_lt_one : ‖u ^ N + 1‖ < 1 := by
    have h_mem : (u' ^ N + 1 : O) ∈ IsLocalRing.maximalIdeal O := hu_pow_N_add_one_mem_maximalIdeal
    have h_lt_one := ((vs_mem_maximalIdeal_iff O hO (u' ^ N + 1 : O)).mp h_mem)
    simpa [u] using h_lt_one
  exact ⟨u, hu_norm_eq_one, h_norm_lt_one⟩

end Residue

/-! ## Completions of number fields -/

section Adic

open IsDedekindDomain NumberField

/-! The residue field of a completion (adapted from `exists_valued_sub_lt_one` and
`residueFieldEquivAdicCompletionIntegers` of Toolbox/Stoll/Mathlib/AdicCompletionExtension.lean, a port of
https://github.com/MichaelStollBayreuth/EllipticCurves, Apache License 2.0; restated here on the vendored
copy FurioLombardo.M1.Vendor.Stoll.Basic, since the Toolbox and the M1 copies of Stoll's Basic cannot be
imported together). -/

/-- Every element of the ring of integers of the completion is congruent to an element of `R`
modulo the maximal ideal. -/
theorem adic_exists_valued_sub_lt_one {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R)
    (x : v.adicCompletionIntegers K) :
    ∃ a : R, Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a) < 1 := by
  have hball : {y | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) := by
    rw [Valued.mem_nhds]
    exact ⟨1, fun y hy ↦ by simpa using hy⟩
  obtain ⟨w, hwball, z, rfl⟩ :=
    mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap (K := K) v _) _ hball
  rw [Set.mem_ofPred_eq] at hwball
  have hz1 : v.valuation K z ≤ 1 := by
    rw [show v.valuation K z = Valued.v (algebraMap K (v.adicCompletion K) z) from
      (v.valuedAdicCompletion_eq_valuation' z).symm]
    calc Valued.v (algebraMap K (v.adicCompletion K) z)
        = Valued.v (algebraMap K (v.adicCompletion K) z - (x : v.adicCompletion K)
            + (x : v.adicCompletion K)) := by ring_nf
      _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) z - (x : v.adicCompletion K)))
            (Valued.v (x : v.adicCompletion K)) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hwball.le x.2
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hz1 1
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap K (v.adicCompletion K) z -
      algebraMap R (v.adicCompletion K) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub,
      show Valued.v (algebraMap K (v.adicCompletion K) (z - algebraMap R K a)) =
        v.valuation K (z - algebraMap R K a) from v.valuedAdicCompletion_eq_valuation' _,
      Valuation.map_sub_swap]
    simpa using ha
  calc Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a)
      = Valued.v (((x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) z)
          + (algebraMap K (v.adicCompletion K) z - algebraMap R (v.adicCompletion K) a)) := by
        ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < 1 := max_lt (by rwa [Valuation.map_sub_swap] at hwball) ha'

/-- The residue field of `v` maps isomorphically onto the residue field of the ring of integers of
the completion at `v`. -/
noncomputable def adicResidueEquiv {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) :
    (R ⧸ v.asIdeal) ≃+*
      (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  refine RingEquiv.ofBijective (Ideal.quotientMap (IsLocalRing.maximalIdeal _)
    (algebraMap R (v.adicCompletionIntegers K))
    (le_of_eq (v.comap_maximalIdeal_adicCompletionIntegers (K := K)).symm)) ⟨?_, ?_⟩
  · exact Ideal.quotientMap_injective'
      (le_of_eq (v.comap_maximalIdeal_adicCompletionIntegers (K := K)))
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := adic_exists_valued_sub_lt_one (K := K) v x
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk]
    refine (Ideal.Quotient.eq).mpr ?_
    refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
      (WithZero (Multiplicative ℤ))))).mpr ?_
    rw [show ((algebraMap R (v.adicCompletionIntegers K) a - x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = algebraMap R (v.adicCompletion K) a - (x : v.adicCompletion K)
      from rfl, Valuation.map_sub_swap]
    exact ha

theorem adic_mem_integers_iff {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : v.adicCompletion K) :
    x ∈ v.adicCompletionIntegers K ↔ ‖x‖ ≤ 1 := by
  rw [Valued.toNormedField.norm_le_one_iff, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]

/-- The completion is proper (complete, DVR integers, finite residue field). -/
theorem adic_properSpace {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : ProperSpace (v.adicCompletion K) := by
  rw [Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField]
  refine ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  · have h_finite_quotient : Finite (NumberField.RingOfIntegers K ⧸ v.asIdeal) :=
      Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    exact (adicResidueEquiv (K := K) v).toEquiv.finite_iff.mp h_finite_quotient

theorem adic_residue_card {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Nat.card (𝓞 K ⧸ v.asIdeal) := by
  exact Nat.card_congr (adicResidueEquiv (K := K) v).symm.toEquiv

/-- Norms of global elements from their valuations, for a global `ϖ` of valuation `exp (-1)`. -/
theorem adic_norm_coe {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1)) (x : K) (n : ℤ)
    (hx : v.valuation K x = WithZero.exp (-n)) :
    ‖(x : v.adicCompletion K)‖ = ‖(ϖ : v.adicCompletion K)‖ ^ n := by
  have h_val_x : Valued.v (x : v.adicCompletion K) = Valued.v ((ϖ : v.adicCompletion K) ^ n) := by
    calc
      Valued.v (x : v.adicCompletion K) = v.valuation K x := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
      _ = WithZero.exp (-n) := hx
      _ = (WithZero.exp (-1 : ℤ)) ^ n := by
        rw [← WithZero.exp_zsmul, show (n • (-1 : ℤ)) = -n by simp]
      _ = (v.valuation K ϖ) ^ n := by rw [hϖ]
      _ = Valued.v (ϖ : v.adicCompletion K) ^ n := by rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ϖ]
      _ = Valued.v ((ϖ : v.adicCompletion K) ^ n) := by rw [map_zpow₀]
  have h_norm_eq : ‖(x : v.adicCompletion K)‖ = ‖(ϖ : v.adicCompletion K) ^ n‖ := by
    have h_le_iff := Valued.toNormedField.norm_le_iff (x := (x : v.adicCompletion K)) (x' := (ϖ : v.adicCompletion K) ^ n)
    apply le_antisymm
    · rw [h_le_iff]
      rw [h_val_x]
    · have h_le_iff' := Valued.toNormedField.norm_le_iff (x := (ϖ : v.adicCompletion K) ^ n) (x' := (x : v.adicCompletion K))
      rw [h_le_iff']
      rw [h_val_x]
  calc
    ‖(x : v.adicCompletion K)‖ = ‖(ϖ : v.adicCompletion K) ^ n‖ := h_norm_eq
    _ = ‖(ϖ : v.adicCompletion K)‖ ^ n := by rw [norm_zpow]

theorem adic_norm_coe_lt {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1)) (x : K) (n : ℤ)
    (hx : v.valuation K x < WithZero.exp (-n)) :
    ‖(x : v.adicCompletion K)‖ < ‖(ϖ : v.adicCompletion K)‖ ^ n := by
  have h_val_x : Valued.v (x : v.adicCompletion K) = v.valuation K x :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) x
  have h_val_ϖ_pow : Valued.v (((ϖ : v.adicCompletion K)) ^ n) = WithZero.exp (-n) := by
    calc
      Valued.v (((ϖ : v.adicCompletion K)) ^ n) = (Valued.v (ϖ : v.adicCompletion K)) ^ n := by
        simpa using map_zpow₀ (Valued.v : v.adicCompletion K →*₀ WithZero (Multiplicative ℤ)) (ϖ : v.adicCompletion K) n
      _ = (v.valuation K ϖ) ^ n := by simpa using IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (ϖ : K)
      _ = (WithZero.exp (-1)) ^ n := by rw [hϖ]
      _ = WithZero.exp (n • (-1 : ℤ)) := by simpa using WithZero.exp_zsmul n (-1 : ℤ)
      _ = WithZero.exp (-n) := by simp
  rw [← norm_zpow]
  rw [Valued.toNormedField.norm_lt_iff]
  calc
    Valued.v (x : v.adicCompletion K) = v.valuation K x := h_val_x
    _ < WithZero.exp (-n) := hx
    _ = Valued.v (((ϖ : v.adicCompletion K)) ^ n) := by symm; exact h_val_ϖ_pow

/-- The image of a global element of valuation `exp (-1)` is a norm uniformizer. -/
theorem adic_normUnif {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {ϖ : K} (hϖ : v.valuation K ϖ = WithZero.exp (-1)) :
    NormUnif (ϖ : v.adicCompletion K) := by
  let π : v.adicCompletion K := (ϖ : v.adicCompletion K)
  have hπ_val : Valued.v π = WithZero.exp (-1) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ϖ, hϖ]
  have hlt : ‖π‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff]
    rw [hπ_val]
    simpa using WithZero.exp_lt_one_iff.mpr (by norm_num : (-1 : ℤ) < 0)
  have hπ_ne_zero : π ≠ 0 := by
    intro hzero
    have hval : Valued.v π = 0 := by simpa [hzero]
    rw [hπ_val] at hval
    have h := WithZero.exp_ne_zero (a := (-1 : ℤ))
    exact h hval
  refine {
    ne_zero := hπ_ne_zero
    norm_lt_one := hlt
    disc := ?_
  }
  · intro x hx0
    have hx_val_ne_zero : Valued.v x ≠ 0 :=
      mt (Valued.v.zero_iff.mp ·) hx0
    let m := WithZero.log (Valued.v x)
    have hx_val_eq : Valued.v x = WithZero.exp m := (WithZero.exp_log hx_val_ne_zero).symm
    have hx_val_mul : Valued.v (x * π ^ m) = 1 := by
      have h_map_zpow : Valued.v (π ^ m) = (Valued.v π) ^ m := by
        simpa using map_zpow (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))) π m
      calc
        Valued.v (x * π ^ m) = Valued.v x * Valued.v (π ^ m) := map_mul _ _ _
        _ = Valued.v x * (Valued.v π) ^ m := by rw [h_map_zpow]
        _ = WithZero.exp m * (WithZero.exp (-1)) ^ m := by rw [hx_val_eq, hπ_val]
        _ = WithZero.exp m * WithZero.exp (m • (-1 : ℤ)) := by rw [WithZero.exp_zsmul]
        _ = WithZero.exp (m + m • (-1 : ℤ)) := by rw [← WithZero.exp_add]
        _ = WithZero.exp 0 := by
          have : m + m • (-1 : ℤ) = 0 := by
            dsimp
            omega
          rw [this]
        _ = 1 := WithZero.exp_zero
    have hnorm_mul : ‖x * π ^ m‖ = 1 := by
      rw [Valued.toNormedField.norm_eq_one_iff]
      exact hx_val_mul
    have hnorm_mul' : ‖x * π ^ m‖ = ‖x‖ * ‖π ^ m‖ := norm_mul _ _
    have hnorm_pow : ‖π ^ m‖ = ‖π‖ ^ m := norm_zpow _ _
    rw [hnorm_mul', hnorm_pow] at hnorm_mul
    -- now hnorm_mul: ‖x‖ * ‖π‖ ^ m = 1
    refine ⟨-m, ?_⟩
    -- from ‖x‖ * ‖π‖ ^ m = 1, we get ‖x‖ = ‖π‖ ^ (-m)
    have hpos : ‖π‖ ^ m ≠ 0 := zpow_ne_zero _ (norm_ne_zero_iff.mpr hπ_ne_zero)
    calc
      ‖x‖ = (‖x‖ * ‖π‖ ^ m) * (‖π‖ ^ m)⁻¹ := by field_simp [hnorm_mul, hpos]
      _ = 1 * (‖π‖ ^ m)⁻¹ := by rw [hnorm_mul]
      _ = (‖π‖ ^ m)⁻¹ := by simp
      _ = ‖π‖ ^ (-m) := by simp [zpow_neg]


end Adic

end

end FurioLombardo.Discharge.SelmerBasis
