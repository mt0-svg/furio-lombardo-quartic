import Mathlib
import FurioLombardo.M1.Vendor.Stoll.FractionalIdeal
import FurioLombardo.Discharge.SelmerBasis.SchaeferAux

/-!
# Schaefer's unramifiedness lemma for the `x - T` map in genus 2, with no completion

`M` is a field with a valuation `v` (any linearly ordered value group), `f` of degree 6 with
`v`-integral coefficients and unit leading coefficient, `θ` a root of `f` with `f'(θ)` a unit,
`u` of degree 2, `V` of degree at most 1 and `V² - f = u w`, and `c` such that `c⁻¹ u` is
integral and primitive. Then `v(u(θ) / c)` is a square in the value group (`schaefer_local_sq`),
an even power in `ℤᵐ⁰` (`schaefer_local`), and at a height one prime `P` of a Dedekind domain the
multiplicity of `(u(θ) / c)` at `P` is even (`schaefer_count`).
-/

open Polynomial
open scoped nonZeroDivisors

namespace FurioLombardo.Discharge.SelmerBasis

namespace Schaefer

theorem lift_eval {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) {P : M[X]} {P₀ : v.valuationSubring[X]}
    (h : P₀.map (algebraMap v.valuationSubring M) = P) (x : v.valuationSubring) :
    P.eval (x : M) = ((P₀.eval x : v.valuationSubring) : M) := by
  rw [← h, eval_map, ← ValuationSubring.algebraMap_apply, eval₂_at_apply]; rfl

theorem lift_coeff {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) {P : M[X]} {P₀ : v.valuationSubring[X]}
    (h : P₀.map (algebraMap v.valuationSubring M) = P) (i : ℕ) :
    P.coeff i = ((P₀.coeff i : v.valuationSubring) : M) := by
  rw [← h, coeff_map]; rfl

theorem residue_ne_zero_of_val {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {x : v.valuationSubring}
    (hx : v (x : M) = 1) : IsLocalRing.residue v.valuationSubring x ≠ 0 :=
  (IsLocalRing.residue_ne_zero_iff_isUnit x).mpr
    ((Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one.mpr hx)

/-- The non-integral case: when `U W = z V² - e f` with `v z = 1`, `v e < 1`, all
integral, `U`, `W` primitive and both non-units at `θ`, the resultant `Res_{2,5}(U, f / (X - θ))`
is a unit. -/
theorem resultant_val_eq_one {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {f U W V : M[X]} {θ z e : M}
    (hf : ∀ i, v (f.coeff i) ≤ 1) (hdeg : f.natDegree = 6) (hl : v f.leadingCoeff = 1)
    (hθ : f.eval θ = 0) (hθ' : v (f.derivative.eval θ) = 1) (hθi : v θ ≤ 1)
    (hUi : ∀ i, v (U.coeff i) ≤ 1) (hU1 : ∃ i, v (U.coeff i) = 1) (hUdeg : U.natDegree = 2)
    (hWi : ∀ i, v (W.coeff i) ≤ 1) (hW1 : ∃ i, v (W.coeff i) = 1)
    (hVi : ∀ i, v (V.coeff i) ≤ 1) (hVdeg : V.natDegree ≤ 1)
    (hz : v z = 1) (he : v e < 1) (h : U * W = C z * V ^ 2 - C e * f)
    (hUlt : v (U.eval θ) < 1) (hWlt : v (W.eval θ) < 1) :
    v (resultant U (f /ₘ (X - C θ)) 2 5) = 1 := by
  classical
  obtain ⟨θ₀, rfl⟩ : ∃ θ₀ : v.valuationSubring, (θ₀ : M) = θ := ⟨⟨θ, hθi⟩, rfl⟩
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : v.valuationSubring, (z₀ : M) = z := ⟨⟨z, le_of_eq hz⟩, rfl⟩
  obtain ⟨e₀, rfl⟩ : ∃ e₀ : v.valuationSubring, (e₀ : M) = e := ⟨⟨e, he.le⟩, rfl⟩
  have hι : Function.Injective (algebraMap v.valuationSubring M) := fun a b hab => Subtype.ext hab
  obtain ⟨U₀, rfl⟩ := exists_lift v hUi
  obtain ⟨W₀, rfl⟩ := exists_lift v hWi
  obtain ⟨V₀, rfl⟩ := exists_lift v hVi
  obtain ⟨f₀, rfl⟩ := exists_lift v hf
  have hrel : U₀ * W₀ = C z₀ * V₀ ^ 2 - C e₀ * f₀ := by
    apply Polynomial.map_injective _ hι
    simpa only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      ValuationSubring.algebraMap_apply] using h
  have hg₀ : (f₀ /ₘ (X - C θ₀)).map (algebraMap v.valuationSubring M) =
      f₀.map (algebraMap v.valuationSubring M) /ₘ (X - C (θ₀ : M)) := by
    rw [map_divByMonic _ (monic_X_sub_C θ₀), Polynomial.map_sub, map_X, map_C]; rfl
  rw [← hg₀, resultant_map_map]
  refine (Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one.mp ?_
  refine (IsLocalRing.residue_ne_zero_iff_isUnit _).mp ?_
  rw [← resultant_map_map]
  have hf₀deg : f₀.natDegree = 6 := by
    rw [← natDegree_map_eq_of_injective hι f₀, hdeg]
  have hU₀deg : U₀.natDegree = 2 := by
    rw [← natDegree_map_eq_of_injective hι U₀, hUdeg]
  have hV₀deg : V₀.natDegree ≤ 1 := by
    rw [← natDegree_map_eq_of_injective hι V₀]; exact hVdeg
  have hevπ : ∀ (P₀ : v.valuationSubring[X]) (x : v.valuationSubring),
      (P₀.map (IsLocalRing.residue v.valuationSubring)).eval
        (IsLocalRing.residue v.valuationSubring x) =
      IsLocalRing.residue v.valuationSubring (P₀.eval x) := fun P₀ x => by
    rw [eval_map, eval₂_at_apply]
  have hθroot : f₀.map (algebraMap v.valuationSubring M) = (X - C (θ₀ : M)) *
      (f₀.map (algebraMap v.valuationSubring M) /ₘ (X - C (θ₀ : M))) :=
    (mul_divByMonic_eq_iff_isRoot.mpr hθ).symm
  apply resultant_ne_zero_of_sq (S := V₀.map (IsLocalRing.residue v.valuationSubring))
    (Q := W₀.map (IsLocalRing.residue v.valuationSubring))
    (t := IsLocalRing.residue v.valuationSubring θ₀)
    (z := IsLocalRing.residue v.valuationSubring z₀)
  · obtain ⟨i, hi⟩ := hU1
    exact map_residue_ne_zero v ⟨i, by rw [← lift_coeff v rfl]; exact hi⟩
  · obtain ⟨i, hi⟩ := hW1
    exact map_residue_ne_zero v ⟨i, by rw [← lift_coeff v rfl]; exact hi⟩
  · exact natDegree_map_le.trans hV₀deg
  · have he₀ : IsLocalRing.residue v.valuationSubring e₀ = 0 := (residue_eq_zero_iff v e₀).mpr he
    rw [← Polynomial.map_mul, hrel]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, he₀,
      map_zero, zero_mul, sub_zero]
  · rw [hevπ]
    exact (residue_eq_zero_iff v _).mpr (by rw [← lift_eval v rfl]; exact hUlt)
  · rw [hevπ]
    exact (residue_eq_zero_iff v _).mpr (by rw [← lift_eval v rfl]; exact hWlt)
  · exact natDegree_map_le.trans hU₀deg.le
  · have hf₀0 : f₀ ≠ 0 := by
      rintro h0; rw [h0, natDegree_zero] at hf₀deg; exact absurd hf₀deg (by norm_num)
    have hg₀deg : (f₀ /ₘ (X - C θ₀)).natDegree = 5 := by
      rw [natDegree_divByMonic f₀ (monic_X_sub_C θ₀), hf₀deg, natDegree_X_sub_C]
    have hdeg0 : f₀.degree ≠ 0 := by
      rw [degree_eq_natDegree hf₀0, hf₀deg]; decide
    rw [natDegree_map_of_leadingCoeff_ne_zero, hg₀deg]
    rw [leadingCoeff_divByMonic_X_sub_C f₀ hdeg0 θ₀]
    apply residue_ne_zero_of_val v
    rw [← ValuationSubring.algebraMap_apply, ← leadingCoeff_map_of_injective hι]
    exact hl
  · rw [hevπ]
    apply residue_ne_zero_of_val v
    rw [← lift_eval v hg₀, eval_eq_derivative_eval hθroot]
    exact hθ'


end Schaefer

/-- **Schaefer's lemma, value group form.** -/
theorem schaefer_local_sq {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀)
    {f u V w : M[X]} {θ c : M}
    (hf : ∀ i, v (f.coeff i) ≤ 1) (hdeg : f.natDegree = 6) (hl : v f.leadingCoeff = 1)
    (hθ : f.eval θ = 0) (hθ' : v (f.derivative.eval θ) = 1)
    (hu2 : u.natDegree = 2) (hV : V.natDegree ≤ 1) (hw : V ^ 2 - f = u * w)
    (hU : ∀ i, v (u.coeff i / c) ≤ 1) (hprim : ∃ i, v (u.coeff i / c) = 1) :
    ∃ y : M, v (u.eval θ / c) = v y ^ 2 := by
  classical
  have hc : c ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hprim
    simp at hi
  set U : M[X] := C c⁻¹ * u with hUdef
  have hUc : ∀ i, U.coeff i = u.coeff i / c := fun i => by
    rw [hUdef, coeff_C_mul, div_eq_inv_mul]
  have hUi : ∀ i, v (U.coeff i) ≤ 1 := fun i => by rw [hUc]; exact hU i
  have hU1 : ∃ i, v (U.coeff i) = 1 := by
    obtain ⟨i, hi⟩ := hprim
    exact ⟨i, by rw [hUc]; exact hi⟩
  have hUdeg : U.natDegree = 2 := by rw [hUdef, natDegree_C_mul (inv_ne_zero hc)]; exact hu2
  have hUθ : U.eval θ = u.eval θ / c := by rw [hUdef, eval_mul, eval_C, div_eq_inv_mul]
  rw [← hUθ]
  set W : M[X] := C c * w with hWdef
  have hUW : V ^ 2 - f = U * W := by
    rw [hw, hUdef, hWdef, show C c⁻¹ * u * (C c * w) = C (c⁻¹ * c) * (u * w) by
      rw [C_mul]; ring, inv_mul_cancel₀ hc, C_1, one_mul]
  clear_value U W
  have hθi : v θ ≤ 1 := Schaefer.root_le_one v hf hl (by omega) hθ
  have hW4 : W.natDegree = 4 := Schaefer.natDegree_eq_four hUdeg hV hdeg hUW
  have hW0 : W ≠ 0 := by
    rintro h0
    rw [h0, natDegree_zero] at hW4
    omega
  obtain ⟨a, ha0, W', hWa, hW'i, hW'1⟩ := Schaefer.exists_primitive v hW0
  have hA : U.eval θ * (a * W'.eval θ) = V.eval θ ^ 2 := by
    have h1 := congrArg (eval θ) hUW
    rw [eval_sub, eval_pow, hθ, sub_zero, eval_mul, hWa, eval_mul, eval_C] at h1
    exact h1.symm
  have hUWi : ∀ i, v ((U * W').coeff i) ≤ 1 := Schaefer.integral_mul v hUi hW'i
  have hUW1 : ∃ i, v ((U * W').coeff i) = 1 := Schaefer.primitive_mul v hUi hW'i hU1 hW'1
  have hUθi : v (U.eval θ) ≤ 1 := Schaefer.eval_le_one v hUi hθi
  have hW'θi : v (W'.eval θ) ≤ 1 := Schaefer.eval_le_one v hW'i hθi
  have hva0 : v a ≠ 0 := (Valuation.ne_zero_iff v).mpr ha0
  by_cases hVi : ∀ i, v (V.coeff i) ≤ 1
  · -- `V` integral: `v a = 1`
    obtain ⟨hPi, hP1⟩ := Schaefer.sq_sub_primitive v hVi hV hf hdeg hl
    have hUW' : C a⁻¹ * (V ^ 2 - f) = U * W' := by
      rw [hUW, hWa, show U * (C a * W') = C a * (U * W') by ring, ← mul_assoc, ← C_mul,
        inv_mul_cancel₀ ha0, C_1, one_mul]
    have h1 : v a⁻¹ = 1 := Schaefer.val_eq_one_of_primitive v hPi hP1
      (by rw [hUW']; exact hUWi) (by rw [hUW']; exact hUW1)
    have hva : v a = 1 := by rw [map_inv₀] at h1; exact inv_eq_one.mp h1
    rcases hUθi.lt_or_eq with hUlt | hUeq
    · rcases hW'θi.lt_or_eq with hWlt | hWeq
      · exfalso
        have hrel : C a * (U * W') = V ^ 2 - f := by
          rw [hUW, hWa]; ring
        have := Schaefer.derivative_eval_lt_one v hUi hW'i hVi hθi hva.le hrel hθ hUlt hWlt
        rw [hθ'] at this
        exact lt_irrefl _ this
      · refine ⟨V.eval θ, ?_⟩
        have h2 := congrArg v hA
        rw [map_mul, map_mul, hva, hWeq, one_mul, mul_one, map_pow] at h2
        exact h2
    · exact ⟨1, by rw [hUeq, map_one, one_pow]⟩
  · -- `V` not integral: `V = b V'` with `v b > 1` and `v a = v b ^ 2`
    have hV0 : V ≠ 0 := by
      rintro rfl
      exact hVi fun i => by simp
    obtain ⟨b, hb0, V', hVb, hV'i, hV'1⟩ := Schaefer.exists_primitive v hV0
    have hb1 : 1 < v b := Schaefer.one_lt_of_not_integral v hVb hV'i hVi
    have hvb0 : v b ≠ 0 := (Valuation.ne_zero_iff v).mpr hb0
    have hV'deg : V'.natDegree ≤ 1 := by
      rw [hVb, natDegree_C_mul hb0] at hV
      exact hV
    have hQ := Schaefer.primitive_sub v (P := V' ^ 2) (E := C (b ^ 2)⁻¹ * f)
      (by rw [sq]; exact Schaefer.integral_mul v hV'i hV'i)
      (by rw [sq]; exact Schaefer.primitive_mul v hV'i hV'i hV'1 hV'1)
      (Schaefer.coeff_C_mul_lt_one v hf (by
        rw [map_inv₀, map_pow]
        exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hb1 two_ne_zero)))
    have hUWQ : C (b ^ 2 / a) * (V' ^ 2 - C (b ^ 2)⁻¹ * f) = U * W' := by
      have hsplit : V ^ 2 - f = C a * (U * W') := by rw [hUW, hWa]; ring
      have hb2 : b ^ 2 ≠ 0 := pow_ne_zero 2 hb0
      rw [hVb] at hsplit
      have hmul : C a * (C (b ^ 2 / a) * (V' ^ 2 - C (b ^ 2)⁻¹ * f)) = C a * (U * W') := by
        rw [← hsplit, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ ha0, mul_sub, ← mul_assoc, ← C_mul,
          mul_inv_cancel₀ hb2, C_1, one_mul, mul_pow, ← C_pow]
      exact mul_left_cancel₀ (C_ne_zero.mpr ha0) hmul
    have hz : v (b ^ 2 / a) = 1 := Schaefer.val_eq_one_of_primitive v hQ.1 hQ.2
      (by rw [hUWQ]; exact hUWi) (by rw [hUWQ]; exact hUW1)
    have hva : v a = v b ^ 2 := by
      rw [map_div₀, map_pow, div_eq_one_iff_eq hva0] at hz
      exact hz.symm
    rcases hUθi.lt_or_eq with hUlt | hUeq
    · rcases hW'θi.lt_or_eq with hWlt | hWeq
      · -- identity B
        have hres := Schaefer.resultant_val_eq_one v hf hdeg hl hθ hθ' hθi hUi hU1 hUdeg hW'i
          hW'1 hV'i hV'deg hz
          (e := a⁻¹) (by
            rw [map_inv₀, hva]
            exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hb1 two_ne_zero))
          (by rw [← hUWQ, mul_sub, ← mul_assoc, ← C_mul, div_mul_eq_mul_div, mul_inv_cancel₀
            (pow_ne_zero 2 hb0), one_div]) hUlt hWlt
        have hroot : f = (X - C θ) * (f /ₘ (X - C θ)) := (mul_divByMonic_eq_iff_isRoot.mpr hθ).symm
        have hg5 : (f /ₘ (X - C θ)).natDegree = 5 := by
          rw [natDegree_divByMonic f (monic_X_sub_C θ), hdeg, natDegree_X_sub_C]
        obtain ⟨y, hy⟩ := Schaefer.identityB (U := U) (V := V) (W := W) hUdeg.le hV hW4.le hg5
          (by rw [← hroot]; exact hUW)
        refine ⟨y, ?_⟩
        have h2 := congrArg v hy
        rw [map_mul, hres, mul_one, map_pow] at h2
        exact h2
      · refine ⟨V.eval θ / b, ?_⟩
        have h2 := congrArg v hA
        rw [map_mul, map_mul, hva, hWeq, mul_one, map_pow] at h2
        rw [map_div₀, div_pow, ← h2, mul_div_cancel_right₀ _ (pow_ne_zero 2 hvb0)]
    · exact ⟨1, by rw [hUeq, map_one, one_pow]⟩

/-- **Schaefer's lemma** (`ℤᵐ⁰` form). -/
theorem schaefer_local {M : Type*} [Field M] (v : Valuation M (WithZero (Multiplicative ℤ)))
    {f u V w : M[X]} {θ c : M}
    (hf : ∀ i, v (f.coeff i) ≤ 1) (hdeg : f.natDegree = 6) (hl : v f.leadingCoeff = 1)
    (hθ : f.eval θ = 0) (hθ' : v (f.derivative.eval θ) = 1)
    (hu2 : u.natDegree = 2) (hV : V.natDegree ≤ 1) (hw : V ^ 2 - f = u * w)
    (huθ : u.eval θ ≠ 0)
    (hU : ∀ i, v (u.coeff i / c) ≤ 1) (hprim : ∃ i, v (u.coeff i / c) = 1) :
    ∃ n : ℤ, v (u.eval θ / c) = WithZero.coe (Multiplicative.ofAdd (2 * n)) := by
  have hc : c ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hprim
    simp at hi
  obtain ⟨y, hy⟩ := schaefer_local_sq v hf hdeg hl hθ hθ' hu2 hV hw hU hprim
  exact Schaefer.exists_two_mul ((Valuation.ne_zero_iff v).mpr (div_ne_zero huθ hc)) hy

/-- **Bridge**: the adic valuation of `x ≠ 0` at `P` is `exp (- count P (x))`. -/
theorem valuation_eq_coe_neg_count {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K] (P : IsDedekindDomain.HeightOneSpectrum R)
    {x : K} (hx : x ≠ 0) :
    P.valuation K x = WithZero.coe (Multiplicative.ofAdd
      (- FractionalIdeal.count K P (FractionalIdeal.spanSingleton R⁰ x))) := by
  rw [FractionalIdeal.valuation_eq_exp_neg_count P hx, WithZero.exp_eq_coe_ofAdd]

/-- An even power valuation gives an even multiplicity. -/
theorem even_count_of_valuation {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K] (P : IsDedekindDomain.HeightOneSpectrum R)
    {x : K} (hx : x ≠ 0)
    (h : ∃ n : ℤ, P.valuation K x = WithZero.coe (Multiplicative.ofAdd (2 * n))) :
    Even (FractionalIdeal.count K P (FractionalIdeal.spanSingleton R⁰ x)) := by
  obtain ⟨n, hn⟩ := h
  rw [valuation_eq_coe_neg_count P hx, WithZero.coe_inj, EmbeddingLike.apply_eq_iff_eq] at hn
  exact ⟨-n, by omega⟩

/-- **Schaefer's lemma, count form** at a height one prime `P` of a Dedekind domain `R` with
fraction field `K` (for a number field `F`: `R = 𝓞 F`, `K = F`), as used by
`Toolbox.Chevalley.exists_sUnit_mul_sq`. -/
theorem schaefer_count {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (P : IsDedekindDomain.HeightOneSpectrum R)
    {f u V w : K[X]} {θ c : K}
    (hf : ∀ i, P.valuation K (f.coeff i) ≤ 1) (hdeg : f.natDegree = 6)
    (hl : P.valuation K f.leadingCoeff = 1)
    (hθ : f.eval θ = 0) (hθ' : P.valuation K (f.derivative.eval θ) = 1)
    (hu2 : u.natDegree = 2) (hV : V.natDegree ≤ 1) (hw : V ^ 2 - f = u * w)
    (huθ : u.eval θ ≠ 0)
    (hU : ∀ i, P.valuation K (u.coeff i / c) ≤ 1)
    (hprim : ∃ i, P.valuation K (u.coeff i / c) = 1) :
    Even (FractionalIdeal.count K P (FractionalIdeal.spanSingleton R⁰ (u.eval θ / c))) := by
  have hc : c ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hprim
    simp at hi
  exact even_count_of_valuation P (div_ne_zero huθ hc)
    (schaefer_local (P.valuation K) hf hdeg hl hθ hθ' hu2 hV hw huθ hU hprim)

end FurioLombardo.Discharge.SelmerBasis
