import FurioLombardo.Discharge.M3b.K21Real

/-!
# The fields `L = K21(√ε)` and `N = L(√e')` of the M3b discharge

* `L42 = QuadraticAlgebra K21 ε 0` (Mathlib's `K21[ω]/(ω² = ε)`): a field because `ε` is not a
  square in `K21` (`not_sq_epsK`), of degree 2 over `K21`.
* `eN = (ea + eb ω) / 2 ∈ L42` (`eaL`, `ebL` of DataL.lean): its norm to `K21` is
  `m = (ea² - ε eb²) / 4` (`mL`, kernel identity `ck_norm_eN`), and `m` is negative at every real
  embedding of `K21` (`realEmb_m_neg`), so `eN` is not a square in `L42`.
* `N84 = QuadraticAlgebra L42 eN 0`, of degree 2 over `L42`.
-/

namespace FurioLombardo.Discharge.M3b

open FurioLombardo.M1 FurioLombardo.M1.Kron NumberField QuadraticAlgebra

theorem not_isSquare_epsK : ¬ IsSquare epsK := by
  rintro ⟨r, hr⟩
  exact not_sq_epsK ⟨r, by rw [hr, sq]⟩

instance fact_not_isSquare_epsK : Fact (¬ IsSquare epsK) := ⟨not_isSquare_epsK⟩

/-- `L = K21(√ε)`, degree 42 over `ℚ`. -/
abbrev L42 : Type := QuadraticAlgebra K21 epsK 0

instance numberField_L42 : NumberField L42 := NumberField.of_module_finite K21 L42

theorem finrank_L42 : Module.finrank K21 L42 = 2 := QuadraticAlgebra.finrank_eq_two _ _

/-- `ea`, `eb` and `m` in `K21`. -/
noncomputable def eaK : K21 := zkE eaL
noncomputable def ebK : K21 := zkE ebL
noncomputable def mK : K21 := zkE mL

/-- `e' = (ea + eb ω) / 2`. -/
noncomputable def eN : L42 := ⟨eaK / 2, ebK / 2⟩

theorem ck_norm_eN : checkK 2048 (.sub (.sub (.mul (.lin eaL) (.lin eaL))
    (.mul (.lin epsL) (.mul (.lin ebL) (.lin ebL)))) (.mul (.int 4) (.lin mL))) = true := by
  decide +kernel

theorem ea_sq_sub : eaK ^ 2 - epsK * ebK ^ 2 = 4 * mK := by
  have h := evK_eq_of_check _ _ _ ck_norm_eN
  simp only [evK_mul, evK_sub, evK_lin, evK_int] at h
  rw [eaK, ebK, mK, epsK_eq, sq, sq, h]
  push_cast
  ring

theorem norm_eN : QuadraticAlgebra.norm eN = mK := by
  rw [norm_def]
  simp only [eN, zero_mul, add_zero]
  have h := ea_sq_sub
  linear_combination h / 4

theorem not_isSquare_eN : ¬ IsSquare eN := by
  rintro ⟨s, hs⟩
  have h := congrArg QuadraticAlgebra.norm hs
  rw [norm_eN, map_mul] at h
  have h2 := realEmb_m_neg 0
  rw [← mK, h, map_mul] at h2
  nlinarith [mul_self_nonneg (realEmb 0 (QuadraticAlgebra.norm s))]

instance fact_not_isSquare_eN : Fact (¬ IsSquare eN) := ⟨not_isSquare_eN⟩

/-- `N = L(√e')`, degree 84 over `ℚ`. -/
abbrev N84 : Type := QuadraticAlgebra L42 eN 0

instance numberField_N84 : NumberField N84 := NumberField.of_module_finite L42 N84

theorem finrank_N84 : Module.finrank L42 N84 = 2 := QuadraticAlgebra.finrank_eq_two _ _

end FurioLombardo.Discharge.M3b
