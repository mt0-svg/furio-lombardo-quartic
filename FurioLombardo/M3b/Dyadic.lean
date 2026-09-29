import FurioLombardo.M3b.Characters

/-!
# Lane M3b: a local non-norm test through a residue ring

For a quadratic extension `L = K(δ)`, `δ² = d`, of number fields, a valuation `v` of `K` with
`v d ≤ 1`, and a ring homomorphism `ρ` from the valuation ring `v.integer` to any ring `R`:
if no `a, b, c ∈ R` with one of them equal to `1` satisfy `ρ(u) c² = a² - ρ(d) b²`, then `u` is
not a norm from `L` (`norm_ne_of_residue`, `not_mem_normUnits_of_residue`).

Proof: every `x ∈ L` is `a + b δ` with `N(x) = a² - d b²` (`exists_eq_add_mul`,
`norm_add_mul`); dividing `(a, b, 1)` by the entry of largest valuation gives a solution in
`v.integer` with one entry equal to `1` (`exists_normalized`), whose image under `ρ` contradicts the
hypothesis. When `R` is finite, the hypothesis is a finite check (`DyadicCert.lean`).
-/

namespace FurioLombardo.M3b

open NumberField Module

set_option linter.unusedSectionVars false

section Quadratic

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Every element of `L = K(δ)` is `a + b δ`. -/
theorem exists_eq_add_mul (h2 : Module.finrank K L = 2) {δ : L}
    (hδK : ∀ k : K, algebraMap K L k ≠ δ) (x : L) :
    ∃ a b : K, x = algebraMap K L a + algebraMap K L b * δ := by
  have hli : LinearIndependent K ![(1 : L), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hδK (-s / t)
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      rw [map_div₀, map_neg, div_eq_iff ((map_ne_zero _).2 ht)]
      linear_combination -hst
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, h2])
  refine ⟨b.repr x 0, b.repr x 1, ?_⟩
  have hx := b.sum_repr x
  rw [Fin.sum_univ_two] at hx
  simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at hx
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hx
  exact hx.symm

/-- The norm of `a + b δ` is `a² - d b²`. -/
theorem norm_add_mul (h2 : Module.finrank K L = 2) {δ : L} {d : K}
    (hδ : δ ^ 2 = algebraMap K L d) (hδK : ∀ k : K, algebraMap K L k ≠ δ) (a b : K) :
    Algebra.norm K (algebraMap K L a + algebraMap K L b * δ) = a ^ 2 - d * b ^ 2 := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  obtain ⟨σ, hσ1, -⟩ := exists_involution (K := K) (L := L) h2
  -- `σ δ = -δ`
  have hsq : σ δ ^ 2 = δ ^ 2 := by rw [← map_pow, hδ, AlgEquiv.commutes]
  have hσδ : σ δ = -δ := by
    have h0 : (σ δ - δ) * (σ δ + δ) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 h0 with h | h
    · exfalso
      have hfix : ∀ τ : L ≃ₐ[K] L, τ δ = δ := by
        intro τ
        rcases aut_eq_one_or h2 σ hσ1 τ with rfl | rfl
        · rfl
        · exact sub_eq_zero.1 h
      obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed _).2 hfix)
      exact hδK k hk
    · exact eq_neg_of_add_eq_zero_left h
  apply (algebraMap K L).injective
  rw [algebraMap_norm_eq h2 σ hσ1, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hσδ]
  simp only [map_sub, map_mul, map_pow]
  linear_combination (-(algebraMap K L b) ^ 2) * hδ

end Quadratic

section Normalize

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Normalisation**: a solution `(a, b, 1)` of `u c² = a² - d b²` in `K` gives a solution in the
valuation ring of `v` with one entry equal to `1`. -/
theorem exists_normalized (v : Valuation K Γ₀) (u d : v.integer) (a b : K)
    (h : (u : K) = a ^ 2 - d * b ^ 2) :
    ∃ α β γ : v.integer, (α = 1 ∨ β = 1 ∨ γ = 1) ∧ u * γ ^ 2 = α ^ 2 - d * β ^ 2 := by
  by_cases hab : v a ≤ 1 ∧ v b ≤ 1
  · refine ⟨⟨a, hab.1⟩, ⟨b, hab.2⟩, 1, Or.inr (Or.inr rfl), ?_⟩
    apply Subtype.ext
    push_cast
    rw [h]; ring
  · rw [not_and_or, not_le, not_le] at hab
    by_cases hba : v b ≤ v a
    · -- divide by `a`
      have ha1 : 1 < v a := by rcases hab with h1 | h1; exact h1; exact h1.trans_le hba
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [map_zero] at ha1; exact not_lt.2 zero_le' ha1
      have hva : 0 < v a := zero_lt_one.trans ha1
      have hb' : v (b / a) ≤ 1 := by rw [map_div₀, div_le_one₀ hva]; exact hba
      have hc' : v (1 / a) ≤ 1 := by rw [map_div₀, map_one, div_le_one₀ hva]; exact ha1.le
      refine ⟨1, ⟨b / a, hb'⟩, ⟨1 / a, hc'⟩, Or.inl rfl, ?_⟩
      apply Subtype.ext
      push_cast
      rw [h]; field_simp
    · -- divide by `b`
      rw [not_le] at hba
      have hb1 : 1 < v b := by rcases hab with h1 | h1; exact h1.trans hba; exact h1
      have hb0 : b ≠ 0 := by
        rintro rfl; rw [map_zero] at hb1; exact not_lt.2 zero_le' hb1
      have hvb : 0 < v b := zero_lt_one.trans hb1
      have ha' : v (a / b) ≤ 1 := by rw [map_div₀, div_le_one₀ hvb]; exact hba.le
      have hc' : v (1 / b) ≤ 1 := by rw [map_div₀, map_one, div_le_one₀ hvb]; exact hb1.le
      refine ⟨⟨a / b, ha'⟩, 1, ⟨1 / b, hc'⟩, Or.inr (Or.inl rfl), ?_⟩
      apply Subtype.ext
      push_cast
      rw [h]; field_simp

end Normalize

section Test

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Residue ring non-norm test.** -/
theorem norm_ne_of_residue (h2 : Module.finrank K L = 2) (v : Valuation K Γ₀) {R : Type*}
    [Ring R] (ρ : v.integer →+* R) {δ : L} (d : v.integer) (hδ : δ ^ 2 = algebraMap K L d)
    (hδK : ∀ k : K, algebraMap K L k ≠ δ) (u : v.integer)
    (hcert : ∀ a b c : R, (a = 1 ∨ b = 1 ∨ c = 1) → ρ u * c ^ 2 ≠ a ^ 2 - ρ d * b ^ 2)
    (x : L) : Algebra.norm K x ≠ u := by
  intro hx
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul h2 hδK x
  rw [norm_add_mul h2 hδ hδK] at hx
  obtain ⟨α, β, γ, h1, heq⟩ := exists_normalized v u d a b hx.symm
  have := congrArg ρ heq
  simp only [map_mul, map_pow, map_sub] at this
  rcases h1 with h | h | h <;> subst h
  · exact hcert 1 (ρ β) (ρ γ) (Or.inl rfl) (by rw [map_one] at this; exact this)
  · exact hcert (ρ α) 1 (ρ γ) (Or.inr (Or.inl rfl)) (by rw [map_one] at this; exact this)
  · exact hcert (ρ α) (ρ β) 1 (Or.inr (Or.inr rfl)) (by rw [map_one] at this; exact this)

/-- The unit form of `norm_ne_of_residue`. -/
theorem not_mem_normUnits_of_residue (h2 : Module.finrank K L = 2) (v : Valuation K Γ₀)
    {R : Type*} [Ring R] (ρ : v.integer →+* R) {δ : L} (d : v.integer)
    (hδ : δ ^ 2 = algebraMap K L d) (hδK : ∀ k : K, algebraMap K L k ≠ δ) (u : (𝓞 K)ˣ)
    (u' : v.integer) (hu : (u' : K) = ((u : 𝓞 K) : K))
    (hcert : ∀ a b c : R, (a = 1 ∨ b = 1 ∨ c = 1) → ρ u' * c ^ 2 ≠ a ^ 2 - ρ d * b ^ 2) :
    u ∉ normUnits K L := by
  rintro ⟨x, hx⟩
  exact norm_ne_of_residue h2 v ρ d hδ hδK u' hcert x (hx.trans hu.symm)

end Test

end FurioLombardo.M3b
