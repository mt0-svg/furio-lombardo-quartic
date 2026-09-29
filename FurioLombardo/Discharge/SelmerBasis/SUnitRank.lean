import FurioLombardo.Discharge.M3b.Signs
import FurioLombardo.M1.Signature

/-!
# Unit ranks of `L42` and `N84`

* A real embedding `τ` of `L42 = K21(√ε)` restricts to one of the three `realEmb k` of `K21` and
  sends `ω` to `±√(realEmb k ε)`: `τ = τp k` or `τ = τm k` (`eq_τp_or_τm`). So `r1(L42) ≤ 6`.
* A real embedding `σ` of `N84 = L42(√e')` restricts to `τp k` or `τm k` with `τ e' = σ(ω)² ≥ 0`;
  since `τp k e' · τm k e' < 0` (`τp_mul_τm`, the norm `m < 0`), `k` determines the restriction,
  and the sign of `σ ω` determines `σ`. So `r1(N84) ≤ 6`.
* `r1 + 2 r2 = 42` (resp. `84`) gives `rank L42 ≤ 23`, `rank N84 ≤ 44`.
-/

namespace FurioLombardo.Discharge.SelmerBasis

open NumberField FurioLombardo.M1 FurioLombardo.Discharge.M3b QuadraticAlgebra

/-- Every real embedding of `L42` is `τp k` or `τm k`. -/
theorem eq_τp_or_τm (τ : L42 →+* ℝ) : ∃ k : Fin 3, τ = τp k ∨ τ = τm k := by
  obtain ⟨k, hk⟩ := exists_eq_realEmb (τ.comp (algebraMap K21 L42))
  refine ⟨k, ?_⟩
  have hs := map_omega_mul_self τ
  rw [hk] at hs
  have h0 : (τ ω - sqrtEps k) * (τ ω + sqrtEps k) = 0 := by
    linear_combination hs - sqrtEps_mul k
  rcases mul_eq_zero.mp h0 with h | h
  · left
    refine quad_hom_ext (by rw [hk, τp, extendHom_comp_algebraMap]) ?_
    rw [τp, extendHom_omega]; linear_combination h
  · right
    refine quad_hom_ext (by rw [hk, τm, extendHom_comp_algebraMap]) ?_
    rw [τm, extendHom_omega]; linear_combination h

/-- The index `k` of a real embedding of `L42`. -/
noncomputable def idxL (τ : L42 →+* ℝ) : Fin 3 := (eq_τp_or_τm τ).choose

theorem idxL_spec (τ : L42 →+* ℝ) : τ = τp (idxL τ) ∨ τ = τm (idxL τ) :=
  (eq_τp_or_τm τ).choose_spec

/-- The sign of `τ ω` separates `τp k` and `τm k`. -/
theorem τp_omega (k : Fin 3) : τp k (ω : L42) = sqrtEps k := by rw [τp, extendHom_omega]

theorem τm_omega (k : Fin 3) : τm k (ω : L42) = -sqrtEps k := by rw [τm, extendHom_omega]

theorem sqrtEps_pos (k : Fin 3) : 0 < sqrtEps k := Real.sqrt_pos.mpr (realEmb_epsK_pos k)

/-- Real embeddings of `L42` are determined by `k` and the sign of `τ ω`. -/
theorem realEmb_L42_inj (τ₁ τ₂ : L42 →+* ℝ) (hk : idxL τ₁ = idxL τ₂)
    (hs : (0 ≤ τ₁ ω) = (0 ≤ τ₂ ω)) : τ₁ = τ₂ := by
  have hp := sqrtEps_pos (idxL τ₁)
  rcases idxL_spec τ₁ with h1 | h1 <;> rcases idxL_spec τ₂ with h2 | h2 <;> rw [← hk] at h2
  · rw [h1, h2]
  · exfalso; rw [h1, h2, τp_omega, τm_omega] at hs
    have : ¬ (0 ≤ -sqrtEps (idxL τ₁)) := by linarith
    exact this (hs ▸ hp.le)
  · exfalso; rw [h1, h2, τp_omega, τm_omega] at hs
    have : ¬ (0 ≤ -sqrtEps (idxL τ₁)) := by linarith
    exact this (hs.symm ▸ hp.le)
  · rw [h1, h2]

/-- A real embedding of `N84` restricted to `L42`. -/
noncomputable def resN (σ : N84 →+* ℝ) : L42 →+* ℝ := σ.comp (algebraMap L42 N84)

theorem resN_eN_nonneg (σ : N84 →+* ℝ) : 0 ≤ resN σ eN := by
  have h := map_omega_mul_self σ
  simp only [resN] at h ⊢
  rw [← h]; exact mul_self_nonneg _

/-- Two real embeddings of `N84` with the same index have the same restriction to `L42`. -/
theorem resN_eq (σ₁ σ₂ : N84 →+* ℝ) (hk : idxL (resN σ₁) = idxL (resN σ₂)) :
    resN σ₁ = resN σ₂ := by
  have h1 := resN_eN_nonneg σ₁
  have h2 := resN_eN_nonneg σ₂
  have hm := τp_mul_τm (idxL (resN σ₁))
  rcases idxL_spec (resN σ₁) with e1 | e1 <;> rcases idxL_spec (resN σ₂) with e2 | e2 <;>
    rw [← hk] at e2
  · rw [e1, e2]
  · exfalso; rw [e1] at h1; rw [e2] at h2; nlinarith [mul_nonneg h1 h2]
  · exfalso; rw [e1] at h1; rw [e2] at h2; nlinarith [mul_nonneg h1 h2]
  · rw [e1, e2]

/-- Real embeddings of `N84` are determined by the index of the restriction and the sign of
`σ ω`. -/
theorem realEmb_N84_inj (σ₁ σ₂ : N84 →+* ℝ) (hk : idxL (resN σ₁) = idxL (resN σ₂))
    (hs : (0 ≤ σ₁ ω) = (0 ≤ σ₂ ω)) : σ₁ = σ₂ := by
  have hr := resN_eq σ₁ σ₂ hk
  have e1 := map_omega_mul_self σ₁
  have e2 := map_omega_mul_self σ₂
  have he : σ₁.comp (algebraMap L42 N84) eN = σ₂.comp (algebraMap L42 N84) eN := by
    have := congrArg (fun f => f eN) hr
    simpa [resN] using this
  refine quad_hom_ext hr ?_
  have h0 : (σ₁ ω - σ₂ ω) * (σ₁ ω + σ₂ ω) = 0 := by linear_combination e1 - e2 + he
  rcases mul_eq_zero.mp h0 with h | h
  · linarith
  · by_cases hz : 0 ≤ σ₁ ω
    · have hz2 : 0 ≤ σ₂ ω := hs ▸ hz
      linarith
    · have hz2 : ¬ 0 ≤ σ₂ ω := hs ▸ hz
      linarith

/-- The number of real places is at most the number of values of an injective invariant of real
embeddings. -/
theorem nrRealPlaces_le_of_inj (F : Type*) [Field F] [NumberField F] {ι : Type*} [Fintype ι]
    (g : (F →+* ℝ) → ι) (hg : Function.Injective g) :
    InfinitePlace.nrRealPlaces F ≤ Fintype.card ι := by
  classical
  let g' : {φ : F →+* ℂ // ComplexEmbedding.IsReal φ} → ι := fun φ => g φ.2.embedding
  have hinj : Function.Injective g' := by
    intro φ ψ h
    apply Subtype.ext
    refine RingHom.ext fun x => ?_
    rw [← ComplexEmbedding.IsReal.coe_embedding_apply φ.2 x,
      ← ComplexEmbedding.IsReal.coe_embedding_apply ψ.2 x, hg h]
  rw [← InfinitePlace.card_real_embeddings]
  exact Fintype.card_le_of_injective g' hinj

theorem nrRealPlaces_L42_le : InfinitePlace.nrRealPlaces L42 ≤ 6 := by
  classical
  have h := nrRealPlaces_le_of_inj L42 (ι := Fin 3 × Bool)
    (fun τ => (idxL τ, decide (0 ≤ τ ω))) (by
      intro τ₁ τ₂ h
      simp only [Prod.mk.injEq, decide_eq_decide] at h
      exact realEmb_L42_inj τ₁ τ₂ h.1 (propext h.2))
  simpa using h

theorem nrRealPlaces_N84_le : InfinitePlace.nrRealPlaces N84 ≤ 6 := by
  classical
  have h := nrRealPlaces_le_of_inj N84 (ι := Fin 3 × Bool)
    (fun σ => (idxL (resN σ), decide (0 ≤ σ ω))) (by
      intro σ₁ σ₂ h
      simp only [Prod.mk.injEq, decide_eq_decide] at h
      exact realEmb_N84_inj σ₁ σ₂ h.1 (propext h.2))
  simpa using h

theorem finrank_ℚ_L42 : Module.finrank ℚ L42 = 42 := by
  rw [← Module.finrank_mul_finrank ℚ K21 L42, finrank_K21, finrank_L42]

theorem finrank_ℚ_N84 : Module.finrank ℚ N84 = 84 := by
  rw [← Module.finrank_mul_finrank ℚ L42 N84, finrank_ℚ_L42, finrank_N84]

/-- The unit rank from the number of real places and the degree. -/
theorem rank_le_of_nrRealPlaces (F : Type*) [Field F] [NumberField F] {n r : ℕ}
    (hn : Module.finrank ℚ F = n) (hr : InfinitePlace.nrRealPlaces F ≤ r) :
    2 * (Units.rank F + 1) ≤ n + r := by
  have h_card_eq : InfinitePlace.nrRealPlaces F + 2 * InfinitePlace.nrComplexPlaces F = n := by
    rw [← hn]; exact InfinitePlace.card_add_two_mul_card_eq_rank F
  have h_rank_def : Units.rank F = Fintype.card (InfinitePlace F) - 1 := rfl
  have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F] at hpos
  rw [h_rank_def, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F]
  omega

/-- **Piece (a), `L42`.** -/
theorem rank_L42_le : Units.rank L42 ≤ 23 := by
  have := rank_le_of_nrRealPlaces L42 finrank_ℚ_L42 nrRealPlaces_L42_le
  omega

/-- **Piece (a), `N84`.** -/
theorem rank_N84_le : Units.rank N84 ≤ 44 := by
  have := rank_le_of_nrRealPlaces N84 finrank_ℚ_N84 nrRealPlaces_N84_le
  omega

end FurioLombardo.Discharge.SelmerBasis
