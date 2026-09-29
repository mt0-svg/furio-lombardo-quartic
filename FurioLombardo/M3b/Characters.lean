import FurioLombardo.M3b.Formula

/-!
# Lane M3b: characters that kill norms, lower bounds for `[E_K : E_K ∩ N(Lˣ)]`

For a quadratic extension `L/K` of number fields:

* `index_normUnits_ne_zero`: the index `[E_K : E_K ∩ N(Lˣ)]` is finite (from Chevalley's formula).
* `two_le_index_of_not_mem`: one unit of `K` that is not a norm from `L` gives index `≥ 2`.
* `embedding_norm_eq_normSq`: at a real place `v` of `K` ramified in `L` (below a complex place),
  `v(N x) = |φ x|²` for a complex embedding `φ` of `L`; so norms are positive at `v`
  (`embedding_norm_re_pos`).
* `pow_le_index_of_signs`: `n` real places of `K` ramified in `L` and `n` units with the diagonal
  sign pattern (`u i` negative at `w j` iff `i = j`) give index `≥ 2 ^ n`.
-/

namespace FurioLombardo.M3b

open NumberField InfinitePlace Module
open scoped ComplexConjugate

set_option linter.unusedSectionVars false

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- A unit of `𝓞 K` is nonzero in `K`. -/
theorem coe_unit_ne_zero (u : (𝓞 K)ˣ) : ((u : 𝓞 K) : K) ≠ 0 :=
  RingOfIntegers.coe_ne_zero_iff.2 u.ne_zero

/-- The index `[E_K : E_K ∩ N(Lˣ)]` is finite. -/
theorem index_normUnits_ne_zero (h2 : Module.finrank K L = 2) : (normUnits K L).index ≠ 0 := by
  obtain ⟨σ, hσ1, -⟩ := exists_involution (K := K) (L := L) h2
  have hf := chevalley_formula h2 σ hσ1
  intro h0
  rw [h0, mul_zero, zero_mul] at hf
  exact (Nat.mul_ne_zero (classNumber_ne_zero K) (by positivity)) hf.symm

/-- A unit that is not a norm gives `[E_K : E_K ∩ N(Lˣ)] ≥ 2`. -/
theorem two_le_index_of_not_mem (h2 : Module.finrank K L = 2) {u : (𝓞 K)ˣ}
    (hu : u ∉ normUnits K L) : 2 ≤ (normUnits K L).index := by
  have h0 := index_normUnits_ne_zero h2
  have h1 : (normUnits K L).index ≠ 1 := by
    rw [Ne, Subgroup.index_eq_one]
    rintro htop
    exact hu (htop ▸ Subgroup.mem_top u)
  omega

/-- **Norms at a ramified real place**: if the real place `v` of `K` lies below a complex place of
`L`, there is a complex embedding `φ` of `L` with `v(N_{L/K} x) = |φ x|²` for every `x`. -/
theorem embedding_norm_eq_normSq (h2 : Module.finrank K L = 2) {v : InfinitePlace K}
    (hv : v ∈ ramifiedRealPlaces K L) :
    ∃ φ : L →+* ℂ, ∀ x : L, v.embedding (Algebra.norm K x) = (Complex.normSq (φ x) : ℂ) := by
  have : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  obtain ⟨hvr, w, hwv, hwc⟩ := hv
  set φ := w.embedding
  have hram : IsRamified K (mk φ) := by
    rw [mk_embedding, isRamified_iff]
    exact ⟨hwc, hwv ▸ hvr⟩
  obtain ⟨τ, hτ⟩ := exists_isConj_of_isRamified hram
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply isComplex_iff.1 hwc
    rw [ComplexEmbedding.isReal_iff]
    exact hτ
  obtain ⟨σ, hσ1, -⟩ := exists_involution (K := K) (L := L) h2
  have hτσ : τ = σ := (aut_eq_one_or h2 σ hσ1 τ).resolve_left hτ1
  subst hτσ
  refine ⟨φ, fun x => ?_⟩
  -- `φ (N x) = φ x * φ (σ x) = φ x * conj (φ x) = |φ x|²`
  have hN : φ (algebraMap K L (Algebra.norm K x)) = (Complex.normSq (φ x) : ℂ) := by
    rw [algebraMap_norm_eq h2 τ hσ1 x, map_mul, ComplexEmbedding.IsConj.eq hτ x,
      Complex.star_def, Complex.mul_conj]
  -- `v.embedding` is `φ ∘ algebraMap` or its conjugate, and the value is real
  have hv' : v = mk (φ.comp (algebraMap K L)) := by
    rw [← hwv, ← comap_mk, mk_embedding]
  rcases embedding_mk_eq (φ.comp (algebraMap K L)) with h | h
  · rw [hv', h, RingHom.comp_apply, hN]
  · rw [hv', h, ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, hN, Complex.conj_ofReal]

/-- Norms of nonzero elements are positive at a real place of `K` ramified in `L`. -/
theorem embedding_norm_re_pos (h2 : Module.finrank K L = 2) {v : InfinitePlace K}
    (hv : v ∈ ramifiedRealPlaces K L) {x : L} (hx : x ≠ 0) :
    0 < (v.embedding (Algebra.norm K x)).re := by
  obtain ⟨φ, hφ⟩ := embedding_norm_eq_normSq h2 hv
  rw [hφ x, Complex.ofReal_re]
  exact Complex.normSq_pos.2 ((map_ne_zero φ).2 hx)

/-- A unit of `K` that is a norm from `L` is positive at every real place ramified in `L`. -/
theorem embedding_re_pos_of_mem_normUnits (h2 : Module.finrank K L = 2) {v : InfinitePlace K}
    (hv : v ∈ ramifiedRealPlaces K L) {u : (𝓞 K)ˣ} (hu : u ∈ normUnits K L) :
    0 < (v.embedding ((u : 𝓞 K) : K)).re := by
  obtain ⟨x, hx⟩ := hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hx
    exact coe_unit_ne_zero u hx.symm
  rw [← hx]
  exact embedding_norm_re_pos h2 hv hx0

section Sign

/-- The value of a real place is real. -/
theorem embedding_im_eq_zero {w : InfinitePlace K} (hw : w.IsReal) (x : K) :
    (w.embedding x).im = 0 := by
  rw [← embedding_of_isReal_apply hw, Complex.ofReal_im]

/-- The sign at a real place, as a character of `Kˣ`. -/
noncomputable def signHom {w : InfinitePlace K} (hw : w.IsReal) : Kˣ →* ℤˣ where
  toFun x := if 0 < embedding_of_isReal hw (x : K) then 1 else -1
  map_one' := by simp
  map_mul' x y := by
    have hx : embedding_of_isReal hw (x : K) ≠ 0 := (map_ne_zero _).2 x.ne_zero
    have hy : embedding_of_isReal hw (y : K) ≠ 0 := (map_ne_zero _).2 y.ne_zero
    simp only [Units.val_mul, map_mul]
    rcases hx.lt_or_gt with hx' | hx' <;> rcases hy.lt_or_gt with hy' | hy'
    · simp [mul_pos_of_neg_of_neg hx' hy', not_lt.2 hx'.le, not_lt.2 hy'.le]
    · simp [not_lt.2 (mul_neg_of_neg_of_pos hx' hy').le, not_lt.2 hx'.le, hy']
    · simp [not_lt.2 (mul_neg_of_pos_of_neg hx' hy').le, hx', not_lt.2 hy'.le]
    · simp [mul_pos hx' hy', hx', hy']

theorem signHom_apply {w : InfinitePlace K} (hw : w.IsReal) (x : Kˣ) :
    signHom hw x = if 0 < (w.embedding (x : K)).re then 1 else -1 := by
  simp only [signHom, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← embedding_of_isReal_apply hw, Complex.ofReal_re]

/-- The signs at a family of real places, as a character of the units of `𝓞 K`. -/
noncomputable def signsHom {n : ℕ} (w : Fin n → InfinitePlace K) (hw : ∀ j, (w j).IsReal) :
    (𝓞 K)ˣ →* (Fin n → ℤˣ) :=
  MonoidHom.pi fun j => (signHom (hw j)).comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom)

theorem signsHom_apply {n : ℕ} (w : Fin n → InfinitePlace K) (hw : ∀ j, (w j).IsReal)
    (u : (𝓞 K)ˣ) (j : Fin n) :
    signsHom w hw u j = if 0 < ((w j).embedding ((u : 𝓞 K) : K)).re then 1 else -1 := by
  simp only [signsHom, MonoidHom.pi_apply, MonoidHom.comp_apply]
  rw [signHom_apply]
  rfl

/-- **Index from signs**: `n` real places of `K` ramified in `L` and `n` units with the diagonal
sign pattern give `2 ^ n ≤ [E_K : E_K ∩ N(Lˣ)]`. -/
theorem pow_le_index_of_signs (h2 : Module.finrank K L = 2) {n : ℕ} (w : Fin n → InfinitePlace K)
    (hw : ∀ j, w j ∈ ramifiedRealPlaces K L) (u : Fin n → (𝓞 K)ˣ)
    (hu : ∀ i j, ((w j).embedding ((u i : 𝓞 K) : K)).re < 0 ↔ i = j) :
    2 ^ n ≤ (normUnits K L).index := by
  set χ := signsHom w (fun j => (hw j).1)
  have hker : normUnits K L ≤ χ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    funext j
    rw [signsHom_apply, if_pos (embedding_re_pos_of_mem_normUnits h2 (hw j) hx)]
    rfl
  have hχu : ∀ i, χ (u i) = Pi.mulSingle i (-1) := by
    intro i
    funext j
    rw [signsHom_apply]
    by_cases hij : i = j
    · subst hij
      rw [Pi.mulSingle_eq_same, if_neg (not_lt.2 ((hu i i).2 rfl).le)]
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hij), if_pos]
      have hne : ¬ ((w j).embedding ((u i : 𝓞 K) : K)).re < 0 := fun h => hij ((hu i j).1 h)
      have h0 : ((w j).embedding ((u i : 𝓞 K) : K)).re ≠ 0 := by
        intro h
        have hz : (w j).embedding ((u i : 𝓞 K) : K) = 0 :=
          Complex.ext h (embedding_im_eq_zero (hw j).1 _)
        rw [map_eq_zero] at hz
        exact coe_unit_ne_zero (u i) hz
      exact lt_of_le_of_ne (not_lt.1 hne) (Ne.symm h0)
  have htop : χ.range = ⊤ := by
    rw [eq_top_iff]
    intro g _
    rw [← Finset.univ_prod_mulSingle g]
    refine Subgroup.prod_mem _ fun j _ => ?_
    rcases Int.units_eq_one_or (g j) with h | h
    · rw [h, Pi.mulSingle_one]
      exact Subgroup.one_mem _
    · rw [h, ← hχu j]
      exact ⟨u j, rfl⟩
  have hcard : Nat.card χ.range = 2 ^ n := by
    rw [htop, Subgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_units_int,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hdvd := card_range_dvd_index χ hker
  rw [hcard] at hdvd
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (index_normUnits_ne_zero h2)) hdvd

end Sign

end FurioLombardo.M3b
