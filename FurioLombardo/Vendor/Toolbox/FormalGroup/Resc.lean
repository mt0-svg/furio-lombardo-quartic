import Mathlib
import FurioLombardo.Vendor.Toolbox.FormalGroup.ScaledPoints

/-!
# Conjugating a formal group law by a homothety, and descent to a subring (item R7)

For a formal group law `Φ` over a field `K` (Stoll's `FormalGroupLaw`) and `l ≠ 0`, the family
`resc l (Φ.F i) = l⁻¹ Φ.F i (l X, l Y)` is again a formal group law (`fglResc`). If all its
coefficients lie in a subring `O`, it descends to a formal group law over `O` (`descend`). For
`l = π ^ M` the coefficient of degree `d` is `π ^ (M (|d| - 1))` times the one of `Φ`
(`coeff_resc`), which gives integrality when `Φ` converges after the rescaling by `π ^ κ` and
`M ≥ 2 κ` (`coeff_resc_mem`).

Origin: written for this formalization (the formal group of the Jacobian at the place above 2,
`FurioLombardo.Discharge.R7`).
-/

open MvPowerSeries FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman

namespace FurioLombardo.Vendor.Toolbox.FGLResc

variable {K : Type*} [Field K]

/-- The conjugate `l⁻¹ F(l X)` of a series by the homothety of ratio `l`. -/
noncomputable def resc {τ : Type*} (l : K) (F : MvPowerSeries τ K) : MvPowerSeries τ K :=
  C l⁻¹ * rescale (fun _ => l) F

section Subst

variable {σ τ : Type*}

theorem rescale_subst' (c : τ → K) {b : σ → MvPowerSeries τ K} (hb : HasSubst b)
    (f : MvPowerSeries σ K) :
    subst (fun s => rescale c (b s)) f = rescale c (subst b f) := by
  conv_rhs => rw [rescale_eq_subst]
  rw [subst_comp_subst_apply hb (HasSubst.smul_X c)]
  congr 1
  funext s
  rw [rescale_eq_subst]

theorem subst_rescale' (c : σ → K) {b : σ → MvPowerSeries τ K} (hb : HasSubst b)
    (f : MvPowerSeries σ K) :
    subst b (rescale c f) = subst (fun s => c s • b s) f := by
  rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X c) hb]
  congr 1
  funext s
  rw [Pi.smul_apply', subst_smul hb, subst_X hb]

/-- Substitution of a family on which the homothety acts linearly commutes with `resc`. -/
theorem subst_resc_of {l : K} {b : σ → MvPowerSeries τ K} (hb : HasSubst b)
    (hlin : ∀ s, l • b s = rescale (fun _ => l) (b s)) (F : MvPowerSeries σ K) :
    subst b (resc l F) = resc l (subst b F) := by
  rw [resc, resc, subst_mul hb, subst_C, subst_rescale' _ hb]
  congr 1
  rw [← rescale_subst' _ hb]
  congr 1
  funext s
  exact hlin s

theorem smul_X_eq_rescale (l : K) (s : τ) :
    l • (X s : MvPowerSeries τ K) = rescale (fun _ => l) (X s) := by
  rw [rescale_eq_subst, subst_X (HasSubst.smul_X _), Pi.smul_apply']

theorem smul_zero_eq_rescale (l : K) :
    l • (0 : MvPowerSeries τ K) = rescale (fun _ => l) 0 := by
  rw [smul_zero, map_zero]

theorem smul_resc {l : K} (hl : l ≠ 0) (F : MvPowerSeries τ K) :
    l • resc l F = rescale (fun _ => l) F := by
  rw [resc, smul_eq_C_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hl, map_one, one_mul]

theorem resc_X {l : K} (hl : l ≠ 0) (s : τ) : resc l (X s : MvPowerSeries τ K) = X s := by
  rw [resc, ← smul_X_eq_rescale, smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hl,
    map_one, one_mul]

theorem constantCoeff_resc (l : K) (F : MvPowerSeries τ K) :
    constantCoeff (resc l F) = l⁻¹ * constantCoeff F := by
  rw [resc, map_mul, constantCoeff_C, ← coeff_zero_eq_constantCoeff_apply,
    ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, Finsupp.prod_zero_index, one_mul]

theorem coeff_resc (l : K) (F : MvPowerSeries τ K) (d : τ →₀ ℕ) :
    coeff d (resc l F) = l⁻¹ * (l ^ d.degree * coeff d F) := by
  rw [resc, coeff_C_mul, coeff_rescale]
  congr 2
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum]; rfl

end Subst

/-! ### The conjugate formal group law -/

section Conj

variable {ι : Type*} [Finite ι]

theorem hasSubst_assocLeftFam (F : ι → MvPowerSeries (ι ⊕ ι) K)
    (hF0 : ∀ i, constantCoeff (F i) = 0) : HasSubst (assocLeftFam F) := by
  refine hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero
      (by rintro (a | a) <;> simp)) (by rintro (a | a) <;> simp) (hF0 j)
  · simp [assocLeftFam]

theorem hasSubst_assocRightFam (F : ι → MvPowerSeries (ι ⊕ ι) K)
    (hF0 : ∀ i, constantCoeff (F i) = 0) : HasSubst (assocRightFam F) := by
  refine hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · simp [assocRightFam]
  · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero
      (by rintro (a | a) <;> simp)) (by rintro (a | a) <;> simp) (hF0 j)

theorem smul_assocLeftFam {l : K} (hl : l ≠ 0) (F : ι → MvPowerSeries (ι ⊕ ι) K) (s : ι ⊕ ι) :
    l • assocLeftFam (fun j => resc l (F j)) s = rescale (fun _ => l) (assocLeftFam F s) := by
  rcases s with j | j
  · simp only [assocLeftFam, Sum.elim_inl]
    have he : HasSubst (Sum.elim (fun a ↦ (X (Sum.inl a) : MvPowerSeries (ι ⊕ ι ⊕ ι) K))
        fun b ↦ X (Sum.inr (Sum.inl b))) :=
      hasSubst_of_constantCoeff_zero (by rintro (a | a) <;> simp)
    rw [subst_resc_of he (by rintro (a | a) <;> exact smul_X_eq_rescale l _), smul_resc hl]
  · simp only [assocLeftFam, Sum.elim_inr]
    exact smul_X_eq_rescale l _

theorem smul_assocRightFam {l : K} (hl : l ≠ 0) (F : ι → MvPowerSeries (ι ⊕ ι) K) (s : ι ⊕ ι) :
    l • assocRightFam (fun j => resc l (F j)) s = rescale (fun _ => l) (assocRightFam F s) := by
  rcases s with j | j
  · simp only [assocRightFam, Sum.elim_inl]
    exact smul_X_eq_rescale l _
  · simp only [assocRightFam, Sum.elim_inr]
    have he : HasSubst (Sum.elim (fun a ↦ (X (Sum.inr (Sum.inl a)) :
        MvPowerSeries (ι ⊕ ι ⊕ ι) K)) fun b ↦ X (Sum.inr (Sum.inr b))) :=
      hasSubst_of_constantCoeff_zero (by rintro (a | a) <;> simp)
    rw [subst_resc_of he (by rintro (a | a) <;> exact smul_X_eq_rescale l _), smul_resc hl]

/-- A general form of `subst_resc_of`, where the family is itself a `resc` family. -/
theorem subst_resc_fam {σ τ : Type*} {l : K} {b : σ → MvPowerSeries τ K} (hb : HasSubst b)
    {b' : σ → MvPowerSeries τ K} (hb' : HasSubst b')
    (hlin : ∀ s, l • b s = rescale (fun _ => l) (b' s)) (F : MvPowerSeries σ K) :
    subst b (resc l F) = resc l (subst b' F) := by
  rw [resc, resc, subst_mul hb, subst_C, subst_rescale' _ hb]
  congr 1
  rw [← rescale_subst' _ hb']
  congr 1
  funext s
  exact hlin s

/-- **The conjugate formal group law** `l⁻¹ Φ(l X, l Y)`. -/
noncomputable def fglResc (Φ : FormalGroupLaw K ι) {l : K} (hl : l ≠ 0) : FormalGroupLaw K ι where
  F i := resc l (Φ.F i)
  zero_constantCoeff i := by rw [constantCoeff_resc, Φ.zero_constantCoeff i, mul_zero]
  add_zero' i := by
    rw [subst_resc_of FormalGroupLaw.hasSubst_unitR
      (by rintro (j | j) <;> first | exact smul_X_eq_rescale l _ | exact smul_zero_eq_rescale l),
      Φ.add_zero' i, resc_X hl]
  zero_add' i := by
    rw [subst_resc_of FormalGroupLaw.hasSubst_unitL
      (by rintro (j | j) <;> first | exact smul_X_eq_rescale l _ | exact smul_zero_eq_rescale l),
      Φ.zero_add' i, resc_X hl]
  comm' i := by
    rw [subst_resc_of FormalGroupLaw.hasSubst_swap (fun s => smul_X_eq_rescale l _), Φ.comm' i]
  assoc' i := by
    have hF0 : ∀ j, constantCoeff (resc l (Φ.F j)) = 0 := fun j => by
      rw [constantCoeff_resc, Φ.zero_constantCoeff j, mul_zero]
    rw [subst_resc_fam (hasSubst_assocLeftFam _ hF0)
        (hasSubst_assocLeftFam _ Φ.zero_constantCoeff) (smul_assocLeftFam hl Φ.F),
      subst_resc_fam (hasSubst_assocRightFam _ hF0)
        (hasSubst_assocRightFam _ Φ.zero_constantCoeff) (smul_assocRightFam hl Φ.F),
      Φ.assoc' i]

theorem fglResc_F (Φ : FormalGroupLaw K ι) {l : K} (hl : l ≠ 0) (i : ι) :
    (fglResc Φ hl).F i = resc l (Φ.F i) := rfl

end Conj

/-! ### Descent to a subring -/

section Descend

variable (O : Subring K) {τ : Type*}

/-- A series over `K` with coefficients in `O`, as a series over `O`. -/
def descendSeries (F : MvPowerSeries τ K) (h : ∀ d, coeff d F ∈ O) : MvPowerSeries τ O :=
  fun d => ⟨coeff d F, h d⟩

theorem map_descendSeries (F : MvPowerSeries τ K) (h : ∀ d, coeff d F ∈ O) :
    map O.subtype (descendSeries O F h) = F := by
  ext d; rfl

theorem map_subtype_injective : Function.Injective (map (σ := τ) O.subtype) := by
  intro f g h
  ext d
  have := congrArg (coeff d) h
  simpa [coeff_map] using this

variable {ι : Type*} [Finite ι]

theorem map_assocLeftFam (F : ι → MvPowerSeries (ι ⊕ ι) O) (s : ι ⊕ ι) :
    map O.subtype (assocLeftFam F s) = assocLeftFam (fun j => map O.subtype (F j)) s := by
  rcases s with j | j
  · simp only [assocLeftFam, Sum.elim_inl]
    rw [map_subst (hasSubst_of_constantCoeff_zero (by rintro (a | a) <;> simp))]
    congr 1
    funext s; rcases s with a | a <;> simp
  · simp [assocLeftFam]

theorem map_assocRightFam (F : ι → MvPowerSeries (ι ⊕ ι) O) (s : ι ⊕ ι) :
    map O.subtype (assocRightFam F s) = assocRightFam (fun j => map O.subtype (F j)) s := by
  rcases s with j | j
  · simp [assocRightFam]
  · simp only [assocRightFam, Sum.elim_inr]
    rw [map_subst (hasSubst_of_constantCoeff_zero (by rintro (a | a) <;> simp))]
    congr 1
    funext s; rcases s with a | a <;> simp

/-- **Descent**: a formal group law over `K` with coefficients in `O` is one over `O`. -/
noncomputable def descend (Ψ : FormalGroupLaw K ι) (hO : ∀ i d, coeff d (Ψ.F i) ∈ O) :
    FormalGroupLaw O ι where
  F i := descendSeries O (Ψ.F i) (hO i)
  zero_constantCoeff i := by
    apply Subtype.ext
    change coeff 0 (Ψ.F i) = 0
    rw [coeff_zero_eq_constantCoeff_apply, Ψ.zero_constantCoeff i]
  add_zero' i := by
    apply map_subtype_injective O
    rw [map_subst FormalGroupLaw.hasSubst_unitR, map_descendSeries, map_X]
    convert Ψ.add_zero' i using 2
    funext s; rcases s with j | j <;> simp
  zero_add' i := by
    apply map_subtype_injective O
    rw [map_subst FormalGroupLaw.hasSubst_unitL, map_descendSeries, map_X]
    convert Ψ.zero_add' i using 2
    funext s; rcases s with j | j <;> simp
  comm' i := by
    apply map_subtype_injective O
    rw [map_subst FormalGroupLaw.hasSubst_swap, map_descendSeries]
    convert Ψ.comm' i using 2
    funext s; simp
  assoc' i := by
    have hF0 : ∀ j, constantCoeff (descendSeries O (Ψ.F j) (hO j)) = 0 := fun j => by
      apply Subtype.ext
      change coeff 0 (Ψ.F j) = 0
      rw [coeff_zero_eq_constantCoeff_apply, Ψ.zero_constantCoeff j]
    apply map_subtype_injective O
    rw [map_subst (hasSubst_of_constantCoeff_zero (fun s => by
        rcases s with j | j
        · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero
            (by rintro (a | a) <;> simp)) (by rintro (a | a) <;> simp) (hF0 j)
        · simp [assocLeftFam])),
      map_subst (hasSubst_of_constantCoeff_zero (fun s => by
        rcases s with j | j
        · simp [assocRightFam]
        · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero
            (by rintro (a | a) <;> simp)) (by rintro (a | a) <;> simp) (hF0 j))),
      map_descendSeries]
    have hL : (fun s => map O.subtype (assocLeftFam (fun j => descendSeries O (Ψ.F j) (hO j)) s))
        = assocLeftFam Ψ.F := by
      funext s; rw [map_assocLeftFam]; simp only [map_descendSeries]
    have hR : (fun s => map O.subtype (assocRightFam (fun j => descendSeries O (Ψ.F j) (hO j)) s))
        = assocRightFam Ψ.F := by
      funext s; rw [map_assocRightFam]; simp only [map_descendSeries]
    rw [hL, hR]
    exact Ψ.assoc' i

theorem map_descend_F (Ψ : FormalGroupLaw K ι) (hO : ∀ i d, coeff d (Ψ.F i) ∈ O) (i : ι) :
    map O.subtype ((descend O Ψ hO).F i) = Ψ.F i :=
  map_descendSeries O _ _

end Descend

/-! ### Integrality of the conjugate by `π ^ M` -/

section Integral

variable (O : Subring K) {ι : Type*} [Finite ι]

theorem coeff_mem_of_degree_eq_one (Φ : FormalGroupLaw K ι) (i : ι) (d : ι ⊕ ι →₀ ℕ)
    (hd : d.degree = 1) : coeff d (Φ.F i) ∈ O := by
  classical
  have h := FurioLombardo.Vendor.Toolbox.FormalGroup.coeff_F_sub_eq_zero Φ i d (by omega)
  rw [map_sub, map_sub, sub_sub, sub_eq_zero] at h
  rw [h, coeff_X, coeff_X]
  exact O.add_mem (by split_ifs <;> simp) (by split_ifs <;> simp)

theorem pow_mul_coeff_mem {π : K} (hπ : π ∈ O) {κ M : ℕ} (hM : 2 * κ ≤ M) {τ : Type*}
    {G : MvPowerSeries τ K} (h0 : constantCoeff G = 0)
    (h1 : ∀ d : τ →₀ ℕ, d.degree = 1 → coeff d G ∈ O)
    (hG : ∀ d : τ →₀ ℕ, π ^ (κ * d.degree) * coeff d G ∈ O) (d : τ →₀ ℕ) :
    π ^ (M * (d.degree - 1)) * coeff d G ∈ O := by
  rcases Nat.lt_or_ge d.degree 2 with hlt | hge
  · rcases Nat.lt_or_ge d.degree 1 with h00 | h11
    · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
      rw [coeff_zero_eq_constantCoeff_apply, h0, mul_zero]; exact O.zero_mem
    · have hd1 : d.degree = 1 := by omega
      rw [hd1, Nat.sub_self, mul_zero, pow_zero, one_mul]; exact h1 d hd1
  · have hle : κ * d.degree ≤ M * (d.degree - 1) := by
      have : κ * d.degree ≤ 2 * κ * (d.degree - 1) := by
        obtain ⟨n, hn⟩ : ∃ n, d.degree = n + 2 := ⟨d.degree - 2, by omega⟩
        rw [hn, show n + 2 - 1 = n + 1 by omega, show 2 * κ * (n + 1) = κ * (2 * n + 2) by ring]
        exact Nat.mul_le_mul_left κ (by omega)
      exact this.trans (Nat.mul_le_mul_right _ hM)
    rw [show M * (d.degree - 1) = (M * (d.degree - 1) - κ * d.degree) + κ * d.degree by omega,
      pow_add, mul_assoc]
    exact O.mul_mem (O.pow_mem hπ _) (hG d)

/-- **Integrality**: if `Φ(π^κ X)` is integral, so is `π^(-M) Φ(π^M X)` for `M ≥ 2 κ`. -/
theorem coeff_resc_mem {π : K} (hπ : π ∈ O) (hπ0 : π ≠ 0) {κ M : ℕ} (hM : 2 * κ ≤ M)
    (Φ : FormalGroupLaw K ι) (hG : ∀ i d, π ^ (κ * d.degree) * coeff d (Φ.F i) ∈ O) (i : ι)
    (d : ι ⊕ ι →₀ ℕ) : coeff d (resc (π ^ M) (Φ.F i)) ∈ O := by
  rw [coeff_resc]
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    rw [coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff i, mul_zero, mul_zero]
    exact O.zero_mem
  · have e : (π ^ M)⁻¹ * ((π ^ M) ^ d.degree * coeff d (Φ.F i)) =
        π ^ (M * (d.degree - 1)) * coeff d (Φ.F i) := by
      obtain ⟨n, hn⟩ : ∃ n, d.degree = n + 1 := ⟨d.degree - 1, by omega⟩
      have hπM : π ^ M ≠ 0 := pow_ne_zero _ hπ0
      rw [hn, Nat.add_sub_cancel, ← pow_mul, show M * (n + 1) = M * n + M by ring, pow_add,
        mul_comm (π ^ (M * n)) (π ^ M), mul_assoc, ← mul_assoc (π ^ M)⁻¹, inv_mul_cancel₀ hπM,
        one_mul]
    rw [e]
    exact pow_mul_coeff_mem O hπ hM (Φ.zero_constantCoeff i)
      (fun d hd => coeff_mem_of_degree_eq_one O Φ i d hd) (hG i) d

end Integral

end FurioLombardo.Vendor.Toolbox.FGLResc
