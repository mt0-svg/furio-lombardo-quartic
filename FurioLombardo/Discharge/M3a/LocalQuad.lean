import Mathlib

/-!
# Quartics of norm form over a field (WP5 of the M3a discharge)

`F` is a field with `2 ≠ 0`, `δ ∈ F` is not a square and `N = F(ω) = QuadraticAlgebra F δ 0`
(`ω² = δ`; a field by Mathlib's instance from `Fact (¬ IsSquare δ)`). For `A = X² + a1 X + a0` and
`B = b1 X + b0` over `F` put `P1 = a1 + b1 ω`, `P0 = a0 + b0 ω` in `N`, so that
`A + ω B = X² + P1 X + P0` and `A² - δ B² = (A + ω B)(A - ω B)`.

* `not_isSquare_mk`: `z0 + z1 ω` is not a square in `N` if `n² = z0² - δ z1²` in `F` and
  `2 (z0 + n)`, `2 (z0 - n)` are not squares in `F` (a square `(a + b ω)²` has `n = ± (a² - δ b²)`, and
  then `2 (z0 ± n) = (2a)²`).
* `no_root_of_not_isSquare`: `X² + P1 X + P0` has no root in `N` if `P1² - 4 P0` is not a square.
* `irreducible_normForm`: `A² - δ B²` is irreducible over `F` if `b1 ≠ 0` and `X² + P1 X + P0` has no
  root in `N`.
* `nsq_normForm`: for `f = c q h` with `q = X² + q1 X + q0`, `q1² - 4 q0 = δ`, `h = A² - δ B²`, `c ≠ 0`
  and `q`, `h` coprime, `(q - c h)(T)` is not of the form `c' y²` in `F[T]/(f)` as soon as
  `ρ = p0² - p0 p1 P1 + p1² P0` (`p_i = q_i - P_i`, the resultant of `q` and `X² + P1 X + P0`) is not a
  square in `N`. The proof maps the relation to `M = F[x]/(h)` and to `N` (at the root
  `τ = (-q1 + ω)/2` of `q`), embeds `N` into `M` by `ω ↦ -A(x)/B(x)`, writes `M = N ⊕ N x` and takes the
  norm from `M` to `N`.
-/

namespace FurioLombardo.Discharge.M3a

open Polynomial

section Quad

variable {F : Type*} [Field F] {δ : F}

/-- The ring homomorphism `QuadraticAlgebra F δ 0 → S` extending `φ` by `ω ↦ s`, `s * s = φ δ`. -/
def extQ {S : Type*} [CommRing S] (φ : F →+* S) (s : S) (hs : s * s = φ δ) :
    QuadraticAlgebra F δ 0 →+* S where
  toFun z := φ z.re + φ z.im * s
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, zero_mul, add_zero]
    linear_combination (-(φ z.im * φ w.im)) * hs
  map_zero' := by simp
  map_add' z w := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring

theorem extQ_apply {S : Type*} [CommRing S] (φ : F →+* S) (s : S) (hs : s * s = φ δ)
    (z : QuadraticAlgebra F δ 0) : extQ φ s hs z = φ z.re + φ z.im * s := rfl

theorem extQ_algebraMap {S : Type*} [CommRing S] (φ : F →+* S) (s : S) (hs : s * s = φ δ) (r : F) :
    extQ φ s hs (algebraMap F (QuadraticAlgebra F δ 0) r) = φ r := by
  simp [extQ_apply, QuadraticAlgebra.algebraMap_eq]

/-- **Non-square test in `N`** through the norm. -/
theorem not_isSquare_mk {z0 z1 n : F} (hn : n ^ 2 = z0 ^ 2 - δ * z1 ^ 2)
    (hp : ¬ IsSquare (2 * (z0 + n))) (hm : ¬ IsSquare (2 * (z0 - n))) :
    ¬ IsSquare (⟨z0, z1⟩ : QuadraticAlgebra F δ 0) := by
  rintro ⟨w, hw⟩
  have h0 : z0 = w.re * w.re + δ * w.im * w.im := by
    simpa using congrArg QuadraticAlgebra.re hw
  have h1 : z1 = w.re * w.im + w.im * w.re := by
    simpa using congrArg QuadraticAlgebra.im hw
  have key : (n - (w.re ^ 2 - δ * w.im ^ 2)) * (n + (w.re ^ 2 - δ * w.im ^ 2)) = 0 := by
    rw [h0, h1] at hn; linear_combination hn
  rcases mul_eq_zero.1 key with h | h
  · exact hp ⟨2 * w.re, by rw [h0]; linear_combination 2 * h⟩
  · exact hm ⟨2 * w.re, by rw [h0]; linear_combination (-2) * h⟩

/-- A monic quadratic over `N` with non-square discriminant has no root. -/
theorem no_root_of_not_isSquare {P1 P0 : QuadraticAlgebra F δ 0} (hD : ¬ IsSquare (P1 ^ 2 - 4 * P0))
    (r : QuadraticAlgebra F δ 0) : r ^ 2 + P1 * r + P0 ≠ 0 := by
  intro hr
  exact hD ⟨2 * r + P1, by linear_combination (-4) * hr⟩

end Quad
section Norm

variable {F : Type*} [Field F] {δ : F}

/-- The quartic `A² - δ B²`. -/
noncomputable def normForm (δ a0 a1 b0 b1 : F) : F[X] :=
  (X ^ 2 + C a1 * X + C a0) ^ 2 - C δ * (C b1 * X + C b0) ^ 2

/-- `A + ω B = X² + P1 X + P0` over `N`. -/
noncomputable def normP (δ a0 a1 b0 b1 : F) : (QuadraticAlgebra F δ 0)[X] :=
  X ^ 2 + C ⟨a1, b1⟩ * X + C ⟨a0, b0⟩

/-- `A - ω B` over `N`. -/
noncomputable def normPbar (δ a0 a1 b0 b1 : F) : (QuadraticAlgebra F δ 0)[X] :=
  X ^ 2 + C ⟨a1, -b1⟩ * X + C ⟨a0, -b0⟩

theorem normForm_natDegree (δ a0 a1 b0 b1 : F) : (normForm δ a0 a1 b0 b1).natDegree = 4 := by
  unfold normForm; compute_degree!

theorem normForm_monic (δ a0 a1 b0 b1 : F) : (normForm δ a0 a1 b0 b1).Monic := by
  unfold normForm; monicity!

theorem normP_natDegree (δ a0 a1 b0 b1 : F) : (normP δ a0 a1 b0 b1).natDegree = 2 := by
  unfold normP; compute_degree!

theorem normP_monic (δ a0 a1 b0 b1 : F) : (normP δ a0 a1 b0 b1).Monic := by
  unfold normP; monicity!

/-- `A² - δ B² = (A + ω B)(A - ω B)` over `N`. -/
theorem map_normForm (a0 a1 b0 b1 : F) :
    (normForm δ a0 a1 b0 b1).map (algebraMap F (QuadraticAlgebra F δ 0)) =
      normP δ a0 a1 b0 b1 * normPbar δ a0 a1 b0 b1 := by
  set ι := algebraMap F (QuadraticAlgebra F δ 0)
  set w : QuadraticAlgebra F δ 0 := ⟨0, 1⟩
  have hw : C w * C w = C (ι δ) := by
    rw [← C_mul]; congr 1; ext <;> simp [w, ι, QuadraticAlgebra.algebraMap_eq]
  have e1 : (⟨a1, b1⟩ : QuadraticAlgebra F δ 0) = ι a1 + ι b1 * w := by
    ext <;> simp [w, ι, QuadraticAlgebra.algebraMap_eq]
  have e0 : (⟨a0, b0⟩ : QuadraticAlgebra F δ 0) = ι a0 + ι b0 * w := by
    ext <;> simp [w, ι, QuadraticAlgebra.algebraMap_eq]
  have e1' : (⟨a1, -b1⟩ : QuadraticAlgebra F δ 0) = ι a1 - ι b1 * w := by
    ext <;> simp [w, ι, QuadraticAlgebra.algebraMap_eq]
  have e0' : (⟨a0, -b0⟩ : QuadraticAlgebra F δ 0) = ι a0 - ι b0 * w := by
    ext <;> simp [w, ι, QuadraticAlgebra.algebraMap_eq]
  simp only [normForm, normP, normPbar, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_mul, map_X, map_C, e1, e0, e1', e0', C_add, C_sub, C_mul]
  linear_combination (C (ι b1) * X + C (ι b0)) ^ 2 * hw

theorem eval₂_normForm {S : Type*} [CommRing S] (φ : F →+* S) (t : S) (a0 a1 b0 b1 : F) :
    (normForm δ a0 a1 b0 b1).eval₂ φ t = (t ^ 2 + φ a1 * t + φ a0) ^ 2 - φ δ * (φ b1 * t + φ b0) ^ 2 := by
  simp only [normForm, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_add, eval₂_C, eval₂_X]

/-- **Irreducibility of a quartic of norm form.** -/
theorem irreducible_normForm [Fact (¬ IsSquare δ)] {a0 a1 b0 b1 : F} (hb1 : b1 ≠ 0)
    (hP : ∀ r : QuadraticAlgebra F δ 0, r ^ 2 + ⟨a1, b1⟩ * r + ⟨a0, b0⟩ ≠ 0) :
    Irreducible (normForm δ a0 a1 b0 b1) := by
  have hmon := normForm_monic δ a0 a1 b0 b1
  have hdeg := normForm_natDegree δ a0 a1 b0 b1
  have h1 : normForm δ a0 a1 b0 b1 ≠ 1 := by
    intro e; rw [e, natDegree_one] at hdeg; norm_num at hdeg
  rw [hmon.irreducible_iff_lt_natDegree_lt h1, hdeg]
  intro g hg hgdeg hgdvd
  simp only [Finset.mem_Ioc] at hgdeg
  have hd : g.natDegree = 1 ∨ g.natDegree = 2 := by omega
  rcases hd with hd1 | hd2
  · -- a linear factor gives a root `r` of `A² - δ B²` in `F`, hence `A(r) = B(r) = 0`
    have hgx := hg.eq_X_add_C hd1
    set r := -g.coeff 0
    have hroot : (normForm δ a0 a1 b0 b1).IsRoot r := by
      rw [← dvd_iff_isRoot]
      convert hgdvd using 1
      rw [hgx]; simp [r, sub_eq_add_neg]
    have ev : (normForm δ a0 a1 b0 b1).eval r =
        (r ^ 2 + a1 * r + a0) ^ 2 - δ * (b1 * r + b0) ^ 2 := by
      simp [normForm]
    rw [IsRoot, ev] at hroot
    have hB : b1 * r + b0 = 0 := by
      by_contra hB
      apply (Fact.out : ¬ IsSquare δ)
      refine ⟨(r ^ 2 + a1 * r + a0) / (b1 * r + b0), ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hB hB)]
      linear_combination -hroot
    have hA : r ^ 2 + a1 * r + a0 = 0 := by
      rw [hB] at hroot
      exact pow_eq_zero_iff (two_ne_zero) |>.mp (by linear_combination hroot)
    apply hP (algebraMap F _ r)
    ext
    · simp [QuadraticAlgebra.algebraMap_eq, sq]; linear_combination hA
    · simp [QuadraticAlgebra.algebraMap_eq, sq]; linear_combination hB
  · -- a quadratic factor: `A + ω B` is prime in `N[X]` and would be defined over `F`
    obtain ⟨g', hgg'⟩ := hgdvd
    have hg' : g'.Monic := hg.of_mul_monic_left (hgg' ▸ hmon)
    have hd' : g'.natDegree = 2 := by
      have := hg.natDegree_mul hg'
      rw [← hgg', hdeg, hd2] at this; omega
    set ι := algebraMap F (QuadraticAlgebra F δ 0)
    have hPirr : Irreducible (normP δ a0 a1 b0 b1) := by
      apply irreducible_of_degree_le_three_of_not_isRoot
      · rw [normP_natDegree]; decide
      · intro z hz
        apply hP z
        simpa [normP, IsRoot] using hz
    have hdvd : normP δ a0 a1 b0 b1 ∣ g.map ι * g'.map ι := by
      rw [← Polynomial.map_mul, ← hgg', map_normForm]; exact dvd_mul_right _ _
    have key : ∀ G : F[X], G.Monic → G.natDegree = 2 → normP δ a0 a1 b0 b1 ∣ G.map ι → False := by
      intro G hG hG2 hdv
      have e := eq_of_monic_of_dvd_of_natDegree_le (normP_monic δ a0 a1 b0 b1) (hG.map ι) hdv
        (by rw [natDegree_map, hG2, normP_natDegree])
      have := congrArg (fun p => (p.coeff 1).im) e
      simp [coeff_map, normP, ι, QuadraticAlgebra.algebraMap_eq, coeff_C] at this
      exact hb1 this.symm
    rcases hPirr.prime.dvd_or_dvd hdvd with h' | h'
    · exact key g hg hd2 h'
    · exact key g' hg' hd' h'

end Norm
section Nsq

variable {F : Type*} [Field F] {δ : F}

/-- `ρ = p0² - p0 p1 P1 + p1² P0` with `P1 = a1 + b1 ω`, `P0 = a0 + b0 ω`, `p_i = q_i - P_i`: the
resultant of `X² + q1 X + q0` and `X² + P1 X + P0`. -/
def rhoN (δ a0 a1 b0 b1 q0 q1 : F) : QuadraticAlgebra F δ 0 :=
  (algebraMap F _ q0 - ⟨a0, b0⟩) ^ 2 -
    (algebraMap F _ q0 - ⟨a0, b0⟩) * (algebraMap F _ q1 - ⟨a1, b1⟩) * ⟨a1, b1⟩ +
    (algebraMap F _ q1 - ⟨a1, b1⟩) ^ 2 * ⟨a0, b0⟩

/-- **The obstruction to `(q - c h)(T) ∈ F^× (F[T]/(f))^×2`** for `f = c q h`, `h = A² - δ B²`,
`disc q = δ`: the resultant `ρ` of `q` and `A + ω B` is not a square in `N`. -/
theorem nsq_normForm [Fact (¬ IsSquare δ)] (h2 : (2 : F) ≠ 0) {a0 a1 b0 b1 q0 q1 c : F}
    (hb1 : b1 ≠ 0) (hc : c ≠ 0) (hδ : q1 ^ 2 - 4 * q0 = δ)
    (hP : ∀ r : QuadraticAlgebra F δ 0, r ^ 2 + ⟨a1, b1⟩ * r + ⟨a0, b0⟩ ≠ 0)
    (hρ : ¬ IsSquare (rhoN δ a0 a1 b0 b1 q0 q1))
    {q h f : F[X]} (hq : q = X ^ 2 + C q1 * X + C q0) (hh : h = normForm δ a0 a1 b0 b1)
    (hf : f = C c * q * h) (hcop : IsCoprime q h) (c' : F) (y : AdjoinRoot f) :
    AdjoinRoot.mk f (q - C c * h) ≠ algebraMap F (AdjoinRoot f) c' * y ^ 2 := by
  intro hy
  -- `M = F[x]/(h)` is a field
  have hirr : Irreducible h := hh ▸ irreducible_normForm hb1 hP
  have : Fact (Irreducible h) := ⟨hirr⟩
  set x : AdjoinRoot h := AdjoinRoot.root h with hx
  set ιM := algebraMap F (AdjoinRoot h) with hιM
  set ιN := algebraMap F (QuadraticAlgebra F δ 0) with hιN
  have hofM : AdjoinRoot.of h = ιM := (AdjoinRoot.algebraMap_eq h).symm
  have hhx : h.eval₂ ιM x = 0 := by rw [← hofM]; exact AdjoinRoot.eval₂_root h
  have hfx : f.eval₂ ιM x = 0 := by rw [hf, eval₂_mul, hhx, mul_zero]
  -- the relation in `M`: `q(x) = c' Y1²`
  set πM := AdjoinRoot.lift ιM x hfx
  have e1 := congrArg πM hy
  rw [map_mul, map_pow, AdjoinRoot.lift_mk, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of,
    eval₂_sub, eval₂_mul, hhx, mul_zero, sub_zero] at e1
  -- the relation in `N`: `ν = -c h(τ) = c' Y2²` with `τ = (-q1 + ω)/2`
  obtain ⟨i2, hi2⟩ : ∃ i2 : F, 2 * i2 = 1 := ⟨_, mul_inv_cancel₀ h2⟩
  set τ : QuadraticAlgebra F δ 0 := ⟨-q1 * i2, i2⟩
  have hqτ : q.eval₂ ιN τ = 0 := by
    rw [hq]
    ext
    · simp [τ, ιN, QuadraticAlgebra.algebraMap_eq, sq]
      linear_combination (-(i2 ^ 2)) * hδ + (q1 ^ 2 * i2 - q0 * (2 * i2 + 1)) * hi2
    · simp [τ, ιN, QuadraticAlgebra.algebraMap_eq, sq]
      linear_combination (-(q1 * i2)) * hi2
  have hfτ : f.eval₂ ιN τ = 0 := by rw [hf, eval₂_mul, eval₂_mul, hqτ, mul_zero, zero_mul]
  set πN := AdjoinRoot.lift ιN τ hfτ
  have e2 := congrArg πN hy
  rw [map_mul, map_pow, AdjoinRoot.lift_mk, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of,
    eval₂_sub, eval₂_mul, hqτ, eval₂_C, zero_sub] at e2
  set ν := -(ιN c * h.eval₂ ιN τ) with hν
  have hν0 : ν ≠ 0 := by
    obtain ⟨u, v, huv⟩ := hcop
    have := congrArg (eval₂ ιN τ) huv
    rw [eval₂_add, eval₂_mul, eval₂_mul, hqτ, mul_zero, zero_add, eval₂_one] at this
    have hhτ : h.eval₂ ιN τ ≠ 0 := right_ne_zero_of_mul_eq_one this
    have hcN : ιN c ≠ 0 := (map_ne_zero ιN).mpr hc
    exact neg_ne_zero.mpr (mul_ne_zero hcN hhτ)
  -- the square root `s = -A(x)/B(x)` of `δ` in `M`
  set Ax := x ^ 2 + ιM a1 * x + ιM a0
  set Bx := ιM b1 * x + ιM b0
  have hAB : Ax ^ 2 - ιM δ * Bx ^ 2 = 0 := by
    rw [← hhx, congrArg (eval₂ ιM x) hh, eval₂_normForm]
  have hBx : Bx ≠ 0 := by
    intro hB0
    have hmk : AdjoinRoot.mk h (C b1 * X + C b0) = 0 := by
      rw [← hB0]; simp [Bx, hx, hιM, AdjoinRoot.algebraMap_eq]
    rw [AdjoinRoot.mk_eq_zero] at hmk
    have hne : C b1 * X + C b0 ≠ 0 := by
      intro h0; apply hb1; simpa using congrArg (coeff · 1) h0
    have := natDegree_le_of_dvd hmk hne
    rw [hh, normForm_natDegree] at this
    have h1 : (C b1 * X + C b0).natDegree ≤ 1 := by compute_degree
    omega
  set s : AdjoinRoot h := -Ax / Bx
  have hs : s * s = ιM δ := by
    rw [show s * s = Ax ^ 2 / Bx ^ 2 by simp only [s]; rw [neg_div, neg_mul_neg, div_mul_div_comm, sq, sq], div_eq_iff (pow_ne_zero 2 hBx)]
    linear_combination hAB
  set φ := extQ ιM s hs
  have hφι : ∀ r, φ (ιN r) = ιM r := fun r => extQ_algebraMap ιM s hs r
  have hφinj : Function.Injective φ := φ.injective
  have hφP1 : φ ⟨a1, b1⟩ = ιM a1 + ιM b1 * s := extQ_apply ιM s hs _
  have hφP0 : φ ⟨a0, b0⟩ = ιM a0 + ιM b0 * s := extQ_apply ιM s hs _
  have hx2 : x ^ 2 = -(φ ⟨a1, b1⟩ * x) - φ ⟨a0, b0⟩ := by
    rw [hφP1, hφP0]
    have : Ax + s * Bx = 0 := by simp only [s]; field_simp; ring
    linear_combination this
  -- every element of `M` is `φ u + φ v x`, uniquely
  have hdec : ∀ m : AdjoinRoot h, ∃ u v : QuadraticAlgebra F δ 0, m = φ u + φ v * x := by
    intro m
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective m
    induction p using Polynomial.induction_on with
    | C a => exact ⟨ιN a, 0, by rw [AdjoinRoot.mk_C, hφι, map_zero, zero_mul, add_zero]; rfl⟩
    | add p p' hp hp' =>
      obtain ⟨u, v, huv⟩ := hp
      obtain ⟨u', v', huv'⟩ := hp'
      exact ⟨u + u', v + v', by rw [map_add, huv, huv', map_add, map_add]; ring⟩
    | monomial n a ih =>
      obtain ⟨u, v, huv⟩ := ih
      refine ⟨-(v * ⟨a0, b0⟩), u - v * ⟨a1, b1⟩, ?_⟩
      have : AdjoinRoot.mk h (C a * X ^ (n + 1)) = AdjoinRoot.mk h (C a * X ^ n) * x := by
        rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
      rw [this, huv, map_neg, map_mul, map_sub, map_mul]
      linear_combination φ v * hx2
  have huniq : ∀ u v u' v' : QuadraticAlgebra F δ 0,
      φ u + φ v * x = φ u' + φ v' * x → u = u' ∧ v = v' := by
    intro u v u' v' he
    by_cases hv : v = v'
    · subst hv
      exact ⟨hφinj (by linear_combination he), rfl⟩
    · exfalso
      have hvv : v' - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
      set r := (u - u') / (v' - v)
      have hxr : x = φ r := by
        have hφv : φ (v' - v) ≠ 0 := (map_ne_zero φ).mpr hvv
        have : φ (v' - v) * x = φ (u - u') := by rw [map_sub, map_sub]; linear_combination -he
        rw [map_div₀, ← this]; field_simp
      apply hP r
      apply hφinj
      rw [map_zero, map_add, map_add, map_pow, map_mul, ← hxr]
      linear_combination hx2
  -- `q(x) φ(ν)` is a square in `M`
  set Y := ιM c' * πM y * φ (πN y)
  have hqx : x ^ 2 + ιM q1 * x + ιM q0 = φ (ιN q0 - ⟨a0, b0⟩) + φ (ιN q1 - ⟨a1, b1⟩) * x := by
    rw [map_sub, map_sub, hφι, hφι]; linear_combination hx2
  have e1' : q.eval₂ ιM x = x ^ 2 + ιM q1 * x + ιM q0 := by rw [hq]; simp
  have hY : q.eval₂ ιM x * φ ν = Y ^ 2 := by
    rw [e1, e2, map_mul, map_pow, hφι]
    simp only [Y]; ring
  obtain ⟨u, v, hYuv⟩ := hdec Y
  have hlhs : q.eval₂ ιM x * φ ν =
      φ (ν * (ιN q0 - ⟨a0, b0⟩)) + φ (ν * (ιN q1 - ⟨a1, b1⟩)) * x := by
    rw [e1', hqx, map_mul, map_mul]; ring
  have hrhs : Y ^ 2 = φ (u ^ 2 - v ^ 2 * ⟨a0, b0⟩) + φ (2 * u * v - v ^ 2 * ⟨a1, b1⟩) * x := by
    rw [hYuv]; simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination φ v ^ 2 * hx2
  obtain ⟨h0, h1⟩ := huniq _ _ _ _ (hlhs.symm.trans (hY.trans hrhs))
  -- the norm to `N`: `ν² ρ = (u² - u v P1 + v² P0)²`
  apply hρ
  refine ⟨(u ^ 2 - u * v * ⟨a1, b1⟩ + v ^ 2 * ⟨a0, b0⟩) / ν, ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hν0 hν0), rhoN]
  linear_combination (ν * (ιN q0 - ⟨a0, b0⟩) + (u ^ 2 - v ^ 2 * ⟨a0, b0⟩)) * h0 -
    ⟨a1, b1⟩ * (ν * (ιN q1 - ⟨a1, b1⟩) * h0 + (u ^ 2 - v ^ 2 * ⟨a0, b0⟩) * h1) +
    ⟨a0, b0⟩ * (ν * (ιN q1 - ⟨a1, b1⟩) + (2 * u * v - v ^ 2 * ⟨a1, b1⟩)) * h1

/-- The rational part of `ρ`. -/
def rho0 (δ a0 a1 b0 b1 q0 q1 : F) : F :=
  q0 * a1 ^ 2 - q1 * a0 * a1 - q0 * q1 * a1 + δ * q0 * b1 ^ 2 - δ * q1 * b0 * b1 + a0 ^ 2 +
    (q1 ^ 2 - 2 * q0) * a0 + δ * b0 ^ 2 + q0 ^ 2

/-- The `ω` part of `ρ`. -/
def rho1 (_δ a0 a1 b0 b1 q0 q1 : F) : F :=
  2 * q0 * a1 * b1 - q1 * a1 * b0 - q1 * a0 * b1 - q0 * q1 * b1 + 2 * a0 * b0 + (q1 ^ 2 - 2 * q0) * b0

theorem rhoN_eq (δ a0 a1 b0 b1 q0 q1 : F) :
    rhoN δ a0 a1 b0 b1 q0 q1 = ⟨rho0 δ a0 a1 b0 b1 q0 q1, rho1 δ a0 a1 b0 b1 q0 q1⟩ := by
  ext <;> simp [rhoN, rho0, rho1, sq, QuadraticAlgebra.algebraMap_eq]
  · ring_nf
  · ring_nf

/-- The discriminant `P1² - 4 P0` of `X² + P1 X + P0` in coordinates. -/
theorem discN_eq (δ a0 a1 b0 b1 : F) :
    (⟨a1, b1⟩ : QuadraticAlgebra F δ 0) ^ 2 - 4 * ⟨a0, b0⟩ =
      ⟨a1 ^ 2 + δ * b1 ^ 2 - 4 * a0, 2 * a1 * b1 - 4 * b0⟩ := by
  ext <;> simp [sq, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring

/-- The coefficients of `A² - δ B²`. -/
theorem normForm_eq (δ a0 a1 b0 b1 : F) :
    normForm δ a0 a1 b0 b1 = X ^ 4 + C (2 * a1) * X ^ 3 + C (a1 ^ 2 + 2 * a0 - δ * b1 ^ 2) * X ^ 2 +
      C (2 * a0 * a1 - 2 * δ * b0 * b1) * X + C (a0 ^ 2 - δ * b0 ^ 2) := by
  simp only [normForm, map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

theorem map_normForm_ringHom {F' : Type*} [Field F'] (φ : F →+* F') (δ a0 a1 b0 b1 : F) :
    (normForm δ a0 a1 b0 b1).map φ = normForm (φ δ) (φ a0) (φ a1) (φ b0) (φ b1) := by
  simp only [normForm, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
    map_X, map_C]

end Nsq

end FurioLombardo.Discharge.M3a
