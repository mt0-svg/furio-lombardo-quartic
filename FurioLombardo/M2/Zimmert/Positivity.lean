import FurioLombardo.M2.Zimmert.Defs

/-!
# Zimmert's Lemma 1 at `γ = 1/2` (lane M2)

The inverse Mellin transform of Zimmert's `Q(s) = R(s) (2/s)^a (2/(s+1))^b` against a Dirichlet
series with nonnegative coefficients has nonnegative real part on the line `Re s = 2`.
Proof: `Q(2+it)` is `2^(a+b) (Π₁(t) + α Π₂(t))` with `Π` products of `(λ + it)⁻¹`, `λ > 0`;
`re_integral_prod_inv_nonneg` by Gaussian damping, Fubini and dominated convergence.
-/

namespace FurioLombardo.M2.Zimmert

open Complex MeasureTheory

namespace PosAux

open Filter Topology Set

lemma lam_add_ne_zero {l : ℝ} (hl : 0 < l) (t : ℝ) : (l : ℂ) + t * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

lemma norm_lam_add_ge {l c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hcl : c ≤ l) (t : ℝ) :
    c * Real.sqrt (1 + t ^ 2) ≤ ‖(l : ℂ) + t * I‖ := by
  rw [Complex.norm_add_mul_I]
  rw [← Real.sqrt_sq hc0.le, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  have h1 : c ^ 2 ≤ l ^ 2 := pow_le_pow_left₀ hc0.le hcl 2
  have h2 : c ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg t]

lemma norm_prod_inv_le {N : ℕ} (hN : 2 ≤ N) (lam : Fin N → ℝ) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1) (hc : ∀ j, c ≤ lam j) (t : ℝ) :
    ‖∏ j, ((lam j : ℂ) + t * I)⁻¹‖ ≤ (c ^ N)⁻¹ * (1 + t ^ 2)⁻¹ := by
  set w := Real.sqrt (1 + t ^ 2) with hw
  have hw1 : 1 ≤ w := by
    rw [hw, Real.one_le_sqrt]; nlinarith [sq_nonneg t]
  have hw0 : 0 < w := by linarith
  rw [norm_prod]
  calc ∏ j, ‖((lam j : ℂ) + t * I)⁻¹‖ ≤ ∏ _j : Fin N, (c * w)⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro j _; exact norm_nonneg _
        · intro j _
          rw [norm_inv]
          exact inv_anti₀ (by positivity) (norm_lam_add_ge hc0 hc1 (hc j) t)
    _ = (c ^ N)⁻¹ * (w ^ N)⁻¹ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, mul_pow, mul_inv]
    _ ≤ (c ^ N)⁻¹ * (1 + t ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply inv_anti₀ (by positivity)
        calc 1 + t ^ 2 = w ^ 2 := by rw [hw, Real.sq_sqrt (by positivity)]
          _ ≤ w ^ N := pow_le_pow_right₀ hw1 hN

lemma exists_lower {N : ℕ} (hN : 2 ≤ N) (lam : Fin N → ℝ) (hlam : ∀ j, 0 < lam j) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ j, c ≤ lam j := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  refine ⟨min 1 (Finset.univ.inf' hne lam), ?_, min_le_left _ _, fun j => ?_⟩
  · apply lt_min one_pos
    rw [Finset.lt_inf'_iff]
    intro j _; exact hlam j
  · exact (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ j))

lemma continuous_prod_inv {N : ℕ} (lam : Fin N → ℝ) (hlam : ∀ j, 0 < lam j) :
    Continuous fun t : ℝ => ∏ j, ((lam j : ℂ) + t * I)⁻¹ := by
  apply continuous_finsetProd
  intro j _
  exact Continuous.inv₀ (by fun_prop) (fun t => lam_add_ne_zero (hlam j) t)

lemma integrable_prod_inv {N : ℕ} (hN : 2 ≤ N) (lam : Fin N → ℝ) (hlam : ∀ j, 0 < lam j)
    (y : ℝ) : Integrable fun t : ℝ => cexp (y * t * I) * ∏ j, ((lam j : ℂ) + t * I)⁻¹ := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_lower hN lam hlam
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (c ^ N)⁻¹) ?_ ?_
  · exact (Continuous.mul (by fun_prop) (continuous_prod_inv lam hlam)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun t => ?_)
    rw [norm_mul]
    have : ‖cexp (y * t * I)‖ = 1 := by
      rw [← Complex.ofReal_mul]; exact Complex.norm_exp_ofReal_mul_I _
    rw [this, one_mul]
    exact norm_prod_inv_le hN lam hc0 hc1 hc t

lemma norm_gauss (ε t : ℝ) : ‖cexp (-(ε : ℂ) * (t : ℂ) ^ 2)‖ = Real.exp (-ε * t ^ 2) := by
  rw [Complex.norm_exp, ← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    Complex.ofReal_re]

lemma norm_exp_lam (l t w : ℝ) : ‖cexp (-((l : ℂ) + t * I) * w)‖ = Real.exp (-l * w) := by
  rw [Complex.norm_exp]
  congr 1
  simp

lemma integral_exp_Ioi_eq_inv {l : ℝ} (hl : 0 < l) (t : ℝ) :
    ∫ w in Ioi (0 : ℝ), cexp (-((l : ℂ) + t * I) * w) = ((l : ℂ) + t * I)⁻¹ := by
  have ha : (-((l : ℂ) + t * I)).re < 0 := by simp; linarith
  rw [integral_exp_mul_complex_Ioi ha 0, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    neg_div_neg_eq, one_div]

lemma prod_inv_eq_integral {N : ℕ} (lam : Fin N → ℝ) (hlam : ∀ j, 0 < lam j) (t : ℝ) :
    ∫ v, ∏ j, cexp (-((lam j : ℂ) + t * I) * v j)
        ∂(Measure.pi fun _ : Fin N => (volume : Measure ℝ).restrict (Ioi 0))
      = ∏ j, ((lam j : ℂ) + t * I)⁻¹ := by
  rw [integral_fintype_prod_eq_prod (f := fun j (w : ℝ) => cexp (-((lam j : ℂ) + t * I) * (w : ℂ)))]
  exact Finset.prod_congr rfl (fun j _ => integral_exp_Ioi_eq_inv (hlam j) t)

lemma inner_eq {N : ℕ} (lam : Fin N → ℝ) (y : ℝ) {ε : ℝ} (hε : 0 < ε) (v : Fin N → ℝ) :
    ∫ t : ℝ, cexp (-(ε : ℂ) * (t : ℂ) ^ 2) *
        (cexp (y * t * I) * ∏ j, cexp (-((lam j : ℂ) + t * I) * v j))
      = ((Real.exp (-∑ j, lam j * v j) * ((Real.pi / ε) ^ (1 / 2 : ℝ) *
          Real.exp (-(y - ∑ j, v j) ^ 2 / (4 * ε))) : ℝ) : ℂ) := by
  have hpt : ∀ t : ℝ, cexp (-(ε : ℂ) * (t : ℂ) ^ 2) *
        (cexp (y * t * I) * ∏ j, cexp (-((lam j : ℂ) + t * I) * v j))
      = cexp (-(∑ j, (lam j : ℂ) * v j)) *
        (cexp (I * ((y : ℂ) - ∑ j, (v j : ℂ)) * t) * cexp (-(ε : ℂ) * (t : ℂ) ^ 2)) := by
    intro t
    rw [← Complex.exp_sum]
    simp only [← Complex.exp_add]
    congr 1
    have hs : ∑ j, (-((lam j : ℂ) + t * I) * v j)
        = -(∑ j, (lam j : ℂ) * v j) - t * I * ∑ j, (v j : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hs]; ring
  simp_rw [hpt]
  rw [integral_const_mul, fourierIntegral_gaussian (by simpa using hε)]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_cpow (by positivity)]
  push_cast
  ring_nf

lemma integrable_G {N : ℕ} (lam : Fin N → ℝ) (hlam : ∀ j, 0 < lam j) (y : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    Integrable (Function.uncurry fun (t : ℝ) (v : Fin N → ℝ) =>
        cexp (-(ε : ℂ) * (t : ℂ) ^ 2) *
          (cexp (y * t * I) * ∏ j, cexp (-((lam j : ℂ) + t * I) * v j)))
      ((volume : Measure ℝ).prod
        (Measure.pi fun _ : Fin N => (volume : Measure ℝ).restrict (Ioi 0))) := by
  have hb : Integrable (fun p : ℝ × (Fin N → ℝ) =>
      Real.exp (-ε * p.1 ^ 2) * ∏ j, Real.exp (-lam j * p.2 j))
      ((volume : Measure ℝ).prod
        (Measure.pi fun _ : Fin N => (volume : Measure ℝ).restrict (Ioi 0))) := by
    exact Integrable.mul_prod (f := fun t : ℝ => Real.exp (-ε * t ^ 2))
      (g := fun v : Fin N → ℝ => ∏ j, Real.exp (-lam j * v j)) (integrable_exp_neg_mul_sq hε)
      (Integrable.fintype_prod (f := fun j w => Real.exp (-lam j * w))
      (fun j => exp_neg_integrableOn_Ioi 0 (hlam j)))
  refine hb.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    show Continuous fun p : ℝ × (Fin N → ℝ) => cexp (-(ε : ℂ) * (p.1 : ℂ) ^ 2) *
          (cexp (y * p.1 * I) * ∏ j, cexp (-((lam j : ℂ) + p.1 * I) * p.2 j))
    fun_prop
  · refine Filter.Eventually.of_forall (fun p => ?_)
    show ‖cexp (-(ε : ℂ) * (p.1 : ℂ) ^ 2) *
          (cexp (y * p.1 * I) * ∏ j, cexp (-((lam j : ℂ) + p.1 * I) * p.2 j))‖ ≤ _
    rw [norm_mul, norm_mul, norm_prod, norm_gauss]
    have : ‖cexp (y * p.1 * I)‖ = 1 := by
      rw [← Complex.ofReal_mul]; exact Complex.norm_exp_ofReal_mul_I _
    rw [this, one_mul]
    simp_rw [norm_exp_lam]
    rfl

lemma re_damped_nonneg {N : ℕ} (lam : Fin N → ℝ) (hlam : ∀ j, 0 < lam j) (y : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    0 ≤ (∫ t : ℝ, cexp (-(ε : ℂ) * (t : ℂ) ^ 2) *
      (cexp (y * t * I) * ∏ j, ((lam j : ℂ) + t * I)⁻¹)).re := by
  have h1 : ∀ t : ℝ, cexp (-(ε : ℂ) * (t : ℂ) ^ 2) *
        (cexp (y * t * I) * ∏ j, ((lam j : ℂ) + t * I)⁻¹)
      = ∫ v, cexp (-(ε : ℂ) * (t : ℂ) ^ 2) *
          (cexp (y * t * I) * ∏ j, cexp (-((lam j : ℂ) + t * I) * v j))
          ∂(Measure.pi fun _ : Fin N => (volume : Measure ℝ).restrict (Ioi 0)) := by
    intro t
    rw [integral_const_mul, integral_const_mul, prod_inv_eq_integral lam hlam t]
  simp_rw [h1]
  rw [integral_integral_swap (integrable_G lam hlam y hε)]

  simp_rw [inner_eq lam y hε]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  apply integral_nonneg
  intro v
  positivity

/-- Proof of `re_integral_prod_inv_nonneg`: Gaussian damping `exp(-ε t²)`, Fubini against
the Laplace representation of the product, and dominated convergence as `ε → 0+`. -/
theorem re_integral_prod_inv_nonneg_aux {N : ℕ} (hN : 2 ≤ N) (lam : Fin N → ℝ)
    (hlam : ∀ j, 0 < lam j) (y : ℝ) :
    0 ≤ (∫ t : ℝ, cexp (y * t * I) * ∏ j, ((lam j : ℂ) + t * I)⁻¹).re := by
  have hint := integrable_prod_inv hN lam hlam y
  have hT : Tendsto (fun ε : ℝ => ∫ t : ℝ, cexp (-(ε : ℂ) * (t : ℂ) ^ 2) *
      (cexp (y * t * I) * ∏ j, ((lam j : ℂ) + t * I)⁻¹))
      (𝓝[>] 0) (𝓝 (∫ t : ℝ, cexp (y * t * I) * ∏ j, ((lam j : ℂ) + t * I)⁻¹)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => ‖cexp (y * t * I) * ∏ j, ((lam j : ℂ) + t * I)⁻¹‖)
    · refine Filter.Eventually.of_forall (fun ε => ?_)
      exact (Continuous.mul (by fun_prop)
        (Continuous.mul (by fun_prop) (continuous_prod_inv lam hlam))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Filter.Eventually.of_forall (fun t => ?_)
      rw [norm_mul]
      have h0 : 0 ≤ ε := le_of_lt hε
      have : ‖cexp (-(ε : ℂ) * (t : ℂ) ^ 2)‖ ≤ 1 := by
        rw [norm_gauss, Real.exp_le_one_iff]
        nlinarith [sq_nonneg t]
      calc _ ≤ 1 * ‖cexp (y * t * I) * ∏ j, ((lam j : ℂ) + t * I)⁻¹‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = _ := one_mul _
    · exact hint.norm
    · refine Filter.Eventually.of_forall (fun t => ?_)
      have hc : Continuous (fun ε : ℝ => cexp (-(ε : ℂ) * (t : ℂ) ^ 2)) := by fun_prop
      have h2 : Tendsto (fun ε : ℝ => cexp (-(ε : ℂ) * (t : ℂ) ^ 2)) (𝓝[>] 0) (𝓝 1) := by
        have := hc.tendsto 0
        simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      simpa using h2.mul_const (cexp (y * t * I) * ∏ j, ((lam j : ℂ) + t * I)⁻¹)
  have hre := (Complex.continuous_re.tendsto _).comp hT
  exact ge_of_tendsto hre
    (eventually_nhdsWithin_of_forall (fun ε hε => re_damped_nonneg lam hlam y hε))

end PosAux

/-- For at least two factors with `λ_j > 0`, the Fourier integral of `Π (λ_j + it)⁻¹` has
nonnegative real part at every frequency `y`. -/
theorem re_integral_prod_inv_nonneg {N : ℕ} (hN : 2 ≤ N) (lam : Fin N → ℝ)
    (hlam : ∀ j, 0 < lam j) (y : ℝ) :
    0 ≤ (∫ t : ℝ, cexp (y * t * I) * ∏ j, ((lam j : ℂ) + t * I)⁻¹).re := by
  exact PosAux.re_integral_prod_inv_nonneg_aux hN lam hlam y

namespace PosAux

open Filter Topology Set

lemma prod_list_eq (L : List ℝ) (t : ℝ) :
    ∏ j : Fin L.length, (((L[j.1] : ℝ) : ℂ) + t * I)⁻¹
      = (L.map fun l : ℝ => ((l : ℂ) + t * I)⁻¹).prod :=
  Fin.prod_univ_fun_getElem L (fun l : ℝ => ((l : ℂ) + t * I)⁻¹)

lemma integrable_list (L : List ℝ) (hL : 2 ≤ L.length) (hpos : ∀ l ∈ L, 0 < l) (y : ℝ) :
    Integrable fun t : ℝ => cexp (y * t * I) * (L.map fun l : ℝ => ((l : ℂ) + t * I)⁻¹).prod := by
  have h := integrable_prod_inv hL (fun j : Fin L.length => L[j.1])
    (fun j => hpos _ (List.getElem_mem _)) y
  simp only [prod_list_eq] at h
  exact h

lemma re_integral_list_nonneg (L : List ℝ) (hL : 2 ≤ L.length) (hpos : ∀ l ∈ L, 0 < l)
    (y : ℝ) :
    0 ≤ (∫ t : ℝ, cexp (y * t * I) * (L.map fun l : ℝ => ((l : ℂ) + t * I)⁻¹).prod).re := by
  have h := re_integral_prod_inv_nonneg hL (fun j : Fin L.length => L[j.1])
    (fun j => hpos _ (List.getElem_mem _)) y
  simp only [prod_list_eq] at h
  exact h

lemma comb_integrable_re (L1 L2 : List ℝ) (h1 : 2 ≤ L1.length) (h2 : 2 ≤ L2.length)
    (p1 : ∀ l ∈ L1, 0 < l) (p2 : ∀ l ∈ L2, 0 < l) {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (Q : ℝ → ℂ)
    (hQ : ∀ t : ℝ, Q t = (c1 : ℂ) * (L1.map fun l : ℝ => ((l : ℂ) + t * I)⁻¹).prod
      + (c2 : ℂ) * (L2.map fun l : ℝ => ((l : ℂ) + t * I)⁻¹).prod) (y : ℝ) :
    Integrable (fun t : ℝ => cexp (y * t * I) * Q t) ∧
      0 ≤ (∫ t : ℝ, cexp (y * t * I) * Q t).re := by
  have e : ∀ t : ℝ, cexp (y * t * I) * Q t
      = (c1 : ℂ) * (cexp (y * t * I) * (L1.map fun l : ℝ => ((l : ℂ) + t * I)⁻¹).prod)
        + (c2 : ℂ) * (cexp (y * t * I) * (L2.map fun l : ℝ => ((l : ℂ) + t * I)⁻¹).prod) := by
    intro t; rw [hQ]; ring
  have i1 := integrable_list L1 h1 p1 y
  have i2 := integrable_list L2 h2 p2 y
  simp_rw [e]
  refine ⟨(i1.const_mul _).add (i2.const_mul _), ?_⟩
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  exact add_nonneg (mul_nonneg hc1 (re_integral_list_nonneg L1 h1 p1 y))
    (mul_nonneg hc2 (re_integral_list_nonneg L2 h2 p2 y))

lemma dirichlet_part {ι : Type*} (ν : ι → ℝ) (hν : ∀ i, 1 ≤ ν i)
    (hνs : Summable fun i => ν i ^ (-2 : ℝ)) {x : ℝ} (hx : 0 < x) (Q : ℝ → ℂ)
    (hQi : ∀ y : ℝ, Integrable fun t : ℝ => cexp (y * t * I) * Q t)
    (hQr : ∀ y : ℝ, 0 ≤ (∫ t : ℝ, cexp (y * t * I) * Q t).re) :
    0 ≤ (∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Q t * dser ν (2 + t * I)).re := by
  have hνpos : ∀ i, 0 < ν i := fun i => lt_of_lt_of_le one_pos (hν i)
  have : Countable ι := by
    have hs := hνs.countable_support
    have : Function.support (fun i => ν i ^ (-2 : ℝ)) = Set.univ := by
      ext i; simp [(hνpos i).ne']
    rw [this] at hs
    exact Set.countable_univ_iff.mp hs
  obtain ⟨c, hc⟩ : ∃ c : ι → ℝ, c = fun i => Real.exp (Real.log x * 2 + Real.log (ν i) * (-2)) :=
    ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ι → ℝ, L = fun i => Real.log x - Real.log (ν i) := ⟨_, rfl⟩
  have hc0 : ∀ i, 0 ≤ c i := fun i => by rw [hc]; exact (Real.exp_pos _).le
  have hF : ∀ i (t : ℝ), (x : ℂ) ^ ((2 : ℂ) + t * I) * Q t * ((ν i : ℝ) : ℂ) ^ (-((2 : ℂ) + t * I))
      = ((c i : ℝ) : ℂ) * (cexp (L i * t * I) * Q t) := by
    intro i t
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hν0 : ((ν i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hνpos i).ne'
    rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hν0,
      ← Complex.ofReal_log hx.le, ← Complex.ofReal_log (hνpos i).le]
    have e : cexp (↑(Real.log x) * ((2 : ℂ) + t * I)) *
        cexp (↑(Real.log (ν i)) * -((2 : ℂ) + t * I))
        = ((c i : ℝ) : ℂ) * cexp (L i * t * I) := by
      simp only [hc, hL]
      rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
      congr 1; push_cast; ring
    calc _ = cexp (↑(Real.log x) * ((2 : ℂ) + t * I)) *
          cexp (↑(Real.log (ν i)) * -((2 : ℂ) + t * I)) * Q t := by ring
      _ = _ := by rw [e]; ring
  have hsum : ∀ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) * Q t * dser ν (2 + t * I)
      = ∑' i, ((c i : ℝ) : ℂ) * (cexp (L i * t * I) * Q t) := by
    intro t
    rw [dser, ← tsum_mul_left]
    exact tsum_congr (fun i => hF i t)
  have hint : ∀ i, Integrable fun t : ℝ => ((c i : ℝ) : ℂ) * (cexp (L i * t * I) * Q t) :=
    fun i => (hQi (L i)).const_mul _
  have hnorm : ∀ i, ∫ t : ℝ, ‖((c i : ℝ) : ℂ) * (cexp (L i * t * I) * Q t)‖
      = c i * ∫ t : ℝ, ‖Q t‖ := by
    intro i
    rw [← integral_const_mul]
    congr 1; ext t
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 i),
      ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hcs : Summable c := by
    have : c = fun i => x ^ (2 : ℝ) * ν i ^ (-2 : ℝ) := by
      rw [hc]; ext i
      rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos (hνpos i), ← Real.exp_add]
    rw [this]; exact hνs.mul_left _
  have hS : Summable fun i => ∫ t : ℝ, ‖((c i : ℝ) : ℂ) * (cexp (L i * t * I) * Q t)‖ := by
    simp_rw [hnorm]; exact hcs.mul_right _
  have hHas := hasSum_integral_of_summable_integral_norm hint hS
  simp_rw [hsum]
  refine (Complex.hasSum_re hHas).nonneg (fun i => ?_)
  show 0 ≤ (∫ t : ℝ, ((c i : ℝ) : ℂ) * (cexp (L i * t * I) * Q t)).re
  rw [integral_const_mul, Complex.re_ofReal_mul]
  exact mul_nonneg (hc0 i) (hQr (L i))

lemma Q_alg (a' b : ℕ) (α β : ℝ) (z : ℂ) (h0 : z ≠ 0) :
    (z + α) / ((z + β) * (z + 1 - β) * (z + 1 - α)) * (2 / z) ^ (a' + 1) * (2 / (z + 1)) ^ b
      = 2 ^ (a' + 1 + b) * ((z + β)⁻¹ * (z + 1 - β)⁻¹ * (z + 1 - α)⁻¹ * z⁻¹ ^ a' * (z + 1)⁻¹ ^ b)
        + 2 ^ (a' + 1 + b) * α *
          (z⁻¹ * ((z + β)⁻¹ * (z + 1 - β)⁻¹ * (z + 1 - α)⁻¹ * z⁻¹ ^ a' * (z + 1)⁻¹ ^ b)) := by
  have hu : z * z⁻¹ = 1 := mul_inv_cancel₀ h0
  rw [div_eq_mul_inv (z + α), mul_inv, mul_inv]
  linear_combination (2 ^ (a' + 1 + b) *
    ((z + β)⁻¹ * (z + 1 - β)⁻¹ * (z + 1 - α)⁻¹ * z⁻¹ ^ a' * (z + 1)⁻¹ ^ b)) * hu

end PosAux

/-- Zimmert's Lemma 1 at `γ = 1/2`, integrated against a Dirichlet series `Σ ν_i^{-s}`. -/
theorem re_integral_right_nonneg (a b : ℕ) (ha : 1 ≤ a) {α β : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (hβ : 0 ≤ β) (hβ1 : β < 1) {x : ℝ} (hx : 0 < x) {ι : Type*} (ν : ι → ℝ)
    (hν : ∀ i, 1 ≤ ν i) (hνs : Summable fun i => ν i ^ (-2 : ℝ)) :
    0 ≤ (∫ t : ℝ, (x : ℂ) ^ ((2 : ℂ) + t * I) *
      (Rz α β (2 + t * I) * (2 / (2 + t * I)) ^ a * (2 / (2 + t * I + 1)) ^ b) *
        dser ν (2 + t * I)).re := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨L1, hL1⟩ : ∃ L1 : List ℝ,
      L1 = [2 + β, 3 - β, 3 - α] ++ List.replicate a' 2 ++ List.replicate b 3 := ⟨_, rfl⟩
  have hL1pos : ∀ l ∈ L1, 0 < l := by
    intro l hl
    rw [hL1] at hl
    simp only [List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil,
      or_false] at hl
    rcases hl with ((rfl | rfl | rfl) | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> linarith
  have hL2pos : ∀ l ∈ (2 :: L1), 0 < l := by
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · norm_num
    · exact hL1pos l hl
  have hL1len : 2 ≤ L1.length := by
    rw [hL1]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
    omega
  have hL2len : 2 ≤ (2 :: L1).length := by simp; omega
  have hQ : ∀ t : ℝ, Rz α β (2 + t * I) * (2 / (2 + t * I)) ^ (a' + 1) *
        (2 / (2 + t * I + 1)) ^ b
      = ((2 ^ (a' + 1 + b) : ℝ) : ℂ) * (L1.map fun l : ℝ => ((l : ℂ) + t * I)⁻¹).prod
        + ((2 ^ (a' + 1 + b) * α : ℝ) : ℂ) *
          ((2 :: L1).map fun l : ℝ => ((l : ℂ) + t * I)⁻¹).prod := by
    intro t
    have h0 : (2 : ℂ) + t * I ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have e1 : ((2 + β : ℝ) : ℂ) + t * I = (2 + t * I) + β := by push_cast; ring
    have e2 : ((3 - β : ℝ) : ℂ) + t * I = (2 + t * I) + 1 - β := by push_cast; ring
    have e3 : ((3 - α : ℝ) : ℂ) + t * I = (2 + t * I) + 1 - α := by push_cast; ring
    have e4 : ((2 : ℝ) : ℂ) + t * I = 2 + t * I := by push_cast; ring
    have e5 : ((3 : ℝ) : ℂ) + t * I = (2 + t * I) + 1 := by push_cast; ring
    rw [Rz, PosAux.Q_alg a' b α β _ h0, hL1]
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, List.map_replicate, List.prod_replicate, e1, e2, e3, e4, e5]
    push_cast
    ring
  have hc1 : (0 : ℝ) ≤ 2 ^ (a' + 1 + b) := by positivity
  have hc2 : (0 : ℝ) ≤ 2 ^ (a' + 1 + b) * α := by positivity
  have hcomb := PosAux.comb_integrable_re L1 (2 :: L1) hL1len hL2len hL1pos hL2pos hc1 hc2
    (fun t : ℝ => Rz α β (2 + t * I) * (2 / (2 + t * I)) ^ (a' + 1) *
      (2 / (2 + t * I + 1)) ^ b) hQ
  exact PosAux.dirichlet_part ν hν hνs hx
    (fun t : ℝ => Rz α β (2 + t * I) * (2 / (2 + t * I)) ^ (a' + 1) *
      (2 / (2 + t * I + 1)) ^ b)
    (fun y => (hcomb y).1) (fun y => (hcomb y).2)

end FurioLombardo.M2.Zimmert
