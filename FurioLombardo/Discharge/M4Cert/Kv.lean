import Mathlib

/-!
# The completion `K_v` of K21 at the place above 2 with `e = 3`, as `ℚ_2[x]/(E)`

`E` is the Eisenstein cubic of code/earlier-computations/completion_kv.gp (integer coefficients,
`E ≡ x³ + 2 mod 4`), `Kv = ℚ_[2][x]/(E)` and `pv` the class of `x`; the coordinates of lane M4
(`V = Fin 6 → ℤ_[2]`, O_v on the basis 1, π, π²) are the coordinates on the power basis
`1, pv, pv²`. `Kv` carries the spectral norm of `Kv/ℚ_[2]` (Mathlib `spectralNorm`): a complete
ultrametric nontrivially normed field whose norm extends the 2-adic norm. Integer triples `T3` with
the multiplication of `ℤ[x]/(E)` map to `Kv` by `evZ`; the unit ball is the set of
`ℤ_[2]`-combinations of `1, pv, pv²` (`norm_evQ`).

## Instances

* `NontriviallyNormedField Kv` is `spectralNorm.nontriviallyNormedField ℚ_[2] Kv`, so
  `‖x‖ = spectralNorm ℚ_[2] Kv x` holds by `rfl`.
* `NormedAlgebra ℚ_[2] Kv` reuses the `Algebra ℚ_[2] Kv` instance as its `toAlgebra` field (the
  two agree at reducible-and-instances transparency, checked below); its `norm_smul_le` is the
  one of `spectralNorm.normedAlgebra`.
* `CompleteSpace Kv` is `FiniteDimensional.complete ℚ_[2] Kv`, for the uniform structure of the
  normed field instance; `spectralNorm.completeSpace ℚ_[2] Kv` has the same type (checked below).
* `IsUltrametricDist Kv` comes from `isNonarchimedean_spectralNorm`.
-/

namespace FurioLombardo.Discharge.M4Cert

open Polynomial

/-! ## The Eisenstein cubic -/

/-- Constant coefficient of `E`. -/
def e0 : ℤ := 17325639337422721302482
/-- Coefficient of `x` in `E`. -/
def e1 : ℤ := 16418729904282180494548
/-- Coefficient of `x²` in `E`. -/
def e2 : ℤ := 37469486047374096441064

/-- `E = x³ + e2 x² + e1 x + e0` over `ℤ`. -/
noncomputable def EZ : ℤ[X] := X ^ 3 + C e2 * X ^ 2 + C e1 * X + C e0

/-- `E` over `ℚ_[2]`. -/
noncomputable def EQ : ℚ_[2][X] := EZ.map (Int.castRingHom ℚ_[2])

/-- `E` is monic over `ℤ`. -/
theorem EZ_monic : EZ.Monic := by unfold EZ; monicity!

/-- `E` has degree 3 over `ℤ`. -/
theorem EZ_natDegree : EZ.natDegree = 3 := by unfold EZ; compute_degree!

/-- The constant coefficient of `E` is `e0`. -/
theorem EZ_coeff_zero : EZ.coeff 0 = e0 := by
  rw [EZ]; simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]; norm_num

/-- The coefficient of `x` in `E` is `e1`. -/
theorem EZ_coeff_one : EZ.coeff 1 = e1 := by
  rw [EZ]; simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]; norm_num

/-- The coefficient of `x²` in `E` is `e2`. -/
theorem EZ_coeff_two : EZ.coeff 2 = e2 := by
  rw [EZ]; simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]; norm_num

theorem EQ_monic : EQ.Monic := EZ_monic.map _

theorem EQ_natDegree : EQ.natDegree = 3 := by
  rw [EQ, EZ_monic.natDegree_map, EZ_natDegree]

/-- `2 ∣ e1`. -/
theorem two_dvd_e1 : (2 : ℤ) ∣ e1 := by unfold e1; norm_num
/-- `2 ∣ e2`. -/
theorem two_dvd_e2 : (2 : ℤ) ∣ e2 := by unfold e2; norm_num
/-- `2 ∣ e0`. -/
theorem two_dvd_e0 : (2 : ℤ) ∣ e0 := by unfold e0; norm_num
/-- `4 ∤ e0`. -/
theorem not_four_dvd_e0 : ¬ (4 : ℤ) ∣ e0 := by unfold e0; norm_num

/-- `(k : ℤ_[2]) ∈ (2^n)` iff `2^n ∣ k`. -/
theorem intCast_mem_span_two_pow (k : ℤ) (n : ℕ) :
    (k : ℤ_[2]) ∈ (Ideal.span {((2 : ℕ) : ℤ_[2]) ^ n} : Ideal ℤ_[2]) ↔ (2 ^ n : ℤ) ∣ k := by
  rw [← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_int_le_pow_iff_dvd]
  norm_num

/-- `E` over `ℤ_[2]` is irreducible (Eisenstein at the prime `2` of `ℤ_[2]`). -/
theorem EZ2_irreducible : Irreducible (EZ.map (Int.castRingHom ℤ_[2])) := by
  have hmon : (EZ.map (Int.castRingHom ℤ_[2])).Monic := EZ_monic.map _
  have hdeg : (EZ.map (Int.castRingHom ℤ_[2])).natDegree = 3 := by
    rw [EZ_monic.natDegree_map, EZ_natDegree]
  have hP : (Ideal.span {((2 : ℕ) : ℤ_[2])}).IsPrime :=
    (Ideal.span_singleton_prime (PadicInt.prime_p (p := 2)).ne_zero).2 PadicInt.prime_p
  have hcoeff : ∀ n, (EZ.map (Int.castRingHom ℤ_[2])).coeff n = ((EZ.coeff n : ℤ) : ℤ_[2]) := by
    intro n; simp [coeff_map]
  apply irreducible_of_eisenstein_criterion hP
  · rw [hmon.leadingCoeff]
    exact fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  · intro n hn
    rw [degree_eq_natDegree hmon.ne_zero, hdeg] at hn
    have hn' : n < 3 := by exact_mod_cast hn
    rw [hcoeff, ← pow_one ((2 : ℕ) : ℤ_[2]), intCast_mem_span_two_pow, pow_one]
    interval_cases n
    · rw [EZ_coeff_zero]; exact two_dvd_e0
    · rw [EZ_coeff_one]; exact two_dvd_e1
    · rw [EZ_coeff_two]; exact two_dvd_e2
  · rw [degree_eq_natDegree hmon.ne_zero, hdeg]; norm_num
  · rw [hcoeff, Ideal.span_singleton_pow, intCast_mem_span_two_pow, EZ_coeff_zero]
    simpa using not_four_dvd_e0
  · exact hmon.isPrimitive

/-- `E` is irreducible over `ℚ_[2]` (Eisenstein at 2 over `ℤ_[2]`, then Gauss). -/
theorem EQ_irreducible : Irreducible EQ := by
  have h := (EZ_monic.map (Int.castRingHom ℤ_[2])).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ_[2]) |>.mp EZ2_irreducible
  rw [Polynomial.map_map] at h
  have : (algebraMap ℤ_[2] ℚ_[2]).comp (Int.castRingHom ℤ_[2]) = Int.castRingHom ℚ_[2] :=
    RingHom.ext_int _ _
  rw [this] at h
  exact h

instance : Fact (Irreducible EQ) := ⟨EQ_irreducible⟩

/-- `E ≠ 0` over `ℚ_[2]`. -/
theorem EQ_ne_zero : EQ ≠ 0 := EQ_monic.ne_zero

/-! ## The field `Kv` -/

/-- `K_v = ℚ_[2][x]/(E)`. -/
def Kv : Type := AdjoinRoot EQ

noncomputable instance : Field Kv := inferInstanceAs (Field (AdjoinRoot EQ))

noncomputable instance : Algebra ℚ_[2] Kv := inferInstanceAs (Algebra ℚ_[2] (AdjoinRoot EQ))

noncomputable instance : Algebra ℚ Kv := ((algebraMap ℚ_[2] Kv).comp (algebraMap ℚ ℚ_[2])).toAlgebra

instance : IsScalarTower ℚ ℚ_[2] Kv := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The power basis `1, pv, pv²` of `Kv` over `ℚ_[2]` (`AdjoinRoot.powerBasis`). -/
noncomputable def pbKv : PowerBasis ℚ_[2] Kv := AdjoinRoot.powerBasis EQ_ne_zero

instance : FiniteDimensional ℚ_[2] Kv := pbKv.finite

instance : Algebra.IsAlgebraic ℚ_[2] Kv := Algebra.IsAlgebraic.of_finite ℚ_[2] Kv

/-- The spectral norm of `Kv/ℚ_[2]`. -/
noncomputable instance : NontriviallyNormedField Kv := spectralNorm.nontriviallyNormedField ℚ_[2] Kv

noncomputable instance : NormedAlgebra ℚ_[2] Kv where
  toAlgebra := inferInstance
  norm_smul_le r x := (spectralNorm.normedAlgebra ℚ_[2] Kv).norm_smul_le r x

instance : CompleteSpace Kv := FiniteDimensional.complete ℚ_[2] Kv

instance : IsUltrametricDist Kv :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm

-- The `Algebra` field of the `NormedAlgebra` instance is the `Algebra ℚ_[2] Kv` instance.
example : @NormedAlgebra.toAlgebra ℚ_[2] Kv _ _ inferInstance =
    instAlgebraPadicOfNatNatKv := by with_reducible_and_instances rfl

-- Mathlib's completeness instance is stated for `spectralNorm.uniformSpace`; it typechecks
-- against the uniform structure of the normed field instance.
example : CompleteSpace Kv := spectralNorm.completeSpace ℚ_[2] Kv

/-- The class of `x`, a uniformizer of `Kv` (the π of lanes M4 and M3b). -/
noncomputable def pv : Kv := AdjoinRoot.root EQ

theorem norm_algebraMap (a : ℚ_[2]) : ‖algebraMap ℚ_[2] Kv a‖ = ‖a‖ := spectralNorm_extends a

/-- The 2-adic norm of an integer `2 u` with `u` odd is `1/2`. -/
theorem norm_intCast_two_mul_odd (u : ℤ) (hu : ¬ (2 : ℤ) ∣ u) :
    ‖((2 * u : ℤ) : ℚ_[2])‖ = 2⁻¹ := by
  have h1 : ‖(u : ℚ_[2])‖ = 1 := by
    refine le_antisymm (Padic.norm_int_le_one u) (not_lt.mp fun h => hu ?_)
    exact_mod_cast Padic.norm_intCast_lt_one_iff.mp h
  have h2 : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
    simpa using (Padic.norm_p (p := 2))
  push_cast
  rw [norm_mul, h1, h2, mul_one]

/-- `‖e0‖ = 1/2` in `ℚ_[2]`. -/
theorem norm_e0 : ‖(e0 : ℚ_[2])‖ = 2⁻¹ := by
  have : e0 = 2 * 8662819668711360651241 := by unfold e0; norm_num
  rw [this]
  exact norm_intCast_two_mul_odd _ (by norm_num)

/-- The minimal polynomial of `pv` over `ℚ_[2]` is `E`. -/
theorem minpoly_pv : minpoly ℚ_[2] pv = EQ :=
  AdjoinRoot.minpoly_powerBasis_gen_of_monic EQ_monic

theorem norm_pv_pow_three : ‖pv‖ ^ 3 = 2⁻¹ := by
  change spectralNorm ℚ_[2] Kv pv ^ 3 = _
  rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, minpoly_pv, EQ_natDegree, EQ, coeff_map,
    EZ_coeff_zero]
  simp only [eq_intCast, norm_e0, one_div]
  exact Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)

/-! ## Coordinates -/

/-- The element `a₀ + a₁ pv + a₂ pv²`. -/
noncomputable def evQ (a : Fin 3 → ℚ_[2]) : Kv :=
  algebraMap ℚ_[2] Kv (a 0) + algebraMap ℚ_[2] Kv (a 1) * pv + algebraMap ℚ_[2] Kv (a 2) * pv ^ 2

/-- The power basis `pbKv` has dimension 3. -/
theorem pbKv_dim : pbKv.dim = 3 := by
  rw [pbKv, AdjoinRoot.powerBasis_dim, EQ_natDegree]

/-- The generator of `pbKv` is `pv`. -/
theorem pbKv_gen : pbKv.gen = pv := AdjoinRoot.powerBasis_gen EQ_ne_zero

/-- The basis `1, pv, pv²` of `Kv` over `ℚ_[2]`, indexed by `Fin 3`. -/
noncomputable def bKv : Module.Basis (Fin 3) ℚ_[2] Kv := pbKv.basis.reindex (finCongr pbKv_dim)

/-- `bKv i = pv ^ i`. -/
theorem bKv_apply (i : Fin 3) : bKv i = pv ^ (i : ℕ) := by
  rw [bKv, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, pbKv_gen]
  simp

/-- `evQ` is the inverse of the coordinate map of the basis `bKv`. -/
theorem evQ_eq_equivFun (a : Fin 3 → ℚ_[2]) : evQ a = bKv.equivFun.symm a := by
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_three, bKv_apply, bKv_apply, bKv_apply, evQ]
  simp [Algebra.smul_def]

theorem evQ_surjective (x : Kv) : ∃ a, evQ a = x :=
  ⟨bKv.equivFun x, by rw [evQ_eq_equivFun, LinearEquiv.symm_apply_apply]⟩

theorem evQ_injective : Function.Injective evQ := by
  intro a b h
  rw [evQ_eq_equivFun, evQ_eq_equivFun] at h
  exact bKv.equivFun.symm.injective h

/-! ### Norms of coordinates -/

/-- `‖2‖ = 1/2` in `ℚ_[2]`. -/
theorem norm_two_padic : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by
  simpa using (Padic.norm_p (p := 2))

/-- A nonzero 2-adic number has norm an integral power of 2. -/
theorem norm_padic_eq_zpow {a : ℚ_[2]} (ha : a ≠ 0) : ∃ k : ℤ, ‖a‖ = (2 : ℝ) ^ k :=
  ⟨-a.valuation, by rw [Padic.norm_eq_zpow_neg_valuation ha]; norm_num⟩

/-- A 2-adic number of norm `> 1` has norm `≥ 2`. -/
theorem two_le_norm_of_one_lt {b : ℚ_[2]} (hb : 1 < ‖b‖) : 2 ≤ ‖b‖ := by
  have hb0 : b ≠ 0 := by rintro rfl; rw [norm_zero] at hb; linarith
  obtain ⟨k, hk⟩ := norm_padic_eq_zpow hb0
  rw [hk] at hb ⊢
  have hk0 : 0 < k := by
    by_contra hk0; push Not at hk0
    have := zpow_le_one_of_nonpos₀ (by norm_num : (1:ℝ) ≤ 2) hk0; linarith
  calc (2:ℝ) = 2 ^ (1:ℤ) := by norm_num
    _ ≤ 2 ^ k := zpow_le_zpow_right₀ (by norm_num) (by omega)

/-- `‖pv‖ > 0`. -/
theorem norm_pv_pos : 0 < ‖pv‖ := by
  have h := norm_pv_pow_three
  have : ‖pv‖ ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
  exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm this)

/-- `‖pv‖ < 1`. -/
theorem norm_pv_lt_one : ‖pv‖ < 1 := by
  by_contra hc; push Not at hc
  have : 1 ≤ ‖pv‖ ^ 3 := one_le_pow₀ hc
  rw [norm_pv_pow_three] at this; norm_num at this

/-- `‖pv‖ > 1/2`. -/
theorem half_lt_norm_pv : 2⁻¹ < ‖pv‖ := by
  by_contra hc; push Not at hc
  have : ‖pv‖ ^ 3 ≤ (2⁻¹) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hc 3
  rw [norm_pv_pow_three] at this; norm_num at this

/-- `‖pv‖² > 1/2`. -/
theorem half_lt_norm_pv_sq : 2⁻¹ < ‖pv‖ ^ 2 := by
  by_contra hc; push Not at hc
  have : (‖pv‖ ^ 2) ^ 3 ≤ (2⁻¹) ^ 3 := pow_le_pow_left₀ (by positivity) hc 3
  rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, norm_pv_pow_three] at this
  norm_num at this

/-- `‖pv‖` and `‖pv‖²` are not integral powers of 2 (their cubes are `2⁻¹`, `2⁻²`). -/
theorem norm_pv_pow_ne_zpow (r : ℕ) (hr : r = 1 ∨ r = 2) (m : ℤ) : ‖pv‖ ^ r ≠ (2 : ℝ) ^ m := by
  intro h
  have h3 : (‖pv‖ ^ r) ^ 3 = ((2 : ℝ) ^ m) ^ 3 := by rw [h]
  rw [← pow_mul, mul_comm, pow_mul, norm_pv_pow_three, ← zpow_natCast ((2:ℝ) ^ m), ← zpow_mul,
    inv_pow, ← zpow_natCast, ← zpow_neg] at h3
  have := zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num) h3
  omega

/-- If `‖a‖ = ‖b‖ ‖pv‖^r` with `r ∈ {1, 2}`, then `a = 0`. -/
theorem eq_zero_of_norm_eq_mul_norm_pv_pow (a b : ℚ_[2]) (r : ℕ) (hr : r = 1 ∨ r = 2)
    (h : ‖a‖ = ‖b‖ * ‖pv‖ ^ r) : a = 0 := by
  by_contra ha
  by_cases hb : b = 0
  · rw [hb, norm_zero, zero_mul, norm_eq_zero] at h; exact ha h
  obtain ⟨j, hj⟩ := norm_padic_eq_zpow ha
  obtain ⟨k, hk⟩ := norm_padic_eq_zpow hb
  apply norm_pv_pow_ne_zpow r hr (j - k)
  rw [zpow_sub₀ two_ne_zero, ← hj, ← hk, h, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hb)]

/-- Three terms whose norms are pairwise distinct unless zero: the norm of the sum is the max. -/
theorem norm_add_add_eq_max {x y z : Kv} (hxy : ‖x‖ = ‖y‖ → x = 0) (hxz : ‖x‖ = ‖z‖ → x = 0)
    (hyz : ‖y‖ = ‖z‖ → y = 0) : ‖x + y + z‖ = max ‖x‖ (max ‖y‖ ‖z‖) := by
  have h1 : ‖x + y‖ = max ‖x‖ ‖y‖ := by
    by_cases h : ‖x‖ = ‖y‖
    · have hx := hxy h
      have hy : y = 0 := by rw [hx, norm_zero, eq_comm, norm_eq_zero] at h; exact h
      simp [hx, hy]
    · exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h
  by_cases h : ‖x + y‖ = ‖z‖
  · rw [h1] at h
    rcases le_total ‖x‖ ‖y‖ with hle | hle
    · rw [max_eq_right hle] at h
      have hy := hyz h
      have hz : z = 0 := by rw [hy, norm_zero, eq_comm, norm_eq_zero] at h; exact h
      have hx : x = 0 := by rw [hy, norm_zero] at hle; exact norm_le_zero_iff.mp hle
      simp [hx, hy, hz]
    · rw [max_eq_left hle] at h
      have hx := hxz h
      have hz : z = 0 := by rw [hx, norm_zero, eq_comm, norm_eq_zero] at h; exact h
      have hy : y = 0 := by rw [hx, norm_zero] at hle; exact norm_le_zero_iff.mp hle
      simp [hx, hy, hz]
  · rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h, h1, max_assoc]

/-- The norm on coordinates: the three terms have distinct norms (`‖pv‖³ = 1/2`). -/
theorem norm_evQ (a : Fin 3 → ℚ_[2]) :
    ‖evQ a‖ = max ‖a 0‖ (max (‖a 1‖ * ‖pv‖) (‖a 2‖ * ‖pv‖ ^ 2)) := by
  have n0 : ‖algebraMap ℚ_[2] Kv (a 0)‖ = ‖a 0‖ := norm_algebraMap _
  have n1 : ‖algebraMap ℚ_[2] Kv (a 1) * pv‖ = ‖a 1‖ * ‖pv‖ := by rw [norm_mul, norm_algebraMap]
  have n2 : ‖algebraMap ℚ_[2] Kv (a 2) * pv ^ 2‖ = ‖a 2‖ * ‖pv‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_algebraMap]
  rw [evQ, norm_add_add_eq_max, n0, n1, n2]
  · rw [n0, n1]; intro h
    rw [eq_zero_of_norm_eq_mul_norm_pv_pow (a 0) (a 1) 1 (Or.inl rfl) (by rw [pow_one]; exact h),
      map_zero]
  · rw [n0, n2]; intro h
    rw [eq_zero_of_norm_eq_mul_norm_pv_pow (a 0) (a 2) 2 (Or.inr rfl) h, map_zero]
  · rw [n1, n2]; intro h
    have h' : ‖a 1‖ = ‖a 2‖ * ‖pv‖ ^ 1 := by
      apply mul_right_cancel₀ (ne_of_gt norm_pv_pos)
      rw [h]; ring
    rw [eq_zero_of_norm_eq_mul_norm_pv_pow (a 1) (a 2) 1 (Or.inl rfl) h', map_zero, zero_mul]

/-- If `‖b‖ c ≤ 1` with `c > 1/2`, then `‖b‖ ≤ 1` (norms of `ℚ_[2]` are powers of 2). -/
theorem norm_le_one_of_mul_le {b : ℚ_[2]} {c : ℝ} (hc : 2⁻¹ < c) (h : ‖b‖ * c ≤ 1) : ‖b‖ ≤ 1 := by
  by_contra hb; push Not at hb
  have h2 := two_le_norm_of_one_lt hb
  nlinarith

/-- The unit ball is `ℤ_[2] + ℤ_[2] pv + ℤ_[2] pv²`. -/
theorem norm_evQ_le_one_iff (a : Fin 3 → ℚ_[2]) : ‖evQ a‖ ≤ 1 ↔ ∀ i, ‖a i‖ ≤ 1 := by
  rw [norm_evQ]
  simp only [max_le_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact h0
    · exact norm_le_one_of_mul_le half_lt_norm_pv h1
    · exact norm_le_one_of_mul_le half_lt_norm_pv_sq h2
  · intro h
    refine ⟨h 0, ?_, ?_⟩
    · calc ‖a 1‖ * ‖pv‖ ≤ 1 * 1 := mul_le_mul (h 1) norm_pv_lt_one.le (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · calc ‖a 2‖ * ‖pv‖ ^ 2 ≤ 1 * 1 :=
          mul_le_mul (h 2) (pow_le_one₀ (norm_nonneg _) norm_pv_lt_one.le) (by positivity)
            zero_le_one
        _ = 1 := one_mul 1

/-! ## Integer triples -/

/-- Integer triples `(a₀, a₁, a₂)`, standing for `a₀ + a₁ pv + a₂ pv²`. -/
abbrev T3 := ℤ × ℤ × ℤ

/-- The element `a₀ + a₁ pv + a₂ pv²` of an integer triple. -/
noncomputable def evZ (a : T3) : Kv := (a.1 : Kv) + (a.2.1 : Kv) * pv + (a.2.2 : Kv) * pv ^ 2

/-- Multiplication of `ℤ[x]/(E)` on triples: `pv³ = -(e0 + e1 pv + e2 pv²)`. -/
def mulZ (a b : T3) : T3 :=
  let c0 := a.1 * b.1
  let c1 := a.1 * b.2.1 + a.2.1 * b.1
  let c2 := a.1 * b.2.2 + a.2.1 * b.2.1 + a.2.2 * b.1
  let c3 := a.2.1 * b.2.2 + a.2.2 * b.2.1
  let c4 := a.2.2 * b.2.2
  -- pv³ = -e0 - e1 pv - e2 pv², pv⁴ = -e0 pv - e1 pv² - e2 pv³
  let d3 := c3 - e2 * c4
  (c0 - e0 * d3, c1 - e1 * d3 - e0 * c4, c2 - e2 * d3 - e1 * c4)

theorem pv_cube : pv ^ 3 = -((e0 : Kv) + (e1 : Kv) * pv + (e2 : Kv) * pv ^ 2) := by
  have h := minpoly.aeval ℚ_[2] pv
  rw [minpoly_pv, EQ, EZ] at h
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C] at h
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C] at h
  simp only [eq_intCast, map_intCast] at h
  linear_combination h

theorem evZ_mul (a b : T3) : evZ (mulZ a b) = evZ a * evZ b := by
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  simp only [evZ, mulZ]
  push_cast
  linear_combination
    (-((a1 * b2 + a2 * b1 : Kv) - (e2 : Kv) * (a2 * b2) + (a2 * b2 : Kv) * pv)) * pv_cube

theorem evZ_add (a b : T3) : evZ (a + b) = evZ a + evZ b := by
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  simp only [evZ, Prod.mk_add_mk]
  push_cast
  ring

/-- The `ℚ_[2]`-coordinates of an integer triple. -/
noncomputable def qOfT3 (a : T3) : Fin 3 → ℚ_[2] :=
  ![(a.1 : ℚ_[2]), (a.2.1 : ℚ_[2]), (a.2.2 : ℚ_[2])]

/-- `evZ` is `evQ` of the coordinates `qOfT3`. -/
theorem evZ_eq_evQ (a : T3) : evZ a = evQ (qOfT3 a) := by
  simp [evZ, evQ, qOfT3, map_intCast]

theorem norm_evZ_le_one (a : T3) : ‖evZ a‖ ≤ 1 := by
  rw [evZ_eq_evQ, norm_evQ_le_one_iff]
  intro i
  fin_cases i <;> simp [qOfT3, Padic.norm_int_le_one]

theorem norm_two_Kv : ‖(2 : Kv)‖ = 2⁻¹ := by
  rw [← map_ofNat (algebraMap ℚ_[2] Kv) 2, norm_algebraMap, norm_two_padic]

/-- `evQ` is `ℚ_[2]`-homogeneous. -/
theorem evQ_smul (d : ℚ_[2]) (a : Fin 3 → ℚ_[2]) :
    evQ (fun i => d * a i) = algebraMap ℚ_[2] Kv d * evQ a := by
  simp only [evQ, map_mul]; ring

/-- `evQ` commutes with subtraction. -/
theorem evQ_sub (a b : Fin 3 → ℚ_[2]) : evQ (a - b) = evQ a - evQ b := by
  simp only [evQ, Pi.sub_apply, map_sub]; ring

/-- Divisibility of the coordinates by `2^m` is the norm bound `2^(-m)`. -/
theorem norm_evQ_le_two_pow_iff (a : Fin 3 → ℚ_[2]) (m : ℕ) :
    ‖evQ a‖ ≤ (2⁻¹ : ℝ) ^ m ↔ ∀ i, ‖a i‖ ≤ (2⁻¹ : ℝ) ^ m := by
  have hd : ‖((2 : ℚ_[2]) ^ m)⁻¹‖ = (2 : ℝ) ^ m := by
    rw [norm_inv, norm_pow, norm_two_padic, inv_pow, inv_inv]
  have key : ∀ t : ℝ, t ≤ (2⁻¹ : ℝ) ^ m ↔ (2 : ℝ) ^ m * t ≤ 1 := by
    intro t
    rw [inv_pow, ← one_div, le_div_iff₀ (by positivity), mul_comm]
  have h := norm_evQ_le_one_iff (fun i => ((2 : ℚ_[2]) ^ m)⁻¹ * a i)
  rw [evQ_smul, norm_mul, norm_algebraMap, hd] at h
  simp only [norm_mul, hd] at h
  rw [key, h]
  exact forall_congr' fun i => (key _).symm

/-- `‖k‖ ≤ 2^(-m)` in `ℚ_[2]` iff `2^m ∣ k`, for an integer `k`. -/
theorem norm_intCast_le_two_pow_iff (k : ℤ) (m : ℕ) :
    ‖(k : ℚ_[2])‖ ≤ (2⁻¹ : ℝ) ^ m ↔ (2 : ℤ) ^ m ∣ k := by
  have h := Padic.norm_int_le_pow_iff_dvd (p := 2) k m
  rw [zpow_neg, zpow_natCast, ← inv_pow] at h
  exact_mod_cast h

/-- An integer triple of norm at most `2^(-m)` has coordinates divisible by `2^m`. -/
theorem dvd_of_norm_evZ_le (a : T3) (m : ℕ) (h : ‖evZ a‖ ≤ (2⁻¹ : ℝ) ^ m) :
    (2 : ℤ) ^ m ∣ a.1 ∧ (2 : ℤ) ^ m ∣ a.2.1 ∧ (2 : ℤ) ^ m ∣ a.2.2 := by
  rw [evZ_eq_evQ, norm_evQ_le_two_pow_iff] at h
  refine ⟨?_, ?_, ?_⟩
  · exact (norm_intCast_le_two_pow_iff _ _).1 (by simpa [qOfT3] using h 0)
  · exact (norm_intCast_le_two_pow_iff _ _).1 (by simpa [qOfT3] using h 1)
  · exact (norm_intCast_le_two_pow_iff _ _).1 (by simpa [qOfT3] using h 2)

/-- The converse of `dvd_of_norm_evZ_le`. -/
theorem norm_evZ_le_of_dvd (a : T3) (m : ℕ)
    (h : (2 : ℤ) ^ m ∣ a.1 ∧ (2 : ℤ) ^ m ∣ a.2.1 ∧ (2 : ℤ) ^ m ∣ a.2.2) :
    ‖evZ a‖ ≤ (2⁻¹ : ℝ) ^ m := by
  rw [evZ_eq_evQ, norm_evQ_le_two_pow_iff]
  intro i
  fin_cases i
  · simpa [qOfT3] using (norm_intCast_le_two_pow_iff _ _).2 h.1
  · simpa [qOfT3] using (norm_intCast_le_two_pow_iff _ _).2 h.2.1
  · simpa [qOfT3] using (norm_intCast_le_two_pow_iff _ _).2 h.2.2

/-- A 2-adic number of norm at most 1 is a natural number modulo `2^m` (`PadicInt.appr`). -/
theorem exists_nat_approx (c : ℚ_[2]) (hc : ‖c‖ ≤ 1) (m : ℕ) :
    ∃ n : ℕ, ‖c - (n : ℚ_[2])‖ ≤ (2⁻¹ : ℝ) ^ m := by
  let z : ℤ_[2] := ⟨c, hc⟩
  refine ⟨PadicInt.appr z m, ?_⟩
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 (PadicInt.appr_spec m z)
  rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast, zpow_neg, zpow_natCast,
    ← inv_pow] at h1
  exact_mod_cast h1

/-- Every element of the unit ball is an integer triple modulo `2^m`. -/
theorem exists_evZ_approx (x : Kv) (hx : ‖x‖ ≤ 1) (m : ℕ) :
    ∃ b : T3, ‖x - evZ b‖ ≤ (2⁻¹ : ℝ) ^ m := by
  obtain ⟨a, rfl⟩ := evQ_surjective x
  have ha := (norm_evQ_le_one_iff a).1 hx
  obtain ⟨n0, h0⟩ := exists_nat_approx (a 0) (ha 0) m
  obtain ⟨n1, h1⟩ := exists_nat_approx (a 1) (ha 1) m
  obtain ⟨n2, h2⟩ := exists_nat_approx (a 2) (ha 2) m
  refine ⟨((n0 : ℤ), (n1 : ℤ), (n2 : ℤ)), ?_⟩
  rw [evZ_eq_evQ, ← evQ_sub, norm_evQ_le_two_pow_iff]
  intro i
  fin_cases i
  · simpa [qOfT3] using h0
  · simpa [qOfT3] using h1
  · simpa [qOfT3] using h2

end FurioLombardo.Discharge.M4Cert
