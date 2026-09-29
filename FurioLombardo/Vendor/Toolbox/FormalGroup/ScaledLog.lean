import FurioLombardo.Vendor.Toolbox.Stoll.Mathlib.Chabauty.LogIso

/-!
# The scaled logarithm of a formal group law, at every prime and every ramification

Let `O` be a complete local ring with the adic topology of its maximal ideal `𝔪`, `p` a prime
with `p ∈ 𝔪`, `f : O →+* K` injective into a field of characteristic zero and `Φ` a formal group
law over `O` of dimension `ι`. Stoll's kit (`FurioLombardo.Vendor.Toolbox.Stoll.Mathlib.Chabauty.LogIso`) proves that
the logarithm is an injective homomorphism on `(pO)^ι` when `p` is odd and `𝔪 = pO`. This file
removes both restrictions by scaling the variables with an element `c` satisfying
`ScalingHyp p c`: for every `n ≥ 1`, `c ^ (n - 1) = p ^ Dexp p n * b` with `b ∈ 𝔪 ^ (n - 1)`,
where `Dexp p n = (n - 1)/(p - 1)` bounds the denominators of the formal exponential
(`FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.FormalGroupLaw.exp_bounded`, valid for every prime). Both
`c = p ^ 2` (`scalingHyp_sq`, every prime, every `O`) and `c = π ^ (e + 1)` when `p = π ^ e u`
with `u` a unit (`scalingHyp_uniformizer`, the sharp radius in a ramified base) qualify.

Main definitions (all over `O`, with coefficients in `𝔪 ^ (deg - 1)`):
* `FurioLombardo.Vendor.Toolbox.FormalGroup.logC`: the scaled logarithm `log(cX)/c`;
* `FurioLombardo.Vendor.Toolbox.FormalGroup.expC`: the scaled exponential `exp(cX)/c`;
* `FurioLombardo.Vendor.Toolbox.FormalGroup.addC`: the scaled group law `F(cX, cY)/c`;
* `FurioLombardo.Vendor.Toolbox.FormalGroup.logVal`, `expVal`, `addVal`: their values, maps `O^ι → O^ι`
  (and `O^ι × O^ι → O^ι`).

Main results: `expVal_logVal` and `logVal_expVal` (the two are inverse bijections of `O^ι`),
`logVal_injective`, `logVal_surjective`, `logVal_addVal` (the scaled logarithm turns the scaled
group law into addition). Over `K` the three series are the conjugates `a⁻¹ L(aX)` (`a = f c`)
of `log`, `exp`, `F` (`map_logC`, `map_expC`, `map_addC`); conjugation commutes with
substitution (`conjScale_subst`), which descends `exp ∘ log = X`, `log ∘ exp = X` and
`log ∘ F = log X + log Y` to `O`. Neither a domain nor a discrete valuation hypothesis is needed.

Origin: written for this formalization (the discharge of the analytic hypotheses,
`FurioLombardo.Discharge.Analytic`), on Michael Stoll's formal group law kit
(`FurioLombardo.Vendor.Toolbox.Stoll.Mathlib.Chabauty`, Apache 2.0).
-/

open MvPowerSeries IsLocalRing Filter Topology
open FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman

namespace FurioLombardo.Vendor.Toolbox.FormalGroup

/-! ### The scaling hypothesis -/

section Scaling

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- The scaling hypothesis on `c : O` at the prime `p`: for every `n ≥ 1`,
`c ^ (n - 1) = p ^ Dexp p n * b` for some `b ∈ 𝔪 ^ (n - 1)`. It makes the coefficients of
`log(cX)/c` and `exp(cX)/c` integral and `𝔪`-adically decaying. -/
def ScalingHyp (p : ℕ) (c : O) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ b ∈ maximalIdeal O ^ (n - 1), c ^ (n - 1) = (p : O) ^ Dexp p n * b

/-- `Dexp p n ≤ n - 1` for every `p`. -/
theorem Dexp_le_pred (p n : ℕ) : Dexp p n ≤ n - 1 := Nat.div_le_self _ _

/-- A scaling element lies in the maximal ideal. -/
theorem ScalingHyp.mem_maximalIdeal {p : ℕ} {c : O} (hc : ScalingHyp p c) :
    c ∈ maximalIdeal O := by
  obtain ⟨b, hb, hcb⟩ := hc 2 (by norm_num)
  have hc' : c = (p : O) ^ Dexp p 2 * b := by simpa using hcb
  rw [hc']
  exact Ideal.mul_mem_left _ _ (by simpa using hb)

/-- `c = p ^ 2` satisfies the scaling hypothesis, for every prime `p ∈ 𝔪` and every local ring. -/
theorem scalingHyp_sq {p : ℕ} (hpm : (p : O) ∈ maximalIdeal O) : ScalingHyp p ((p : O) ^ 2) := by
  intro n _
  have hD := Dexp_le_pred p n
  refine ⟨(p : O) ^ (2 * (n - 1) - Dexp p n), ?_, ?_⟩
  · exact Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hpm _)
  · rw [← pow_mul, ← pow_add]
    congr 1
    omega

/-- `c = π ^ (e + 1)` satisfies the scaling hypothesis when `p = π ^ e * u` with `u` a unit (for
instance `π` a uniformizer of a discrete valuation ring of absolute ramification index `e`). -/
theorem scalingHyp_uniformizer {p : ℕ} (hpm : (p : O) ∈ maximalIdeal O) {π u : O} {e : ℕ}
    (hu : IsUnit u) (hpe : (p : O) = π ^ e * u) : ScalingHyp p (π ^ (e + 1)) := by
  have hπ : π ∈ maximalIdeal O := by
    by_contra h
    rw [IsLocalRing.notMem_maximalIdeal] at h
    exact IsLocalRing.notMem_maximalIdeal.mpr ((h.pow e).mul hu) (hpe ▸ hpm)
  obtain ⟨v, rfl⟩ := hu
  intro n _
  have hD := Dexp_le_pred p n
  have heD : e * Dexp p n ≤ e * (n - 1) := Nat.mul_le_mul_left e hD
  have hsplit : (e + 1) * (n - 1) = e * (n - 1) + (n - 1) := by ring
  obtain ⟨t, ht⟩ : ∃ t, (e + 1) * (n - 1) = e * Dexp p n + t :=
    ⟨(e + 1) * (n - 1) - e * Dexp p n, by omega⟩
  refine ⟨π ^ t * (↑v⁻¹ : O) ^ Dexp p n, ?_, ?_⟩
  · exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hπ _))
  · rw [hpe, ← pow_mul, ht, pow_add, mul_pow, ← pow_mul]
    have hvv : (↑v : O) ^ Dexp p n * (↑v⁻¹ : O) ^ Dexp p n = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    calc π ^ (e * Dexp p n) * π ^ t
        = π ^ (e * Dexp p n) * π ^ t * ((↑v : O) ^ Dexp p n * (↑v⁻¹ : O) ^ Dexp p n) := by
          rw [hvv, mul_one]
      _ = π ^ (e * Dexp p n) * (↑v : O) ^ Dexp p n * (π ^ t * (↑v⁻¹ : O) ^ Dexp p n) := by ring

/-- When `𝔪 = (π)`, `𝔪 ^ n ≤ (π ^ n)`: the hypothesis `𝔪 ^ N ≤ (c)` of the points level for
`c = π ^ (e + 1)` and `N = e + 1`. -/
theorem maximalIdeal_pow_le_span_pow {π : O} (hπ : maximalIdeal O = Ideal.span {π}) (n : ℕ) :
    maximalIdeal O ^ n ≤ Ideal.span {π ^ n} := by
  rw [hπ, Ideal.span_singleton_pow]

/-- When `𝔪 = (π)` and `p = π ^ e * u` with `u` a unit, `𝔪 ^ (2 e) ≤ (p ^ 2)`: the hypothesis
`𝔪 ^ N ≤ (c)` of the points level for `c = p ^ 2` and `N = 2 e`. -/
theorem maximalIdeal_pow_le_span_sq {p : ℕ} {π u : O} {e : ℕ}
    (hπ : maximalIdeal O = Ideal.span {π}) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u) :
    maximalIdeal O ^ (2 * e) ≤ Ideal.span {(p : O) ^ 2} := by
  rw [hπ, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  obtain ⟨v, rfl⟩ := hu
  refine ⟨(↑v⁻¹ : O) ^ 2, ?_⟩
  rw [hpe]
  calc π ^ (2 * e) = π ^ (2 * e) * ((↑v : O) * ↑v⁻¹) ^ 2 := by
        rw [Units.mul_inv, one_pow, mul_one]
    _ = (π ^ e * ↑v) ^ 2 * (↑v⁻¹ : O) ^ 2 := by ring

end Scaling

/-! ### Conjugation by a scalar over a field -/

section Conj

variable {K : Type*} [Field K] {σ τ : Type*}

/-- The conjugate `a⁻¹ L(aX)` of a power series by a scalar `a`. -/
noncomputable def conjScale (a : K) (L : MvPowerSeries σ K) : MvPowerSeries σ K :=
  a⁻¹ • rescale (fun _ ↦ a) L

/-- Coefficients of the conjugate: `a⁻¹ a ^ deg d` times those of `L`. -/
theorem coeff_conjScale (a : K) (L : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    coeff d (conjScale a L) = a⁻¹ * (a ^ d.degree * coeff d L) := by
  rw [conjScale, coeff_smul, coeff_rescale, Finsupp.prod, Finset.prod_pow_eq_pow_sum,
    ← Finsupp.degree_apply]

/-- Coefficients of the conjugate in positive degree: `a ^ (deg d - 1)` times those of `L`. -/
theorem coeff_conjScale_of_pos {a : K} (ha : a ≠ 0) (L : MvPowerSeries σ K) {d : σ →₀ ℕ}
    (hd : 1 ≤ d.degree) : coeff d (conjScale a L) = a ^ (d.degree - 1) * coeff d L := by
  rw [coeff_conjScale, ← mul_assoc]
  congr 1
  obtain ⟨n, hn⟩ : ∃ n, d.degree = n + 1 := ⟨d.degree - 1, by omega⟩
  rw [hn, pow_succ', ← mul_assoc, inv_mul_cancel₀ ha, one_mul, Nat.add_sub_cancel]

/-- The constant coefficient of the conjugate. -/
theorem constantCoeff_conjScale (a : K) (L : MvPowerSeries σ K) :
    constantCoeff (conjScale a L) = a⁻¹ * constantCoeff L := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_conjScale, map_zero Finsupp.degree, pow_zero,
    one_mul, coeff_zero_eq_constantCoeff_apply]

/-- Conjugation is additive. -/
theorem conjScale_add (a : K) (L M : MvPowerSeries σ K) :
    conjScale a (L + M) = conjScale a L + conjScale a M := by
  rw [conjScale, map_add, smul_add]
  rfl

/-- Conjugation fixes the variables. -/
theorem conjScale_X {a : K} (ha : a ≠ 0) (s : σ) :
    conjScale a (X s : MvPowerSeries σ K) = X s := by
  classical
  ext d
  rw [coeff_conjScale, coeff_X]
  split_ifs with h
  · rw [h, Finsupp.degree_single, pow_one, mul_one, inv_mul_cancel₀ ha]
  · rw [mul_zero, mul_zero]

/-- The conjugate as a substitution: `a⁻¹ • L(a • X)`. -/
theorem conjScale_eq (a : K) (L : MvPowerSeries σ K) :
    conjScale a L = a⁻¹ • subst (fun k : σ ↦ a • (X k : MvPowerSeries σ K)) L := by
  rw [conjScale, FormalGroupLaw.rescale_const_eq_subst]

/-- **Conjugation commutes with substitution**: `a⁻¹ (E ∘ Q)(aX) = (a⁻¹ E(aX)) ∘ (a⁻¹ Q(aX))`. -/
theorem conjScale_subst [Finite σ] [Finite τ] {a : K} (ha : a ≠ 0) {Q : σ → MvPowerSeries τ K}
    (hQ : ∀ j, constantCoeff (Q j) = 0) (E : MvPowerSeries σ K) :
    conjScale a (subst Q E) = subst (fun j ↦ conjScale a (Q j)) (conjScale a E) := by
  have hQs : HasSubst Q := hasSubst_of_constantCoeff_zero hQ
  have haσ : HasSubst (fun j : σ ↦ a • (X j : MvPowerSeries σ K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have haτ : HasSubst (fun j : τ ↦ a • (X j : MvPowerSeries τ K)) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hcQ : HasSubst (fun j ↦ conjScale a (Q j)) :=
    hasSubst_of_constantCoeff_zero fun j ↦ by rw [constantCoeff_conjScale, hQ, mul_zero]
  rw [conjScale_eq a (subst Q E), conjScale_eq a E, subst_smul hcQ, subst_comp_subst_apply haσ hcQ,
    subst_comp_subst_apply hQs haτ]
  refine congrArg (a⁻¹ • ·) (congrArg (fun F ↦ subst F E) (funext fun j ↦ ?_))
  rw [subst_smul hcQ, subst_X hcQ, conjScale_eq a (Q j), smul_smul, mul_inv_cancel₀ ha, one_smul]

end Conj

/-! ### The scaled series over `O` -/

section Series

variable {O : Type*} [CommRing O] {K : Type*} [Field K]

open scoped Classical in
/-- A preimage of `x` under `f` (the junk value `0` when there is none). -/
noncomputable def descend (f : O →+* K) (x : K) : O :=
  if h : ∃ b, f b = x then h.choose else 0

/-- `descend f x` is a preimage of `x` when there is one. -/
theorem map_descend {f : O →+* K} {x : K} (h : ∃ b, f b = x) : f (descend f x) = x := by
  rw [descend, dite_eq_left h]
  exact h.choose_spec

/-- For injective `f`, `descend f (f b) = b`. -/
theorem descend_eq {f : O →+* K} (hf : Function.Injective f) {b : O} {x : K} (h : f b = x) :
    descend f x = b :=
  hf ((map_descend ⟨b, h⟩).trans h.symm)

/-- A nonzero natural number stays nonzero in a ring with a ring homomorphism to a field of
characteristic zero (so `c = p ^ 2 ≠ 0`). -/
theorem natCast_ne_zero_of_ringHom [CharZero K] (f : O →+* K) {n : ℕ} (hn : n ≠ 0) :
    (n : O) ≠ 0 := fun h ↦
  hn (by exact_mod_cast (show (n : K) = 0 by rw [← map_natCast f n, h, map_zero]))

variable {ι : Type*}

/-- The scaled formal group law `F(cX, cY)/c` over `O` (Stoll's `scaledF` with `c` in place
of `p`). -/
noncomputable def addC (Φ : FormalGroupLaw O ι) (c : O) (j : ι) : MvPowerSeries (ι ⊕ ι) O :=
  fun d ↦ c ^ (d.degree - 1) * coeff d (Φ.F j)

/-- Coefficients of the scaled group law. -/
theorem coeff_addC (Φ : FormalGroupLaw O ι) (c : O) (j : ι) (d : ι ⊕ ι →₀ ℕ) :
    coeff d (addC Φ c j) = c ^ (d.degree - 1) * coeff d (Φ.F j) := rfl

/-- The scaled group law has no constant term. -/
theorem constantCoeff_addC (Φ : FormalGroupLaw O ι) (c : O) (j : ι) :
    constantCoeff (addC Φ c j) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_addC, coeff_zero_eq_constantCoeff_apply,
    Φ.zero_constantCoeff, mul_zero]

/-- The scaled group law can be substituted. -/
theorem hasSubst_addC [Finite ι] (Φ : FormalGroupLaw O ι) (c : O) : HasSubst (addC Φ c) :=
  hasSubst_of_constantCoeff_zero fun j ↦ constantCoeff_addC Φ c j

/-- Over `K`, the scaled group law is the conjugate of `F` by `f c`. -/
theorem map_addC [Finite ι] (Φ : FormalGroupLaw O ι) {f : O →+* K} {c : O} (hfc : f c ≠ 0)
    (j : ι) : MvPowerSeries.map f (addC Φ c j) = conjScale (f c) ((Φ.map f).F j) := by
  ext d
  rw [coeff_map, coeff_addC, FormalGroupLaw.F_map]
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    rw [coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff, mul_zero, map_zero,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_conjScale,
      ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      Φ.zero_constantCoeff, map_zero, mul_zero]
  · rw [coeff_conjScale_of_pos hfc _ hpos, coeff_map, map_mul, map_pow]

variable [Fintype ι] [DecidableEq ι]

/-- The scaled logarithm `log(cX)/c` over `O`: its image in `K` has the coefficients
`f(c) ^ (deg d - 1) · coeff_d log` (`map_coeff_logC`). -/
noncomputable def logC (Φ : FormalGroupLaw O ι) (f : O →+* K) (c : O) (i : ι) : MvPowerSeries ι O :=
  fun d ↦ descend f (f c ^ (d.degree - 1) * coeff d ((Φ.map f).log i))

/-- The scaled exponential `exp(cX)/c` over `O`: its image in `K` has the coefficients
`f(c) ^ (deg d - 1) · coeff_d exp` (`map_coeff_expC`). -/
noncomputable def expC (Φ : FormalGroupLaw O ι) (f : O →+* K) (c : O) (i : ι) : MvPowerSeries ι O :=
  fun d ↦ descend f (f c ^ (d.degree - 1) * coeff d ((Φ.map f).exp i))

/-- The formal exponential has no constant term. -/
theorem constantCoeff_exp (Φ : FormalGroupLaw K ι) (i : ι) :
    constantCoeff (Φ.exp i) = 0 :=
  constantCoeff_invSubst Φ.log_sub_X_order i

variable [IsLocalRing O] [CharZero K] {p : ℕ} {c : O}

/-- The coefficients of `log(cX)/c` are integral and lie in `𝔪 ^ (deg d - 1)`. -/
theorem exists_coeff_logC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    (f : O →+* K) (Φ : FormalGroupLaw O ι) (i : ι) (d : ι →₀ ℕ) :
    ∃ b ∈ maximalIdeal O ^ (d.degree - 1),
      f b = f c ^ (d.degree - 1) * coeff d ((Φ.map f).log i) := by
  have hfp : f (p : O) ≠ 0 := by rw [map_natCast]; exact_mod_cast hp.ne_zero
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    refine ⟨0, zero_mem _, ?_⟩
    rw [map_zero, coeff_zero_eq_constantCoeff_apply, (Φ.map f).constantCoeff_log, mul_zero]
  · obtain ⟨c', hc'⟩ := Φ.coeff_log_map_padic hp hpm f hfp i d
    obtain ⟨b0, hb0, hcb⟩ := hc d.degree hpos
    have hv := padicValNat_le_Dexp hp hpos
    refine ⟨(p : O) ^ (Dexp p d.degree - padicValNat p d.degree) * b0 * c',
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hb0), ?_⟩
    have hfc : f c ^ (d.degree - 1) = f (p : O) ^ (Dexp p d.degree - padicValNat p d.degree)
        * f (p : O) ^ padicValNat p d.degree * f b0 := by
      rw [← map_pow, hcb, map_mul, map_pow, ← pow_add, Nat.sub_add_cancel hv]
    rw [hfc, map_mul, map_mul, map_pow, ← hc']
    ring

/-- The coefficients of `exp(cX)/c` are integral and lie in `𝔪 ^ (deg d - 1)`. -/
theorem exists_coeff_expC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    (f : O →+* K) (Φ : FormalGroupLaw O ι) (i : ι) (d : ι →₀ ℕ) :
    ∃ b ∈ maximalIdeal O ^ (d.degree - 1),
      f b = f c ^ (d.degree - 1) * coeff d ((Φ.map f).exp i) := by
  have hfp : f (p : O) ≠ 0 := by rw [map_natCast]; exact_mod_cast hp.ne_zero
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    refine ⟨0, zero_mem _, ?_⟩
    rw [map_zero, coeff_zero_eq_constantCoeff_apply, FormalGroupLaw.exp,
      constantCoeff_invSubst (Φ.map f).log_sub_X_order, mul_zero]
  · obtain ⟨c', hc'⟩ := FormalGroupLaw.exp_bounded hp hpm hfp Φ i d
    obtain ⟨b0, hb0, hcb⟩ := hc d.degree hpos
    refine ⟨b0 * c', Ideal.mul_mem_right _ _ hb0, ?_⟩
    have hfc : f c ^ (d.degree - 1) = f (p : O) ^ Dexp p d.degree * f b0 := by
      rw [← map_pow, hcb, map_mul, map_pow]
    rw [hfc, map_mul, ← hc']
    ring

/-- The image of a coefficient of `log(cX)/c` in `K`. -/
theorem map_coeff_logC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    (f : O →+* K) (Φ : FormalGroupLaw O ι) (i : ι) (d : ι →₀ ℕ) :
    f (coeff d (logC Φ f c i)) = f c ^ (d.degree - 1) * coeff d ((Φ.map f).log i) := by
  obtain ⟨b, -, hb⟩ := exists_coeff_logC hp hpm hc f Φ i d
  exact map_descend ⟨b, hb⟩

/-- The image of a coefficient of `exp(cX)/c` in `K`. -/
theorem map_coeff_expC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    (f : O →+* K) (Φ : FormalGroupLaw O ι) (i : ι) (d : ι →₀ ℕ) :
    f (coeff d (expC Φ f c i)) = f c ^ (d.degree - 1) * coeff d ((Φ.map f).exp i) := by
  obtain ⟨b, -, hb⟩ := exists_coeff_expC hp hpm hc f Φ i d
  exact map_descend ⟨b, hb⟩

/-- The coefficients of `log(cX)/c` lie in `𝔪 ^ (deg d - 1)`. -/
theorem coeff_logC_mem (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (Φ : FormalGroupLaw O ι) (i : ι) (d : ι →₀ ℕ) :
    coeff d (logC Φ f c i) ∈ maximalIdeal O ^ (d.degree - 1) := by
  obtain ⟨b, hbm, hb⟩ := exists_coeff_logC hp hpm hc f Φ i d
  change descend f _ ∈ _
  rw [descend_eq hf hb]
  exact hbm

/-- The coefficients of `exp(cX)/c` lie in `𝔪 ^ (deg d - 1)`. -/
theorem coeff_expC_mem (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (Φ : FormalGroupLaw O ι) (i : ι) (d : ι →₀ ℕ) :
    coeff d (expC Φ f c i) ∈ maximalIdeal O ^ (d.degree - 1) := by
  obtain ⟨b, hbm, hb⟩ := exists_coeff_expC hp hpm hc f Φ i d
  change descend f _ ∈ _
  rw [descend_eq hf hb]
  exact hbm

omit [Fintype ι] [DecidableEq ι] in
/-- The coefficients of `F(cX, cY)/c` lie in `𝔪 ^ (deg d - 1)`. -/
theorem coeff_addC_mem (hcm : c ∈ maximalIdeal O) (Φ : FormalGroupLaw O ι) (j : ι)
    (d : ι ⊕ ι →₀ ℕ) : coeff d (addC Φ c j) ∈ maximalIdeal O ^ (d.degree - 1) := by
  rw [coeff_addC]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hcm _)

/-- The scaled logarithm has no constant term. -/
theorem constantCoeff_logC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (Φ : FormalGroupLaw O ι) (i : ι) :
    constantCoeff (logC Φ f c i) = 0 := hf (by
  rw [← coeff_zero_eq_constantCoeff_apply, map_coeff_logC hp hpm hc f Φ i 0,
    coeff_zero_eq_constantCoeff_apply, (Φ.map f).constantCoeff_log, mul_zero, map_zero])

/-- The scaled exponential has no constant term. -/
theorem constantCoeff_expC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (Φ : FormalGroupLaw O ι) (i : ι) :
    constantCoeff (expC Φ f c i) = 0 := hf (by
  rw [← coeff_zero_eq_constantCoeff_apply, map_coeff_expC hp hpm hc f Φ i 0,
    coeff_zero_eq_constantCoeff_apply, FormalGroupLaw.exp,
    constantCoeff_invSubst (Φ.map f).log_sub_X_order, mul_zero, map_zero])

/-- Over `K`, the scaled logarithm is the conjugate of `log` by `f c`. -/
theorem map_logC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hfc : f c ≠ 0) (Φ : FormalGroupLaw O ι) (i : ι) :
    MvPowerSeries.map f (logC Φ f c i) = conjScale (f c) ((Φ.map f).log i) := by
  ext d
  rw [coeff_map, map_coeff_logC hp hpm hc f Φ i d]
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_conjScale, (Φ.map f).constantCoeff_log, mul_zero, mul_zero]
  · rw [coeff_conjScale_of_pos hfc _ hpos]

/-- Over `K`, the scaled exponential is the conjugate of `exp` by `f c`. -/
theorem map_expC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hfc : f c ≠ 0) (Φ : FormalGroupLaw O ι) (i : ι) :
    MvPowerSeries.map f (expC Φ f c i) = conjScale (f c) ((Φ.map f).exp i) := by
  ext d
  rw [coeff_map, map_coeff_expC hp hpm hc f Φ i d]
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_conjScale, constantCoeff_exp, mul_zero, mul_zero]
  · rw [coeff_conjScale_of_pos hfc _ hpos]

/-! ### Descent of the formal identities -/

/-- `exp ∘ log = X` descends to the scaled series over `O`. -/
theorem subst_logC_expC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) (i : ι) :
    subst (logC Φ f c) (expC Φ f c i) = X i := by
  have hfc : f c ≠ 0 := fun h ↦ hc0 (hf (by rw [h, map_zero]))
  have hLs : HasSubst (logC Φ f c) :=
    hasSubst_of_constantCoeff_zero fun j ↦ constantCoeff_logC hp hpm hc hf Φ j
  apply FormalGroupLaw.map_injective_of_injective hf
  rw [map_subst hLs, map_expC hp hpm hc hfc Φ i, MvPowerSeries.map_X]
  simp only [map_logC hp hpm hc hfc Φ]
  rw [← conjScale_subst hfc (fun j ↦ (Φ.map f).constantCoeff_log j), (Φ.map f).exp_comp_log,
    conjScale_X hfc]

/-- `log ∘ exp = X` descends to the scaled series over `O`. -/
theorem subst_expC_logC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) (i : ι) :
    subst (expC Φ f c) (logC Φ f c i) = X i := by
  have hfc : f c ≠ 0 := fun h ↦ hc0 (hf (by rw [h, map_zero]))
  have hEs : HasSubst (expC Φ f c) :=
    hasSubst_of_constantCoeff_zero fun j ↦ constantCoeff_expC hp hpm hc hf Φ j
  apply FormalGroupLaw.map_injective_of_injective hf
  rw [map_subst hEs, map_logC hp hpm hc hfc Φ i, MvPowerSeries.map_X]
  simp only [map_expC hp hpm hc hfc Φ]
  rw [← conjScale_subst hfc (fun j ↦ constantCoeff_exp (Φ.map f) j),
    (Φ.map f).log_comp_exp, conjScale_X hfc]

/-- `log ∘ F = log X + log Y` descends to the scaled series over `O`. -/
theorem subst_addC_logC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) (i : ι) :
    subst (addC Φ c) (logC Φ f c i)
      = subst (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) (logC Φ f c i)
        + subst (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) (logC Φ f c i) := by
  have hfc : f c ≠ 0 := fun h ↦ hc0 (hf (by rw [h, map_zero]))
  apply FormalGroupLaw.map_injective_of_injective hf
  rw [map_add, map_subst (hasSubst_addC Φ c), map_subst FormalGroupLaw.hasSubst_Xemb,
    map_subst FormalGroupLaw.hasSubst_Yemb]
  simp only [map_addC Φ hfc, map_logC hp hpm hc hfc Φ, MvPowerSeries.map_X]
  rw [← conjScale_subst hfc (fun j ↦ (Φ.map f).zero_constantCoeff j), (Φ.map f).log_subst_F i,
    conjScale_add, conjScale_subst hfc (fun s ↦ constantCoeff_X (Sum.inl s)),
    conjScale_subst hfc (fun s ↦ constantCoeff_X (Sum.inr s))]
  simp only [conjScale_X hfc]

end Series

/-! ### Values: the scaled logarithm is a bijection of `O^ι`, additive for the scaled group law -/

section Values

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {K : Type*} [Field K] [CharZero K] {p : ℕ} {c : O}

/-- The scaled logarithm on `O^ι`: `y ↦ (log(cy)/c)_i`, the `evalT` values of `logC`. -/
noncomputable def logVal (Φ : FormalGroupLaw O ι) (f : O →+* K) (c : O) (y : ι → O) : ι → O :=
  fun i ↦ MvPSeries.evalT y (logC Φ f c i)

/-- The scaled exponential on `O^ι`: `x ↦ (exp(cx)/c)_i`, the `evalT` values of `expC`. -/
noncomputable def expVal (Φ : FormalGroupLaw O ι) (f : O →+* K) (c : O) (x : ι → O) : ι → O :=
  fun i ↦ MvPSeries.evalT x (expC Φ f c i)

/-- The scaled group law on `O^ι`: `(y, y') ↦ F(cy, cy')/c`, the `evalT` values of `addC`. -/
noncomputable def addVal (Φ : FormalGroupLaw O ι) (c : O) (y y' : ι → O) : ι → O :=
  fun j ↦ MvPSeries.evalT (Sum.elim y y') (addC Φ c j)

omit [IsLocalRing O] [Fintype ι] [DecidableEq ι] in
/-- The coefficients of a variable tend to zero. -/
theorem decay_X {σ : Type*} (s : σ) :
    Tendsto (fun d ↦ coeff d (X s : MvPowerSeries σ O)) cofinite (𝓝 0) := by
  classical
  refine tendsto_nhds_of_eventually_eq ?_
  rw [eventually_cofinite]
  refine (Set.finite_singleton (Finsupp.single s 1)).subset fun d hd ↦ ?_
  simp only [Set.mem_ofPred_eq] at hd
  simp only [Set.mem_singleton_iff]
  by_contra hne
  exact hd (by simp [coeff_X, hne])

omit [IsLocalRing O] [Fintype ι] [DecidableEq ι] in
/-- `evalT` at the zero point is the constant coefficient. -/
theorem evalT_zero_point {σ : Type*} (h : MvPowerSeries σ O) :
    MvPSeries.evalT (0 : σ → O) h = constantCoeff h := by
  classical
  rw [MvPSeries.evalT_eq_tsum, tsum_eq_single 0]
  · rw [Finsupp.prod_zero_index, mul_one, coeff_zero_eq_constantCoeff_apply]
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
    rw [Finsupp.prod, Finset.prod_eq_zero hs (by
      rw [Pi.zero_apply, zero_pow (Finsupp.mem_support_iff.mp hs)]), mul_zero]

/-- The scaled logarithm vanishes at `0`. -/
theorem logVal_zero (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (Φ : FormalGroupLaw O ι) :
    logVal Φ f c 0 = 0 := by
  funext i
  exact (evalT_zero_point _).trans (constantCoeff_logC hp hpm hc hf Φ i)

variable [Fact (IsAdic (maximalIdeal O))]

/-- The coefficients of the scaled logarithm tend to zero. -/
theorem decay_logC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (Φ : FormalGroupLaw O ι) (i : ι) :
    Tendsto (fun d ↦ coeff d (logC Φ f c i)) cofinite (𝓝 0) :=
  MvPSeries.tendsto_coeff_zero_of_mem_pow (fun d ↦ coeff_logC_mem hp hpm hc hf Φ i d)
    ((tendsto_sub_atTop_nat 1).comp Finsupp.tendsto_degree_cofinite)

/-- The coefficients of the scaled exponential tend to zero. -/
theorem decay_expC (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (Φ : FormalGroupLaw O ι) (i : ι) :
    Tendsto (fun d ↦ coeff d (expC Φ f c i)) cofinite (𝓝 0) :=
  MvPSeries.tendsto_coeff_zero_of_mem_pow (fun d ↦ coeff_expC_mem hp hpm hc hf Φ i d)
    ((tendsto_sub_atTop_nat 1).comp Finsupp.tendsto_degree_cofinite)

omit [Fintype ι] [DecidableEq ι] in
/-- The coefficients of the scaled group law tend to zero. -/
theorem decay_addC [Finite ι] (hcm : c ∈ maximalIdeal O) (Φ : FormalGroupLaw O ι) (j : ι) :
    Tendsto (fun d ↦ coeff d (addC Φ c j)) cofinite (𝓝 0) :=
  MvPSeries.tendsto_coeff_zero_of_mem_pow (fun d ↦ coeff_addC_mem hcm Φ j d)
    ((tendsto_sub_atTop_nat 1).comp Finsupp.tendsto_degree_cofinite)

variable [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

/-- `exp ∘ log = id` on `O^ι`, for the scaled series. -/
theorem expVal_logVal (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι)
    (y : ι → O) : expVal Φ f c (logVal Φ f c y) = y := by
  funext i
  have hLs : HasSubst (logC Φ f c) :=
    hasSubst_of_constantCoeff_zero fun j ↦ constantCoeff_logC hp hpm hc hf Φ j
  change MvPSeries.evalT (fun s ↦ MvPSeries.evalT y (logC Φ f c s)) (expC Φ f c i) = y i
  rw [← MvPSeries.evalT_subst y hLs (decay_expC hp hpm hc hf Φ i)
      (decay_logC hp hpm hc hf Φ), subst_logC_expC hp hpm hc hf hc0 Φ i, MvPSeries.evalT_X]

/-- `log ∘ exp = id` on `O^ι`, for the scaled series. -/
theorem logVal_expVal (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι)
    (x : ι → O) : logVal Φ f c (expVal Φ f c x) = x := by
  funext i
  have hEs : HasSubst (expC Φ f c) :=
    hasSubst_of_constantCoeff_zero fun j ↦ constantCoeff_expC hp hpm hc hf Φ j
  change MvPSeries.evalT (fun s ↦ MvPSeries.evalT x (expC Φ f c s)) (logC Φ f c i) = x i
  rw [← MvPSeries.evalT_subst x hEs (decay_logC hp hpm hc hf Φ i)
      (decay_expC hp hpm hc hf Φ), subst_expC_logC hp hpm hc hf hc0 Φ i, MvPSeries.evalT_X]

/-- **The scaled logarithm is injective** on `O^ι` (every prime, every ramification). -/
theorem logVal_injective (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) :
    Function.Injective (logVal Φ f c) :=
  Function.LeftInverse.injective (g := expVal Φ f c) (expVal_logVal hp hpm hc hf hc0 Φ)

/-- **The scaled logarithm is surjective** onto `O^ι`: every `x` is the value at `expVal x`. -/
theorem logVal_surjective (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) :
    Function.Surjective (logVal Φ f c) :=
  Function.RightInverse.surjective (g := expVal Φ f c) (logVal_expVal hp hpm hc hf hc0 Φ)

/-- The scaled logarithm is a bijection of `O^ι`. -/
theorem logVal_bijective (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) :
    Function.Bijective (logVal Φ f c) :=
  ⟨logVal_injective hp hpm hc hf hc0 Φ, logVal_surjective hp hpm hc hf hc0 Φ⟩

/-- **The scaled logarithm is additive**: it turns the scaled group law `F(cy, cy')/c` into
addition. -/
theorem logVal_addVal (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι)
    (y y' : ι → O) :
    logVal Φ f c (addVal Φ c y y') = logVal Φ f c y + logVal Φ f c y' := by
  funext i
  change MvPSeries.evalT (fun j ↦ MvPSeries.evalT (Sum.elim y y') (addC Φ c j)) (logC Φ f c i)
    = MvPSeries.evalT y (logC Φ f c i) + MvPSeries.evalT y' (logC Φ f c i)
  have hdec := decay_logC hp hpm hc hf Φ i
  have hTCl : TendstoCofinite (Sum.inl : ι → ι ⊕ ι) :=
    tendstoCofinite_of_injective Sum.inl_injective
  have hTCr : TendstoCofinite (Sum.inr : ι → ι ⊕ ι) :=
    tendstoCofinite_of_injective Sum.inr_injective
  have hdXl : Tendsto (fun d ↦ coeff d (subst
      (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) (logC Φ f c i))) cofinite (𝓝 0) := by
    have h1 : (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) = X ∘ Sum.inl := rfl
    rw [h1, ← rename_eq_subst]
    exact MvPSeries.decay_rename Sum.inl_injective hdec
  have hdXr : Tendsto (fun d ↦ coeff d (subst
      (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) (logC Φ f c i))) cofinite (𝓝 0) := by
    have h1 : (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) = X ∘ Sum.inr := rfl
    rw [h1, ← rename_eq_subst]
    exact MvPSeries.decay_rename Sum.inr_injective hdec
  rw [← MvPSeries.evalT_subst (Sum.elim y y') (hasSubst_addC Φ c) hdec
      (decay_addC hc.mem_maximalIdeal Φ),
    subst_addC_logC hp hpm hc hf hc0 Φ i, MvPSeries.evalT_add _ hdXl hdXr,
    MvPSeries.evalT_subst (Sum.elim y y') FormalGroupLaw.hasSubst_Xemb hdec
      fun s ↦ decay_X _,
    MvPSeries.evalT_subst (Sum.elim y y') FormalGroupLaw.hasSubst_Yemb hdec
      fun s ↦ decay_X _]
  have hyl : (fun s ↦ MvPSeries.evalT (Sum.elim y y')
      (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) = y :=
    funext fun s ↦ by rw [MvPSeries.evalT_X, Sum.elim_inl]
  have hyr : (fun s ↦ MvPSeries.evalT (Sum.elim y y')
      (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) = y' :=
    funext fun s ↦ by rw [MvPSeries.evalT_X, Sum.elim_inr]
  rw [hyl, hyr]

/-- The scaled logarithm vanishes only at `0`. -/
theorem logVal_eq_zero_iff (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι)
    (y : ι → O) : logVal Φ f c y = 0 ↔ y = 0 := by
  constructor
  · intro h
    exact logVal_injective hp hpm hc hf hc0 Φ (h.trans (logVal_zero hp hpm hc hf Φ).symm)
  · rintro rfl
    exact logVal_zero hp hpm hc hf Φ

end Values

end FurioLombardo.Vendor.Toolbox.FormalGroup
