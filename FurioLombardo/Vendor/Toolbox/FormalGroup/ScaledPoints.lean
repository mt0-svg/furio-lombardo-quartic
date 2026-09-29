import FurioLombardo.Vendor.Toolbox.FormalGroup.ScaledLog

/-!
# The logarithm on the points of a formal group law: injective near `0`, torsion kernel

Standing setting of `FurioLombardo.Vendor.Toolbox.FormalGroup.ScaledLog`, with `O` a domain for the logarithm: `O` a
complete local ring with the adic topology of `𝔪`, `p` prime in `𝔪`, `f : O →+* K` injective
into a field of characteristic zero, `Φ` a formal group law over `O` of dimension `ι`, and
`c ≠ 0` with `ScalingHyp p c`. The points `Φ.Points = 𝔪^ι` form a commutative monoid under `F`
(Stoll's `Points.lean`).

* `FurioLombardo.Vendor.Toolbox.FormalGroup.B1 Φ c`: the submonoid of points with coordinates in `cO`. For points
  `cy`, `cy'` the sum is `c · addVal y y'` (`coe_add_of_eq_mul`), so `logB1`,
  `z = cy ↦ logVal y`, is an additive bijection `B1 Φ c ≃ O^ι` (`logB1_bijective`): the
  logarithm is an isomorphism `B1 → cO^ι`.
* Every point has a multiple in `B1` once `𝔪 ^ N ≤ (c)` (true in a discrete valuation ring):
  `p ^ k • z` has coordinates in `𝔪 ^ (k + 1)` (`coe_pow_nsmul_mem`), from
  `F(z, w) ≡ z + w mod 𝔪 ^ (2k)` on points of `𝔪 ^ k` (`coe_add_sub_mem`). No noetherian
  hypothesis: `𝔪 ^ (2k)` is open, hence closed.
* `FurioLombardo.Vendor.Toolbox.FormalGroup.logPoints`, `z ↦ f(p) ^ (-N) f(c · logVal (p ^ N z / c))`, the logarithm
  on all of `Φ.Points` with values in `K^ι`: additive (`logPointsHom`), independent of `N`
  (`logPoints_eq_of_nsmul_mem`), with kernel the torsion (`logPoints_eq_zero_iff`), image
  containing `f(c) O^ι` (`exists_logPoints_eq`) and contained in `f(c) f(p) ^ (-N) O^ι`
  (`exists_logPoints_eq_mul`).
* `FurioLombardo.Vendor.Toolbox.FormalGroup.LogChart`, `log_chart`: the summary in abstract form, for use without the
  kit; `log_chart_uniformizer` (`c = π ^ (e + 1)`) and `log_chart_sq` (`c = p ^ 2`) in a discrete
  valuation ring.

Origin: written for this formalization (the discharge of the analytic hypotheses,
`FurioLombardo.Discharge.Analytic`), on Michael Stoll's formal group law kit
(`FurioLombardo.Vendor.Toolbox.Stoll.Mathlib.Chabauty`, Apache 2.0).
-/

open MvPowerSeries IsLocalRing Filter Topology
open FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman

namespace FurioLombardo.Vendor.Toolbox.FormalGroup

/-! ### Division by `c` -/

section Div

variable {O : Type*} [CommRing O]

open scoped Classical in
/-- `x / c` when `c ∣ x` (the junk value `0` otherwise). -/
noncomputable def divC (c x : O) : O :=
  if h : c ∣ x then h.choose else 0

/-- `c · (x / c) = x` when `x ∈ (c)`. -/
theorem mul_divC {c x : O} (h : x ∈ Ideal.span {c}) : c * divC c x = x := by
  have h' : c ∣ x := Ideal.mem_span_singleton.mp h
  rw [divC, dite_eq_left h']
  exact h'.choose_spec.symm

/-- `(c y) / c = y` for `c ≠ 0` in a domain. -/
theorem divC_eq [IsDomain O] {c x y : O} (hc0 : c ≠ 0) (h : x = c * y) : divC c x = y :=
  mul_left_cancel₀ hc0 ((mul_divC (Ideal.mem_span_singleton.mpr ⟨y, h⟩)).trans h)

end Div

/-! ### Degree bounds for values at points of `𝔪 ^ k` -/

section Bounds

variable {O : Type*} [CommRing O]

/-- A multi-index of total degree `1` is a single variable. -/
theorem exists_eq_single_of_degree_eq_one {σ : Type*} {d : σ →₀ ℕ} (h : d.degree = 1) :
    ∃ s, d = Finsupp.single s 1 := by
  classical
  have hne : d ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hsum : ∑ t ∈ d.support, d t = 1 := by rw [← Finsupp.degree_apply]; exact h
  have hds : d s = 1 := by
    have h1 := Finset.single_le_sum (fun t _ ↦ Nat.zero_le (d t)) hs
    have h2 := Finsupp.mem_support_iff.mp hs
    omega
  refine ⟨s, Finsupp.ext fun t ↦ ?_⟩
  by_cases hts : t = s
  · rw [hts, Finsupp.single_eq_same, hds]
  · rw [Finsupp.single_eq_of_ne hts]
    by_contra hne'
    have hsub : ({s, t} : Finset σ) ⊆ d.support := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hs
      · exact Finsupp.mem_support_iff.mpr hne'
    have h2 := Finset.sum_le_sum_of_subset (f := fun u ↦ d u) hsub
    rw [Finset.sum_pair (Ne.symm hts)] at h2
    have h3 := Nat.pos_of_ne_zero hne'
    omega

/-- A monomial in elements of an ideal `I` lies in `I ^ deg`. -/
theorem prod_pow_mem_pow {σ : Type*} {I : Ideal O} {u : σ → O} (hu : ∀ s, u s ∈ I)
    (d : σ →₀ ℕ) : (d.prod fun s e ↦ u s ^ e) ∈ I ^ d.degree := by
  rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun s _ ↦ Ideal.pow_mem_pow (hu s) _

variable [IsLocalRing O] [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

/-- The value of a power series of order at least `n` at a point of `(𝔪 ^ k)^σ` lies in
`𝔪 ^ (k n)`. -/
theorem eval_mem_pow {σ : Type*} [Finite σ] {k : ℕ} {u : σ → O}
    (hu : ∀ s, u s ∈ maximalIdeal O ^ k) (hk : 1 ≤ k) {h : MvPowerSeries σ O} {n : ℕ}
    (hh : ∀ d : σ →₀ ℕ, d.degree < n → coeff d h = 0) :
    MvPSeries.eval u h ∈ maximalIdeal O ^ (k * n) := by
  have hum : ∀ s, u s ∈ maximalIdeal O := fun s ↦
    Ideal.pow_le_self (by omega) (hu s)
  rw [← (MvPSeries.hasSum_eval (MvPSeries.hasEval_of_mem hum) h).tsum_eq]
  refine tsum_mem ((Fact.out : IsAdic (maximalIdeal O)).isClosed_pow _) fun d ↦ ?_
  rcases lt_or_ge d.degree n with hd | hd
  · rw [hh d hd, zero_mul]
    exact zero_mem _
  · refine Ideal.mul_mem_left _ _ ?_
    have hmem := prod_pow_mem_pow hu d
    rw [← pow_mul] at hmem
    exact Ideal.pow_le_pow_right (Nat.mul_le_mul_left k hd) hmem

end Bounds

/-! ### The group law on points of `𝔪 ^ k` and of `cO` -/

section PointsArith

variable {O : Type*} [CommRing O] {ι : Type*} [Finite ι] (Φ : FormalGroupLaw O ι)

/-- The linear part of `F` in the second block: `∂F_i/∂Y_j (0) = δ_ij`. -/
theorem coeff_F_single_inr [DecidableEq ι] (i j : ι) :
    coeff (Finsupp.single (Sum.inr j) 1) (Φ.F i) = if i = j then 1 else 0 := by
  have h := congrArg (fun A ↦ A i j) Φ.diffMatrix_map_constantCoeff
  simp only [Matrix.map_apply, Matrix.one_apply] at h
  rw [show Φ.diffMatrix i j = MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X (fun _ ↦ 0) : ι ⊕ ι → MvPowerSeries ι O)
      (pderiv (Sum.inr j) (Φ.F i)) from rfl,
    MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero FormalGroupLaw.hasSubst_unitR
      (by rintro (a | a) <;> simp),
    ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add] at h
  simpa using h

/-- The linear part of `F` in the first block: `∂F_i/∂X_j (0) = δ_ij` (by commutativity). -/
theorem coeff_F_single_inl [DecidableEq ι] (i j : ι) :
    coeff (Finsupp.single (Sum.inl j) 1) (Φ.F i) = if i = j then 1 else 0 := by
  have hren : rename (Sum.swap : ι ⊕ ι → ι ⊕ ι) (Φ.F i) = Φ.F i := by
    rw [rename_eq_subst]
    exact Φ.comm' i
  have hemb := coeff_embDomain_rename
    (⟨Sum.swap, Sum.swap_leftInverse.injective⟩ : ι ⊕ ι ↪ ι ⊕ ι) (Φ.F i)
    (Finsupp.single (Sum.inr j) 1)
  rw [Finsupp.embDomain_single] at hemb
  change coeff (Finsupp.single (Sum.inl j) 1) (rename Sum.swap (Φ.F i)) = _ at hemb
  rw [hren] at hemb
  rw [hemb, coeff_F_single_inr]

/-- `F_i - X_i - Y_i` has no terms of degree `≤ 1`. -/
theorem coeff_F_sub_eq_zero (i : ι) (d : ι ⊕ ι →₀ ℕ) (hd : d.degree < 2) :
    coeff d (Φ.F i - X (Sum.inl i) - X (Sum.inr i)) = 0 := by
  classical
  rcases Nat.lt_or_ge d.degree 1 with h0 | h1
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    simp [coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff i]
  · obtain ⟨s, rfl⟩ := exists_eq_single_of_degree_eq_one (by omega : d.degree = 1)
    have hsingle : ∀ a b : ι ⊕ ι,
        (Finsupp.single a 1 : ι ⊕ ι →₀ ℕ) = Finsupp.single b 1 ↔ a = b :=
      fun a b ↦ Finsupp.single_left_inj one_ne_zero
    rw [map_sub, map_sub, coeff_X, coeff_X]
    rcases s with j | j
    · by_cases hij : i = j
      · subst hij
        simp [coeff_F_single_inl, hsingle]
      · simp [coeff_F_single_inl, hsingle, hij, Ne.symm hij]
    · by_cases hij : i = j
      · subst hij
        simp [coeff_F_single_inr, hsingle]
      · simp [coeff_F_single_inr, hsingle, hij, Ne.symm hij]

variable [IsLocalRing O] [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

/-- On points of `𝔪 ^ k`, `F(z, w) ≡ z + w` modulo `𝔪 ^ (2k)`. -/
theorem coe_add_sub_mem {k : ℕ} (hk : 1 ≤ k) {z w : Φ.Points}
    (hz : ∀ j, (z j : O) ∈ maximalIdeal O ^ k) (hw : ∀ j, (w j : O) ∈ maximalIdeal O ^ k)
    (j : ι) : ((z + w) j : O) - z j - w j ∈ maximalIdeal O ^ (k * 2) := by
  have hu : ∀ s, FormalGroupLaw.pairFam Φ z w s ∈ maximalIdeal O ^ k := by
    rintro (s | s)
    · exact hz s
    · exact hw s
  have hE := FormalGroupLaw.hasEval_pairFam Φ z w
  have hval : ((z + w) j : O) - z j - w j
      = MvPSeries.eval (FormalGroupLaw.pairFam Φ z w)
          (Φ.F j - X (Sum.inl j) - X (Sum.inr j)) := by
    rw [MvPSeries.eval_sub hE, MvPSeries.eval_sub hE, MvPSeries.eval_X, MvPSeries.eval_X,
      FormalGroupLaw.add_apply_coe]
    rfl
  rw [hval]
  exact eval_mem_pow hu hk fun d hd ↦ coeff_F_sub_eq_zero Φ j d hd

/-- On a point of `𝔪 ^ k`, the multiples `n • z` stay in `𝔪 ^ k` and `n • z ≡ n z` modulo
`𝔪 ^ (2k)`. -/
theorem coe_nsmul_sub_mem {k : ℕ} (hk : 1 ≤ k) {z : Φ.Points}
    (hz : ∀ j, (z j : O) ∈ maximalIdeal O ^ k) (n : ℕ) :
    (∀ j, ((n • z) j : O) ∈ maximalIdeal O ^ k) ∧
      ∀ j, ((n • z) j : O) - n * z j ∈ maximalIdeal O ^ (k * 2) := by
  have hle : maximalIdeal O ^ (k * 2) ≤ maximalIdeal O ^ k := Ideal.pow_le_pow_right (by omega)
  induction n with
  | zero =>
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
    · rw [zero_nsmul, FormalGroupLaw.zero_apply_coe]
      exact zero_mem _
    · rw [zero_nsmul, FormalGroupLaw.zero_apply_coe, Nat.cast_zero, zero_mul, sub_zero]
      exact zero_mem _
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hadd := coe_add_sub_mem Φ hk ih1 hz
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
    · rw [succ_nsmul]
      have : ((n • z + z) j : O)
          = (((n • z + z) j : O) - (n • z) j - z j) + (n • z) j + z j := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.add_mem _ (hle (hadd j)) (ih1 j)) (hz j)
    · rw [succ_nsmul]
      have : ((n • z + z) j : O) - ((n + 1 : ℕ) : O) * z j
          = (((n • z + z) j : O) - (n • z) j - z j) + (((n • z) j : O) - n * z j) := by
        push_cast
        ring
      rw [this]
      exact Ideal.add_mem _ (hadd j) (ih2 j)

/-- `[p]` maps points of `𝔪 ^ k` (`k ≥ 1`) to points of `𝔪 ^ (k + 1)`. -/
theorem coe_nsmul_prime_mem {p : ℕ} (hpm : (p : O) ∈ maximalIdeal O) {k : ℕ} (hk : 1 ≤ k)
    {z : Φ.Points} (hz : ∀ j, (z j : O) ∈ maximalIdeal O ^ k) (j : ι) :
    ((p • z) j : O) ∈ maximalIdeal O ^ (k + 1) := by
  have h2 := (coe_nsmul_sub_mem Φ hk hz p).2 j
  have : ((p • z) j : O) = (((p • z) j : O) - p * z j) + p * z j := by ring
  rw [this]
  refine Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) h2) ?_
  rw [pow_succ']
  exact Ideal.mul_mem_mul hpm (hz j)

/-- `p ^ k • z` has coordinates in `𝔪 ^ (k + 1)`, for every point `z`. -/
theorem coe_pow_nsmul_mem {p : ℕ} (hpm : (p : O) ∈ maximalIdeal O) (z : Φ.Points) (k : ℕ)
    (j : ι) : (((p ^ k) • z) j : O) ∈ maximalIdeal O ^ (k + 1) := by
  induction k generalizing j with
  | zero =>
    rw [pow_zero, one_nsmul, zero_add, pow_one]
    exact (z j).2
  | succ k ih =>
    have hpk : (p ^ (k + 1)) • z = p • ((p ^ k) • z) := by rw [pow_succ', mul_nsmul']
    rw [hpk]
    exact coe_nsmul_prime_mem Φ hpm (by omega) ih j

/-- The sum of the points `c y` and `c y'` is the point `c · addVal y y'`. -/
theorem coe_add_of_eq_mul {c : O} (hcm : c ∈ maximalIdeal O) {z w : Φ.Points} {y y' : ι → O}
    (hz : ∀ j, (z j : O) = c * y j) (hw : ∀ j, (w j : O) = c * y' j) (j : ι) :
    ((z + w) j : O) = c * addVal Φ c y y' j := by
  have hfam : FormalGroupLaw.pairFam Φ z w = fun s ↦ c * Sum.elim y y' s := by
    funext s
    rcases s with s | s
    · exact hz s
    · exact hw s
  rw [FormalGroupLaw.add_apply_coe,
    ← MvPSeries.evalT_eq_eval (FormalGroupLaw.hasEval_pairFam Φ z w), hfam, addVal,
    ← ((MvPSeries.hasSum_evalT (Sum.elim y y') (decay_addC hcm Φ j)).mul_left c).tsum_eq,
    MvPSeries.evalT_eq_tsum]
  refine tsum_congr fun d ↦ ?_
  rw [coeff_addC]
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    simp [coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff j]
  · have hprod : (d.prod fun s e ↦ (c * Sum.elim y y' s) ^ e)
        = c ^ d.degree * d.prod fun s e ↦ Sum.elim y y' s ^ e := by
      rw [Finsupp.prod, Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun s _ ↦ mul_pow _ _ _
    have hcc : c * c ^ (d.degree - 1) = c ^ d.degree := by
      rw [← pow_succ', Nat.sub_add_cancel hpos]
    rw [hprod, ← hcc]
    ring

end PointsArith

/-! ### The submonoid `B1` of points in `cO` and the logarithm on it -/

section B1

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {ι : Type*} [Finite ι]
  {K : Type*} [Field K] [CharZero K] {p : ℕ} {c : O}

/-- The points with coordinates in `cO`, a submonoid of `Φ.Points`. -/
def B1 (Φ : FormalGroupLaw O ι) (c : O) : AddSubmonoid Φ.Points where
  carrier := {z | ∀ j, (z j : O) ∈ Ideal.span {c}}
  zero_mem' j := by
    rw [FormalGroupLaw.zero_apply_coe]
    exact zero_mem _
  add_mem' {z w} hz hw j := by
    by_cases hcm : c ∈ maximalIdeal O
    · rw [coe_add_of_eq_mul Φ hcm (fun j ↦ (mul_divC (hz j)).symm)
        (fun j ↦ (mul_divC (hw j)).symm) j]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)
    · rw [(Ideal.span_singleton_eq_top).mpr (IsLocalRing.notMem_maximalIdeal.mp hcm)]
      exact Submodule.mem_top

/-- Membership in `B1`. -/
theorem mem_B1 (Φ : FormalGroupLaw O ι) (z : Φ.Points) :
    z ∈ B1 Φ c ↔ ∀ j, (z j : O) ∈ Ideal.span {c} := Iff.rfl

/-- The point with coordinates `c y`, for `c ∈ 𝔪`. -/
def ofMul (Φ : FormalGroupLaw O ι) (hcm : c ∈ maximalIdeal O) (y : ι → O) : Φ.Points :=
  fun j ↦ ⟨c * y j, Ideal.mul_mem_right _ _ hcm⟩

/-- The point `c y` lies in `B1`. -/
theorem ofMul_mem_B1 (Φ : FormalGroupLaw O ι) (hcm : c ∈ maximalIdeal O) (y : ι → O) :
    ofMul Φ hcm y ∈ B1 Φ c := fun _ ↦ Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)

/-- Every point has a multiple in `B1` once `𝔪 ^ N ≤ (c)`: `p ^ k • z ∈ B1` for `N ≤ k + 1`. -/
theorem pow_nsmul_mem_B1 (hpm : (p : O) ∈ maximalIdeal O) (Φ : FormalGroupLaw O ι) {N : ℕ}
    (hN : maximalIdeal O ^ N ≤ Ideal.span {c}) (z : Φ.Points) {k : ℕ} (hk : N ≤ k + 1) :
    (p ^ k) • z ∈ B1 Φ c := fun j ↦
  hN (Ideal.pow_le_pow_right hk (coe_pow_nsmul_mem Φ hpm z k j))

end B1

section LogB1

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] [CharZero K] {p : ℕ} {c : O}

/-- The scaled logarithm on `B1`: a point `z = c y` goes to `logVal y`, i.e. `c⁻¹ log z`. -/
noncomputable def logB1 (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) :
    B1 Φ c →+ (ι → O) where
  toFun z := logVal Φ f c fun j ↦ divC c ((z : Φ.Points) j)
  map_zero' := by
    have h0 : (fun j ↦ divC c (((0 : B1 Φ c) : Φ.Points) j : O)) = 0 := funext fun j ↦
      divC_eq hc0 (by rw [ZeroMemClass.coe_zero, FormalGroupLaw.zero_apply_coe, Pi.zero_apply,
        mul_zero])
    rw [h0, logVal_zero hp hpm hc hf Φ]
  map_add' z w := by
    have hcm := hc.mem_maximalIdeal
    have hsum : (fun j ↦ divC c (((z + w : B1 Φ c) : Φ.Points) j : O))
        = addVal Φ c (fun j ↦ divC c ((z : Φ.Points) j)) (fun j ↦ divC c ((w : Φ.Points) j)) :=
      funext fun j ↦ divC_eq hc0 (by
        rw [AddMemClass.coe_add]
        exact coe_add_of_eq_mul Φ hcm (fun j ↦ (mul_divC (z.2 j)).symm)
          (fun j ↦ (mul_divC (w.2 j)).symm) j)
    rw [hsum, logVal_addVal hp hpm hc hf hc0 Φ]

/-- `logB1` at a point with coordinates `c y` is `logVal y`. -/
theorem logB1_apply (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι)
    (z : B1 Φ c) {y : ι → O} (hz : ∀ j, ((z : Φ.Points) j : O) = c * y j) :
    logB1 hp hpm hc hf hc0 Φ z = logVal Φ f c y := by
  change logVal Φ f c (fun j ↦ divC c ((z : Φ.Points) j)) = _
  rw [show (fun j ↦ divC c ((z : Φ.Points) j : O)) = y from funext fun j ↦ divC_eq hc0 (hz j)]

/-- **The logarithm is an isomorphism `B1 ≃ O^ι`** (`z = cy ↦ logVal y`): additive, injective
and onto. -/
theorem logB1_bijective (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) :
    Function.Bijective (logB1 hp hpm hc hf hc0 Φ) := by
  have hcm := hc.mem_maximalIdeal
  constructor
  · intro z w hzw
    have hdiv : (fun j ↦ divC c ((z : Φ.Points) j : O)) = fun j ↦ divC c ((w : Φ.Points) j : O) :=
      logVal_injective hp hpm hc hf hc0 Φ hzw
    refine Subtype.ext (funext fun j ↦ Subtype.ext ?_)
    rw [← mul_divC (z.2 j), ← mul_divC (w.2 j)]
    exact congrArg (c * ·) (congrFun hdiv j)
  · intro x
    refine ⟨⟨ofMul Φ hcm (expVal Φ f c x), ofMul_mem_B1 Φ hcm _⟩, ?_⟩
    rw [logB1_apply hp hpm hc hf hc0 Φ _ (fun j ↦ rfl), logVal_expVal hp hpm hc hf hc0 Φ]

end LogB1

/-! ### The logarithm on all points -/

section LogPoints

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] [CharZero K] {p : ℕ} {c : O}

/-- The logarithm of a point, with values in `K^ι`:
`f(p) ^ (-N) · f(c · logVal (p ^ N • z / c))`. For
`𝔪 ^ N ≤ (c)` it is additive with kernel the torsion; it does not depend on `N`
(`logPoints_eq_of_nsmul_mem`). -/
noncomputable def logPoints (Φ : FormalGroupLaw O ι) (f : O →+* K) (c : O) (p N : ℕ)
    (z : Φ.Points) : ι → K :=
  fun i ↦ (f (p : O) ^ N)⁻¹ * f (c * logVal Φ f c (fun j ↦ divC c (((p ^ N) • z) j : O)) i)

/-- `logPoints` through `logB1`. -/
theorem logPoints_eq_logB1 (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) {N : ℕ}
    (hN : maximalIdeal O ^ N ≤ Ideal.span {c}) (z : Φ.Points) :
    logPoints Φ f c p N z = fun i ↦ (f (p : O) ^ N)⁻¹
      * f (c * logB1 hp hpm hc hf hc0 Φ ⟨(p ^ N) • z, pow_nsmul_mem_B1 hpm Φ hN z (by omega)⟩ i) :=
  rfl

/-- `logB1` commutes with `n • ·`: `logB1 (n • w) = n • logB1 w`. -/
theorem logB1_nsmul (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι)
    (w : B1 Φ c) (n : ℕ) (hmem : n • (w : Φ.Points) ∈ B1 Φ c) :
    logB1 hp hpm hc hf hc0 Φ ⟨n • (w : Φ.Points), hmem⟩ = n • logB1 hp hpm hc hf hc0 Φ w := by
  rw [← map_nsmul]
  rfl

/-- On `B1`, `logPoints` is `f(c)` times the scaled logarithm:
`logPoints (c y) = f(c) f(logVal y)`. -/
theorem logPoints_of_eq_mul (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) {N : ℕ}
    (hN : maximalIdeal O ^ N ≤ Ideal.span {c}) {z : Φ.Points} {y : ι → O}
    (hz : ∀ j, (z j : O) = c * y j) :
    logPoints Φ f c p N z = fun i ↦ f c * f (logVal Φ f c y i) := by
  have hzB : z ∈ B1 Φ c := fun j ↦ by
    rw [hz j]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)
  have hfp : f (p : O) ≠ 0 := by rw [map_natCast]; exact_mod_cast hp.ne_zero
  rw [logPoints_eq_logB1 hp hpm hc hf hc0 Φ hN z]
  have h1 := logB1_nsmul hp hpm hc hf hc0 Φ ⟨z, hzB⟩ (p ^ N)
    (pow_nsmul_mem_B1 hpm Φ hN z (by omega))
  have h2 := logB1_apply hp hpm hc hf hc0 Φ ⟨z, hzB⟩ hz
  simp only at h1
  rw [h1, h2]
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul, map_mul, map_mul, Nat.cast_pow, map_pow]
  generalize f (p : O) = P at hfp ⊢
  field_simp

/-- **Independence of the exponent**: for any `k` with `p ^ k • z ∈ B1`,
`logPoints z = f(p) ^ (-k) f(c · logVal (p ^ k • z / c))`. -/
theorem logPoints_eq_of_nsmul_mem (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O)
    (hc : ScalingHyp p c) {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0)
    (Φ : FormalGroupLaw O ι) {N : ℕ} (hN : maximalIdeal O ^ N ≤ Ideal.span {c}) (z : Φ.Points)
    {k : ℕ} (hk : (p ^ k) • z ∈ B1 Φ c) :
    logPoints Φ f c p N z = fun i ↦ (f (p : O) ^ k)⁻¹
      * f (c * logVal Φ f c (fun j ↦ divC c (((p ^ k) • z) j : O)) i) := by
  have hfp : f (p : O) ≠ 0 := by rw [map_natCast]; exact_mod_cast hp.ne_zero
  set wN : B1 Φ c := ⟨(p ^ N) • z, pow_nsmul_mem_B1 hpm Φ hN z (by omega)⟩ with hwN
  set wk : B1 Φ c := ⟨(p ^ k) • z, hk⟩ with hwk
  have hmemNk : (p ^ N) • (wk : Φ.Points) ∈ B1 Φ c := (p ^ N • wk).2
  have hmemkN : (p ^ k) • (wN : Φ.Points) ∈ B1 Φ c := (p ^ k • wN).2
  have hsame : (p ^ N) • (wk : Φ.Points) = (p ^ k) • (wN : Φ.Points) := by
    change (p ^ N) • ((p ^ k) • z) = (p ^ k) • ((p ^ N) • z)
    rw [← mul_nsmul', ← mul_nsmul', Nat.mul_comm]
  have hL : p ^ N • logB1 hp hpm hc hf hc0 Φ wk = p ^ k • logB1 hp hpm hc hf hc0 Φ wN := by
    rw [← logB1_nsmul hp hpm hc hf hc0 Φ wk _ hmemNk, ← logB1_nsmul hp hpm hc hf hc0 Φ wN _ hmemkN]
    congr 1
    exact Subtype.ext hsame
  rw [logPoints_eq_logB1 hp hpm hc hf hc0 Φ hN z]
  funext i
  have hLi := congrArg (fun v ↦ f (v i)) hL
  simp only [Pi.smul_apply, nsmul_eq_mul, map_mul, Nat.cast_pow, map_pow] at hLi
  change (f (p : O) ^ N)⁻¹ * f (c * logB1 hp hpm hc hf hc0 Φ wN i)
    = (f (p : O) ^ k)⁻¹ * f (c * logB1 hp hpm hc hf hc0 Φ wk i)
  rw [map_mul, map_mul]
  generalize f (p : O) = P at hfp hLi ⊢
  generalize f (logB1 hp hpm hc hf hc0 Φ wN i) = a at hLi ⊢
  generalize f (logB1 hp hpm hc hf hc0 Φ wk i) = b at hLi ⊢
  calc (P ^ N)⁻¹ * (f c * a) = (P ^ N)⁻¹ * (P ^ k)⁻¹ * f c * (P ^ k * a) := by field_simp
    _ = (P ^ N)⁻¹ * (P ^ k)⁻¹ * f c * (P ^ N * b) := by rw [hLi]
    _ = (P ^ k)⁻¹ * (f c * b) := by field_simp

/-- `logPoints` vanishes at `0`. -/
theorem logPoints_zero (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) (N : ℕ) :
    logPoints Φ f c p N 0 = 0 := by
  have h0 : (fun j ↦ divC c ((((p ^ N) • (0 : Φ.Points)) j : O))) = 0 := funext fun j ↦
    divC_eq hc0 (by rw [nsmul_zero, FormalGroupLaw.zero_apply_coe, Pi.zero_apply, mul_zero])
  funext i
  simp only [logPoints]
  rw [h0, logVal_zero hp hpm hc hf Φ, Pi.zero_apply, mul_zero, map_zero, mul_zero, Pi.zero_apply]

/-- `logPoints` is additive. -/
theorem logPoints_add (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) {N : ℕ}
    (hN : maximalIdeal O ^ N ≤ Ideal.span {c}) (z w : Φ.Points) :
    logPoints Φ f c p N (z + w) = logPoints Φ f c p N z + logPoints Φ f c p N w := by
  rw [logPoints_eq_logB1 hp hpm hc hf hc0 Φ hN, logPoints_eq_logB1 hp hpm hc hf hc0 Φ hN,
    logPoints_eq_logB1 hp hpm hc hf hc0 Φ hN]
  have hsplit : (⟨(p ^ N) • (z + w), pow_nsmul_mem_B1 hpm Φ hN (z + w) (by omega)⟩ : B1 Φ c)
      = ⟨(p ^ N) • z, pow_nsmul_mem_B1 hpm Φ hN z (by omega)⟩
        + ⟨(p ^ N) • w, pow_nsmul_mem_B1 hpm Φ hN w (by omega)⟩ :=
    Subtype.ext (nsmul_add _ _ _)
  rw [hsplit, map_add]
  funext i
  simp only [Pi.add_apply, mul_add, map_add]

/-- The logarithm on all points as an additive map `Φ.Points →+ K^ι`. -/
noncomputable def logPointsHom (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O)
    (hc : ScalingHyp p c) {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0)
    (Φ : FormalGroupLaw O ι) {N : ℕ} (hN : maximalIdeal O ^ N ≤ Ideal.span {c}) :
    Φ.Points →+ (ι → K) where
  toFun := logPoints Φ f c p N
  map_zero' := logPoints_zero hp hpm hc hf hc0 Φ N
  map_add' := logPoints_add hp hpm hc hf hc0 Φ hN

/-- **The kernel of the logarithm is the torsion**: `logPoints z = 0` iff `n • z = 0` for some
`n > 0`. -/
theorem logPoints_eq_zero_iff (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O)
    (hc : ScalingHyp p c) {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0)
    (Φ : FormalGroupLaw O ι) {N : ℕ} (hN : maximalIdeal O ^ N ≤ Ideal.span {c}) (z : Φ.Points) :
    logPoints Φ f c p N z = 0 ↔ ∃ n : ℕ, 0 < n ∧ n • z = 0 := by
  have hfp : f (p : O) ≠ 0 := by rw [map_natCast]; exact_mod_cast hp.ne_zero
  constructor
  · intro h
    refine ⟨p ^ N, pow_pos hp.pos N, ?_⟩
    set w : B1 Φ c := ⟨(p ^ N) • z, pow_nsmul_mem_B1 hpm Φ hN z (by omega)⟩ with hw
    have hL : logB1 hp hpm hc hf hc0 Φ w = 0 := by
      funext i
      have hi := congrFun h i
      rw [logPoints_eq_logB1 hp hpm hc hf hc0 Φ hN] at hi
      simp only [Pi.zero_apply, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', hfp, ne_eq,
        false_and, false_or] at hi
      have hci : c * logB1 hp hpm hc hf hc0 Φ w i = 0 := hf (by rw [hi, map_zero])
      exact (mul_eq_zero.mp hci).resolve_left hc0
    have hw0 : w = 0 := (logB1_bijective hp hpm hc hf hc0 Φ).1 (hL.trans (map_zero _).symm)
    exact congrArg Subtype.val hw0
  · rintro ⟨n, hn, hnz⟩
    have hmap := map_nsmul (logPointsHom hp hpm hc hf hc0 Φ hN) n z
    rw [hnz, map_zero] at hmap
    change 0 = n • logPoints Φ f c p N z at hmap
    funext i
    have hi := congrFun hmap i
    rw [Pi.zero_apply, Pi.smul_apply, nsmul_eq_mul] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left (Nat.cast_ne_zero.mpr hn.ne')

/-- **The image of the logarithm contains `f(c) O^ι`**. -/
theorem exists_logPoints_eq (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O)
    (hc : ScalingHyp p c) {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0)
    (Φ : FormalGroupLaw O ι) {N : ℕ} (hN : maximalIdeal O ^ N ≤ Ideal.span {c}) (x : ι → O) :
    ∃ z : Φ.Points, logPoints Φ f c p N z = fun i ↦ f c * f (x i) := by
  refine ⟨ofMul Φ hc.mem_maximalIdeal (expVal Φ f c x), ?_⟩
  rw [logPoints_of_eq_mul hp hpm hc hf hc0 Φ hN (y := expVal Φ f c x) (fun j ↦ rfl),
    logVal_expVal hp hpm hc hf hc0 Φ]

omit [IsDomain O] [CharZero K] in
/-- **The image of the logarithm lies in `f(c) f(p) ^ (-N) O^ι`**. -/
theorem exists_logPoints_eq_mul (Φ : FormalGroupLaw O ι) (f : O →+* K) (N : ℕ) (z : Φ.Points) :
    ∃ a : ι → O, logPoints Φ f c p N z = fun i ↦ (f (p : O) ^ N)⁻¹ * (f c * f (a i)) :=
  ⟨logVal Φ f c (fun j ↦ divC c (((p ^ N) • z) j : O)),
    funext fun i ↦ by simp only [logPoints, map_mul]⟩

end LogPoints

/-! ### Summary in abstract form -/

section Summary

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] [CharZero K] {p : ℕ} {c : O}

/-- The **logarithmic chart** of `Φ` scaled by `c`, with exponent `N`:
1. the points with coordinates in `cO` form a submonoid `B1` with an additive bijection
   `L : B1 → O^ι`, `L (c y) = logVal y` (the scaled logarithm, `c⁻¹ log` in `K`);
2. every point `z` has a multiple `n • z` with `n > 0` in `B1`;
3. there is an additive map `LOG : Φ.Points → K^ι`, equal to `f(c) f(L z)` on `B1`, whose kernel
   is the torsion, whose image contains `f(c) O^ι` and lies in `f(c) f(p) ^ (-N) O^ι`. -/
def LogChart (Φ : FormalGroupLaw O ι) (f : O →+* K) (c : O) (p N : ℕ) : Prop :=
  ∃ L : B1 Φ c →+ (ι → O), Function.Bijective L ∧
    (∀ (z : B1 Φ c) (y : ι → O), (∀ j, ((z : Φ.Points) j : O) = c * y j) →
      L z = logVal Φ f c y) ∧
    (∀ z : Φ.Points, ∃ n : ℕ, 0 < n ∧ n • z ∈ B1 Φ c) ∧
    ∃ LOG : Φ.Points →+ (ι → K),
      (∀ z : B1 Φ c, LOG z = fun i ↦ f c * f (L z i)) ∧
      (∀ z : Φ.Points, LOG z = 0 ↔ ∃ n : ℕ, 0 < n ∧ n • z = 0) ∧
      (∀ x : ι → O, ∃ z : Φ.Points, LOG z = fun i ↦ f c * f (x i)) ∧
      (∀ z : Φ.Points, ∃ a : ι → O, LOG z = fun i ↦ (f (p : O) ^ N)⁻¹ * (f c * f (a i)))

/-- **Logarithmic chart of a formal group law**, at every prime and every ramification: for
`c ≠ 0` with `ScalingHyp p c` (for instance `c = p ^ 2`, `scalingHyp_sq`, or `c = π ^ (e + 1)`
when `p = π ^ e u`, `scalingHyp_uniformizer`) and `𝔪 ^ N ≤ (c)`, `LogChart Φ f c p N` holds. -/
theorem log_chart (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) (hc : ScalingHyp p c)
    {f : O →+* K} (hf : Function.Injective f) (hc0 : c ≠ 0) (Φ : FormalGroupLaw O ι) {N : ℕ}
    (hN : maximalIdeal O ^ N ≤ Ideal.span {c}) : LogChart Φ f c p N := by
  refine ⟨logB1 hp hpm hc hf hc0 Φ, logB1_bijective hp hpm hc hf hc0 Φ,
    fun z y hz ↦ logB1_apply hp hpm hc hf hc0 Φ z hz,
    fun z ↦ ⟨p ^ N, pow_pos hp.pos N, pow_nsmul_mem_B1 hpm Φ hN z (by omega)⟩,
    logPointsHom hp hpm hc hf hc0 Φ hN, fun z ↦ ?_,
    logPoints_eq_zero_iff hp hpm hc hf hc0 Φ hN,
    exists_logPoints_eq hp hpm hc hf hc0 Φ hN,
    exists_logPoints_eq_mul Φ f N⟩
  have hz : ∀ j, ((z : Φ.Points) j : O) = c * divC c ((z : Φ.Points) j) :=
    fun j ↦ (mul_divC (z.2 j)).symm
  change logPoints Φ f c p N z = _
  rw [logPoints_of_eq_mul hp hpm hc hf hc0 Φ hN hz, logB1_apply hp hpm hc hf hc0 Φ z hz]

/-- The logarithmic chart at the sharp radius of a ramified base: `𝔪 = (π)`, `p = π ^ e u` with
`u` a unit, `c = π ^ (e + 1)`, `N = e + 1` (for `p = 2`, the chart on `2π O^ι`). -/
theorem log_chart_uniformizer (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) {π u : O} {e : ℕ}
    (hπ : maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0) (hu : IsUnit u)
    (hpe : (p : O) = π ^ e * u) {f : O →+* K} (hf : Function.Injective f)
    (Φ : FormalGroupLaw O ι) : LogChart Φ f (π ^ (e + 1)) p (e + 1) :=
  log_chart hp hpm (scalingHyp_uniformizer hpm hu hpe) hf (pow_ne_zero _ hπ0) Φ
    (maximalIdeal_pow_le_span_pow hπ (e + 1))

/-- The logarithmic chart on `p ^ 2 O^ι` in a discrete valuation ring: `𝔪 = (π)`, `p = π ^ e u`
with `u` a unit, `c = p ^ 2`, `N = 2 e`. -/
theorem log_chart_sq (hp : p.Prime) (hpm : (p : O) ∈ maximalIdeal O) {π u : O} {e : ℕ}
    (hπ : maximalIdeal O = Ideal.span {π}) (hu : IsUnit u) (hpe : (p : O) = π ^ e * u)
    {f : O →+* K} (hf : Function.Injective f) (Φ : FormalGroupLaw O ι) :
    LogChart Φ f ((p : O) ^ 2) p (2 * e) :=
  log_chart hp hpm (scalingHyp_sq hpm) hf
    (pow_ne_zero _ (natCast_ne_zero_of_ringHom f hp.ne_zero)) Φ
    (maximalIdeal_pow_le_span_sq hπ hu hpe)

end Summary

end FurioLombardo.Vendor.Toolbox.FormalGroup
