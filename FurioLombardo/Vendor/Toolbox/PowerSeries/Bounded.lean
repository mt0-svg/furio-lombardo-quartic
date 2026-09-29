import Mathlib
import FurioLombardo.Vendor.Toolbox.Stoll.Mathlib.Chabauty.MvPSeries

/-!
# Power series with bounded denominators and their values at points of the maximal ideal

Let `O` be a subring of a field `K` and `π ∈ O`. Over `K`:

* `intSeries O σ`: the series with all coefficients in `O`, a subring of `MvPowerSeries σ K`,
  identified with `MvPowerSeries σ O` by `toO`;
* `bdd O σ π`: the series `G` with `π ^ N G ∈ intSeries O σ` for some `N`, a subring;
* `evB z : bdd O σ π →+* K`, the value at a point `z : σ → maximalIdeal O`, through Stoll's
  `MvPSeries.eval` of `π ^ N G` divided by `π ^ N` (independent of `N`, `evB_eq`);
* compatibility with rescaling (`evB_rescale`) and with substitution (`evB_subst`);
* polynomials over `bdd O σ π`: the injective inclusion `inclX` into polynomials over
  `MvPowerSeries σ K`, the lift `liftX` of a polynomial with coefficients in `bdd O σ π`, and the
  value map `evBX z = Polynomial.map (evB z)`.

This is the evaluation layer of item R7.

Origin: written for this formalization (the formal group of the Jacobian at the place above 2,
`FurioLombardo.Discharge.R7`).
-/

open MvPowerSeries IsLocalRing

namespace FurioLombardo.Vendor.Toolbox.Bounded

variable {K : Type*} [Field K] (O : Subring K) (σ : Type*)

/-- The series with all coefficients in `O`. -/
def intSeries : Subring (MvPowerSeries σ K) where
  carrier := {G | ∀ d, coeff d G ∈ O}
  mul_mem' := by
    classical
    intro a b ha hb d
    rw [coeff_mul]
    exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (ha _) (hb _)
  one_mem' := by
    classical
    intro d
    rw [coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' := by
    intro a b ha hb d
    rw [map_add]
    exact Subring.add_mem _ (ha d) (hb d)
  zero_mem' := by
    intro d
    rw [map_zero]
    exact Subring.zero_mem _
  neg_mem' := by
    intro a ha d
    rw [map_neg]
    exact Subring.neg_mem _ (ha d)

variable {O σ}

theorem mem_intSeries {G : MvPowerSeries σ K} : G ∈ intSeries O σ ↔ ∀ d, coeff d G ∈ O :=
  Iff.rfl

/-- The `O`-series of a series with coefficients in `O`. -/
def toO {G : MvPowerSeries σ K} (hG : G ∈ intSeries O σ) : MvPowerSeries σ O :=
  fun d => ⟨coeff d G, hG d⟩

theorem coeff_toO {G : MvPowerSeries σ K} (hG : G ∈ intSeries O σ) (d : σ →₀ ℕ) :
    ((coeff d (toO hG) : O) : K) = coeff d G :=
  rfl

theorem map_toO {G : MvPowerSeries σ K} (hG : G ∈ intSeries O σ) :
    MvPowerSeries.map O.subtype (toO hG) = G := by
  ext d
  rw [coeff_map, Subring.coe_subtype, coeff_toO]

theorem map_mem_intSeries (G : MvPowerSeries σ O) :
    MvPowerSeries.map O.subtype G ∈ intSeries O σ := by
  intro d
  rw [coeff_map]
  exact (coeff d G).2

theorem toO_map (G : MvPowerSeries σ O) :
    toO (map_mem_intSeries G) = G := by
  ext d
  rw [coeff_toO, coeff_map, Subring.coe_subtype]

/-- The coefficient map `MvPowerSeries σ O → MvPowerSeries σ K` is injective. -/
theorem map_subtype_injective :
    Function.Injective (MvPowerSeries.map (σ := σ) O.subtype) := by
  intro A B h
  ext d
  have h' := congrArg (coeff d) h
  rwa [coeff_map, coeff_map] at h'

theorem toO_eq_iff {G : MvPowerSeries σ K} (hG : G ∈ intSeries O σ) (F : MvPowerSeries σ O) :
    toO hG = F ↔ MvPowerSeries.map O.subtype F = G := by
  constructor
  · rintro rfl
    exact map_toO hG
  · intro h
    apply map_subtype_injective
    rw [map_toO, h]

/-- An admissible exponent stays admissible when it grows. -/
theorem pow_mul_mem_of_le {π : O} {N M : ℕ} (hNM : N ≤ M) {x : K} (hx : (π : K) ^ N * x ∈ O) :
    (π : K) ^ M * x ∈ O := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  rw [pow_add, mul_comm ((π : K) ^ N), mul_assoc]
  exact Subring.mul_mem _ (Subring.pow_mem _ π.2 _) hx

/-- Admissible exponents add under products. -/
theorem pow_add_mul_coeff_mul_mem {π : O} {N M : ℕ} {G H : MvPowerSeries σ K}
    (hG : ∀ d, (π : K) ^ N * coeff d G ∈ O) (hH : ∀ d, (π : K) ^ M * coeff d H ∈ O)
    (d : σ →₀ ℕ) : (π : K) ^ (N + M) * coeff d (G * H) ∈ O := by
  classical
  rw [coeff_mul, Finset.mul_sum]
  refine Subring.sum_mem _ fun p _ => ?_
  have e : (π : K) ^ (N + M) * (coeff p.1 G * coeff p.2 H) =
      ((π : K) ^ N * coeff p.1 G) * ((π : K) ^ M * coeff p.2 H) := by ring
  rw [e]
  exact Subring.mul_mem _ (hG _) (hH _)

theorem smul_mem_intSeries_iff {π : O} {N : ℕ} {G : MvPowerSeries σ K} :
    (π : K) ^ N • G ∈ intSeries O σ ↔ ∀ d, (π : K) ^ N * coeff d G ∈ O := by
  simp only [mem_intSeries, coeff_smul]

variable (O σ)

/-- The series with bounded denominators: `π ^ N G` has coefficients in `O` for some `N`. -/
def bdd (π : O) : Subring (MvPowerSeries σ K) where
  carrier := {G | ∃ N : ℕ, ∀ d, (π : K) ^ N * coeff d G ∈ O}
  mul_mem' := by
    rintro a b ⟨N, hN⟩ ⟨M, hM⟩
    exact ⟨N + M, pow_add_mul_coeff_mul_mem hN hM⟩
  one_mem' := ⟨0, by
    classical
    intro d
    rw [pow_zero, one_mul, coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _⟩
  add_mem' := by
    rintro a b ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨N + M, fun d => ?_⟩
    rw [map_add, mul_add]
    exact Subring.add_mem _ (pow_mul_mem_of_le (Nat.le_add_right N M) (hN d))
      (pow_mul_mem_of_le (Nat.le_add_left M N) (hM d))
  zero_mem' := ⟨0, fun d => by rw [map_zero, mul_zero]; exact Subring.zero_mem _⟩
  neg_mem' := by
    rintro a ⟨N, hN⟩
    exact ⟨N, fun d => by rw [map_neg, mul_neg]; exact Subring.neg_mem _ (hN d)⟩

variable {O σ}

theorem mem_bdd {π : O} {G : MvPowerSeries σ K} :
    G ∈ bdd O σ π ↔ ∃ N : ℕ, ∀ d, (π : K) ^ N * coeff d G ∈ O :=
  Iff.rfl

theorem intSeries_le_bdd (π : O) : intSeries O σ ≤ bdd O σ π :=
  fun G hG => ⟨0, fun d => by rw [pow_zero, one_mul]; exact hG d⟩

theorem mem_bdd_iff_smul {π : O} {G : MvPowerSeries σ K} :
    G ∈ bdd O σ π ↔ ∃ N : ℕ, (π : K) ^ N • G ∈ intSeries O σ := by
  simp only [mem_bdd, smul_mem_intSeries_iff]

theorem map_mem_bdd (π : O) (G : MvPowerSeries σ O) :
    MvPowerSeries.map O.subtype G ∈ bdd O σ π :=
  intSeries_le_bdd π (map_mem_intSeries G)

set_option linter.unusedVariables false in
theorem C_mem_bdd {π : O} (hπ : (π : K) ≠ 0) (hbd : ∀ x : K, ∃ k : ℕ, (π : K) ^ k * x ∈ O)
    (a : K) : C a ∈ bdd O σ π := by
  classical
  obtain ⟨k, hk⟩ := hbd a
  refine ⟨k, fun d => ?_⟩
  rw [coeff_C]
  split_ifs
  · exact hk
  · rw [mul_zero]
    exact Subring.zero_mem _

/-- The product `∏ a ^ n i` of a monomial rescaling lies in `O`. -/
theorem prod_pow_mem (a : O) (n : σ →₀ ℕ) : (n.prod fun _ m => (a : K) ^ m) ∈ O := by
  rw [Finsupp.prod]
  exact Subring.prod_mem _ fun i _ => Subring.pow_mem _ a.2 _

/-- Rescaling by an element of `O` keeps bounded denominators. -/
theorem rescale_mem_bdd {π : O} (a : O) {G : MvPowerSeries σ K} (hG : G ∈ bdd O σ π) :
    rescale (fun _ => (a : K)) G ∈ bdd O σ π := by
  obtain ⟨N, hN⟩ := hG
  refine ⟨N, fun d => ?_⟩
  rw [coeff_rescale, mul_left_comm]
  exact Subring.mul_mem _ (prod_pow_mem a d) (hN d)

/-! ### The `O`-series `π ^ N G` -/

/-- The `O`-series `π ^ N G`, for an admissible exponent `N`. -/
def scaled (π : O) (N : ℕ) (G : MvPowerSeries σ K) (h : ∀ d, (π : K) ^ N * coeff d G ∈ O) :
    MvPowerSeries σ O :=
  fun d => ⟨(π : K) ^ N * coeff d G, h d⟩

theorem coe_coeff_scaled (π : O) (N : ℕ) (G : MvPowerSeries σ K)
    (h : ∀ d, (π : K) ^ N * coeff d G ∈ O) (d : σ →₀ ℕ) :
    ((coeff d (scaled π N G h) : O) : K) = (π : K) ^ N * coeff d G :=
  rfl

theorem map_scaled (π : O) (N : ℕ) (G : MvPowerSeries σ K)
    (h : ∀ d, (π : K) ^ N * coeff d G ∈ O) :
    MvPowerSeries.map O.subtype (scaled π N G h) = (π : K) ^ N • G := by
  ext d
  rw [coeff_map, Subring.coe_subtype, coe_coeff_scaled, coeff_smul]

theorem scaled_eq_iff {π : O} {N : ℕ} {G : MvPowerSeries σ K}
    (h : ∀ d, (π : K) ^ N * coeff d G ∈ O) (F : MvPowerSeries σ O) :
    scaled π N G h = F ↔ MvPowerSeries.map O.subtype F = (π : K) ^ N • G := by
  constructor
  · rintro rfl
    exact map_scaled π N G h
  · intro hF
    apply map_subtype_injective
    rw [map_scaled, hF]

theorem scaled_zero_eq_toO {π : O} {G : MvPowerSeries σ K} (hG : G ∈ intSeries O σ)
    (h : ∀ d, (π : K) ^ 0 * coeff d G ∈ O) : scaled π 0 G h = toO hG := by
  rw [scaled_eq_iff, map_toO, pow_zero, one_smul]

theorem scaled_add_pow {π : O} {N k : ℕ} {G : MvPowerSeries σ K}
    (hN : ∀ d, (π : K) ^ N * coeff d G ∈ O) (hNk : ∀ d, (π : K) ^ (N + k) * coeff d G ∈ O) :
    scaled π (N + k) G hNk = C (π ^ k) * scaled π N G hN := by
  rw [scaled_eq_iff, map_mul, map_C, map_scaled, Subring.coe_subtype, Subring.coe_pow,
    ← smul_eq_C_mul, smul_smul, ← pow_add, add_comm k N]

theorem scaled_add {π : O} {N : ℕ} {G H : MvPowerSeries σ K}
    (hG : ∀ d, (π : K) ^ N * coeff d G ∈ O) (hH : ∀ d, (π : K) ^ N * coeff d H ∈ O)
    (hGH : ∀ d, (π : K) ^ N * coeff d (G + H) ∈ O) :
    scaled π N (G + H) hGH = scaled π N G hG + scaled π N H hH := by
  rw [scaled_eq_iff, map_add, map_scaled, map_scaled, smul_add]

theorem scaled_mul {π : O} {N M : ℕ} {G H : MvPowerSeries σ K}
    (hG : ∀ d, (π : K) ^ N * coeff d G ∈ O) (hH : ∀ d, (π : K) ^ M * coeff d H ∈ O)
    (hGH : ∀ d, (π : K) ^ (N + M) * coeff d (G * H) ∈ O) :
    scaled π (N + M) (G * H) hGH = scaled π N G hG * scaled π M H hH := by
  rw [scaled_eq_iff, map_mul, map_scaled, map_scaled, smul_mul_smul_comm, ← pow_add]

theorem scaled_rescale {π : O} {N : ℕ} (a : O) {G : MvPowerSeries σ K}
    (hG : ∀ d, (π : K) ^ N * coeff d G ∈ O)
    (h : ∀ d, (π : K) ^ N * coeff d (rescale (fun _ => (a : K)) G) ∈ O) :
    scaled π N (rescale (fun _ => (a : K)) G) h = rescale (fun _ => a) (scaled π N G hG) := by
  ext d
  rw [coe_coeff_scaled, coeff_rescale, coeff_rescale, Subring.coe_mul, coe_coeff_scaled,
    mul_left_comm]
  congr 1
  rw [Finsupp.prod, Finsupp.prod]
  push_cast
  rfl

/-! ### Substitution of integral series without constant term -/

section Subst

variable {τ : Type*}

theorem constantCoeff_toO {a : MvPowerSeries σ K} (ha : a ∈ intSeries O σ)
    (ha0 : constantCoeff a = 0) : constantCoeff (toO ha) = 0 := by
  apply Subtype.ext
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_toO, coeff_zero_eq_constantCoeff_apply, ha0,
    ZeroMemClass.coe_zero]

theorem hasSubst_toO [Finite τ] {a : τ → MvPowerSeries σ K} (ha : ∀ i, a i ∈ intSeries O σ)
    (ha0 : ∀ i, constantCoeff (a i) = 0) : HasSubst fun i => toO (ha i) :=
  hasSubst_of_constantCoeff_zero fun i => constantCoeff_toO (ha i) (ha0 i)

/-- Substitution commutes with the coefficient map `O → K`. -/
theorem map_subst_toO [Finite τ] {a : τ → MvPowerSeries σ K} (ha : ∀ i, a i ∈ intSeries O σ)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (F : MvPowerSeries τ O) :
    MvPowerSeries.map O.subtype (MvPowerSeries.subst (fun i => toO (ha i)) F) =
      MvPowerSeries.subst a (MvPowerSeries.map O.subtype F) := by
  rw [map_subst (hasSubst_toO ha ha0)]
  simp only [map_toO]

theorem pow_mul_coeff_subst_mem [Finite τ] {π : O} {N : ℕ} {a : τ → MvPowerSeries σ K}
    (ha : ∀ i, a i ∈ intSeries O σ) (ha0 : ∀ i, constantCoeff (a i) = 0)
    {G : MvPowerSeries τ K} (hN : ∀ d, (π : K) ^ N * coeff d G ∈ O) (d : σ →₀ ℕ) :
    (π : K) ^ N * coeff d (MvPowerSeries.subst a G) ∈ O := by
  have key : MvPowerSeries.map O.subtype
      (MvPowerSeries.subst (fun i => toO (ha i)) (scaled π N G hN)) =
        (π : K) ^ N • MvPowerSeries.subst a G := by
    rw [map_subst_toO ha ha0, map_scaled, subst_smul (hasSubst_of_constantCoeff_zero ha0)]
  have h := map_mem_intSeries (MvPowerSeries.subst (fun i => toO (ha i)) (scaled π N G hN)) d
  rwa [key, coeff_smul] at h

theorem scaled_subst [Finite τ] {π : O} {N : ℕ} {a : τ → MvPowerSeries σ K}
    (ha : ∀ i, a i ∈ intSeries O σ) (ha0 : ∀ i, constantCoeff (a i) = 0)
    {G : MvPowerSeries τ K} (hN : ∀ d, (π : K) ^ N * coeff d G ∈ O)
    (h : ∀ d, (π : K) ^ N * coeff d (MvPowerSeries.subst a G) ∈ O) :
    scaled π N (MvPowerSeries.subst a G) h =
      MvPowerSeries.subst (fun i => toO (ha i)) (scaled π N G hN) := by
  rw [scaled_eq_iff, map_subst_toO ha ha0, map_scaled,
    subst_smul (hasSubst_of_constantCoeff_zero ha0)]

/-- Substitution of `O`-series without constant term keeps bounded denominators. -/
theorem subst_mem_bdd [Finite τ] {π : O} {a : τ → MvPowerSeries σ K}
    (ha : ∀ i, a i ∈ intSeries O σ) (ha0 : ∀ i, constantCoeff (a i) = 0)
    {G : MvPowerSeries τ K} (hG : G ∈ bdd O τ π) :
    MvPowerSeries.subst a G ∈ bdd O σ π := by
  obtain ⟨N, hN⟩ := hG
  exact ⟨N, pow_mul_coeff_subst_mem ha ha0 hN⟩

end Subst

theorem pow_zero_mul_coeff_mem {π : O} {G : MvPowerSeries σ K} (hG : G ∈ intSeries O σ) :
    ∀ d, (π : K) ^ 0 * coeff d G ∈ O := fun d => by
  rw [pow_zero, one_mul]
  exact hG d

theorem X_mem_intSeries (i : σ) : (X i : MvPowerSeries σ K) ∈ intSeries O σ := by
  classical
  intro d
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

section Eval

variable [IsLocalRing O] [UniformSpace O]

/-- The value at `z` of a series with coefficients in `O`. -/
noncomputable def evO (z : σ → maximalIdeal O) (G : MvPowerSeries σ O) : O :=
  FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.eval (fun i => (z i : O)) G

theorem evO_C (z : σ → maximalIdeal O) (c : O) : evO z (C c) = c :=
  FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.eval_C c _

theorem evO_X (z : σ → maximalIdeal O) (i : σ) : evO z (X i) = z i :=
  FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.eval_X _ i

/-- The value of a series with bounded denominators, computed with the admissible exponent
`N`. -/
noncomputable def evN (π : O) (z : σ → maximalIdeal O) (N : ℕ) (G : MvPowerSeries σ K)
    (h : ∀ d, (π : K) ^ N * coeff d G ∈ O) : K :=
  ((π : K) ^ N)⁻¹ * (evO z (scaled π N G h) : K)

theorem evN_zero_eq {π : O} (z : σ → maximalIdeal O) {G : MvPowerSeries σ K}
    (hG : G ∈ intSeries O σ) (h0 : ∀ d, (π : K) ^ 0 * coeff d G ∈ O) :
    evN π z 0 G h0 = (evO z (toO hG) : K) := by
  unfold evN
  rw [scaled_zero_eq_toO hG h0, pow_zero, inv_one, one_mul]

variable [Fact (IsAdic (maximalIdeal O))] [Finite σ]

theorem hasEval_coe (z : σ → maximalIdeal O) : HasEval fun i => (z i : O) :=
  FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.hasEval_of_mem fun i => (z i).2

variable [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

/-- Evaluation at `z` over `O`, as a ring homomorphism. -/
noncomputable def evOHom (z : σ → maximalIdeal O) : MvPowerSeries σ O →+* O :=
  FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.evalRingHom (hasEval_coe z)

theorem evOHom_apply (z : σ → maximalIdeal O) (G : MvPowerSeries σ O) :
    evOHom z G = evO z G :=
  FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.evalRingHom_apply _ G

theorem evO_add (z : σ → maximalIdeal O) (G H : MvPowerSeries σ O) :
    evO z (G + H) = evO z G + evO z H := by
  simp only [← evOHom_apply, map_add]

theorem evO_mul (z : σ → maximalIdeal O) (G H : MvPowerSeries σ O) :
    evO z (G * H) = evO z G * evO z H := by
  simp only [← evOHom_apply, map_mul]

theorem evO_one (z : σ → maximalIdeal O) : evO z (1 : MvPowerSeries σ O) = 1 := by
  simp only [← evOHom_apply, map_one]

theorem evO_zero (z : σ → maximalIdeal O) : evO z (0 : MvPowerSeries σ O) = 0 := by
  simp only [← evOHom_apply, map_zero]

theorem evO_C_mul (z : σ → maximalIdeal O) (c : O) (G : MvPowerSeries σ O) :
    evO z (C c * G) = c * evO z G := by
  rw [evO_mul, evO_C]

/-- Rescaling by `a ∈ O` is evaluation at `a z`, over `O`. -/
theorem evO_rescale (z : σ → maximalIdeal O) (a : O) (F : MvPowerSeries σ O) :
    evO z (rescale (fun _ => a) F) =
      evO (fun i => ⟨a * (z i : O), Ideal.mul_mem_left _ _ (z i).2⟩) F := by
  unfold evO
  rw [rescale_eq_subst, FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.eval_subst (hasEval_coe z)
    (HasSubst.smul_X _)]
  congr 1
  funext i
  rw [Pi.smul_apply', smul_eq_C_mul,
    FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.eval_mul (hasEval_coe z),
    FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.eval_C,
    FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.eval_X]

theorem evN_add_pow {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) {N k : ℕ}
    {G : MvPowerSeries σ K} (hN : ∀ d, (π : K) ^ N * coeff d G ∈ O)
    (hNk : ∀ d, (π : K) ^ (N + k) * coeff d G ∈ O) :
    evN π z (N + k) G hNk = evN π z N G hN := by
  unfold evN
  rw [scaled_add_pow hN hNk, evO_C_mul, Subring.coe_mul, Subring.coe_pow, pow_add, mul_inv,
    mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero k hπ)]

/-- The value does not depend on the admissible exponent. -/
theorem evN_indep {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) {N M : ℕ}
    {G : MvPowerSeries σ K} (hN : ∀ d, (π : K) ^ N * coeff d G ∈ O)
    (hM : ∀ d, (π : K) ^ M * coeff d G ∈ O) :
    evN π z N G hN = evN π z M G hM := by
  rcases le_total N M with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (evN_add_pow hπ z hN hM).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact evN_add_pow hπ z hM hN

theorem evN_mul {π : O} (z : σ → maximalIdeal O) {N M : ℕ} {G H : MvPowerSeries σ K}
    (hG : ∀ d, (π : K) ^ N * coeff d G ∈ O) (hH : ∀ d, (π : K) ^ M * coeff d H ∈ O)
    (hGH : ∀ d, (π : K) ^ (N + M) * coeff d (G * H) ∈ O) :
    evN π z (N + M) (G * H) hGH = evN π z N G hG * evN π z M H hH := by
  unfold evN
  rw [scaled_mul hG hH hGH, evO_mul, Subring.coe_mul, pow_add, mul_inv]
  ring

theorem evN_add {π : O} (z : σ → maximalIdeal O) {N : ℕ} {G H : MvPowerSeries σ K}
    (hG : ∀ d, (π : K) ^ N * coeff d G ∈ O) (hH : ∀ d, (π : K) ^ N * coeff d H ∈ O)
    (hGH : ∀ d, (π : K) ^ N * coeff d (G + H) ∈ O) :
    evN π z N (G + H) hGH = evN π z N G hG + evN π z N H hH := by
  unfold evN
  rw [scaled_add hG hH hGH, evO_add, Subring.coe_add, mul_add]

/-- The value at `z` of a series with bounded denominators, as a function. -/
noncomputable def evBFun {π : O} (z : σ → maximalIdeal O) (G : bdd O σ π) : K :=
  evN π z (Classical.choose G.2) G.1 (Classical.choose_spec G.2)

theorem evBFun_eq {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) (G : bdd O σ π) (N : ℕ)
    (h : ∀ d, (π : K) ^ N * coeff d G.1 ∈ O) : evBFun z G = evN π z N G.1 h :=
  evN_indep hπ z _ h

/-- The value at `z` of a series with bounded denominators. -/
noncomputable def evB {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) :
    bdd O σ π →+* K where
  toFun := evBFun z
  map_one' := by
    have h1 : (1 : MvPowerSeries σ K) ∈ intSeries O σ := (intSeries O σ).one_mem
    rw [evBFun_eq hπ z 1 0 (pow_zero_mul_coeff_mem h1)]
    refine (evN_zero_eq z h1 _).trans ?_
    rw [(toO_eq_iff h1 1).mpr (map_one _), evO_one, Subring.coe_one]
  map_mul' G H := by
    obtain ⟨N, hN⟩ := G.2
    obtain ⟨M, hM⟩ := H.2
    have hGH := pow_add_mul_coeff_mul_mem hN hM
    rw [evBFun_eq hπ z (G * H) (N + M) hGH, evBFun_eq hπ z G N hN, evBFun_eq hπ z H M hM]
    exact evN_mul z hN hM hGH
  map_zero' := by
    have h1 : (0 : MvPowerSeries σ K) ∈ intSeries O σ := (intSeries O σ).zero_mem
    rw [evBFun_eq hπ z 0 0 (pow_zero_mul_coeff_mem h1)]
    refine (evN_zero_eq z h1 _).trans ?_
    rw [(toO_eq_iff h1 0).mpr (map_zero _), evO_zero, Subring.coe_zero]
  map_add' G H := by
    obtain ⟨N, hN⟩ := G.2
    obtain ⟨M, hM⟩ := H.2
    have hG' : ∀ d, (π : K) ^ (N + M) * coeff d G.1 ∈ O := fun d =>
      pow_mul_mem_of_le (Nat.le_add_right N M) (hN d)
    have hH' : ∀ d, (π : K) ^ (N + M) * coeff d H.1 ∈ O := fun d =>
      pow_mul_mem_of_le (Nat.le_add_left M N) (hM d)
    have hGH : ∀ d, (π : K) ^ (N + M) * coeff d (G.1 + H.1) ∈ O := fun d => by
      rw [map_add, mul_add]; exact Subring.add_mem _ (hG' d) (hH' d)
    rw [evBFun_eq hπ z (G + H) (N + M) hGH, evBFun_eq hπ z G (N + M) hG',
      evBFun_eq hπ z H (N + M) hH']
    exact evN_add z hG' hH' hGH

/-- `evB` computed with any admissible exponent. -/
theorem evB_eq {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) (G : bdd O σ π) (N : ℕ)
    (h : ∀ d, (π : K) ^ N * coeff d G.1 ∈ O) :
    evB hπ z G = ((π : K) ^ N)⁻¹ * (evO z (scaled π N G.1 h) : K) :=
  evBFun_eq hπ z G N h

/-- `evB` of `G` through the integral series `π ^ N • G`. -/
theorem evB_eq_toO {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) (G : bdd O σ π) (N : ℕ)
    (h : (π : K) ^ N • G.1 ∈ intSeries O σ) :
    evB hπ z G = ((π : K) ^ N)⁻¹ * (evO z (toO h) : K) := by
  rw [evB_eq hπ z G N (smul_mem_intSeries_iff.mp h)]
  congr 3

theorem evB_of_mem_intSeries {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O)
    {G : MvPowerSeries σ K} (hG : G ∈ intSeries O σ) :
    evB hπ z ⟨G, intSeries_le_bdd π hG⟩ = (evO z (toO hG) : K) := by
  have h0 : ∀ d, (π : K) ^ 0 * coeff d G ∈ O := fun d => by rw [pow_zero, one_mul]; exact hG d
  rw [evB_eq hπ z _ 0 h0, scaled_zero_eq_toO hG h0, pow_zero, inv_one, one_mul]

/-- `evB` of an `O`-series is its value over `O`. -/
theorem evB_map {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) (F : MvPowerSeries σ O) :
    evB hπ z ⟨MvPowerSeries.map O.subtype F, map_mem_bdd π F⟩ = (evO z F : K) := by
  rw [evB_of_mem_intSeries hπ z (map_mem_intSeries F), toO_map]

theorem evB_C {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) (a : K)
    (ha : C a ∈ bdd O σ π) : evB hπ z ⟨C a, ha⟩ = a := by
  obtain ⟨N, hN⟩ := ha
  have hc : (π : K) ^ N * a ∈ O := by
    have h := hN 0
    rwa [coeff_zero_C] at h
  rw [evB_eq hπ z _ N hN, (scaled_eq_iff hN (C ⟨_, hc⟩)).mpr (by
      rw [map_C, Subring.coe_subtype, smul_eq_C_mul, map_mul]), evO_C,
    inv_mul_cancel_left₀ (pow_ne_zero N hπ)]

theorem evB_X {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) (i : σ)
    (hX : (X i : MvPowerSeries σ K) ∈ bdd O σ π) : evB hπ z ⟨X i, hX⟩ = (z i : K) := by
  rw [evB_of_mem_intSeries hπ z (X_mem_intSeries i),
    (toO_eq_iff (X_mem_intSeries i) (X i)).mpr (map_X _ i), evO_X]

/-- Rescaling by `a ∈ O` is evaluation at `a z`. -/
theorem evB_rescale {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) (a : O)
    {G : MvPowerSeries σ K} (hG : G ∈ bdd O σ π) :
    evB hπ z ⟨rescale (fun _ => (a : K)) G, rescale_mem_bdd a hG⟩ =
      evB hπ (fun i => ⟨a * z i, Ideal.mul_mem_left _ _ (z i).2⟩) ⟨G, hG⟩ := by
  obtain ⟨N, hN⟩ := hG
  have h : ∀ d, (π : K) ^ N * coeff d (rescale (fun _ => (a : K)) G) ∈ O := fun d => by
    rw [coeff_rescale, mul_left_comm]
    exact Subring.mul_mem _ (prod_pow_mem a d) (hN d)
  rw [evB_eq hπ z _ N h, evB_eq hπ _ _ N hN]
  dsimp only
  rw [scaled_rescale a hN h, evO_rescale]

variable {τ : Type*} [Finite τ]

/-- The value of an `O`-series with constant coefficient in the maximal ideal is in the maximal
ideal. -/
theorem evO_mem_maximalIdeal (z : σ → maximalIdeal O) (G : MvPowerSeries σ O)
    (hG : constantCoeff G ∈ maximalIdeal O) : evO z G ∈ maximalIdeal O :=
  FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.eval_mem_maximalIdeal (hasEval_coe z)
    (fun i => (z i).2) G hG

/-- Evaluation of a substitution is evaluation at the evaluated family. -/
theorem evB_subst {π : O} (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O)
    {a : τ → MvPowerSeries σ K} (ha : ∀ i, a i ∈ intSeries O σ)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {G : MvPowerSeries τ K} (hG : G ∈ bdd O τ π) :
    evB hπ z ⟨MvPowerSeries.subst a G, subst_mem_bdd ha ha0 hG⟩ =
      evB hπ (fun i => ⟨evO z (toO (ha i)), evO_mem_maximalIdeal z _ (by
        have h := ha0 i
        rw [← map_toO (ha i), ← coeff_zero_eq_constantCoeff_apply, coeff_map] at h
        rw [← coeff_zero_eq_constantCoeff_apply]
        rw [Subring.coe_subtype] at h
        exact (show coeff 0 (toO (ha i)) = 0 from Subtype.ext h) ▸ Ideal.zero_mem _)⟩)
        ⟨G, hG⟩ := by
  obtain ⟨N, hN⟩ := hG
  have h := pow_mul_coeff_subst_mem ha ha0 hN
  rw [evB_eq hπ z _ N h, evB_eq hπ _ _ N hN]
  dsimp only
  rw [scaled_subst ha ha0 hN h]
  unfold evO
  rw [FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.MvPSeries.eval_subst (hasEval_coe z) (hasSubst_toO ha ha0)]

end Eval

/-! ### Polynomials over `bdd O σ π` -/

section Poly

variable {π : O}

/-- The inclusion of polynomials over `bdd O σ π` into polynomials over `MvPowerSeries σ K`. -/
noncomputable def inclX : Polynomial (bdd O σ π) →+* Polynomial (MvPowerSeries σ K) :=
  Polynomial.mapRingHom (bdd O σ π).subtype

theorem inclX_apply (P : Polynomial (bdd O σ π)) : inclX P = P.map (bdd O σ π).subtype :=
  rfl

theorem inclX_injective : Function.Injective (inclX (O := O) (σ := σ) (π := π)) :=
  Polynomial.map_injective _ Subtype.val_injective

theorem coeff_inclX (P : Polynomial (bdd O σ π)) (n : ℕ) :
    (inclX P).coeff n = (P.coeff n : MvPowerSeries σ K) := by
  rw [inclX_apply, Polynomial.coeff_map, Subring.coe_subtype]

/-- A polynomial with coefficients in `bdd O σ π`, as a polynomial over `bdd O σ π`. -/
noncomputable def liftX (P : Polynomial (MvPowerSeries σ K)) (hP : ∀ n, P.coeff n ∈ bdd O σ π) :
    Polynomial (bdd O σ π) :=
  P.toSubring (bdd O σ π) fun _ hc => by
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
    exact hP n

theorem inclX_liftX (P : Polynomial (MvPowerSeries σ K)) (hP : ∀ n, P.coeff n ∈ bdd O σ π) :
    inclX (liftX P hP) = P :=
  Polynomial.map_toSubring _ _ _

theorem liftX_inclX (P : Polynomial (bdd O σ π)) :
    liftX (inclX P) (fun n => by rw [coeff_inclX]; exact (P.coeff n).2) = P :=
  inclX_injective (inclX_liftX _ _)

theorem coeff_liftX (P : Polynomial (MvPowerSeries σ K)) (hP : ∀ n, P.coeff n ∈ bdd O σ π)
    (n : ℕ) : ((liftX P hP).coeff n : MvPowerSeries σ K) = P.coeff n := by
  rw [← coeff_inclX, inclX_liftX]

theorem coeff_liftX_eq (P : Polynomial (MvPowerSeries σ K)) (hP : ∀ n, P.coeff n ∈ bdd O σ π)
    (n : ℕ) : (liftX P hP).coeff n = ⟨P.coeff n, hP n⟩ :=
  Subtype.ext (coeff_liftX P hP n)

/-- Polynomials over `bdd O σ π` are determined by their image over `MvPowerSeries σ K`. -/
theorem eq_iff_inclX_eq {P Q : Polynomial (bdd O σ π)} : P = Q ↔ inclX P = inclX Q :=
  inclX_injective.eq_iff.symm

theorem liftX_eq_iff {P : Polynomial (MvPowerSeries σ K)} (hP : ∀ n, P.coeff n ∈ bdd O σ π)
    (Q : Polynomial (bdd O σ π)) : liftX P hP = Q ↔ P = inclX Q := by
  rw [eq_iff_inclX_eq, inclX_liftX]

theorem liftX_congr {P Q : Polynomial (MvPowerSeries σ K)} (hP : ∀ n, P.coeff n ∈ bdd O σ π)
    (hQ : ∀ n, Q.coeff n ∈ bdd O σ π) (h : P = Q) : liftX P hP = liftX Q hQ := by
  subst h
  rfl

theorem liftX_add {P Q : Polynomial (MvPowerSeries σ K)} (hP : ∀ n, P.coeff n ∈ bdd O σ π)
    (hQ : ∀ n, Q.coeff n ∈ bdd O σ π) (hPQ : ∀ n, (P + Q).coeff n ∈ bdd O σ π) :
    liftX (P + Q) hPQ = liftX P hP + liftX Q hQ := by
  rw [liftX_eq_iff, map_add, inclX_liftX, inclX_liftX]

theorem liftX_mul {P Q : Polynomial (MvPowerSeries σ K)} (hP : ∀ n, P.coeff n ∈ bdd O σ π)
    (hQ : ∀ n, Q.coeff n ∈ bdd O σ π) (hPQ : ∀ n, (P * Q).coeff n ∈ bdd O σ π) :
    liftX (P * Q) hPQ = liftX P hP * liftX Q hQ := by
  rw [liftX_eq_iff, map_mul, inclX_liftX, inclX_liftX]

theorem liftX_sub {P Q : Polynomial (MvPowerSeries σ K)} (hP : ∀ n, P.coeff n ∈ bdd O σ π)
    (hQ : ∀ n, Q.coeff n ∈ bdd O σ π) (hPQ : ∀ n, (P - Q).coeff n ∈ bdd O σ π) :
    liftX (P - Q) hPQ = liftX P hP - liftX Q hQ := by
  rw [liftX_eq_iff, map_sub, inclX_liftX, inclX_liftX]

theorem liftX_C {c : MvPowerSeries σ K} (hc : c ∈ bdd O σ π)
    (h : ∀ n, (Polynomial.C c).coeff n ∈ bdd O σ π) :
    liftX (Polynomial.C c) h = Polynomial.C ⟨c, hc⟩ := by
  rw [liftX_eq_iff, inclX_apply, Polynomial.map_C, Subring.coe_subtype]

theorem liftX_X (h : ∀ n, (Polynomial.X : Polynomial (MvPowerSeries σ K)).coeff n ∈ bdd O σ π) :
    liftX Polynomial.X h = Polynomial.X := by
  rw [liftX_eq_iff, inclX_apply, Polynomial.map_X]

/-- Coefficients of polynomials with coefficients in `bdd O σ π` stay there under ring
operations. -/
theorem coeff_add_mem_bdd {P Q : Polynomial (MvPowerSeries σ K)}
    (hP : ∀ n, P.coeff n ∈ bdd O σ π) (hQ : ∀ n, Q.coeff n ∈ bdd O σ π) :
    ∀ n, (P + Q).coeff n ∈ bdd O σ π := by
  intro n
  rw [Polynomial.coeff_add]
  exact Subring.add_mem _ (hP n) (hQ n)

theorem coeff_mul_mem_bdd {P Q : Polynomial (MvPowerSeries σ K)}
    (hP : ∀ n, P.coeff n ∈ bdd O σ π) (hQ : ∀ n, Q.coeff n ∈ bdd O σ π) :
    ∀ n, (P * Q).coeff n ∈ bdd O σ π := by
  intro n
  rw [Polynomial.coeff_mul]
  exact Subring.sum_mem _ fun p _ => Subring.mul_mem _ (hP p.1) (hQ p.2)

theorem coeff_sub_mem_bdd {P Q : Polynomial (MvPowerSeries σ K)}
    (hP : ∀ n, P.coeff n ∈ bdd O σ π) (hQ : ∀ n, Q.coeff n ∈ bdd O σ π) :
    ∀ n, (P - Q).coeff n ∈ bdd O σ π := by
  intro n
  rw [Polynomial.coeff_sub]
  exact Subring.sub_mem _ (hP n) (hQ n)

variable [IsLocalRing O] [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O] [Finite σ]

/-- The value at `z` of the coefficients of a polynomial over `bdd O σ π`. -/
noncomputable def evBX (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) :
    Polynomial (bdd O σ π) →+* Polynomial K :=
  Polynomial.mapRingHom (evB hπ z)

theorem evBX_apply (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) (P : Polynomial (bdd O σ π)) :
    evBX hπ z P = P.map (evB hπ z) :=
  rfl

theorem coeff_evBX (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O) (P : Polynomial (bdd O σ π))
    (n : ℕ) : (evBX hπ z P).coeff n = evB hπ z (P.coeff n) := by
  rw [evBX_apply, Polynomial.coeff_map]

/-- An identity between polynomials over `MvPowerSeries σ K` with coefficients in `bdd O σ π`
gives the identity of their values at `z`. -/
theorem evBX_eq_of_inclX_eq (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O)
    {P Q : Polynomial (bdd O σ π)} (h : inclX P = inclX Q) : evBX hπ z P = evBX hπ z Q := by
  rw [inclX_injective h]

theorem coeff_evBX_liftX (hπ : (π : K) ≠ 0) (z : σ → maximalIdeal O)
    (P : Polynomial (MvPowerSeries σ K)) (hP : ∀ n, P.coeff n ∈ bdd O σ π) (n : ℕ) :
    (evBX hπ z (liftX P hP)).coeff n = evB hπ z ⟨P.coeff n, hP n⟩ := by
  rw [coeff_evBX, coeff_liftX_eq]

end Poly

end FurioLombardo.Vendor.Toolbox.Bounded
