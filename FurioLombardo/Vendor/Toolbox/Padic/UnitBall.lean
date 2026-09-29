import Mathlib
import FurioLombardo.Vendor.Toolbox.FormalGroup.ScaledPoints

/-!
# The unit ball of a complete ultrametric field with a uniformizer

For a nontrivially normed field `K` with `IsUltrametricDist K`, `unitBall K` is the subring of
elements of norm at most `1`. With the subspace uniform structure it is

* a local domain (units: norm `1`, maximal ideal: norm `< 1`), for any such `K`;
* complete when `K` is complete;
* adic for its maximal ideal, and a discrete valuation ring, when `K` has a *uniformizer*
  (`IsUniformizer π`: `0 < ‖π‖ < 1` and every norm `< 1` is at most `‖π‖`); the class
  `HasUniformizer K` records that one exists and makes the instance
  `Fact (IsAdic (maximalIdeal (unitBall K)))` available.

These are the instance arguments of `FurioLombardo.Vendor.Toolbox.FormalGroup.log_chart_uniformizer`; the tests at the
end of the file apply it over `unitBall K`.

For an explicit uniformizer `hπ : IsUniformizer π`: `hπ.toBall` is `π` as an element of the ball,
`hπ.maximalIdeal_eq : maximalIdeal = (π)`, `hπ.mem_span_pow_iff : x ∈ (π ^ n) ↔ ‖x‖ ≤ ‖π‖ ^ n`,
`hπ.exists_norm_eq_pow` (every nonzero element of the ball has norm a power of `‖π‖`), and
`exists_pow_mul_mem` (bounded denominators: `π ^ k x` is in the ball for some `k`).

Mathlib's `𝒪[K]` (`Valued.integer`) needs the scoped instance `NormedField.toValued`; the plain
subring used here needs no scoped instance.

Origin: written for this formalization (the formal group of the Jacobian at the place above 2,
`FurioLombardo.Discharge.R7`).
-/

namespace FurioLombardo.Vendor.Toolbox.UnitBall

open IsLocalRing Topology

/-! ### Uniformizers (norm statements) -/

section Norm

variable {K : Type*} [NontriviallyNormedField K]

/-- `π` is a uniformizer of `K`: `0 < ‖π‖ < 1` and every norm `< 1` is at most `‖π‖` (the norm
is discrete). -/
structure IsUniformizer (π : K) : Prop where
  norm_pos : 0 < ‖π‖
  norm_lt_one : ‖π‖ < 1
  norm_le_of_lt_one : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖

variable (K) in
/-- `K` has a uniformizer. -/
class HasUniformizer : Prop where
  exists_isUniformizer : ∃ π : K, IsUniformizer π

namespace IsUniformizer

variable {π : K} (hπ : IsUniformizer π)
include hπ

theorem ne_zero : π ≠ 0 := norm_pos_iff.mp hπ.norm_pos

theorem hasUniformizer : HasUniformizer K := ⟨⟨π, hπ⟩⟩

/-- Discreteness at every level: a norm `< ‖π‖ ^ n` is at most `‖π‖ ^ (n + 1)`. -/
theorem norm_le_pow_succ {x : K} {n : ℕ} (h : ‖x‖ < ‖π‖ ^ n) : ‖x‖ ≤ ‖π‖ ^ (n + 1) := by
  have hpn : 0 < ‖π‖ ^ n := pow_pos hπ.norm_pos n
  have h1 : ‖x / π ^ n‖ < 1 := by
    rw [norm_div, norm_pow, div_lt_one hpn]
    exact h
  have h2 := hπ.norm_le_of_lt_one _ h1
  rw [norm_div, norm_pow, div_le_iff₀ hpn] at h2
  rw [pow_succ, mul_comm]
  exact h2

/-- Every nonzero `x` with `‖x‖ ≤ 1` has norm a power of `‖π‖`. -/
theorem exists_norm_eq_pow {x : K} (hx : x ≠ 0) (hx1 : ‖x‖ ≤ 1) : ∃ n : ℕ, ‖x‖ = ‖π‖ ^ n := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hex : ∃ m : ℕ, ‖π‖ ^ m < ‖x‖ := exists_pow_lt_of_lt_one hx0 hπ.norm_lt_one
  classical
  have hm : ‖π‖ ^ Nat.find hex < ‖x‖ := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hm
    exact absurd hx1 (not_le.mpr hm)
  obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hle : ‖x‖ ≤ ‖π‖ ^ n := not_lt.mp (Nat.find_min hex (by omega))
  refine ⟨n, le_antisymm hle (not_lt.mp fun hlt => ?_)⟩
  have h := hπ.norm_le_pow_succ hlt
  rw [← hn] at h
  exact absurd hm (not_lt.mpr h)

end IsUniformizer

end Norm

/-! ### The unit ball -/

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- The closed unit ball of an ultrametric normed field, as a subring. -/
def unitBall : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    change ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul ha hb (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  one_mem' := by change ‖(1 : K)‖ ≤ 1; rw [norm_one]
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by change ‖(0 : K)‖ ≤ 1; rw [norm_zero]; exact zero_le_one
  neg_mem' {a} ha := by change ‖-a‖ ≤ 1; rw [norm_neg]; exact ha

variable {K}

@[simp]
theorem mem_unitBall_iff {x : K} : x ∈ unitBall K ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem norm_coe_le_one (x : unitBall K) : ‖(x : K)‖ ≤ 1 := x.2

theorem coe_unitBall : (unitBall K : Set K) = Metric.closedBall 0 1 := by
  ext x
  rw [SetLike.mem_coe, mem_unitBall_iff, mem_closedBall_zero_iff]

theorem isClosed_unitBall : IsClosed (unitBall K : Set K) := by
  rw [coe_unitBall]
  exact Metric.isClosed_closedBall

/-- The inclusion `unitBall K →+* K` is injective. -/
theorem subtype_injective : Function.Injective (unitBall K).subtype := Subtype.coe_injective

instance instCompleteSpace [CompleteSpace K] : CompleteSpace (unitBall K) :=
  isClosed_unitBall.completeSpace_coe

/-- The units of the ball are the elements of norm `1`. -/
theorem isUnit_iff_norm_eq_one {x : unitBall K} : IsUnit x ↔ ‖(x : K)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := norm_coe_le_one (u : unitBall K)
    have h2 := norm_coe_le_one (↑u⁻¹ : unitBall K)
    have h3 : ‖((u : unitBall K) : K)‖ * ‖((↑u⁻¹ : unitBall K) : K)‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, norm_one]
    nlinarith [norm_nonneg ((u : unitBall K) : K), norm_nonneg ((↑u⁻¹ : unitBall K) : K)]
  · intro h
    have hx : (x : K) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      exact zero_ne_one h
    refine isUnit_iff_exists_inv.mpr ⟨⟨(x : K)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_unitBall_iff, norm_inv, h, inv_one]
    · rw [Subring.coe_mul, Subring.coe_one]
      exact mul_inv_cancel₀ hx

instance instIsLocalRing : IsLocalRing (unitBall K) :=
  IsLocalRing.of_nonunits_add fun a b ha hb => by
    rw [mem_nonunits_iff, isUnit_iff_norm_eq_one] at ha hb ⊢
    have ha' := lt_of_le_of_ne (norm_coe_le_one a) ha
    have hb' := lt_of_le_of_ne (norm_coe_le_one b) hb
    rw [Subring.coe_add]
    exact ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha' hb')).ne

/-- The maximal ideal of the ball is the set of elements of norm `< 1`. -/
theorem mem_maximalIdeal_iff {x : unitBall K} :
    x ∈ maximalIdeal (unitBall K) ↔ ‖(x : K)‖ < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (norm_coe_le_one x) h, fun h => h.ne⟩

/-- Principal ideals of the ball are closed balls. -/
theorem mem_span_singleton_iff {a x : unitBall K} :
    x ∈ Ideal.span {a} ↔ ‖(x : K)‖ ≤ ‖(a : K)‖ := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    rw [Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_coe_le_one c)
  · intro h
    by_cases ha : (a : K) = 0
    · have hx : (x : K) = 0 := by
        rw [ha, norm_zero] at h
        exact norm_le_zero_iff.mp h
      refine ⟨0, Subtype.ext ?_⟩
      rw [zero_mul, hx, Subring.coe_zero]
    · refine ⟨⟨(x : K) / a, ?_⟩, Subtype.ext ?_⟩
      · rw [mem_unitBall_iff, norm_div]
        exact div_le_one_of_le₀ h (norm_nonneg _)
      · rw [Subring.coe_mul]
        exact div_mul_cancel₀ _ ha

/-- **Bounded denominators**: for `‖π‖ < 1`, every `x : K` has a multiple `π ^ k x` in the
ball. -/
theorem exists_pow_mul_mem {π : K} (hπ : ‖π‖ < 1) (x : K) : ∃ k : ℕ, π ^ k * x ∈ unitBall K := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, mul_zero]; exact (unitBall K).zero_mem⟩
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hx0) hπ
    refine ⟨k, ?_⟩
    rw [mem_unitBall_iff, norm_mul, norm_pow]
    calc ‖π‖ ^ k * ‖x‖ ≤ ‖x‖⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)
      _ = 1 := inv_mul_cancel₀ hx0.ne'

/-! ### The ball over a uniformizer -/

namespace IsUniformizer

variable {π : K} (hπ : IsUniformizer π)
include hπ

/-- The uniformizer as an element of the ball. -/
def toBall : unitBall K := ⟨π, hπ.norm_lt_one.le⟩

@[simp]
theorem coe_toBall : (hπ.toBall : K) = π := rfl

theorem toBall_ne_zero : hπ.toBall ≠ 0 := fun h => hπ.ne_zero (congrArg Subtype.val h)

/-- Bounded denominators, with the uniformizer. -/
theorem exists_pow_mul_mem (x : K) : ∃ k : ℕ, π ^ k * x ∈ unitBall K :=
  UnitBall.exists_pow_mul_mem hπ.norm_lt_one x

/-- `maximalIdeal (unitBall K) = (π)`. -/
theorem maximalIdeal_eq : maximalIdeal (unitBall K) = Ideal.span {hπ.toBall} := by
  ext x
  rw [mem_maximalIdeal_iff, mem_span_singleton_iff, coe_toBall]
  exact ⟨hπ.norm_le_of_lt_one _, fun h => h.trans_lt hπ.norm_lt_one⟩

/-- `(π ^ n)` is the set of elements of norm at most `‖π‖ ^ n`. -/
theorem mem_span_pow_iff (n : ℕ) {x : unitBall K} :
    x ∈ Ideal.span {hπ.toBall ^ n} ↔ ‖(x : K)‖ ≤ ‖π‖ ^ n := by
  rw [mem_span_singleton_iff, SubmonoidClass.coe_pow, coe_toBall, norm_pow]

theorem coe_span_pow (n : ℕ) :
    (Ideal.span {hπ.toBall ^ n} : Set (unitBall K)) = {x : unitBall K | ‖(x : K)‖ ≤ ‖π‖ ^ n} := by
  ext x
  rw [SetLike.mem_coe, hπ.mem_span_pow_iff]
  rfl

theorem mem_maximalIdeal_pow_iff (n : ℕ) {x : unitBall K} :
    x ∈ maximalIdeal (unitBall K) ^ n ↔ ‖(x : K)‖ ≤ ‖π‖ ^ n := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, hπ.mem_span_pow_iff]

/-- **The topology of the ball is the adic topology of its maximal ideal.** -/
theorem isAdic : IsAdic (maximalIdeal (unitBall K)) := by
  rw [isAdic_iff]
  constructor
  · intro n
    have h : ((maximalIdeal (unitBall K) ^ n : Ideal (unitBall K)) : Set (unitBall K)) =
        Subtype.val ⁻¹' Metric.closedBall (0 : K) (‖π‖ ^ n) := by
      ext x
      rw [SetLike.mem_coe, hπ.mem_maximalIdeal_pow_iff, Set.mem_preimage, mem_closedBall_zero_iff]
    rw [h]
    exact (IsUltrametricDist.isOpen_closedBall (0 : K) (pow_pos hπ.norm_pos n).ne').preimage
      continuous_subtype_val
  · intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hπ.norm_lt_one
    refine ⟨n, fun x hx => hball ?_⟩
    rw [SetLike.mem_coe, hπ.mem_maximalIdeal_pow_iff] at hx
    rw [Metric.mem_ball, dist_zero_right, AddSubgroupClass.coe_norm]
    exact hx.trans_lt hn

/-- Every nonzero element of the ball is `π ^ n` times a unit. -/
theorem exists_associated_pow {x : unitBall K} (hx : x ≠ 0) :
    ∃ n : ℕ, Associated (hπ.toBall ^ n) x := by
  have hxK : (x : K) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨n, hn⟩ := hπ.exists_norm_eq_pow hxK (norm_coe_le_one x)
  have hpn : (π ^ n : K) ≠ 0 := pow_ne_zero n hπ.ne_zero
  have hu1 : ‖(x : K) / π ^ n‖ = 1 := by
    rw [norm_div, norm_pow, hn, div_self (pow_ne_zero n (norm_ne_zero_iff.mpr hπ.ne_zero))]
  let u : unitBall K := ⟨(x : K) / π ^ n, hu1.le⟩
  have hu : IsUnit u := isUnit_iff_norm_eq_one.mpr hu1
  refine ⟨n, hu.unit, Subtype.ext ?_⟩
  rw [IsUnit.unit_spec, Subring.coe_mul, SubmonoidClass.coe_pow, coe_toBall]
  exact mul_div_cancel₀ _ hpn

theorem prime_toBall : Prime hπ.toBall := by
  rw [← Ideal.span_singleton_prime hπ.toBall_ne_zero, ← hπ.maximalIdeal_eq]
  exact (maximalIdeal.isMaximal _).isPrime

theorem isDiscreteValuationRing : IsDiscreteValuationRing (unitBall K) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨hπ.toBall, hπ.prime_toBall.irreducible, fun hx => hπ.exists_associated_pow hx⟩

end IsUniformizer

instance instFactIsAdic [HasUniformizer K] : Fact (IsAdic (maximalIdeal (unitBall K))) :=
  ⟨by
    obtain ⟨π, hπ⟩ := HasUniformizer.exists_isUniformizer (K := K)
    exact hπ.isAdic⟩

instance instIsDiscreteValuationRing [HasUniformizer K] : IsDiscreteValuationRing (unitBall K) := by
  obtain ⟨π, hπ⟩ := HasUniformizer.exists_isUniformizer (K := K)
  exact hπ.isDiscreteValuationRing

/-! ### Tests: the logarithmic chart applies over the ball -/

section Test

open FurioLombardo.Vendor.Toolbox.FormalGroup FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman

example : IsDomain (unitBall K) := inferInstance
example : IsLocalRing (unitBall K) := inferInstance
example : IsUniformAddGroup (unitBall K) := inferInstance
example : T2Space (unitBall K) := inferInstance
example : IsTopologicalRing (unitBall K) := inferInstance
example [CompleteSpace K] : CompleteSpace (unitBall K) := inferInstance
example [HasUniformizer K] : Fact (IsAdic (maximalIdeal (unitBall K))) := inferInstance

example [CompleteSpace K] [CharZero K] {π : K} (hπ : IsUniformizer π) {p : ℕ} (hp : p.Prime)
    (hpm : (p : unitBall K) ∈ maximalIdeal (unitBall K)) {u : unitBall K} {e : ℕ} (hu : IsUnit u)
    (hpe : (p : unitBall K) = hπ.toBall ^ e * u) (Φ : FormalGroupLaw (unitBall K) (Fin 2)) :
    haveI := hπ.hasUniformizer
    LogChart Φ (unitBall K).subtype (hπ.toBall ^ (e + 1)) p (e + 1) :=
  haveI := hπ.hasUniformizer
  log_chart_uniformizer hp hpm hπ.maximalIdeal_eq hπ.toBall_ne_zero hu hpe subtype_injective Φ

example [CompleteSpace K] [CharZero K] [HasUniformizer K] (Φ : FormalGroupLaw (unitBall K) (Fin 2))
    {p : ℕ} (hp : p.Prime) (hpm : (p : unitBall K) ∈ maximalIdeal (unitBall K)) :
    Function.Bijective (logB1 hp hpm (scalingHyp_sq hpm) subtype_injective
      (pow_ne_zero 2 (natCast_ne_zero_of_ringHom (unitBall K).subtype hp.ne_zero)) Φ) :=
  logB1_bijective hp hpm (scalingHyp_sq hpm) subtype_injective _ Φ

end Test

end FurioLombardo.Vendor.Toolbox.UnitBall
