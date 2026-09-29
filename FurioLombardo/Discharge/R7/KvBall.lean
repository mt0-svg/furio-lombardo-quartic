import Mathlib
import FurioLombardo.Vendor.Toolbox.Padic.UnitBall
import FurioLombardo.Discharge.M4Cert.Kv

/-!
# The unit ball of `Kv` (item R7)

`pv` is a uniformizer of `Kv = M4Cert.Kv` (`isUniformizer_pv`: a norm `< 1` is at most `‖pv‖`,
because on the coordinates `a₀ + a₁ pv + a₂ pv²` the norm is `max (‖a₀‖, ‖a₁‖ ‖pv‖, ‖a₂‖ ‖pv‖²)`
with `‖aᵢ‖` powers of `2` and `‖pv‖³ = 1/2`). So `OKv := unitBall Kv` carries every instance that
`FurioLombardo.Vendor.Toolbox.FormalGroup.log_chart_uniformizer` needs (through `HasUniformizer Kv`; `CharZero Kv` is
added here). With `pvO` the element `pv` of `OKv` and the unit `u2 = 2 / pv ^ 3`,
`2 = pvO ^ 3 * u2` (`natCast_two_eq`), so the logarithmic chart applies with `p = 2`, `e = 3`
(`log_chart_OKv`). `Kv` is proper and `OKv` compact (`instProperSpaceKv`, `instCompactSpaceOKv`).
-/

namespace FurioLombardo.Discharge.R7

open FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Discharge.M4Cert IsLocalRing

/-- `Kv` has characteristic zero (a `ℚ`-algebra). With this instance in scope, `Algebra ℚ Kv`
still resolves to `instAlgebraRatKv` of `Kv.lean` (test below). -/
instance instCharZeroKv : CharZero Kv := algebraRat.charZero Kv

/-- A 2-adic number of norm `< 1` has norm at most `1/2`. -/
theorem norm_le_half_of_lt_one {b : ℚ_[2]} (hb : ‖b‖ < 1) : ‖b‖ ≤ 2⁻¹ := by
  have h := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one b 0).mp (by simpa using hb)
  simpa using h

/-- **Discreteness of the norm of `Kv`**: a norm `< 1` is at most `‖pv‖`. -/
theorem norm_le_norm_pv_of_lt_one {x : Kv} (hx : ‖x‖ < 1) : ‖x‖ ≤ ‖pv‖ := by
  obtain ⟨a, rfl⟩ := evQ_surjective x
  rw [norm_evQ] at hx ⊢
  simp only [max_lt_iff] at hx
  obtain ⟨h0, h1, h2⟩ := hx
  have hpv0 := norm_pv_pos
  have hpv1 := norm_pv_lt_one
  refine max_le ((norm_le_half_of_lt_one h0).trans half_lt_norm_pv.le) (max_le ?_ ?_)
  · have ha1 : ‖a 1‖ ≤ 1 := by
      by_contra hc
      have h2le := two_le_norm_of_one_lt (not_le.mp hc)
      nlinarith [half_lt_norm_pv]
    exact (mul_le_mul_of_nonneg_right ha1 hpv0.le).trans_eq (one_mul _)
  · have ha2 : ‖a 2‖ ≤ 1 := by
      by_contra hc
      have h2le := two_le_norm_of_one_lt (not_le.mp hc)
      nlinarith [half_lt_norm_pv_sq, pow_pos hpv0 2]
    calc ‖a 2‖ * ‖pv‖ ^ 2 ≤ 1 * ‖pv‖ ^ 2 := mul_le_mul_of_nonneg_right ha2 (by positivity)
      _ = ‖pv‖ * ‖pv‖ := by ring
      _ ≤ 1 * ‖pv‖ := mul_le_mul_of_nonneg_right hpv1.le hpv0.le
      _ = ‖pv‖ := one_mul _

/-- `pv` is a uniformizer of `Kv`. -/
theorem isUniformizer_pv : IsUniformizer pv :=
  ⟨norm_pv_pos, norm_pv_lt_one, fun _ hx => norm_le_norm_pv_of_lt_one hx⟩

instance instHasUniformizerKv : HasUniformizer Kv := isUniformizer_pv.hasUniformizer

/-- The unit ball of `Kv`. -/
abbrev OKv : Type := unitBall Kv

/-- The uniformizer `pv` as an element of `OKv`. -/
noncomputable def pvO : OKv := isUniformizer_pv.toBall

@[simp]
theorem coe_pvO : (pvO : Kv) = pv := rfl

theorem pvO_ne_zero : pvO ≠ 0 := isUniformizer_pv.toBall_ne_zero

theorem maximalIdeal_OKv : maximalIdeal OKv = Ideal.span {pvO} := isUniformizer_pv.maximalIdeal_eq

theorem mem_span_pvO_pow_iff (n : ℕ) {x : OKv} :
    x ∈ Ideal.span {pvO ^ n} ↔ ‖(x : Kv)‖ ≤ ‖pv‖ ^ n :=
  isUniformizer_pv.mem_span_pow_iff n

theorem norm_two_div_pv_pow_three : ‖(2 : Kv) / pv ^ 3‖ = 1 := by
  rw [norm_div, norm_pow, norm_pv_pow_three, norm_two_Kv, div_self (by norm_num)]

/-- The unit `2 / pv ^ 3` of `OKv`. -/
noncomputable def u2 : OKv := ⟨(2 : Kv) / pv ^ 3, norm_two_div_pv_pow_three.le⟩

@[simp]
theorem coe_u2 : (u2 : Kv) = 2 / pv ^ 3 := rfl

theorem isUnit_u2 : IsUnit u2 := isUnit_iff_norm_eq_one.mpr norm_two_div_pv_pow_three

/-- `2 = pv ^ 3 u2` in `OKv` (the hypothesis `hpe` of `log_chart_uniformizer`, `p = 2`,
`e = 3`). -/
theorem natCast_two_eq : ((2 : ℕ) : OKv) = pvO ^ 3 * u2 := by
  apply Subtype.ext
  rw [Subring.coe_mul, SubmonoidClass.coe_pow, coe_pvO, coe_u2, Subring.coe_natCast,
    mul_div_cancel₀ _ (pow_ne_zero 3 isUniformizer_pv.ne_zero)]
  norm_num

theorem two_eq : (2 : OKv) = pvO ^ 3 * u2 := by
  rw [← natCast_two_eq]
  norm_num

theorem natCast_two_mem_maximalIdeal : ((2 : ℕ) : OKv) ∈ maximalIdeal OKv := by
  rw [mem_maximalIdeal_iff, Subring.coe_natCast, Nat.cast_ofNat, norm_two_Kv]
  norm_num

theorem two_mem_maximalIdeal : (2 : OKv) ∈ maximalIdeal OKv := by
  have h := natCast_two_mem_maximalIdeal
  rwa [Nat.cast_ofNat] at h

/-- **The logarithmic chart over `OKv`**, for every formal group law, with `p = 2`, `e = 3`:
the chart on `pv ^ 4 OKv ^ ι`. -/
theorem log_chart_OKv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Φ : FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.FormalGroupLaw OKv ι) :
    FurioLombardo.Vendor.Toolbox.FormalGroup.LogChart Φ (unitBall Kv).subtype (pvO ^ (3 + 1)) 2 (3 + 1) :=
  FurioLombardo.Vendor.Toolbox.FormalGroup.log_chart_uniformizer Nat.prime_two natCast_two_mem_maximalIdeal
    maximalIdeal_OKv pvO_ne_zero isUnit_u2 natCast_two_eq subtype_injective Φ

/-! ### Compactness -/

/-- `Kv` is a proper metric space (finite dimensional over the locally compact field `ℚ_[2]`). -/
instance instProperSpaceKv : ProperSpace Kv := FiniteDimensional.proper ℚ_[2] Kv

theorem isCompact_unitBall_Kv : IsCompact (unitBall Kv : Set Kv) := by
  rw [coe_unitBall]
  exact isCompact_closedBall 0 1

instance instCompactSpaceOKv : CompactSpace OKv :=
  isCompact_iff_compactSpace.mp isCompact_unitBall_Kv

/-! ### Tests -/

example : IsDomain OKv := inferInstance
example : IsLocalRing OKv := inferInstance
example : IsUniformAddGroup OKv := inferInstance
example : CompleteSpace OKv := inferInstance
example : T2Space OKv := inferInstance
example : IsTopologicalRing OKv := inferInstance
example : Fact (IsAdic (maximalIdeal OKv)) := inferInstance
example : IsDiscreteValuationRing OKv := inferInstance
example : (inferInstance : Algebra ℚ Kv) = instAlgebraRatKv := by with_reducible_and_instances rfl

example (Φ : FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.FormalGroupLaw OKv (Fin 2)) :
    FurioLombardo.Vendor.Toolbox.FormalGroup.LogChart Φ (unitBall Kv).subtype (pvO ^ (3 + 1)) 2 (3 + 1) :=
  FurioLombardo.Vendor.Toolbox.FormalGroup.log_chart_uniformizer (p := 2) (e := 3) Nat.prime_two
    natCast_two_mem_maximalIdeal maximalIdeal_OKv pvO_ne_zero isUnit_u2 natCast_two_eq
    subtype_injective Φ

end FurioLombardo.Discharge.R7
