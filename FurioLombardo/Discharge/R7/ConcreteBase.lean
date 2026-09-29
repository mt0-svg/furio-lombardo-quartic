import Mathlib
import FurioLombardo.Discharge.R7.Formal
import FurioLombardo.Discharge.R7.KvBall

/-!
# Base points of the formal chart for the twists `k = 0, 1` (item R7, `Concrete`)

Data and checks: code/local-group/chart_base_points.gp.

## Taylor data of `√f` at `0`

For `f` of degree at most 6 over a field with `2 ≠ 0` and `f(0) ≠ 0`, `tβ f` is the cubic Taylor
polynomial of `√(f / f(0))` at `0`, and `f - f(0) · (tβ f)² = X⁴ (R0 + R1 X + R2 X²)` with explicit
`R0, R1, R2` (`taylor_identity`). For any `b` with `b² = f(0)`, `V0 = b · tβ f` is the cubic
Taylor polynomial of `√f` through `b`; the `R_j` do not depend on `b`.
-/

open Polynomial

namespace FurioLombardo.Vendor.Toolbox.G2Formal.Taylor

variable {K : Type*} [Field K]

/-- `β1 = f1 / (2 f0)`. -/
noncomputable def tb1 (f : K[X]) : K := f.coeff 1 / (2 * f.coeff 0)

/-- `β2 = (f2 / f0 - β1²) / 2`. -/
noncomputable def tb2 (f : K[X]) : K := (f.coeff 2 / f.coeff 0 - tb1 f ^ 2) / 2

/-- `β3 = (f3 / f0 - 2 β1 β2) / 2`. -/
noncomputable def tb3 (f : K[X]) : K := (f.coeff 3 / f.coeff 0 - 2 * tb1 f * tb2 f) / 2

/-- The cubic Taylor polynomial of `√(f / f0)` at `0`. -/
noncomputable def tβ (f : K[X]) : K[X] :=
  1 + C (tb1 f) * X + C (tb2 f) * X ^ 2 + C (tb3 f) * X ^ 3

/-- `R0 = f4 - f0 (β2² + 2 β1 β3)`. -/
noncomputable def tR0 (f : K[X]) : K := f.coeff 4 - f.coeff 0 * (tb2 f ^ 2 + 2 * tb1 f * tb3 f)

/-- `R1 = f5 - 2 f0 β2 β3`. -/
noncomputable def tR1 (f : K[X]) : K := f.coeff 5 - f.coeff 0 * (2 * tb2 f * tb3 f)

/-- `R2 = f6 - f0 β3²`. -/
noncomputable def tR2 (f : K[X]) : K := f.coeff 6 - f.coeff 0 * tb3 f ^ 2

theorem tβ_coeff_zero (f : K[X]) : (tβ f).coeff 0 = 1 := by
  simp [tβ, coeff_X, coeff_X_pow]

theorem tβ_degree_lt (f : K[X]) : (tβ f).degree < 4 := by
  unfold tβ
  compute_degree!

/-- **The Taylor identity.** -/
theorem taylor_identity (f : K[X]) (hf : f.natDegree ≤ 6) (h0 : f.coeff 0 ≠ 0)
    (h2 : (2 : K) ≠ 0) :
    f - C (f.coeff 0) * tβ f ^ 2 =
      X ^ 4 * (C (tR0 f) + C (tR1 f) * X + C (tR2 f) * X ^ 2) := by
  have hsum : f = C (f.coeff 0) + C (f.coeff 1) * X + C (f.coeff 2) * X ^ 2 +
      C (f.coeff 3) * X ^ 3 + C (f.coeff 4) * X ^ 4 + C (f.coeff 5) * X ^ 5 +
      C (f.coeff 6) * X ^ 6 := by
    have := as_sum_range' f 7 (by omega)
    simp only [← C_mul_X_pow_eq_monomial, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, pow_zero, mul_one, pow_one] at this
    exact this
  have e1 : f.coeff 1 = 2 * f.coeff 0 * tb1 f := by
    rw [tb1]; field_simp
  have e2 : f.coeff 2 = f.coeff 0 * (tb1 f ^ 2 + 2 * tb2 f) := by
    rw [tb2]; field_simp; ring
  have e3 : f.coeff 3 = f.coeff 0 * (2 * tb3 f + 2 * tb1 f * tb2 f) := by
    rw [tb3]; field_simp; ring
  have e4 : f.coeff 4 = tR0 f + f.coeff 0 * (tb2 f ^ 2 + 2 * tb1 f * tb3 f) := by
    simp only [tR0]; ring
  have e5 : f.coeff 5 = tR1 f + f.coeff 0 * (2 * tb2 f * tb3 f) := by simp only [tR1]; ring
  have e6 : f.coeff 6 = tR2 f + f.coeff 0 * tb3 f ^ 2 := by simp only [tR2]; ring
  set c0 := f.coeff 0
  set b1 := tb1 f
  set b2 := tb2 f
  set b3 := tb3 f
  have hβ : tβ f = 1 + C b1 * X + C b2 * X ^ 2 + C b3 * X ^ 3 := rfl
  calc f - C c0 * tβ f ^ 2 = (C c0 + C (f.coeff 1) * X + C (f.coeff 2) * X ^ 2 +
      C (f.coeff 3) * X ^ 3 + C (f.coeff 4) * X ^ 4 + C (f.coeff 5) * X ^ 5 +
      C (f.coeff 6) * X ^ 6) - C c0 * tβ f ^ 2 := by rw [← hsum]
    _ = X ^ 4 * (C (tR0 f) + C (tR1 f) * X + C (tR2 f) * X ^ 2) := by
      rw [e1, e2, e3, e4, e5, e6, hβ]
      simp only [map_add, map_mul, map_pow, map_ofNat]
      ring

/-- `R2 ≠ 0` when the leading coefficient is not a square: `R2 = f6 - (b β3)²` for `b² = f0`. -/
theorem tR2_ne_zero (f : K[X]) {b : K} (hb : b ^ 2 = f.coeff 0) (hl : ¬ IsSquare (f.coeff 6)) :
    tR2 f ≠ 0 := by
  intro h
  apply hl
  refine ⟨b * tb3 f, ?_⟩
  unfold tR2 at h
  rw [← hb] at h
  linear_combination h

/-- The numerator of `R0`: `64 f0³ R0 = N0(f0, ..., f4)`. -/
noncomputable def tN0 (c0 c1 c2 c3 c4 : K) : K :=
  64 * c0 ^ 3 * c4 - 16 * c0 ^ 2 * c2 ^ 2 - 32 * c0 ^ 2 * c1 * c3 + 24 * c0 * c1 ^ 2 * c2 - 5 * c1 ^ 4

theorem tN0_eq (f : K[X]) (h0 : f.coeff 0 ≠ 0) (h2 : (2 : K) ≠ 0) :
    64 * f.coeff 0 ^ 3 * tR0 f =
      tN0 (f.coeff 0) (f.coeff 1) (f.coeff 2) (f.coeff 3) (f.coeff 4) := by
  simp only [tR0, tb3, tb2, tb1, tN0]
  field_simp
  ring

theorem tN0_smul (s c0 c1 c2 c3 c4 : K) :
    tN0 (s * c0) (s * c1) (s * c2) (s * c3) (s * c4) = s ^ 4 * tN0 c0 c1 c2 c3 c4 := by
  simp only [tN0]; ring

/-- `R0 ≠ 0` from its numerator. -/
theorem tR0_ne_zero (f : K[X]) (h0 : f.coeff 0 ≠ 0) (h2 : (2 : K) ≠ 0)
    (hN : tN0 (f.coeff 0) (f.coeff 1) (f.coeff 2) (f.coeff 3) (f.coeff 4) ≠ 0) : tR0 f ≠ 0 := by
  intro h
  apply hN
  rw [← tN0_eq f h0 h2, h, mul_zero]

variable {L : Type*} [Field L]

theorem tR0_map (φ : K →+* L) (f : K[X]) : tR0 (f.map φ) = φ (tR0 f) := by
  simp only [tR0, tb3, tb2, tb1, coeff_map, map_sub, map_mul, map_add, map_div₀, map_pow,
    map_ofNat]

theorem tR1_map (φ : K →+* L) (f : K[X]) : tR1 (f.map φ) = φ (tR1 f) := by
  simp only [tR1, tb3, tb2, tb1, coeff_map, map_sub, map_mul, map_div₀, map_pow,
    map_ofNat]

theorem tR2_map (φ : K →+* L) (f : K[X]) : tR2 (f.map φ) = φ (tR2 f) := by
  simp only [tR2, tb3, tb2, tb1, coeff_map, map_sub, map_mul, map_div₀, map_pow,
    map_ofNat]

end FurioLombardo.Vendor.Toolbox.G2Formal.Taylor
