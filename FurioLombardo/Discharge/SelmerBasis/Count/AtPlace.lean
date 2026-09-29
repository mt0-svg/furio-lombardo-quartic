import FurioLombardo.Discharge.SelmerBasis.Count.Place
import FurioLombardo.Discharge.SelmerBasis.Count.Tors
import FurioLombardo.Discharge.SelmerBasis.Count.Base

/-!
# Count lane: `CountBound` at a place from a global base abscissa

`countBound_at`: over a complete proper ultrametric field of characteristic zero with a uniformizer
`π` and a prime `p = π^e u`, `e > 0`, the base point data `lsetupAt σ k x` (Count/Base.lean) and
`countBound_of_reps` (Count/Place.lean). `countBound_dyadic` (`p = 2`, residue field `𝔽₂`,
`n = 2e + B`) and `countBound_odd` (`p` odd, `n = B`) supply the representatives of `O² / 2 O²`.
-/

set_option autoImplicit false

open Polynomial IsLocalRing
open FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall
open FurioLombardo.Discharge.M3a.Bruin (fRev c)

namespace FurioLombardo.Discharge.SelmerBasis.Count

variable {K' : Type*} [NontriviallyNormedField K'] [IsUltrametricDist K'] [CompleteSpace K']
  [CharZero K'] [ProperSpace K']

/-- **`CountBound` at a place from a global base abscissa.** `σ(fRev k (x))` a nonzero square,
`σ(c k)` not a square, `nAt k x ≠ 0`, a prime `p = π^e u` of the ball (`e > 0`), at most `2^A`
representatives of `O² / 2 O²` and at most `2^B` points containing `A(K')[2]`. -/
theorem countBound_at (σ : K21 →+* K') {π : K'} (hπ : IsUniformizer π) {p e : ℕ} (hp : p.Prime)
    (he : 0 < e) {u : unitBall K'} (hu : IsUnit u) (hpe : (p : unitBall K') = hπ.toBall ^ e * u)
    (k : Fin 2) [GoodSextic ((fRev k).map σ)] (x : K21) (hsq : IsSquare (σ ((fRev k).eval x)))
    (hx0 : (fRev k).eval x ≠ 0) (hl : ¬ IsSquare (σ (c k))) (hN : nAt k x ≠ 0) {A B : ℕ}
    (tV : Finset (Fin 2 → unitBall K')) (htV : tV.card ≤ 2 ^ A)
    (htV' : ∀ v : Fin 2 → unitBall K', ∃ r ∈ tV, ∃ w, v = r + 2 • w)
    (tT : Finset (Jac ((fRev k).map σ))) (htT : tT.card ≤ 2 ^ B)
    (htT' : ∀ c : Jac ((fRev k).map σ), c ^ 2 = 1 → c ∈ tT) :
    CountBound ((fRev k).map σ) (A + B) := by
  have : HasUniformizer K' := hπ.hasUniformizer
  obtain ⟨b, hb⟩ := hsq
  have hb2 : b ^ 2 = σ ((fRev k).eval x) := by rw [hb, sq]
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact hx0 ((map_eq_zero σ).mp hb)
  have := goodSextic_lsetupAt hb2 hb0 hl hN
  have hpm : (p : unitBall K') ∈ maximalIdeal (unitBall K') := by
    rw [mem_maximalIdeal_iff, hpe]
    have hu1 : ‖((u : unitBall K') : K')‖ = 1 := isUnit_iff_norm_eq_one.mp hu
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, IsUniformizer.coe_toBall, norm_mul,
      norm_pow, hu1, mul_one]
    exact pow_lt_one₀ hπ.norm_pos.le hπ.norm_lt_one he.ne'
  exact countBound_of_reps hπ e (lsetupAt σ k x hb2 hb0 hl hN) (lsetupAt_comp hb2 hb0 hl hN) hp hpm
    hu hpe tV htV htV' tT htT htT'

/-- **`CountBound` at a dyadic place with residue field `𝔽₂`**: `n = 2e + B`. -/
theorem countBound_dyadic (σ : K21 →+* K') {π : K'} (hπ : IsUniformizer π)
    (hres : ∀ y : K', ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) {e : ℕ} (he : 0 < e)
    (hpe : ∃ u : unitBall K', IsUnit u ∧ ((2 : ℕ) : unitBall K') = hπ.toBall ^ e * u)
    (k : Fin 2) [GoodSextic ((fRev k).map σ)] (x : K21) (hsq : IsSquare (σ ((fRev k).eval x)))
    (hx0 : (fRev k).eval x ≠ 0) (hl : ¬ IsSquare (σ (c k))) (hN : nAt k x ≠ 0) {B : ℕ}
    (hT : ∃ tT : Finset (Jac ((fRev k).map σ)), tT.card ≤ 2 ^ B ∧
      ∀ c : Jac ((fRev k).map σ), c ^ 2 = 1 → c ∈ tT) :
    CountBound ((fRev k).map σ) (2 * e + B) := by
  obtain ⟨u, hu, hpe⟩ := hpe
  obtain ⟨tV, htVc, htV⟩ := reps_dyadic hπ hres hu hpe
  obtain ⟨tT, htTc, htT⟩ := hT
  exact countBound_at σ hπ Nat.prime_two he hu hpe k x hsq hx0 hl hN tV htVc htV tT htTc htT

/-- **`CountBound` at a place above an odd prime**: `n = B`. -/
theorem countBound_odd (σ : K21 →+* K') {π : K'} (hπ : IsUniformizer π) {p e : ℕ} (hp : p.Prime)
    (hp2 : Odd p) (he : 0 < e)
    (hpe : ∃ u : unitBall K', IsUnit u ∧ (p : unitBall K') = hπ.toBall ^ e * u)
    (k : Fin 2) [GoodSextic ((fRev k).map σ)] (x : K21) (hsq : IsSquare (σ ((fRev k).eval x)))
    (hx0 : (fRev k).eval x ≠ 0) (hl : ¬ IsSquare (σ (c k))) (hN : nAt k x ≠ 0) {B : ℕ}
    (hT : ∃ tT : Finset (Jac ((fRev k).map σ)), tT.card ≤ 2 ^ B ∧
      ∀ c : Jac ((fRev k).map σ), c ^ 2 = 1 → c ∈ tT) :
    CountBound ((fRev k).map σ) B := by
  obtain ⟨u, hu, hpe⟩ := hpe
  obtain ⟨tT, htTc, htT⟩ := hT
  have hpm : (p : unitBall K') ∈ maximalIdeal (unitBall K') := by
    rw [mem_maximalIdeal_iff, hpe]
    have hu1 : ‖((u : unitBall K') : K')‖ = 1 := isUnit_iff_norm_eq_one.mp hu
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, IsUniformizer.coe_toBall, norm_mul,
      norm_pow, hu1, mul_one]
    exact pow_lt_one₀ hπ.norm_pos.le hπ.norm_lt_one he.ne'
  have h2 := isUnit_two_of_odd hp2 hpm
  have h := countBound_at σ hπ hp he hu hpe k x hsq hx0 hl hN {0} (A := 0) (by simp)
    (cnt_reps_unit h2 2) tT htTc htT
  rwa [zero_add] at h

end FurioLombardo.Discharge.SelmerBasis.Count
