import Mathlib
import FurioLombardo.Discharge.SelmerBasis.Count.Setup
import FurioLombardo.Discharge.R7.ConcreteBase
import FurioLombardo.Discharge.R7.ConcreteKv

/-!
# Count lane: base point data from a square root

For `g` of degree at most `6` over a field with `2 ≠ 0`, a square root `b ≠ 0` of `g(0)`, a non-square
`g_6` and `N0(g_0, ..., g_4) ≠ 0` (R7's numerator of `R0`), `LSetup.ofSqrt` is the base point data
with `V0 = b · tβ g`, `c0 = R2`, `w0 = X² + (R1/R2) X + R0/R2` (R7's Taylor identity). For a global
abscissa `x` over K21 and `σ : K21 →+* K'`, `lsetupAt σ k x` is the data of `f = F(X + σ x)`,
`F = (fRev k).map σ`, with `f(X - σ x) = F` (`lsetupAt_comp`) and `GoodSextic f`.
-/

set_option autoImplicit false

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal.Taylor
open FurioLombardo.Discharge.R7.ConcreteKv (separable_comp_X_add_C natDegree_leadingCoeff_comp_X_add_C
  comp_X_add_C_comp_X_sub_C)
open FurioLombardo.Discharge.M3a.Bruin (fRev fRev_natDegree fRev_leadingCoeff c)

namespace FurioLombardo.Discharge.SelmerBasis.Count

variable {K : Type*} [Field K]

/-- The base point data of `g` at `0` from a square root `b` of `g(0)`. -/
noncomputable def LSetup.ofSqrt (g : K[X]) (hg : g.natDegree ≤ 6) (h2 : (2 : K) ≠ 0) {b : K}
    (hb : b ^ 2 = g.coeff 0) (hb0 : b ≠ 0) (hl : ¬ IsSquare (g.coeff 6))
    (hN : tN0 (g.coeff 0) (g.coeff 1) (g.coeff 2) (g.coeff 3) (g.coeff 4) ≠ 0) : LSetup K where
  f := g
  hf := hg
  V0 := C b * tβ g
  hV0d := by rw [degree_C_mul hb0]; exact tβ_degree_lt _
  hV00 := by rw [coeff_C_mul, tβ_coeff_zero, mul_one]; exact hb0
  c0 := tR2 g
  hc0 := tR2_ne_zero _ hb hl
  w0 := X ^ 2 + C (tR1 g / tR2 g) * X + C (tR0 g / tR2 g)
  hw0m := by monicity!
  hw0d := by compute_degree!
  hfV0 := by
    have h0 : g.coeff 0 ≠ 0 := by rw [← hb]; exact pow_ne_zero 2 hb0
    have hR2 := tR2_ne_zero _ hb hl
    have e1 : (C b * tβ g) ^ 2 = C (g.coeff 0) * tβ g ^ 2 := by rw [mul_pow, ← C_pow, hb]
    have h1 : tR2 g * (tR1 g / tR2 g) = tR1 g := by field_simp
    have h0' : tR2 g * (tR0 g / tR2 g) = tR0 g := by field_simp
    have e2 : C (tR2 g) * (X ^ 4 * (X ^ 2 + C (tR1 g / tR2 g) * X + C (tR0 g / tR2 g))) =
        X ^ 4 * (C (tR0 g) + C (tR1 g) * X + C (tR2 g) * X ^ 2) := by
      calc C (tR2 g) * (X ^ 4 * (X ^ 2 + C (tR1 g / tR2 g) * X + C (tR0 g / tR2 g))) =
            X ^ 4 * (C (tR2 g * (tR0 g / tR2 g)) + C (tR2 g * (tR1 g / tR2 g)) * X +
              C (tR2 g) * X ^ 2) := by simp only [C_mul]; ring
        _ = _ := by rw [h1, h0']
    rw [e1, e2]
    exact taylor_identity _ hg h0 h2
  hw00 := by
    have h0 : g.coeff 0 ≠ 0 := by rw [← hb]; exact pow_ne_zero 2 hb0
    have e : (X ^ 2 + C (tR1 g / tR2 g) * X + C (tR0 g / tR2 g)).coeff 0 = tR0 g / tR2 g := by
      simp
    rw [e]
    exact div_ne_zero (tR0_ne_zero _ h0 h2 hN) (tR2_ne_zero _ hb hl)

@[simp]
theorem LSetup.ofSqrt_f (g : K[X]) (hg : g.natDegree ≤ 6) (h2 : (2 : K) ≠ 0) {b : K}
    (hb : b ^ 2 = g.coeff 0) (hb0 : b ≠ 0) (hl : ¬ IsSquare (g.coeff 6))
    (hN : tN0 (g.coeff 0) (g.coeff 1) (g.coeff 2) (g.coeff 3) (g.coeff 4) ≠ 0) :
    (LSetup.ofSqrt g hg h2 hb hb0 hl hN).f = g := rfl

/-- `GoodSextic` is invariant under `X ↦ X + a` in characteristic zero. -/
theorem goodSextic_comp_X_add_C [CharZero K] (F : K[X]) [GoodSextic F] (a : K) :
    GoodSextic (F.comp (X + C a)) := by
  have hs : F.Separable := PerfectField.separable_iff_squarefree.mpr GoodSextic.squarefree
  obtain ⟨hd, hl⟩ := natDegree_leadingCoeff_comp_X_add_C F a
  exact FurioLombardo.Discharge.M3a.goodSextic_of (separable_comp_X_add_C hs a)
    (by rw [hd, GoodSextic.natDegree_eq]) (by rw [hl]; exact GoodSextic.not_isSquare_leadingCoeff)
    (GoodSextic.two_ne_zero F)

section Global

variable {K' : Type*} [Field K'] (σ : K21 →+* K') (k : Fin 2) (x : K21)

/-- The translate of `fRev k` by a global abscissa `x`. -/
noncomputable def gAt : K21[X] := (fRev k).comp (X + C x)

theorem gAt_map : (gAt k x).map σ = ((fRev k).map σ).comp (X + C (σ x)) := by
  simp [gAt, Polynomial.map_comp]

theorem gAt_natDegree : (gAt k x).natDegree = 6 := by
  rw [gAt, (natDegree_leadingCoeff_comp_X_add_C _ _).1, fRev_natDegree]

theorem gAt_coeff_zero : (gAt k x).coeff 0 = (fRev k).eval x := by
  simp [gAt, coeff_zero_eq_eval_zero, eval_comp]

theorem gAt_coeff_six : (gAt k x).coeff 6 = c k := by
  rw [← fRev_leadingCoeff, ← (natDegree_leadingCoeff_comp_X_add_C (fRev k) x).2]
  rw [leadingCoeff, (natDegree_leadingCoeff_comp_X_add_C (fRev k) x).1, fRev_natDegree]; rfl

/-- `N0` of the translate `gAt k x` (a global element). -/
noncomputable def nAt : K21 :=
  tN0 ((gAt k x).coeff 0) ((gAt k x).coeff 1) ((gAt k x).coeff 2) ((gAt k x).coeff 3)
    ((gAt k x).coeff 4)

theorem nAt_map : tN0 (((gAt k x).map σ).coeff 0) (((gAt k x).map σ).coeff 1)
    (((gAt k x).map σ).coeff 2) (((gAt k x).map σ).coeff 3) (((gAt k x).map σ).coeff 4) =
      σ (nAt k x) := by
  simp only [coeff_map, nAt, tN0, map_sub, map_mul, map_add, map_pow, map_ofNat]

/-- **Base point data at a global abscissa.** For `σ(fRev k (x)) = b²` with `b ≠ 0`, a non-square
`σ(c k)` and `nAt k x ≠ 0`: the data of `f = F(X + σ x)`, `F = (fRev k).map σ`. -/
noncomputable def lsetupAt [CharZero K'] {b : K'} (hb : b ^ 2 = σ ((fRev k).eval x)) (hb0 : b ≠ 0)
    (hl : ¬ IsSquare (σ (c k))) (hN : nAt k x ≠ 0) : LSetup K' :=
  LSetup.ofSqrt ((gAt k x).map σ) (by rw [natDegree_map, gAt_natDegree]) two_ne_zero
    (b := b) (by rw [coeff_map, gAt_coeff_zero, hb]) hb0 (by rw [coeff_map, gAt_coeff_six]; exact hl)
    (by rw [nAt_map]; exact (map_ne_zero σ).mpr hN)

variable {σ k x}

theorem lsetupAt_f [CharZero K'] {b : K'} (hb : b ^ 2 = σ ((fRev k).eval x)) (hb0 : b ≠ 0)
    (hl : ¬ IsSquare (σ (c k))) (hN : nAt k x ≠ 0) :
    (lsetupAt σ k x hb hb0 hl hN).f = ((fRev k).map σ).comp (X + C (σ x)) := gAt_map σ k x

theorem lsetupAt_comp [CharZero K'] {b : K'} (hb : b ^ 2 = σ ((fRev k).eval x)) (hb0 : b ≠ 0)
    (hl : ¬ IsSquare (σ (c k))) (hN : nAt k x ≠ 0) :
    (lsetupAt σ k x hb hb0 hl hN).f.comp (X - C (σ x)) = (fRev k).map σ := by
  rw [lsetupAt_f]; exact comp_X_add_C_comp_X_sub_C _ _

theorem goodSextic_lsetupAt [CharZero K'] [GoodSextic ((fRev k).map σ)] {b : K'}
    (hb : b ^ 2 = σ ((fRev k).eval x)) (hb0 : b ≠ 0) (hl : ¬ IsSquare (σ (c k)))
    (hN : nAt k x ≠ 0) : GoodSextic (lsetupAt σ k x hb hb0 hl hN).f := by
  rw [lsetupAt_f]; exact goodSextic_comp_X_add_C _ _

end Global

end FurioLombardo.Discharge.SelmerBasis.Count
