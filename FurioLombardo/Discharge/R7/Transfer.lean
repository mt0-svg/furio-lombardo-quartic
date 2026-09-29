import Mathlib
import FurioLombardo.Discharge.R7.FinIdx.Assembly

/-!
# Transfer of `LogChartFin` along a comparison with the chart logarithm

`FinIdx.logChartFin_fRev_uncond` gives `LogChartFin` for R7's own logarithm, which is normalized by
the chart at `E0` with a scale that the statement does not fix (an existential exponent `M` and the
index `[Jac : ψ(B1)]`). The consumers (`M3a.Bruin.TwistInputsKv`) need `LogChartFin` for the
logarithm on which the certificates of lane M4 (`M4RestKv`) are stated. This file transfers it:

* `logChartFin_of_comp`: `LogChartFin lam` and `c • lam' = L lam` on a subgroup of finite index,
  with `c ≠ 0` and `det L ≠ 0`, give `LogChartFin lam'`;
* `logChartFin_of_chart_comp`: for any base point datum over `Kv` and any admissible exponent `M`,
  a homomorphism `lam'` with `c • lam' (ψ z) = L (coords (logVal y))` for every `z = pv⁴ y` of the
  ball `B1 Φ (pv⁴)` satisfies `LogChartFin`;
* `ChartLog k lam`: this comparison for the chart of `baseKv k` at some admissible `M`;
  `ChartLog.logChartFin`; and `exists_chartLog`: R7's logarithm satisfies it (`c = 1`,
  `L = [Jac : ψ(B1)] • 1`), so the condition can be met.
-/

namespace FurioLombardo.Discharge.R7

open Polynomial
open scoped Matrix
open FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Vendor.Toolbox.FormalGroup
open FurioLombardo.Discharge.M4Cert
open FurioLombardo.Discharge.M3a.Bruin (fRev)
open FurioLombardo.Discharge.R7.ConcreteKv

/-! ### Linear algebra over `ℤ_[2]` -/

/-- Cancellation of a nonzero scalar in `ℤ_[2] ^ n`. -/
theorem smul_cancel {n : ℕ} {c : ℤ_[2]} (hc : c ≠ 0) {x y : Fin n → ℤ_[2]}
    (h : c • x = c • y) : x = y :=
  smul_right_injective (Fin n → ℤ_[2]) hc h

theorem adjugate_mulVec_mulVec {n : ℕ} (L : Matrix (Fin n) (Fin n) ℤ_[2]) (x : Fin n → ℤ_[2]) :
    L.adjugate *ᵥ (L *ᵥ x) = L.det • x := by
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem mulVec_adjugate_mulVec {n : ℕ} (L : Matrix (Fin n) (Fin n) ℤ_[2]) (x : Fin n → ℤ_[2]) :
    L *ᵥ (L.adjugate *ᵥ x) = L.det • x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- A nonzero element of `ℤ_[2]` is a unit times a power of `2`. -/
theorem exists_unit_mul_two_pow {x : ℤ_[2]} (hx : x ≠ 0) :
    ∃ (u : ℤ_[2]ˣ) (a : ℕ), x = u * 2 ^ a :=
  ⟨PadicInt.unitCoeff hx, x.valuation, by simpa using PadicInt.unitCoeff_spec hx⟩

/-! ### The transfer -/

/-- **Transfer of `LogChartFin`.** If `lam` satisfies `LogChartFin` and, on a subgroup `H` of
finite index, `c • lam' = L lam` with `c ≠ 0` and `det L ≠ 0`, then `lam'` satisfies
`LogChartFin`. -/
theorem logChartFin_of_comp {B : Type*} [AddCommGroup B] {lam lam' : B →+ (Fin 6 → ℤ_[2])}
    (hlam : Analytic.LogChartFin lam) (H : AddSubgroup B) [H.FiniteIndex] {c : ℤ_[2]}
    (hc : c ≠ 0) (L : Matrix (Fin 6) (Fin 6) ℤ_[2]) (hL : L.det ≠ 0)
    (hcomp : ∀ b ∈ H, c • lam' b = L *ᵥ lam b) : Analytic.LogChartFin lam' := by
  obtain ⟨B1, hB1, hinj, N, hsurj⟩ := hlam
  refine ⟨B1 ⊓ H, inferInstance, fun b hb h0 => hinj b hb.1 ?_, ?_⟩
  · have h1 : L *ᵥ lam b = 0 := by rw [← hcomp b hb.2, h0, smul_zero]
    have h2 : L.det • lam b = 0 := by
      rw [← adjugate_mulVec_mulVec, h1, Matrix.mulVec_zero]
    exact (smul_eq_zero.mp h2).resolve_left hL
  · have hm0 : ((H.index : ℕ) : ℤ_[2]) ≠ 0 :=
      Nat.cast_ne_zero.mpr AddSubgroup.FiniteIndex.index_ne_zero
    obtain ⟨um, a, hma⟩ := exists_unit_mul_two_pow hm0
    obtain ⟨ud, d, hdd⟩ := exists_unit_mul_two_pow hL
    refine ⟨N + a + d, fun v => ?_⟩
    obtain ⟨b0, hb0, hb0v⟩ := hsurj (L.adjugate *ᵥ ((c * ↑um⁻¹ * ↑ud⁻¹) • v))
    have hbH : H.index • b0 ∈ H := AddSubgroup.nsmul_index_mem H b0
    refine ⟨H.index • b0, ⟨B1.nsmul_mem hb0 _, hbH⟩, smul_cancel hc ?_⟩
    rw [hcomp _ hbH, map_nsmul, hb0v, ← Nat.cast_smul_eq_nsmul ℤ_[2], Matrix.mulVec_smul,
      Matrix.mulVec_smul, mulVec_adjugate_mulVec, smul_smul, smul_smul, smul_smul, smul_smul,
      hma, hdd]
    congr 1
    have h1 : (um : ℤ_[2]) * ↑um⁻¹ = 1 := Units.mul_inv um
    have h2 : (ud : ℤ_[2]) * ↑ud⁻¹ = 1 := Units.mul_inv ud
    calc ↑um * 2 ^ a * 2 ^ N * (↑ud * 2 ^ d) * (c * ↑um⁻¹ * ↑ud⁻¹)
        = c * 2 ^ (N + a + d) * (↑um * ↑um⁻¹) * (↑ud * ↑ud⁻¹) := by ring
      _ = c * 2 ^ (N + a + d) := by rw [h1, h2, mul_one, mul_one]

/-- **`LogChartFin` from a comparison with the chart logarithm**, for any base point datum over
`Kv` and any admissible exponent `M`: if `c • lam' (ψ z) = L (coords (logVal y))` for every point
`z = pv⁴ y` of the ball `B1 Φ (pv⁴)`, with `c ≠ 0` and `det L ≠ 0`, then `LogChartFin lam'`. -/
theorem logChartFin_of_chart_comp (D : SetupKv) [GoodSextic D.f] {F : Kv[X]} [GoodSextic F]
    {a : Kv} (hF : D.f.comp (X - C a) = F) {M : ℕ} (hM : D.toSetup.Adm M)
    (lam' : Additive (Jac F) →+ (Fin 6 → ℤ_[2])) {c : ℤ_[2]} (hc : c ≠ 0)
    (L : Matrix (Fin 6) (Fin 6) ℤ_[2]) (hL : L.det ≠ 0)
    (hcomp : ∀ z ∈ B1 (D.toSetup.fglO hM.good) (pvO ^ (3 + 1)), ∀ y : Fin 2 → OKv,
      (∀ j, (z j : OKv) = pvO ^ (3 + 1) * y j) →
      c • lam' (D.toSetup.psi hF hM z) =
        L *ᵥ coordEquiv (logVal (D.toSetup.fglO hM.good) (unitBall Kv).subtype (pvO ^ (3 + 1)) y)) :
    Analytic.LogChartFin lam' := by
  obtain ⟨lam, hlam, H', hH', hfin, hform⟩ :=
    exists_logChartFin_of_chart (D.toSetup.fglO hM.good) (D.toSetup.psi hF hM)
      (D.toSetup.psi_injective hF hM) (FinIdx.hFinIdx_of_setupKv D F a hF hM)
  have hn : ((H'.index : ℕ) : ℤ_[2]) ≠ 0 :=
    Nat.cast_ne_zero.mpr AddSubgroup.FiniteIndex.index_ne_zero
  refine logChartFin_of_comp hlam H' (mul_ne_zero hn hc) L hL fun b hb => ?_
  have hb' : b ∈ (H' : Set (Additive (Jac F))) := hb
  rw [hH'] at hb'
  obtain ⟨z, hz, rfl⟩ := hb'
  have hy : ∀ j, (z j : OKv) = pvO ^ (3 + 1) * divC (pvO ^ (3 + 1)) (z j : OKv) :=
    fun j => (mul_divC (hz j)).symm
  rw [hform z hz _ hy, ← Nat.cast_smul_eq_nsmul ℤ_[2], Matrix.mulVec_smul, ← hcomp z hz _ hy,
    smul_smul]

/-! ### The comparison for the twists -/

/-- **`lam` is a nondegenerate linear image of the chart logarithm** of `baseKv k`: for some
admissible exponent `M` and some `c ≠ 0`, `L` with `det L ≠ 0`, `c • lam (ψ z) = L (coords (logVal
y))` for every `z = pv⁴ y` of the ball `B1 Φ (pv⁴)`. -/
def ChartLog (k : Fin 2) (lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2])) : Prop :=
  ∃ M, ∃ hM : (baseKv k).toSetup.Adm M, ∃ c : ℤ_[2], ∃ L : Matrix (Fin 6) (Fin 6) ℤ_[2],
    c ≠ 0 ∧ L.det ≠ 0 ∧
      ∀ z ∈ B1 ((baseKv k).toSetup.fglO hM.good) (pvO ^ (3 + 1)), ∀ y : Fin 2 → OKv,
        (∀ j, (z j : OKv) = pvO ^ (3 + 1) * y j) →
        c • lam ((baseKv k).toSetup.psi (hF k) hM z) =
          L *ᵥ coordEquiv
            (logVal ((baseKv k).toSetup.fglO hM.good) (unitBall Kv).subtype (pvO ^ (3 + 1)) y)

/-- `ChartLog` gives `LogChartFin`. -/
theorem ChartLog.logChartFin {k : Fin 2} {lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2])}
    (h : ChartLog k lam) : Analytic.LogChartFin lam := by
  obtain ⟨M, hM, c, L, hc, hL, hcomp⟩ := h
  exact logChartFin_of_chart_comp (baseKv k) (hF k) hM lam hc L hL hcomp

/-- R7's logarithm satisfies `ChartLog`, with `c = 1` and `L = [Jac : ψ(B1)] • 1`. -/
theorem exists_chartLog (k : Fin 2) :
    ∃ lam : Additive (Jac ((fRev k).map σ)) →+ (Fin 6 → ℤ_[2]), ChartLog k lam := by
  obtain ⟨M, hM, lam, -, H', -, hfin, hform⟩ := FinIdx.logChartFin_fRev_uncond k
  refine ⟨lam, M, hM, 1, ((H'.index : ℕ) : ℤ_[2]) • (1 : Matrix (Fin 6) (Fin 6) ℤ_[2]),
    one_ne_zero, ?_, fun z hz y hy => ?_⟩
  · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact pow_ne_zero 6 (Nat.cast_ne_zero.mpr AddSubgroup.FiniteIndex.index_ne_zero)
  · rw [one_smul, hform z hz y hy, Matrix.smul_mulVec, Matrix.one_mulVec,
      Nat.cast_smul_eq_nsmul]

end FurioLombardo.Discharge.R7
