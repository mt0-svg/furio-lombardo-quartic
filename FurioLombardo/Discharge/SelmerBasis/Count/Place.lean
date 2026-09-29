import Mathlib
import FurioLombardo.Discharge.SelmerBasis.Interfaces
import FurioLombardo.Discharge.SelmerBasis.Count.FinIdx
import FurioLombardo.Discharge.SelmerBasis.Count.Abstract

/-!
# Count lane: `CountBound` at a nonarchimedean place

Over a complete proper ultrametric field `K` of characteristic zero with a uniformizer `π` and a
prime `p = π^e u` of the unit ball, for `F = f(X - a)` with base point data `D : LSetup K`:

* `countBound_of_reps`: `CountBound F (A + B)` from a finset of at most `2^A` representatives of
  `O² / 2 O²` and a finset of at most `2^B` points containing `A(K)[2]`. The finite index subgroup
  `H ≅ O²` of `A(K)` is `exists_finiteIndex_chart`, the count `cnt_count_of_chart`.
* `reps_dyadic`: `2^(2e)` representatives when `p = 2` and the residue field is `𝔽₂`;
* `isUnit_two_of_odd`: `2` is a unit of the ball when an odd prime lies in its maximal ideal (then
  `O² = 2 O²`, `cnt_reps_unit`).
-/

set_option autoImplicit false

open Polynomial IsLocalRing
open FurioLombardo.M3a.Genus2 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall

namespace FurioLombardo.Discharge.SelmerBasis.Count

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- `O²` has no `2`-torsion. -/
theorem two_nsmul_eq_zero [CharZero K] (v : Fin 2 → unitBall K) (hv : 2 • v = 0) : v = 0 := by
  funext i
  have h := congrArg (fun w : Fin 2 → unitBall K => ((w i : unitBall K) : K)) hv
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at h
  push_cast at h
  apply Subtype.ext
  simpa [two_ne_zero] using h

/-- **`CountBound` at a place.** -/
theorem countBound_of_reps [CompleteSpace K] [CharZero K] [ProperSpace K] [HasUniformizer K]
    {π : K} (hπ : IsUniformizer π) (e : ℕ) (D : LSetup K) [GoodSextic D.f] {F : K[X]} [GoodSextic F]
    {a : K} (hF : D.f.comp (X - C a) = F) {p : ℕ} (hp : p.Prime)
    (hpm : (p : unitBall K) ∈ maximalIdeal (unitBall K)) {u : unitBall K} (hu : IsUnit u)
    (hpe : (p : unitBall K) = hπ.toBall ^ e * u) {A B : ℕ} (tV : Finset (Fin 2 → unitBall K))
    (htV : tV.card ≤ 2 ^ A) (htV' : ∀ v : Fin 2 → unitBall K, ∃ r ∈ tV, ∃ w, v = r + 2 • w)
    (tT : Finset (Jac F)) (htT : tT.card ≤ 2 ^ B) (htT' : ∀ c : Jac F, c ^ 2 = 1 → c ∈ tT) :
    CountBound F (A + B) := by
  obtain ⟨M, hM⟩ := (D.toSetup hπ).exists_adm
  obtain ⟨G, L, hL, hG⟩ := exists_finiteIndex_chart hπ e D hF hM hp hpm hu hpe
  exact cnt_count_of_chart (Q := H F) (muJ F) (H_sq F) G hG L hL two_nsmul_eq_zero tV htV htV' tT htT
    htT'

/-- Representatives of `O² / 2 O²` when the residue field is `𝔽₂` and `2 = π^e u`. -/
theorem reps_dyadic {π : K} (hπ : IsUniformizer π)
    (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) {e : ℕ} {u : unitBall K} (hu : IsUnit u)
    (hpe : ((2 : ℕ) : unitBall K) = hπ.toBall ^ e * u) :
    ∃ tV : Finset (Fin 2 → unitBall K), tV.card ≤ 2 ^ (2 * e) ∧
      ∀ v : Fin 2 → unitBall K, ∃ r ∈ tV, ∃ w, v = r + 2 • w := by
  obtain ⟨t, htc, ht⟩ := cnt_reps_pow hπ.toBall (cnt_res_ball hπ hres) e
  have h2 : (2 : unitBall K) = hπ.toBall ^ e * u := by rw [← hpe, Nat.cast_ofNat]
  obtain ⟨T, hTc, hT⟩ := cnt_reps_pi 2 t (cnt_reps_two_of_pow hπ.toBall u e hu h2 t ht)
  refine ⟨T, hTc.trans ?_, hT⟩
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left htc 2

/-- `2` is a unit of the ball when an odd prime `p` lies in its maximal ideal. -/
theorem isUnit_two_of_odd {p : ℕ} (hp : Odd p)
    (hpm : (p : unitBall K) ∈ maximalIdeal (unitBall K)) : IsUnit (2 : unitBall K) := by
  by_contra h2
  have h2m : (2 : unitBall K) ∈ maximalIdeal (unitBall K) := h2
  obtain ⟨m, rfl⟩ := hp
  have h1 : (1 : unitBall K) = ((2 * m + 1 : ℕ) : unitBall K) - m * 2 := by push_cast; ring
  exact (maximalIdeal.isMaximal (unitBall K)).ne_top
    ((Ideal.eq_top_iff_one _).mpr (h1 ▸ Ideal.sub_mem _ hpm (Ideal.mul_mem_left _ _ h2m)))

end FurioLombardo.Discharge.SelmerBasis.Count
