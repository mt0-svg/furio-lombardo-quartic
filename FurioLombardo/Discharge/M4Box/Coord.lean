import Mathlib
import FurioLombardo.Discharge.M4Log.Defs

/-!
# From norms in `K_v²` to divisibility in `ℤ_[2]⁶` (lane lean-m4box)

Lane M4's vectors live in `ℤ_[2]⁶`, the coordinates of `O_v²` on `1, pv, pv²` (`toKv2`, the inverse
of R7's `coordEquiv`). Since `2 = pv³ · unit`, a vector is divisible by `2^n` when both components of
its image in `K_v²` have norm at most `‖pv‖^(3n)` (`dvdV_of_norm_toKv2_le`). Also: `toKv2` is
`ℤ_[2]`-linear (`toKv2_smul`), every integral vector of `K_v²` is a `toKv2` (`exists_toKv2_eq`), and
`‖2^n u‖ = ‖pv‖^(3n)` for a unit `u` (`norm_toKv_two_pow_mul`).
-/

open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Vendor.Toolbox.UnitBall

namespace FurioLombardo.Discharge.M4Box

/-- A component of `toKv2 x` is `evQ` of its three coordinates. -/
theorem toKv2_apply (x : Fin 6 → ℤ_[2]) (i : Fin 2) :
    toKv2 x i = evQ (fun j => (x (finProdFinEquiv (i, j)) : ℚ_[2])) := by
  rfl

/-- `‖evQ a‖ ≤ ‖pv‖^(3n)` iff every coordinate has norm at most `2^-n`. -/
theorem norm_evQ_le_iff (a : Fin 3 → ℚ_[2]) (n : ℕ) :
    ‖evQ a‖ ≤ ‖pv‖ ^ (3 * n) ↔ ∀ j, ‖a j‖ ≤ (2⁻¹ : ℝ) ^ n := by
  have h2 : (2 : ℚ_[2]) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  have hn2 : 0 < ‖(2 : ℚ_[2]) ^ n‖ := norm_pos_iff.mpr h2
  have e : evQ (fun j => a j / 2 ^ n) = evQ a / algebraMap ℚ_[2] Kv (2 ^ n) := by
    have hK : algebraMap ℚ_[2] Kv (2 ^ n) ≠ 0 := (map_ne_zero _).mpr h2
    field_simp
    simp only [evQ, map_div₀]
    field_simp
  have hpow : ‖pv‖ ^ (3 * n) = ‖(2 : ℚ_[2]) ^ n‖ := by
    rw [pow_mul, norm_pv_pow_three, norm_pow, norm_two_padic]
  have key := norm_evQ_le_one_iff (fun j => a j / 2 ^ n)
  rw [e, norm_div, M4Cert.norm_algebraMap, div_le_one hn2, ← hpow] at key
  rw [key]
  refine forall_congr' fun j => ?_
  rw [norm_div, div_le_one hn2, norm_pow, norm_two_padic]

/-- **Divisibility from norms**: if both components of `toKv2 x` have norm at most
`‖pv‖^(3n)`, every coordinate of `x` is divisible by `2^n`. -/
theorem dvdV_of_norm_toKv2_le {x : Fin 6 → ℤ_[2]} {n : ℕ}
    (h : ∀ i, ‖toKv2 x i‖ ≤ ‖pv‖ ^ (3 * n)) : FurioLombardo.M4.DvdV n x := by
  intro m
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv : Fin 2 × Fin 3 ≃ Fin 6).surjective m
  have hi := h i
  rw [toKv2_apply, norm_evQ_le_iff] at hi
  have hj := hi j
  have hmem : x (finProdFinEquiv (i, j)) ∈ (Ideal.span {((2 : ℕ) : ℤ_[2]) ^ n} : Ideal ℤ_[2]) := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [PadicInt.norm_def]
    simpa [zpow_neg, zpow_natCast, inv_pow] using hj
  rw [Ideal.mem_span_singleton] at hmem
  simpa using hmem

/-- `toKv2` is `ℤ_[2]`-linear. -/
theorem toKv2_smul (a : ℤ_[2]) (x : Fin 6 → ℤ_[2]) : toKv2 (a • x) = toKv a • toKv2 x := by
  funext i
  rw [Pi.smul_apply, toKv2_apply, toKv2_apply, smul_eq_mul]
  simp only [evQ, Pi.smul_apply, smul_eq_mul, PadicInt.coe_mul, map_mul]
  change _ = algebraMap ℚ_[2] Kv (a : ℚ_[2]) * _
  ring

/-- The components of `toKv2 x` are integral. -/
theorem norm_toKv2_le_one (x : Fin 6 → ℤ_[2]) (i : Fin 2) : ‖toKv2 x i‖ ≤ 1 := by
  exact (coordEquiv.symm x i).2

/-- Every integral vector of `K_v²` is a `toKv2`. -/
theorem exists_toKv2_eq {G : Fin 2 → Kv} (hG : ∀ i, ‖G i‖ ≤ 1) :
    ∃ g : Fin 6 → ℤ_[2], toKv2 g = G := by
  refine ⟨coordEquiv (fun i => ⟨G i, mem_unitBall_iff.mpr (hG i)⟩), ?_⟩
  rw [toKv2_coordEquiv]

/-- `‖2^n u‖ = ‖pv‖^(3n)` in `K_v` for a unit `u` of `ℤ_[2]`. -/
theorem norm_toKv_two_pow_mul {u : ℤ_[2]} (hu : IsUnit u) (n : ℕ) :
    ‖toKv (2 ^ n * u)‖ = ‖pv‖ ^ (3 * n) := by
  have hu1 : ‖(u : ℚ_[2])‖ = 1 := PadicInt.isUnit_iff.mp hu
  change ‖algebraMap ℚ_[2] Kv ((2 ^ n * u : ℤ_[2]) : ℚ_[2])‖ = _
  rw [M4Cert.norm_algebraMap, pow_mul, norm_pv_pow_three, PadicInt.coe_mul, norm_mul,
    PadicInt.coe_pow, norm_pow, hu1, mul_one, show ((2 : ℤ_[2]) : ℚ_[2]) = 2 by norm_cast,
    norm_two_padic]

/-- `‖2^n y‖ ≤ ‖pv‖^(3n)` in `K_v` for `y ∈ ℤ_[2]`. -/
theorem norm_toKv_two_pow_mul_le (y : ℤ_[2]) (n : ℕ) : ‖toKv (2 ^ n * y)‖ ≤ ‖pv‖ ^ (3 * n) := by
  change ‖algebraMap ℚ_[2] Kv ((2 ^ n * y : ℤ_[2]) : ℚ_[2])‖ ≤ _
  rw [M4Cert.norm_algebraMap, pow_mul, norm_pv_pow_three, PadicInt.coe_mul, norm_mul,
    PadicInt.coe_pow, norm_pow, ← PadicInt.norm_def]
  have hy : ‖y‖ ≤ 1 := y.norm_le_one
  calc ‖((2 : ℤ_[2]) : ℚ_[2])‖ ^ n * ‖y‖ ≤ ‖((2 : ℤ_[2]) : ℚ_[2])‖ ^ n * 1 := by gcongr
    _ = (2⁻¹ : ℝ) ^ n := by
      rw [mul_one, show ((2 : ℤ_[2]) : ℚ_[2]) = 2 by norm_cast, norm_two_padic]

end FurioLombardo.Discharge.M4Box
