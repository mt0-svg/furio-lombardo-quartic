import Mathlib
import FurioLombardo.Discharge.M3a.Concrete
import FurioLombardo.Discharge.M4Cert.Excl

/-!
# The leading coefficient of `fRev k` is not a square at `v`

For the completion `σ : K21 → K_v` of lane M4's certificate discharge
(`FurioLombardo.Discharge.M4Cert.σ`, `K_v = ℚ_2[x]/(E)`, `E` Eisenstein of degree 3):

* `lead_res`: the zk coordinates `lcL k` of `4 c_k = 4 f_k(0)` pass the residue test of
  `approx_σ_zkE`, and the residue of `σ(4 c_k)` modulo 8 is not the residue of a square (the list
  `sq8`, closed under squares by `sq8_ok`); one kernel check;
* `lead_Kv`: `¬ IsSquare (σ (fRev k).leadingCoeff)`, the first local fact of `LocalFacts`;
* `goodSextic_fRev_Kv`: lane M3a's `GoodSextic ((fRev k).map σ)` over `K_v`.
-/

namespace FurioLombardo.Discharge.M3a.Bruin

open Polynomial FurioLombardo.M1 FurioLombardo.Discharge.M4Cert

/-- The zk coordinates of `4 c_k = 4 f_k(0)`. -/
def lcL (k : Fin 2) : List ℤ := (FnData.getD (k : ℕ) []).getD 0 []

theorem c_eq_zkE (k : Fin 2) : c k = (4 : K21)⁻¹ * zkE (lcL k) := rfl

/-- The residue data of `σ(4 c_k)` modulo 8 (kernel check). -/
theorem lead_res : ∀ k : Fin 2, zresOK (lcL k) ∧ modT (zres (lcL k)) 3 ∉ sq8 := by
  decide +kernel

/-- **The leading coefficient of `fRev k` is not a square in `K_v`.** -/
theorem lead_Kv (k : Fin 2) :
    ¬ IsSquare (FurioLombardo.Discharge.M4Cert.σ (fRev k).leadingCoeff) := by
  rw [fRev_leadingCoeff, c_eq_zkE, map_mul, map_inv₀, map_ofNat]
  rintro ⟨r, hr⟩
  obtain ⟨hok, hnot⟩ := lead_res k
  refine not_sq_of_approx sq8_ok hnot (approx_σ_zkE _ hok (by norm_num)) (2 * r) ?_
  have h4 : (4 : Kv) ≠ 0 := by
    have h := (map_ne_zero FurioLombardo.Discharge.M4Cert.σ).mpr (by norm_num : (4 : K21) ≠ 0)
    rwa [map_ofNat] at h
  have := congrArg (fun z => (4 : Kv) * z) hr
  rw [← mul_assoc, mul_inv_cancel₀ h4, one_mul] at this
  rw [this]
  ring

/-- Lane M3a's standing hypotheses for `fRev k` over `K_v`. -/
theorem goodSextic_fRev_Kv (k : Fin 2) :
    FurioLombardo.M3a.Genus2.GoodSextic ((fRev k).map FurioLombardo.Discharge.M4Cert.σ) :=
  goodSextic_fRev_map _ k (lead_Kv k)

end FurioLombardo.Discharge.M3a.Bruin
