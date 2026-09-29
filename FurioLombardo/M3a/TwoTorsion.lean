import Mathlib
import FurioLombardo.M3a.BaseChange

/-!
# The rational 2-torsion point `T` (lane M3a)

For a monic quadratic factor `q` of `f` (in the application, the quadratic factor of the reversed
Prym sextic `f_δ^rev` over `k = K21`), the class `T = [⟨q, Y⟩]` of the Mumford ideal with `v = 0`
(the divisor `P₁ + P₂ - ∞` of the two Weierstrass points above the roots of `q`):

* `Tpt f hq hqf hdeg : Jac f`, a point of `A(K)`;
* `Tpt_sq`: `T² = 1` (the ideal `⟨q, Y⟩` is its own conjugate, so its class is its own inverse);
* `Tpt_ne_one`: `T ≠ 1` (`⟨q, Y⟩` is not principal).
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.M3a.Genus2

variable {K : Type*} [Field K]

/-- The 2-torsion point `T = [⟨q, Y⟩]` of `A(K)`, for a monic quadratic factor `q` of `f`. -/
noncomputable def Tpt (f : K[X]) [GoodSextic f] {q : K[X]} (hq : q.Monic) (hqf : q ∣ f)
    (hdeg : q.natDegree = 2) : Jac f :=
  mumfordJac f hq (by rw [hdeg]; exact even_two) (mumford_data_of_dvd f hqf).choose_spec.1
    (mumford_data_of_dvd f hqf).choose_spec.2

theorem coe_Tpt (f : K[X]) [GoodSextic f] {q : K[X]} (hq : q.Monic) (hqf : q ∣ f)
    (hdeg : q.natDegree = 2) :
    ((Tpt f hq hqf hdeg : Jac f) : Pic f) = ClassGroup.mk0 (mumford0 f hq.ne_zero 0) := rfl

/-- `2T = 0`. -/
theorem Tpt_sq (f : K[X]) [GoodSextic f] {q : K[X]} (hq : q.Monic) (hqf : q ∣ f)
    (hdeg : q.natDegree = 2) : Tpt f hq hqf hdeg ^ 2 = 1 := by
  obtain ⟨hw, hc⟩ := (mumford_data_of_dvd f hqf).choose_spec
  have hinv := mk0_mumford_neg f hq hw hc
  rw [neg_zero] at hinv
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_Tpt, OneMemClass.coe_one, pow_two]
  nth_rewrite 1 [hinv]
  exact inv_mul_cancel _

/-- `T ≠ 0`. -/
theorem Tpt_ne_one (f : K[X]) [GoodSextic f] {q : K[X]} (hq : q.Monic) (hqf : q ∣ f)
    (hdeg : q.natDegree = 2) : Tpt f hq hqf hdeg ≠ 1 := by
  intro h
  have h1 : ((Tpt f hq hqf hdeg : Jac f) : Pic f) = 1 := by rw [h]; rfl
  rw [coe_Tpt] at h1
  exact mumford_zero_not_isPrincipal f hq hqf hdeg
    ((ClassGroup.mk0_eq_one_iff (mumford0 f hq.ne_zero 0).2).mp h1)

end FurioLombardo.M3a.Genus2
