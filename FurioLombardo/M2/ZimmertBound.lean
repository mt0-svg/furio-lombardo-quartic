import FurioLombardo.M2.Zimmert
import FurioLombardo.M2.Signature

/-!
# From Zimmert's Satz 2 to a class bound for K21 (lane M2)

With the signature `(3, 9)` of K21 (`nrRealPlaces_K21`, `nrComplexPlaces_K21`), a bound
`|discr K21| ≤ 2^22 7^27` and a lower bound `log √(2^22 7^27) - log 120000 ≤ zimmertS2 3 9 (1/2)
(1/12)`, Zimmert's Satz 2 for K21 at `γ = 1/2`, `α = 1/12` gives an ideal of absolute norm at most
120000 in every class. The two numerical inputs are hypotheses here and are proved in Discr.lean and
ZimmertNum.lean.
-/

namespace FurioLombardo.M2

open NumberField

open scoped nonZeroDivisors

theorem classBound_of_zimmertSatz2_aux
    (hnum : Real.log (Real.sqrt (2 ^ 22 * 7 ^ 27)) - Real.log 120000 ≤
      zimmertS2 3 9 (1 / 2) (1 / 12))
    (hd : |discr K21| ≤ 2 ^ 22 * 7 ^ 27) (hZ : ZimmertSatz2K21) : ClassBound K21 120000 := by
  intro C
  obtain ⟨I, hI, hS⟩ := hZ C
  refine ⟨I, hI, ?_⟩
  rw [nrRealPlaces_K21, nrComplexPlaces_K21] at hS
  have hN0 : 0 < (Ideal.absNorm (I : Ideal (𝓞 K21)) : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
  have hd0 : 0 < |(discr K21 : ℝ)| := by
    rw [abs_pos]; exact_mod_cast discr_ne_zero K21
  have hdR : |(discr K21 : ℝ)| ≤ 2 ^ 22 * 7 ^ 27 := by
    have h1 : ((|discr K21| : ℤ) : ℝ) ≤ ((2 ^ 22 * 7 ^ 27 : ℤ) : ℝ) := Int.cast_le.mpr hd
    rw [Int.cast_abs] at h1
    exact_mod_cast h1
  have hsq0 : 0 < Real.sqrt |(discr K21 : ℝ)| := Real.sqrt_pos.mpr hd0
  have hlog : Real.log (Real.sqrt |(discr K21 : ℝ)|) ≤ Real.log (Real.sqrt (2 ^ 22 * 7 ^ 27)) :=
    Real.log_le_log hsq0 (Real.sqrt_le_sqrt hdR)
  rw [Real.log_div hsq0.ne' hN0.ne'] at hS
  have h1 : Real.log (Ideal.absNorm (I : Ideal (𝓞 K21)) : ℝ) ≤
      Real.log (Real.sqrt |(discr K21 : ℝ)|) - zimmertS2 3 9 (1 / 2) (1 / 12) := by linarith [hS]
  have h2 : Real.log (Real.sqrt |(discr K21 : ℝ)|) - zimmertS2 3 9 (1 / 2) (1 / 12) ≤
      Real.log 120000 :=
    (sub_le_sub_right hlog _).trans (sub_le_comm.mp hnum)
  have hle := h1.trans h2
  have := (Real.log_le_log_iff hN0 (by norm_num)).mp hle
  exact_mod_cast this

end FurioLombardo.M2
