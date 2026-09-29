import Mathlib
import FurioLombardo.M1.Vendor.Stoll.Basic

/-!
# Norms on `K[X]/(g)` as resultants with formal degrees (lane K1, brick E0)

For the elementary proof of (K1). `K` is a field,
`N_g(p) = Algebra.norm K (AdjoinRoot.mk g p)`, and `resultant f g m n` is Mathlib's resultant with
formal degrees `m`, `n` (Sylvester matrix of size `m + n`).

* `norm_mk_eq_resultant_of_le` (R2): `N_u(p) = Res_{deg u, n}(u, p)` for monic `u`, `deg p ≤ n`
  (`AdjoinRoot.norm_mk_eq_resultant` and `Monic.resultant_congr_right` of the Stoll file vendored by
  lane M1, FurioLombardo.M1.Vendor.Stoll.Basic, a port of TauCeti's resultant code);
* `lc_pow_mul_norm_mk` (R1): `lc(f)ⁿ N_f(p) = Res_{deg f, n}(f, p)` for `f ≠ 0`, `deg p ≤ n`;
* `resultant_mul_left_of_le` (R6): `Res_{a+b, n}(f₁ f₂, g) = Res_{a,n}(f₁, g) Res_{b,n}(f₂, g)` for nonzero
  `f₁`, `f₂` with `deg f₁ ≤ a`, `deg f₂ ≤ b` and `deg g ≤ n`;
* `norm_mk_swap`: `lc(f)^{deg u} N_f(u) = (-1)^{deg f deg u} N_u(f)` for monic `u`;
* `norm_algebraMap_adjoinRoot`: `N_u(c) = c^{deg u}` for monic `u`.
-/

open Polynomial

namespace FurioLombardo.Discharge.M3a.K1

variable {K : Type*} [Field K]

/-- (R2) The norm on `K[X]/(u)`, `u` monic, as a resultant with formal degree `n ≥ deg p`. -/
theorem norm_mk_eq_resultant_of_le {u p : K[X]} (hu : u.Monic) {n : ℕ} (hn : p.natDegree ≤ n) :
    Algebra.norm K (AdjoinRoot.mk u p) = resultant u p u.natDegree n := by
  rw [AdjoinRoot.norm_mk_eq_resultant hu, hu.resultant_congr_right le_rfl hn]

/-- The monic associate `f / lc f` has the same quotient ring, compatibly with `mk`. -/
theorem norm_mk_eq_norm_mk_monic {f : K[X]} (hf : f ≠ 0) (p : K[X]) :
    Algebra.norm K (AdjoinRoot.mk f p) =
      Algebra.norm K (AdjoinRoot.mk (C f.leadingCoeff⁻¹ * f) p) := by
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hI : Ideal.span {f} = Ideal.span {C f.leadingCoeff⁻¹ * f} := by
    rw [Ideal.span_singleton_eq_span_singleton]
    exact ⟨(Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hlc))).unit,
      by simp [mul_comm]⟩
  show Algebra.norm K (Ideal.Quotient.mk (Ideal.span {f}) p) =
    Algebra.norm K (Ideal.Quotient.mk (Ideal.span {C f.leadingCoeff⁻¹ * f}) p)
  rw [← Algebra.norm_eq_of_algEquiv (Ideal.quotientEquivAlgOfEq K hI),
    Ideal.quotientEquivAlgOfEq_mk]

/-- (R1) `lc(f)ⁿ N_f(p) = Res_{deg f, n}(f, p)` for `f ≠ 0` and `deg p ≤ n`. -/
theorem lc_pow_mul_norm_mk {f p : K[X]} (hf : f ≠ 0) {n : ℕ} (hn : p.natDegree ≤ n) :
    f.leadingCoeff ^ n * Algebra.norm K (AdjoinRoot.mk f p) = resultant f p f.natDegree n := by
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  obtain ⟨f0, hf0⟩ : ∃ f0, f0 = C f.leadingCoeff⁻¹ * f := ⟨_, rfl⟩
  have hmon : f0.Monic := by
    rw [hf0, Monic, leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc]
  have hdeg : f0.natDegree = f.natDegree := by
    rw [hf0, natDegree_C_mul (inv_ne_zero hlc)]
  have hff : f = C f.leadingCoeff * f0 := by
    rw [hf0, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]
  calc f.leadingCoeff ^ n * Algebra.norm K (AdjoinRoot.mk f p)
      = f.leadingCoeff ^ n * resultant f0 p f.natDegree n := by
        rw [norm_mk_eq_norm_mk_monic hf, ← hf0, norm_mk_eq_resultant_of_le hmon hn, hdeg]
    _ = resultant (C f.leadingCoeff * f0) p f.natDegree n := by rw [resultant_C_mul_left]
    _ = resultant f p f.natDegree n := by rw [← hff]

/-- (R6) Formal multiplicativity of the resultant in the first argument. -/
theorem resultant_mul_left_of_le {f₁ f₂ g : K[X]} (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0) {a b n : ℕ}
    (ha : f₁.natDegree ≤ a) (hb : f₂.natDegree ≤ b) (hn : g.natDegree ≤ n) :
    resultant (f₁ * f₂) g (a + b) n = resultant f₁ g a n * resultant f₂ g b n := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hb
  have hmul : (f₁ * f₂).natDegree = f₁.natDegree + f₂.natDegree := natDegree_mul h₁ h₂
  rw [show f₁.natDegree + i + (f₂.natDegree + j) = (f₁ * f₂).natDegree + (i + j) by omega,
    resultant_add_left_deg _ _ _ _ _ le_rfl, resultant_add_left_deg _ _ _ _ _ le_rfl,
    resultant_add_left_deg _ _ _ _ _ le_rfl, hmul, resultant_mul_left _ _ _ _ hn]
  ring

/-- `lc(f)^{deg u} N_f(u) = (-1)^{deg f · deg u} N_u(f)` for monic `u`. -/
theorem norm_mk_swap {f u : K[X]} (hf : f ≠ 0) (hu : u.Monic) :
    f.leadingCoeff ^ u.natDegree * Algebra.norm K (AdjoinRoot.mk f u) =
      (-1) ^ (f.natDegree * u.natDegree) * Algebra.norm K (AdjoinRoot.mk u f) := by
  rw [lc_pow_mul_norm_mk hf le_rfl, resultant_comm, norm_mk_eq_resultant_of_le hu le_rfl]

/-- The norm of a constant in `K[X]/(g)`, `g ≠ 0`. -/
theorem norm_algebraMap_adjoinRoot_of_ne_zero {g : K[X]} (hg : g ≠ 0) (c : K) :
    Algebra.norm K (algebraMap K (AdjoinRoot g) c) = c ^ g.natDegree := by
  rw [Algebra.norm_algebraMap, (AdjoinRoot.powerBasis hg).finrank, AdjoinRoot.powerBasis_dim]

/-- The norm of a constant in `K[X]/(u)`, `u` monic. -/
theorem norm_algebraMap_adjoinRoot {u : K[X]} (hu : u.Monic) (c : K) :
    Algebra.norm K (algebraMap K (AdjoinRoot u) c) = c ^ u.natDegree := by
  rw [Algebra.norm_algebraMap, (AdjoinRoot.powerBasis hu.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim]

end FurioLombardo.Discharge.M3a.K1
