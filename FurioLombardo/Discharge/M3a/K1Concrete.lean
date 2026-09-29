import Mathlib
import FurioLombardo.Discharge.M3a.K1Kernel
import FurioLombardo.Discharge.M3a.LocalFacts
import FurioLombardo.Discharge.M3a.ConcreteInputs

/-!
# The side facts of theorem K1E for the real sextics `fRev k` (lane K1)

With `fRev k = c q h` over K21 (Concrete.lean) and the local facts at the place `v` above 2
(LocalFacts.lean, `σ = M4Cert.σ`):

* `fRev_eval_ne_zero` (H3): `fRev k` has no root in K21: a root of `q` would make `d = disc q` a
  square, and `h` has none since `h^σ` is irreducible of degree 4 over `K_v`;
* `muJ_Tpt_fRev_ne_one` (H4): `q` is the only monic quadratic divisor, and `μ(T) ≠ 1` because its
  image `μ_v(T_v)` at `v` is not trivial (`nsq_Kv`);
* `poonenSchaefer_fRev`: `PoonenSchaefer (fRev k)` is a theorem, and `xtKernel_fRev'`: (K1) for the
  real sextics with no hypothesis.
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route

namespace FurioLombardo.Discharge.M3a.Bruin

open FurioLombardo.Discharge.M4Cert (σ)

attribute [local instance] goodSextic_fRev_Kv

/-- `h k` is irreducible over K21 (its image at `v` is). -/
theorem h_irreducible (k : Fin 2) : Irreducible (h k) :=
  (h_monic k).irreducible_of_irreducible_map σ (h k) (irr_Kv k)

/-- `c k ≠ 0`. -/
theorem c_ne_zero (k : Fin 2) : c k ≠ 0 := fun h0 => c_not_isSquare k ⟨0, by rw [h0, mul_zero]⟩

/-- **(H3) for `fRev k`**: no root in K21. -/
theorem fRev_eval_ne_zero (k : Fin 2) (a : K21) : (fRev k).eval a ≠ 0 := by
  rw [fRev_eq_mul, eval_mul, eval_mul, eval_C]
  refine mul_ne_zero (mul_ne_zero (c_ne_zero k) ?_) ?_
  · intro hq
    apply d_not_isSquare k
    refine ⟨2 * a + (q k).coeff 1, ?_⟩
    rw [q_explicit k] at hq
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at hq
    rw [d]
    linear_combination (-4) * hq
  · intro hh
    have hroot : ((h k).map σ).IsRoot (σ a) := by
      rw [IsRoot, eval_map, eval₂_at_apply, hh, map_zero]
    have h1 := degree_eq_one_of_irreducible_of_root (irr_Kv k) hroot
    rw [degree_map, degree_eq_natDegree (h_monic k).ne_zero, h_natDegree] at h1
    exact absurd h1 (by decide)

/-- **(H4) for `fRev k`**: `μ(T) ≠ 1` for every monic quadratic divisor. -/
theorem muJ_Tpt_fRev_ne_one (k : Fin 2) (q' : K21[X]) (hq : q'.Monic) (hqf : q' ∣ fRev k)
    (hdeg : q'.natDegree = 2) : muJ (fRev k) (Tpt (fRev k) hq hqf hdeg) ≠ 1 := by
  have hirr : Irreducible (C (c k) * h k) :=
    (associated_unit_mul_left (h k) (C (c k)) (isUnit_C.mpr (Ne.isUnit (c_ne_zero k)))).symm.irreducible
      (h_irreducible k)
  have hdeg4 : 2 < (C (c k) * h k).natDegree := by
    rw [natDegree_C_mul (c_ne_zero k), h_natDegree]; norm_num
  obtain rfl := eq_of_monic_quadratic_dvd (fRev_eq_q_mul k) (q_monic k) (q_natDegree k) hirr hdeg4
    q' hq hdeg hqf
  intro h1
  have hqr' : (fRev k).map σ = (q k).map σ * (C (c k) * h k).map σ := by
    rw [fRev_eq_q_mul k, Polynomial.map_mul]
  have hdeg' : ((q k).map σ).natDegree = 2 := by rw [natDegree_map, q_natDegree]
  have hloc := muJ_jacMap σ (fRev k) (Tpt (fRev k) hq hqf hdeg)
  rw [h1, map_one, jacMap_Tpt, muJ_Tpt ((fRev k).map σ) (hq.map σ) _ hdeg' hqr'] at hloc
  exact mk_ne_one_of_forall ((fRev k).map σ) (nsq_Kv k) hloc

/-- **`PoonenSchaefer (fRev k)` is a theorem.** -/
theorem poonenSchaefer_fRev (k : Fin 2) : PoonenSchaefer (fRev k) :=
  poonenSchaefer_of (fRev k) (fRev_eval_ne_zero k) (muJ_Tpt_fRev_ne_one k)

/-- **(K1) for the real sextics, with no hypothesis.** -/
theorem xtKernel_fRev' (k : Fin 2) : XTKernel (fRev k) :=
  xtKernel_fRev k (poonenSchaefer_fRev k)

end FurioLombardo.Discharge.M3a.Bruin
