import Mathlib
import FurioLombardo.Discharge.M3a.Concrete
import FurioLombardo.Discharge.M3a.Refined

/-!
# The finest inputs on the concrete sextics `fRev k` (twists δ0, δ1)

With WP2's concrete data (Concrete.lean, namespace `FurioLombardo.Discharge.M3a.Bruin`):

* `k1_sq`: the data part of (K1): `d k = disc (q k)` is not a square in K21 and is a square in
  `K21[T]/(fRev k)` (WP2's `d_not_isSquare`, `d_isSquare_adjoinRoot`, kernel checked); so
  `k1Inputs k : PoonenSchaefer (fRev k) → K1Inputs (fRev k)` and `xtKernel_fRev`: (K1) for the
  real sextics from `PoonenSchaefer (fRev k)` alone, which is the theorem `poonenSchaefer_fRev`
  (K1Concrete.lean);
* `l1Inputs k`: (L1) for the real sextics from the two local facts at `v` with
  `fRev k = q k * (c k · h k)`: `h^σ` irreducible over `k_v` and
  `(q^σ - c h^σ)(T) ∉ k_v^× (L_v^×)²`.
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route

namespace FurioLombardo.Discharge.M3a.Bruin

/-- The data part of (K1) for the twist `k`. -/
theorem k1_sq (k : Fin 2) : ∃ d : K21, ¬ IsSquare d ∧
    ∃ ε : AdjoinRoot (fRev k), ε ^ 2 = algebraMap K21 (AdjoinRoot (fRev k)) d := by
  obtain ⟨ε, hε⟩ := d_isSquare_adjoinRoot k
  exact ⟨d k, d_not_isSquare k, ε, by rw [sq, ← hε]; rfl⟩

/-- (K1) for the twist `k` from `PoonenSchaefer (fRev k)`. -/
theorem k1Inputs (k : Fin 2) (hPS : PoonenSchaefer (fRev k)) : K1Inputs (fRev k) :=
  ⟨hPS, k1_sq k⟩

/-- **(K1) for the real sextics**, from `PoonenSchaefer (fRev k)` only. -/
theorem xtKernel_fRev (k : Fin 2) (hPS : PoonenSchaefer (fRev k)) : XTKernel (fRev k) :=
  xtKernel_of_K1Inputs (k1Inputs k hPS)

theorem fRev_eq_q_mul (k : Fin 2) : fRev k = q k * (C (c k) * h k) := by
  rw [fRev_eq_mul]; ring

/-- (L1) inputs for the twist `k` from the two local facts at `v`. -/
theorem l1Inputs {kv : Type} [Field kv] (σ : K21 →+* kv) (k : Fin 2)
    (hirr : Irreducible ((h k).map σ))
    (hsq : ∀ (c' : kv) (y : AdjoinRoot ((fRev k).map σ)),
      AdjoinRoot.mk ((fRev k).map σ) ((q k).map σ - (C (c k) * h k).map σ) ≠
        algebraMap kv (AdjoinRoot ((fRev k).map σ)) c' * y ^ 2) :
    L1Inputs σ (fRev k) (q k) := by
  refine ⟨⟨C (c k) * h k, fRev_eq_q_mul k, ?_, hsq⟩⟩
  have hc : c k ≠ 0 := by
    rw [← fRev_leadingCoeff]
    intro h0
    rw [leadingCoeff_eq_zero] at h0
    have h6 := GoodSextic.natDegree_eq (f := fRev k)
    rw [h0, natDegree_zero] at h6
    exact absurd h6 (by norm_num)
  rw [Polynomial.map_mul, map_C]
  exact (associated_unit_mul_left ((h k).map σ) (C (σ (c k)))
    (isUnit_C.mpr (Ne.isUnit ((map_ne_zero σ).mpr hc)))).symm.irreducible hirr

end FurioLombardo.Discharge.M3a.Bruin
