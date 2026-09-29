import FurioLombardo.Discharge.M3a.ConcreteDefs
import FurioLombardo.Discharge.M3a.AbelPrymData2
import FurioLombardo.M1.Conics

/-!
# Bruin's three conics have no common zero over K21: kernel checks (WP4 of the M3a discharge)

For each coordinate `R_j`, quadratic forms `a_(j,i)` (data `cfData`, `cfDen`, AbelPrymData2.lean,
code/genus2-curves/conics_no_common_zero.gp) with `D_j R_j⁴ = Σ_i (D_j a_(j,i)) Q_(i+1)`. The kernel
checks the identity on each of the fifteen quartic monomials (lane M1's `convKE`, `m4`).
-/

namespace FurioLombardo.Discharge.M3a.Bruin

open FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a

def cfDenN (j : ℕ) : ℕ := cfDen.getD j 1

def cfL (j i m : ℕ) : List ℤ := ((cfData.getD j []).getD i []).getD m []

/-- The coefficients of `D_j a_(j,i)`. -/
def aE (j i : ℕ) : Fin 6 → KE := fun m => .lin (cfL j i m)

/-- The coefficients of `Q_(i+1)`. -/
def QE (i : Fin 3) : Fin 6 → KE := fun m => .lin (QcL i m)

/-- The position of `R_j⁴` among the quartic monomials `m4`. -/
def tgt (j : Fin 3) : Fin 15 := ![0, 10, 14] j

/-- The coefficient `μ` of `Σ_i (D_j a_(j,i)) Q_(i+1) - D_j R_j⁴`. -/
def cfChk (j : Fin 3) (μ : Fin 15) : KE :=
  .sub (.add (.add (convKE (aE j 0) (QE 0) μ) (convKE (aE j 1) (QE 1) μ)) (convKE (aE j 2) (QE 2) μ))
    (.int (if μ = tgt j then (cfDenN j : ℤ) else 0))

theorem ck_cf : ∀ j : Fin 3, ∀ μ : Fin 15, checkK 336 (cfChk j μ) = true := by decide +kernel

theorem ck_cfDen : ∀ j : Fin 3, cfDenN j ≠ 0 := by decide +kernel

end FurioLombardo.Discharge.M3a.Bruin
