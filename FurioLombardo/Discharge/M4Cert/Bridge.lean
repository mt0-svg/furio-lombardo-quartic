import Mathlib
import FurioLombardo.Discharge.M4Cert.Excl
import FurioLombardo.Discharge.M4Cert.Discs
import FurioLombardo.Discharge.M4Cert.OnCurve
import FurioLombardo.Discharge.M3a.ConcreteDefs

/-!
# Bridge to the concrete Bruin matrices of the M3a discharge

`FurioLombardo.Discharge.M3a.Bruin.Mmat i` (the symmetric matrices of `Q1, Q2, Q3`, built from the
zk coordinates `QcData`) and `Bruin.δ k` are the matrices and twists of M3a's `Lift`. Their zk data
agree with `qzk` and `dzk` of this directory (one kernel check each), so `QFormData (Mmat i) (qzk i)`
and `δ k = zkE (dzk k)`, and lane M4's `HExcl` holds for the twist predicate of these matrices.
-/

namespace FurioLombardo.Discharge.M4Cert

open FurioLombardo.M1 FurioLombardo.Discharge.M3a.Bruin

theorem QcL_eq : ∀ q : Fin 3, QcL q 0 = qzk q 0 0 ∧ QcL q 1 = qzk q 0 1 ∧ QcL q 2 = qzk q 0 2 ∧
    QcL q 3 = qzk q 1 1 ∧ QcL q 4 = qzk q 1 2 ∧ QcL q 5 = qzk q 2 2 := by
  decide +kernel

theorem dL_eq : ∀ k : Fin 2, FurioLombardo.Discharge.M3a.Bruin.dL k = dzk k := by
  decide +kernel

theorem qFormData_Mmat (q : Fin 3) : QFormData (Mmat q) (qzk q) := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := QcL_eq q
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> simp [Mmat, Qc, e0, e3, e5]
  · fin_cases i <;> fin_cases j <;> simp at hij <;> simp [Mmat, Qc, e1, e2, e4]

theorem δ_eq (k : Fin 2) : δ k = zkE (dzk k) := by
  simp only [δ, dL_eq]

/-- Lane M4's `HExcl` for the twist δ0 and the Bruin matrices of the M3a discharge. -/
theorem hExcl_T0_Mmat : FurioLombardo.M4.HExcl FurioLombardo.M4.T0.data
    (Twist (Mmat 0) (Mmat 1) (Mmat 2) δ0) :=
  hExcl_T0 (qFormData_Mmat 0) (qFormData_Mmat 2) (δ_eq 0)

/-- Lane M4's `HExcl` for the twist δ1 and the Bruin matrices of the M3a discharge. -/
theorem hExcl_T1_Mmat : FurioLombardo.M4.HExcl FurioLombardo.M4.T1.data
    (Twist (Mmat 0) (Mmat 1) (Mmat 2) δ1) :=
  hExcl_T1 (qFormData_Mmat 0) (qFormData_Mmat 2) (δ_eq 1)

/-! ## The lifts of the concrete twists -/

/-- The points of `D_δ(K21)` above rational points lie on `C`, for matrices of the Bruin forms. -/
theorem onC_of_qFormData {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (h1 : QFormData M1 (qzk 0)) (h2 : QFormData M2 (qzk 1)) (h3 : QFormData M3 (qzk 2)) :
    OnC M1 M2 M3 δ :=
  fun x a b c hx => onCurve_of_over h1 h2 h3 x a b c hx

theorem onC_Mmat (δ : K21) : OnC (Mmat 0) (Mmat 1) (Mmat 2) δ :=
  onC_of_qFormData (qFormData_Mmat 0) (qFormData_Mmat 1) (qFormData_Mmat 2)

/-- Every lift of the twist `δ` lies in a disc, at a parameter of twist `δ` (the first two conjuncts
of lane M4's `HDisc`, M3a's `LiftDisc`, with `disc = liftDisc`, `par = liftPar`). -/
theorem liftTwist_Mmat (δ : K21) (x : FurioLombardo.M3a.Route.Lift (Mmat 0) (Mmat 1) (Mmat 2) δ) :
    liftDisc x ∈ [1, 2, 3, 4, 5] ∧ Twist (Mmat 0) (Mmat 1) (Mmat 2) δ (liftDisc x) (liftPar x) :=
  liftTwist (onC_Mmat δ) x

/-- M3a's `TailGood` for δ0 with `disc = liftDisc`, `par = liftPar`. -/
theorem tailGood_T0_Mmat :
    ∀ x : FurioLombardo.M3a.Route.Lift (Mmat 0) (Mmat 1) (Mmat 2) δ0,
      (∃ t ∈ FurioLombardo.M4.T0.data.tails, t.disc = liftDisc x ∧ liftPar x = (t.Xi : ℤ_[2])) →
      FurioLombardo.M3a.Route.GoodLift (0, 0, 1) (2, 0, 1) x.1 :=
  tailGood_T0 (onC_Mmat δ0)

/-- M3a's `TailGood` for δ1 with `disc = liftDisc`, `par = liftPar`. -/
theorem tailGood_T1_Mmat :
    ∀ x : FurioLombardo.M3a.Route.Lift (Mmat 0) (Mmat 1) (Mmat 2) δ1,
      (∃ t ∈ FurioLombardo.M4.T1.data.tails, t.disc = liftDisc x ∧ liftPar x = (t.Xi : ℤ_[2])) →
      FurioLombardo.M3a.Route.GoodLift (1, 1, 1) (-1, 0, 1) x.1 :=
  tailGood_T1 (onC_Mmat δ1)

end FurioLombardo.Discharge.M4Cert
