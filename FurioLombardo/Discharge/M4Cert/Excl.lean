import Mathlib
import FurioLombardo.Discharge.M4Cert.Curve
import FurioLombardo.M4.Instances

/-!
# HExcl for the twists δ0 and δ1 (lane M4)

Kernel checks (`decide +kernel`) of the residue data of `FurioLombardo.Discharge.M4Cert.DataRes`
against the exact data of `FurioLombardo.Discharge.M4Cert.Data` (the residues modulo 8 of `σ` of the
coefficients of Q1 and Q3 and of δ0, δ1 are recomputed from their zk coordinates and θ0), of the
list of squares modulo 8, and of every excluded box of `T0.data` and `T1.data` (by Q1 or by Q3).
`hExcl_T0`, `hExcl_T1`: lane M4's `HExcl` for the predicate `Twist M1 M2 M3 δ` of
`FurioLombardo.Discharge.M4Cert.Curve`, for any matrices `M1`, `M3` with the quadratic forms Q1, Q3
(zk coordinates `qzk 0`, `qzk 2`) and `δ = zkE (dzk k)`; `M2` is arbitrary.
-/

namespace FurioLombardo.Discharge.M4Cert

open FurioLombardo.M1

/-! ## Kernel checks of the residue data -/

theorem qres8_Q1 : ∀ i j : Fin 3, i ≤ j →
    zresOK (qzk 0 i j) ∧ modT (zres (qzk 0 i j)) 3 = qres8 0 i j := by
  decide +kernel

theorem qres8_Q3 : ∀ i j : Fin 3, i ≤ j →
    zresOK (qzk 2 i j) ∧ modT (zres (qzk 2 i j)) 3 = qres8 1 i j := by
  decide +kernel

theorem dres8_ok : ∀ k : Fin 2, zresOK (dzk k) ∧ modT (zres (dzk k)) 3 = dres8 k ∧
    modT (mulZ (dres8 k) (dinv8 k)) 3 = modT (1, 0, 0) 3 := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
theorem sq8_ok : SqClosed sq8 3 := by
  unfold SqClosed
  decide +kernel

/-- Every excluded box of `T0.data` (twist δ0) passes the check at level 2 with Q1 or Q3. -/
theorem boxes_T0 : ∀ e ∈ FurioLombardo.M4.T0.data.excluded,
    boxOK (qres8 0) (dinv8 0) sq8 2 e.1 e.2.1 e.2.2 = true ∨
      boxOK (qres8 1) (dinv8 0) sq8 2 e.1 e.2.1 e.2.2 = true := by
  decide +kernel

/-- Every excluded box of `T1.data` (twist δ1) passes the check at level 2 with Q1 or Q3. -/
theorem boxes_T1 : ∀ e ∈ FurioLombardo.M4.T1.data.excluded,
    boxOK (qres8 0) (dinv8 1) sq8 2 e.1 e.2.1 e.2.2 = true ∨
      boxOK (qres8 1) (dinv8 1) sq8 2 e.1 e.2.1 e.2.2 = true := by
  decide +kernel

/-! ## The residues as congruences in `K_v` -/

theorem approx_Q1 : ∀ i j : Fin 3, i ≤ j → Approx (σ (zkE (qzk 0 i j))) (qres8 0 i j) 3 := by
  intro i j hij
  obtain ⟨hok, heq⟩ := qres8_Q1 i j hij
  rw [← heq]
  exact (approx_σ_zkE _ hok (by norm_num)).reduce

theorem approx_Q3 : ∀ i j : Fin 3, i ≤ j → Approx (σ (zkE (qzk 2 i j))) (qres8 1 i j) 3 := by
  intro i j hij
  obtain ⟨hok, heq⟩ := qres8_Q3 i j hij
  rw [← heq]
  exact (approx_σ_zkE _ hok (by norm_num)).reduce

theorem approx_δ (k : Fin 2) : Approx (σ (zkE (dzk k))) (dres8 k) 3 := by
  obtain ⟨hok, heq, -⟩ := dres8_ok k
  rw [← heq]
  exact (approx_σ_zkE _ hok (by norm_num)).reduce

/-! ## HExcl -/

/-- HExcl for any list of boxes that pass the check, twist `δ = zkE (dzk k)`. -/
theorem hExcl_of (k : Fin 2) (D : FurioLombardo.M4.TwistData)
    {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (h1 : QFormData M1 (qzk 0)) (h3 : QFormData M3 (qzk 2)) (hδ : δ = zkE (dzk k))
    (hbox : ∀ e ∈ D.excluded, boxOK (qres8 0) (dinv8 k) sq8 2 e.1 e.2.1 e.2.2 = true ∨
      boxOK (qres8 1) (dinv8 k) sq8 2 e.1 e.2.1 e.2.2 = true) :
    FurioLombardo.M4.HExcl D (Twist M1 M2 M3 δ) := by
  rintro e he X hX ⟨Y, hF, P, t, ht, hp⟩
  subst hδ
  rcases hbox e he with hb | hb
  · refine no_point_of_boxOK h1 approx_Q1 (approx_δ k) (dres8_ok k).2.2 sq8_ok hb hX Y hF t P.r ht ?_
    rw [← hp]; exact P.eq1
  · refine no_point_of_boxOK h3 approx_Q3 (approx_δ k) (dres8_ok k).2.2 sq8_ok hb hX Y hF t P.s ht ?_
    rw [← hp]; exact P.eq3

/-- **HExcl for the twist δ0** (`FurioLombardo.M4.T0.data`). -/
theorem hExcl_T0 {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (h1 : QFormData M1 (qzk 0)) (h3 : QFormData M3 (qzk 2)) (hδ : δ = zkE (dzk 0)) :
    FurioLombardo.M4.HExcl FurioLombardo.M4.T0.data (Twist M1 M2 M3 δ) :=
  hExcl_of 0 _ h1 h3 hδ boxes_T0

/-- **HExcl for the twist δ1** (`FurioLombardo.M4.T1.data`). -/
theorem hExcl_T1 {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (h1 : QFormData M1 (qzk 0)) (h3 : QFormData M3 (qzk 2)) (hδ : δ = zkE (dzk 1)) :
    FurioLombardo.M4.HExcl FurioLombardo.M4.T1.data (Twist M1 M2 M3 δ) :=
  hExcl_of 1 _ h1 h3 hδ boxes_T1

/-! ## The upper triangular Bruin matrices -/

/-- The upper triangular matrix of the Bruin quadric `Q_(q+1)` over K21. -/
noncomputable def BQ (q : Fin 3) : Matrix (Fin 3) (Fin 3) K21 :=
  fun i j => if i ≤ j then zkE (qzk q i j) else 0

theorem qFormData_BQ (q : Fin 3) : QFormData (BQ q) (qzk q) := by
  refine ⟨fun i => by simp [BQ], fun i j hij => ?_⟩
  simp [BQ, hij.le, not_le.2 hij]

/-- HExcl for δ0 with the upper triangular Bruin matrices. -/
theorem hExcl_T0_BQ : FurioLombardo.M4.HExcl FurioLombardo.M4.T0.data
    (Twist (BQ 0) (BQ 1) (BQ 2) (zkE (dzk 0))) :=
  hExcl_T0 (qFormData_BQ 0) (qFormData_BQ 2) rfl

/-- HExcl for δ1 with the upper triangular Bruin matrices. -/
theorem hExcl_T1_BQ : FurioLombardo.M4.HExcl FurioLombardo.M4.T1.data
    (Twist (BQ 0) (BQ 1) (BQ 2) (zkE (dzk 1))) :=
  hExcl_T1 (qFormData_BQ 0) (qFormData_BQ 2) rfl

end FurioLombardo.Discharge.M4Cert
