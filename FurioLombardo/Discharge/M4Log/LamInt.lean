import Mathlib
import FurioLombardo.Discharge.M4Log.ChartLog
import FurioLombardo.Discharge.SelmerSpan.Indep
import FurioLombardo.Discharge.M3a.ConcreteRoute
import FurioLombardo.Discharge.M3a.ConcreteInputs
import FurioLombardo.Discharge.M3a.LocalFacts
import FurioLombardo.Discharge.M3a.Refined
import FurioLombardo.Discharge.Analytic.Route

/-!
# `LamInt k` from the values `lamK k (D_i)` (lane lean-m4log)

`lamK k = n⁻¹ π^(M0 + 4) Amat (lamR k)` is bounded on the whole group (`lamR` has values in
`ℤ_[2]⁶`). The seven points `D_i = SelmerSpan.Dpt k i` generate the group modulo `2`
(`GenModTwo`, from R7's `LogChartFin`, the 2-torsion `{0, T}` of lane M3a and the independence
`indep_Dpt` of lane selmer-span). Writing `b = Σ c_i D_i + 2 b'` and iterating, a bound `C` on
`‖lamK‖` improves to `max 1 (C / 2^m)` for every `m` once every `‖lamK k (D_i)‖ ≤ 1`
(`le_one_of_genModTwo`). So `LamInt k` reduces to the seven value bounds `hD` (`lamInt_of`).
-/

open Polynomial
open scoped Matrix
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.M3a.Route
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.R7.ConcreteKv
open FurioLombardo.Discharge.Analytic (GenModTwo IndepModTwo genModTwo_of_chart
  two_torsion_of_localTwoTorsion)
open FurioLombardo.Discharge.M3a (localTwoTorsion_of_L1Inputs indepModTwo_of_mu)
open FurioLombardo.Discharge.M3a.Bruin (fRev q q_monic q_dvd_fRev q_natDegree l1Inputs
  localFacts_Kv)

namespace FurioLombardo.Discharge.M4Log

section Gen

variable {B : Type*} [AddCommGroup B]

/-- **Integrality from generators modulo `2`.** If `f : B →+ K_v²` is bounded, its values at
generators of `B / 2B` are integral, then all its values are integral. -/
theorem le_one_of_genModTwo (f : B →+ (Fin 2 → Kv)) {Dpt : Fin 7 → B} (hgen : GenModTwo Dpt)
    (hD : ∀ i j, ‖f (Dpt i) j‖ ≤ 1) {C : ℝ} (hC : ∀ b j, ‖f b j‖ ≤ C) (b : B) (j : Fin 2) :
    ‖f b j‖ ≤ 1 := by
  have key : ∀ m : ℕ, ∀ b j, ‖f b j‖ ≤ max 1 (C / 2 ^ m) := by
    intro m
    induction m with
    | zero =>
      intro b j
      rw [pow_zero, div_one]
      exact le_max_of_le_right (hC b j)
    | succ m ih =>
      intro b j
      obtain ⟨n, b', hb⟩ := hgen b
      rw [hb, map_add, map_sum, map_nsmul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
      have h1 : ‖∑ i, f (n i • Dpt i) j‖ ≤ 1 := by
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
        rw [map_zsmul, Pi.smul_apply, zsmul_eq_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one
          Kv (n i))).trans (hD i j)
      have h2 : ‖(2 : ℕ) • f b' j‖ ≤ max 1 (C / 2 ^ (m + 1)) := by
        rw [nsmul_eq_mul, norm_mul, Nat.cast_ofNat, norm_two_Kv]
        have h := ih b' j
        rcases le_total 1 (C / 2 ^ m) with hc | hc
        · rw [max_eq_right hc] at h
          refine le_max_of_le_right ?_
          rw [pow_succ, ← div_div]
          linarith
        · rw [max_eq_left hc] at h
          exact le_max_of_le_left (by linarith)
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (le_max_of_le_left h1) h2)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
  have hm' : C / 2 ^ m ≤ 1 := (div_le_one (by positivity)).mpr hm.le
  exact (key m b j).trans (max_le le_rfl hm')

end Gen

/-- A matrix over `K_v` applied to a vector of `O_v²`. -/
theorem norm_mulVec_le (A : Matrix (Fin 2) (Fin 2) Kv) (w : Fin 2 → Kv) (hw : ∀ j, ‖w j‖ ≤ 1)
    (i : Fin 2) : ‖(A *ᵥ w) i‖ ≤ ‖A i 0‖ + ‖A i 1‖ := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul] <;>
    exact mul_le_of_le_one_right (norm_nonneg _) (hw _)

/-- `lamK k` is bounded. -/
theorem norm_lamK_le (k : Fin 2) (b : Additive (Jac ((fRev k).map σ))) (i : Fin 2) :
    ‖lamK k b i‖ ≤
      ‖chartMat k (HR k (IntModelKv.admM0 k)).index i 0‖ +
        ‖chartMat k (HR k (IntModelKv.admM0 k)).index i 1‖ := by
  rw [lamK, dite_eq_left_of_eq_true (eq_true (IntModelKv.admM0 k))]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
    Matrix.mulVecLin_apply]
  refine norm_mulVec_le _ _ (fun j => ?_) i
  obtain ⟨x, hx⟩ := coordEquiv.surjective (lamR k (IntModelKv.admM0 k) b)
  rw [← hx, toKv2_coordEquiv]
  exact FurioLombardo.Vendor.Toolbox.UnitBall.mem_unitBall_iff.mp (x j).2

/-- The 2-torsion of `J(K_v)` is `{0, T_v}` (lane M3a). -/
theorem two_torsion_Kv (k : Fin 2) :
    ∃ T : Additive (Jac ((fRev k).map σ)),
      ∀ b : Additive (Jac ((fRev k).map σ)), (2 : ℕ) • b = 0 → b = 0 ∨ b = T :=
  ⟨_, two_torsion_of_localTwoTorsion
    (localTwoTorsion_of_L1Inputs σ (fRev k) (q_monic k) (q_dvd_fRev k) (q_natDegree k)
      (l1Inputs σ k (localFacts_Kv k).irr (localFacts_Kv k).nsq))⟩

/-- **The seven points `D_i` generate `J(K_v)` modulo `2`.** -/
theorem genModTwo_Dpt (k : Fin 2) : GenModTwo (SelmerSpan.Dpt k) := by
  obtain ⟨T, hT⟩ := two_torsion_Kv k
  exact genModTwo_of_chart (exists_chart k (IntModelKv.admM0 k)).choose_spec.1 hT
    (indepModTwo_of_mu (SelmerSpan.Dpt k) (SelmerSpan.indep_Dpt k))

/-- **`LamInt k` from the seven value bounds at the points `D_i`.** -/
theorem lamInt_of (k : Fin 2) (hD : ∀ i j, ‖lamK k (SelmerSpan.Dpt k i) j‖ ≤ 1) : LamInt k := by
  intro b i
  have hC : ∀ b j, ‖lamK k b j‖ ≤ ∑ i' : Fin 2, ∑ j' : Fin 2,
      ‖chartMat k (HR k (IntModelKv.admM0 k)).index i' j'‖ := fun b j => by
    refine (norm_lamK_le k b j).trans ?_
    simp only [Fin.sum_univ_two]
    fin_cases j <;> simp <;> positivity
  exact le_one_of_genModTwo (lamK k) (genModTwo_Dpt k) hD hC b i

/-- **`ChartLog k (lam k)` from the seven value bounds at the points `D_i`.** -/
theorem chartLog_of_values (k : Fin 2) (hD : ∀ i j, ‖lamK k (SelmerSpan.Dpt k i) j‖ ≤ 1) :
    ChartLog k (lam k) :=
  chartLog_of_lamInt k (lamInt_of k hD)

end FurioLombardo.Discharge.M4Log
