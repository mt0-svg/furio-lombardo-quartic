import Mathlib
import FurioLombardo.Discharge.M4Log.IntModelKv
import FurioLombardo.Discharge.M4Box.Amat

/-!
# `ChartLog k (lam k)` from `LamInt k` (lane lean-m4log)

Under `LamInt k`, lane M4's logarithm `lam k` satisfies R7's `ChartLog` at `M = M0 k`
(`admM0`) with `c = 1` and `L` the matrix over `ℤ_[2]` of `v ↦ coordEquiv (A (coordEquiv⁻¹ v))`,
`A = π^(M0 + 4) Amat`. The map is `ℤ_[2]`-linear because `coordEquiv` is the coordinate map of
the `ℚ_[2]`-basis `1, π, π²`, integral because `‖A i j‖ ≤ 1` (`norm_Amat_le_one`), and injective
because `det Amat = -b⁻² ≠ 0`.
-/

open Polynomial
open scoped Matrix
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.R7.ConcreteKv
open FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Vendor.Toolbox.FormalGroup

namespace FurioLombardo.Discharge.M4Log

/-- The coordinates of `coordEquiv` are those of the basis `bKv`. -/
theorem coe_coordEquiv (x : Fin 2 → OKv) (i : Fin 2) (j : Fin 3) :
    (coordEquiv x (finProdFinEquiv (i, j)) : ℚ_[2]) = bKv.equivFun (x i : Kv) j := by
  rw [coordEquiv_apply, coe_okvEquiv_apply]

/-- `toKv2` through the basis `bKv`. -/
theorem toKv2_apply (v : Fin 6 → ℤ_[2]) (i : Fin 2) :
    toKv2 v i = bKv.equivFun.symm (fun j => (v (finProdFinEquiv (i, j)) : ℚ_[2])) := by
  obtain ⟨x, rfl⟩ := coordEquiv.surjective v
  rw [toKv2_coordEquiv]
  simp only [coe_coordEquiv]
  exact (bKv.equivFun.symm_apply_apply _).symm

/-- `toKv2` is `ℤ_[2]`-semilinear. -/
theorem toKv2_smul (c : ℤ_[2]) (v : Fin 6 → ℤ_[2]) :
    toKv2 (c • v) = (c : ℚ_[2]) • toKv2 v := by
  funext i
  rw [toKv2_apply, Pi.smul_apply, toKv2_apply, ← map_smul]
  congr 1

/-- The integral matrix `π^(M0 + 4) Amat` of `lamK` on `ψ(B1)`. -/
noncomputable abbrev Achart (k : Fin 2) : Matrix (Fin 2) (Fin 2) Kv := pv ^ (M0 k + 4) • Amat k

theorem mul_le_one_of_le {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_of_le_one_left hb0 ha).trans hb

theorem norm_Achart_le_one (k : Fin 2) (i j : Fin 2) : ‖Achart k i j‖ ≤ 1 := by
  simp only [Achart, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  exact mul_le_one_of_le (pow_le_one₀ (norm_nonneg _) norm_pv_lt_one.le) (norm_nonneg _)
    (M4Box.norm_Amat_le_one k i j)

theorem norm_Achart_mulVec_le_one (k : Fin 2) (v : Fin 6 → ℤ_[2]) (i : Fin 2) :
    ‖(Achart k *ᵥ toKv2 v) i‖ ≤ 1 := by
  have hv : ∀ j, ‖toKv2 v j‖ ≤ 1 := fun j => by
    obtain ⟨x, rfl⟩ := coordEquiv.surjective v
    rw [toKv2_coordEquiv]
    exact mem_unitBall_iff.mp (x j).2
  have hm : ∀ j, ‖Achart k i j * toKv2 v j‖ ≤ 1 := fun j => by
    rw [norm_mul]
    exact mul_le_one_of_le (norm_Achart_le_one k i j) (norm_nonneg _) (hv j)
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hm 0) (hm 1))

/-- `A (coordEquiv⁻¹ v)` in `O_v²`. -/
noncomputable def chartOK (k : Fin 2) (v : Fin 6 → ℤ_[2]) : Fin 2 → OKv := fun i =>
  ⟨(Achart k *ᵥ toKv2 v) i, mem_unitBall_iff.mpr (norm_Achart_mulVec_le_one k v i)⟩

theorem coe_chartOK (k : Fin 2) (v : Fin 6 → ℤ_[2]) (i : Fin 2) :
    (chartOK k v i : Kv) = (Achart k *ᵥ toKv2 v) i := rfl

theorem chartOK_add (k : Fin 2) (v w : Fin 6 → ℤ_[2]) :
    chartOK k (v + w) = chartOK k v + chartOK k w := by
  funext i
  apply Subtype.ext
  rw [Pi.add_apply, AddMemClass.coe_add, coe_chartOK, coe_chartOK, coe_chartOK, map_add,
    Matrix.mulVec_add, Pi.add_apply]

/-- `v ↦ coordEquiv (A (coordEquiv⁻¹ v))` on `ℤ_[2]⁶`. -/
noncomputable def chartLin (k : Fin 2) : (Fin 6 → ℤ_[2]) →ₗ[ℤ_[2]] (Fin 6 → ℤ_[2]) where
  toFun v := coordEquiv (chartOK k v)
  map_add' v w := by
    rw [chartOK_add, map_add]
  map_smul' c v := by
    funext m
    obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv (m := 2) (n := 3)).surjective m
    apply PadicInt.ext
    rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, PadicInt.coe_mul, coe_coordEquiv,
      coe_coordEquiv, coe_chartOK, coe_chartOK, toKv2_smul, Matrix.mulVec_smul, Pi.smul_apply,
      map_smul, Pi.smul_apply, smul_eq_mul]

theorem toKv2_chartLin (k : Fin 2) (v : Fin 6 → ℤ_[2]) :
    toKv2 (chartLin k v) = Achart k *ᵥ toKv2 v := by
  change toKv2 (coordEquiv (chartOK k v)) = _
  rw [toKv2_coordEquiv]
  rfl

theorem det_Amat_ne_zero (k : Fin 2) : (Amat k).det ≠ 0 := by
  have hb := bK_ne k
  rw [Amat, Matrix.det_smul, Matrix.det_fin_two_of]
  simp only [Fintype.card_fin]
  refine mul_ne_zero (pow_ne_zero _ (inv_ne_zero hb)) ?_
  ring_nf
  exact neg_ne_zero.mpr one_ne_zero

theorem det_Achart_ne_zero (k : Fin 2) : (Achart k).det ≠ 0 := by
  rw [Achart, Matrix.det_smul]
  have hp : pv ≠ 0 := norm_pos_iff.mp norm_pv_pos
  exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hp)) (det_Amat_ne_zero k)

theorem chartLin_injective (k : Fin 2) (v : Fin 6 → ℤ_[2]) (h : chartLin k v = 0) : v = 0 := by
  have h1 : Achart k *ᵥ toKv2 v = 0 := by
    rw [← toKv2_chartLin, h, map_zero]
  have h2 : toKv2 v = 0 := Matrix.eq_zero_of_mulVec_eq_zero (det_Achart_ne_zero k) h1
  exact toKv2_injective (h2.trans (map_zero _).symm)

theorem det_chartMat_ne_zero (k : Fin 2) : (LinearMap.toMatrix' (chartLin k)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, h⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  rw [LinearMap.toMatrix'_mulVec] at h
  exact hv (chartLin_injective k v h)

/-- **`ChartLog k (lam k)` under `LamInt k`.** -/
theorem chartLog_of_lamInt (k : Fin 2) (hI : LamInt k) : ChartLog k (lam k) := by
  refine ⟨M0 k, IntModelKv.admM0 k, 1, LinearMap.toMatrix' (chartLin k), one_ne_zero,
    det_chartMat_ne_zero k, fun z hz y hy => ?_⟩
  rw [one_smul, LinearMap.toMatrix'_mulVec]
  apply toKv2_injective
  rw [toKv2_chartLin, toKv2_coordEquiv]
  exact lam_chart k (IntModelKv.admM0 k) hI z hz y hy

end FurioLombardo.Discharge.M4Log
