import Mathlib
import FurioLombardo.Discharge.KvArith.Cantor
import FurioLombardo.Discharge.R7.ChartKv

/-!
# Reading a class in R7's chart (lane lean-kv-arith, D6)

For a base point `D : R7.SetupKv` of the model `F = D.f ∘ (X - a)` and an admissible `M`, R7's chart is
`psi z = chartCls z · E0⁻¹`, `chartCls z = [⟨uT(π^M z)(X - a), Y - vPt z (X - a)⟩]` (R7/Psi.lean). Here:

* `Mum.chartT`, `Mum.chartW`: a pair `[u, v]` of the model `F`, read in the translated coordinates
  (`u = uT t ∘ (X - a)`, `v = w ∘ (X - a)`), with `Mum.cls_eq_clsA`;
* `chartPt`: for chart coordinates `t` with `‖tᵢ‖ ≤ ‖pv‖^(M+4)`, the point `z = t/pv^M` of
  `B1 (fglO) pv⁴` (`chartPt_mem_B1`, `tPt_chartPt`);
* `clsA_eq_chartCls`: the class `[uT t, w]` is the chart class of `z` as soon as `w + vPt z` is coprime to
  `uT t` (`resQ ≠ 0`): the two square roots of `f` modulo `uT t` then agree (Hensel uniqueness in
  `K[X]/(uT t)`);
* `psi_chartPt`: a pair whose class is `Q · E0` gives `Q = psi z`;
* `resQ_ne_zero_of_norm`: the norm criterion for `resQ ≠ 0`.
-/

namespace FurioLombardo.Discharge.KvArith

open Polynomial FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M4Cert
open FurioLombardo.Discharge.R7 FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.UnitBall

/-- The chart coordinates `t = (u₁ + 2a, u₀ + a u₁ + a²)` of a pair of the model `F`. -/
noncomputable def Mum.chartT {K : Type*} [Field K] (a : K) (D : Mum K) : Fin 2 → K :=
  ![D.u1 + 2 * a, D.u0 + a * D.u1 + a ^ 2]

/-- The translated `v`: `w = v ∘ (X + a)`. -/
noncomputable def Mum.chartW {K : Type*} [Field K] (a : K) (D : Mum K) : K[X] :=
  C D.v1 * X + C (D.v0 + a * D.v1)

section Reading

variable {K : Type*} [Field K] {F f0 : K[X]} [GoodSextic F] {a : K}

theorem Mum.u_eq_comp (a : K) (D : Mum K) : D.u = (uT (D.chartT a)).comp (X - C a) := by
  unfold Mum.u uT Mum.chartT
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_comp, mul_comp, pow_comp, X_comp,
    C_comp, C_add, C_mul, C_pow, C_ofNat, ofNat_comp]
  ring

theorem Mum.v_eq_comp (a : K) (D : Mum K) : D.v = (D.chartW a).comp (X - C a) := by
  unfold Mum.v Mum.chartW
  simp [add_comp, mul_comp, X_comp, C_comp, C_add, C_mul]
  ring

theorem Mum.chartW_degree (a : K) (D : Mum K) : (D.chartW a).degree < 2 := by
  unfold Mum.chartW
  exact Polynomial.degree_linear_lt

/-- The pair on `F` is a translated chart class. -/
theorem mk0_mumford_eq {u u' v v' : K[X]} (hu : u ≠ 0) (hu' : u' ≠ 0) (h1 : u = u') (h2 : v = v') :
    ClassGroup.mk0 (mumford0 F hu v) = ClassGroup.mk0 (mumford0 F hu' v') := by
  subst h1 h2
  rfl

theorem Mum.cls_eq_clsA (a : K) (D : Mum K) : D.cls F = clsA F a (D.chartT a) (D.chartW a) :=
  mk0_mumford_eq _ _ (Mum.u_eq_comp a D) (Mum.v_eq_comp a D)

/-- `clsA` only depends on `v` modulo `uT t`. -/
theorem clsA_congr (a : K) (t : Fin 2 → K) {v v' : K[X]} (h : uT t ∣ v' - v) :
    clsA F a t v' = clsA F a t v := by
  unfold clsA
  apply mk0_mumford_congr
  have := map_dvd (compRingHom (X - C a)) h
  simpa only [coe_compRingHom_apply, sub_comp] using this

/-- The chart coordinates as the translated pair (`Mum.shift`, the program run on balls and Taylor models). -/
theorem Mum.chartT_eq_shift (a : K) (D : Mum K) :
    D.chartT a = ![(Mum.shift (fieldOps K) a D).u1, (Mum.shift (fieldOps K) a D).u0] := by
  funext i
  fin_cases i <;> simp [Mum.chartT, Mum.shift, fieldOps] <;> ring

theorem Mum.chartW_eq_shift (a : K) (D : Mum K) : D.chartW a = (Mum.shift (fieldOps K) a D).v := by
  rfl

/-- The curve condition in translated coordinates. -/
theorem Mum.dvd_chart (hf : f0.comp (X - C a) = F) {D : Mum K} (hD : D.OnCurve F) :
    uT (D.chartT a) ∣ f0 - D.chartW a ^ 2 := by
  have hC2 : C (2 : K) = (2 : K[X]) := by
    simpa using map_natCast (C : K →+* K[X]) 2
  have hu_eq : D.u = (uT (D.chartT a)).comp (X - C a) := by
    dsimp [Mum.u, uT, Mum.chartT]
    simp [add_comp, mul_comp, X_comp, C_comp]
    ring_nf
    simp [hC2]
  have hv_eq : D.v = (D.chartW a).comp (X - C a) := by
    dsimp [Mum.v, Mum.chartW]
    simp [add_comp, mul_comp, X_comp, C_comp]
    ring_nf
  have hF : F.comp (X + C a) = f0 := by
    calc
      F.comp (X + C a) = (f0.comp (X - C a)).comp (X + C a) := by rw [hf]
      _ = f0.comp ((X - C a).comp (X + C a)) := by rw [Polynomial.comp_assoc]
      _ = f0.comp X := by
        simp
      _ = f0 := by simp
  have h_dvd : D.u.comp (X + C a) ∣ (F - D.v ^ 2).comp (X + C a) :=
    map_dvd (Polynomial.compRingHom (X + C a)) hD
  have h_right : (F - D.v ^ 2).comp (X + C a) = f0 - (D.chartW a) ^ 2 := by
    calc
      (F - D.v ^ 2).comp (X + C a) = F.comp (X + C a) - (D.v ^ 2).comp (X + C a) := by
        simpa using map_sub (Polynomial.compRingHom (X + C a)) F (D.v ^ 2)
      _ = f0 - (D.v ^ 2).comp (X + C a) := by rw [hF]
      _ = f0 - ((D.v.comp (X + C a)) ^ 2) := by
        simpa using map_pow (Polynomial.compRingHom (X + C a)) D.v 2
      _ = f0 - (((D.chartW a).comp (X - C a)).comp (X + C a)) ^ 2 := by rw [hv_eq]
      _ = f0 - (D.chartW a) ^ 2 := by
        have hcomp : (X - C a).comp (X + C a) = X := by simp
        simp [Polynomial.comp_assoc, hcomp]
  have h_left : D.u.comp (X + C a) = uT (D.chartT a) := by
    calc
      D.u.comp (X + C a) = ((uT (D.chartT a)).comp (X - C a)).comp (X + C a) := by rw [hu_eq]
      _ = (uT (D.chartT a)).comp ((X - C a).comp (X + C a)) := by rw [Polynomial.comp_assoc]
      _ = (uT (D.chartT a)).comp X := by simp
      _ = uT (D.chartT a) := by simp
  rw [h_left, h_right] at h_dvd
  exact h_dvd

end Reading

/-- `resQ t y ≠ 0` when `y₀` dominates: `‖t₀ y₀ y₁‖ < ‖y₀‖²` and `‖t₁ y₁²‖ < ‖y₀‖²`. -/
theorem resQ_ne_zero_of_norm {t : Fin 2 → Kv} {y : Kv[X]} (h0 : y.coeff 0 ≠ 0)
    (h1 : ‖t 0 * y.coeff 0 * y.coeff 1‖ < ‖y.coeff 0‖ ^ 2) (h2 : ‖t 1 * y.coeff 1 ^ 2‖ < ‖y.coeff 0‖ ^ 2) :
    resQ t y ≠ 0 := by
  have hy0 : 0 < ‖y.coeff 0‖ ^ 2 := by positivity
  have hsmall : ‖- (t 0 * y.coeff 0 * y.coeff 1) + t 1 * y.coeff 1 ^ 2‖ < ‖y.coeff 0 ^ 2‖ := by
    rw [norm_pow]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ h2)
    rwa [norm_neg]
  intro h0
  have e : resQ t y = y.coeff 0 ^ 2 + (- (t 0 * y.coeff 0 * y.coeff 1) + t 1 * y.coeff 1 ^ 2) := by
    rw [resQ]
    ring
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hsmall)
  rw [← e, h0, norm_zero, max_eq_left hsmall.le, norm_pow] at this
  exact (ne_of_gt hy0) this.symm

section Chart

variable (Dk : SetupKv) [GoodSextic Dk.f] {F : Kv[X]} [GoodSextic F] {a : Kv}

theorem chartPt_norm_le {M : ℕ} {t : Fin 2 → Kv} (ht : ∀ i, ‖t i‖ ≤ ‖pv‖ ^ (M + 4)) (i : Fin 2) :
    ‖t i / pv ^ M‖ ≤ ‖pv‖ ^ 4 := by
  rw [norm_div, norm_pow, div_le_iff₀ (pow_pos norm_pv_pos M), ← pow_add, add_comm 4 M]
  exact ht i

theorem chartPt_mem_unitBall {M : ℕ} {t : Fin 2 → Kv} (ht : ∀ i, ‖t i‖ ≤ ‖pv‖ ^ (M + 4))
    (i : Fin 2) : t i / pv ^ M ∈ unitBall Kv :=
  mem_unitBall_iff.mpr ((chartPt_norm_le ht i).trans (pow_le_one₀ (norm_nonneg _) norm_pv_lt_one.le))

theorem chartPt_mem_maximalIdeal {M : ℕ} {t : Fin 2 → Kv} (ht : ∀ i, ‖t i‖ ≤ ‖pv‖ ^ (M + 4))
    (i : Fin 2) :
    (⟨t i / pv ^ M, chartPt_mem_unitBall ht i⟩ : OKv) ∈ IsLocalRing.maximalIdeal OKv := by
  rw [maximalIdeal_OKv, ← pow_one pvO, mem_span_pvO_pow_iff]
  exact (chartPt_norm_le ht i).trans
    (pow_le_pow_of_le_one (norm_nonneg _) norm_pv_lt_one.le (by norm_num))

/-- The chart point `z = t / pv^M`. -/
noncomputable def chartPt (M : ℕ) (t : Fin 2 → Kv) (ht : ∀ i, ‖t i‖ ≤ ‖pv‖ ^ (M + 4)) :
    Fin 2 → IsLocalRing.maximalIdeal OKv :=
  fun i => ⟨⟨t i / pv ^ M, chartPt_mem_unitBall ht i⟩, chartPt_mem_maximalIdeal ht i⟩

theorem tPt_chartPt (M : ℕ) (t : Fin 2 → Kv) (ht : ∀ i, ‖t i‖ ≤ ‖pv‖ ^ (M + 4)) :
    Dk.toSetup.tPt M (chartPt M t ht) = t := by
  funext i
  have hp : pv ^ M ≠ 0 := pow_ne_zero _ (norm_pos_iff.mp norm_pv_pos)
  change pv ^ M * (t i / pv ^ M) = t i
  field_simp

theorem chartPt_mem_B1 {M : ℕ} (hM : Dk.toSetup.Adm M) (t : Fin 2 → Kv)
    (ht : ∀ i, ‖t i‖ ≤ ‖pv‖ ^ (M + 4)) :
    (chartPt M t ht : (Dk.toSetup.fglO hM.good).Points) ∈
      FurioLombardo.Vendor.Toolbox.FormalGroup.B1 (Dk.toSetup.fglO hM.good) (pvO ^ (3 + 1)) := by
  intro j
  rw [mem_span_pvO_pow_iff]
  exact chartPt_norm_le ht j

/-- **Chart identification**: `[uT t, w] = chartCls z` when `resQ t (w + vPt z) ≠ 0`. -/
theorem clsA_eq_chartCls {M : ℕ} (hM : Dk.toSetup.Adm M) {t : Fin 2 → Kv}
    (ht : ∀ i, ‖t i‖ ≤ ‖pv‖ ^ (M + 4)) {w : Kv[X]} (hw : w.degree < 2)
    (hdvd : uT t ∣ Dk.f - w ^ 2) (hres : resQ t (w + Dk.toSetup.vPt hM (chartPt M t ht)) ≠ 0) :
    clsA F a t w = Dk.toSetup.chartCls F a hM (chartPt M t ht) := by
  set z := chartPt M t ht
  have htz : Dk.toSetup.tPt M z = t := tPt_chartPt Dk M t ht
  change clsA F a t w = clsA F a (Dk.toSetup.tPt M z) (Dk.toSetup.vPt hM z)
  rw [htz]
  apply clsA_congr
  have hpt := Dk.toSetup.dvd_pt hM z
  rw [htz] at hpt
  have hdeg : (w + Dk.toSetup.vPt hM z).degree < 2 :=
    lt_of_le_of_lt (degree_add_le _ _) (max_lt hw (Dk.toSetup.vPt_degree hM z))
  have hcop := isCoprime_uT t hdeg hres
  have hprod : uT t ∣ (w - Dk.toSetup.vPt hM z) * (w + Dk.toSetup.vPt hM z) := by
    have := dvd_sub hpt hdvd
    have e : Dk.toSetup.f - Dk.toSetup.vPt hM z ^ 2 - (Dk.f - w ^ 2) =
        (w - Dk.toSetup.vPt hM z) * (w + Dk.toSetup.vPt hM z) := by
      simp only [SetupKv.toSetup]
      ring
    rwa [e] at this
  exact hcop.dvd_of_dvd_mul_right hprod

/-- **Reading `Q` in the chart**: a class `Q · E0` in chart position is `psi z`. -/
theorem psi_chartPt (hF : Dk.f.comp (X - C a) = F) {M : ℕ} (hM : Dk.toSetup.Adm M)
    {t : Fin 2 → Kv} (ht : ∀ i, ‖t i‖ ≤ ‖pv‖ ^ (M + 4)) {w : Kv[X]} (hw : w.degree < 2)
    (hdvd : uT t ∣ Dk.f - w ^ 2) (hres : resQ t (w + Dk.toSetup.vPt hM (chartPt M t ht)) ≠ 0)
    {Q : Pic F} (hQ : clsA F a t w = Q * clsA F a 0 Dk.toSetup.v0) :
    ((Additive.toMul (Dk.toSetup.psi hF hM (chartPt M t ht)) : Jac F) : Pic F) = Q := by
  change Dk.toSetup.chartCls F a hM (chartPt M t ht) * (clsA F a 0 Dk.toSetup.v0)⁻¹ = Q
  rw [← clsA_eq_chartCls Dk hM ht hw hdvd hres, hQ, mul_inv_cancel_right]

end Chart

end FurioLombardo.Discharge.KvArith
