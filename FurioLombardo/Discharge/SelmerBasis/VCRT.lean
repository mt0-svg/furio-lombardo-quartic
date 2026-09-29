import FurioLombardo.Discharge.SelmerBasis.VGen
import FurioLombardo.Discharge.SelmerBasis.VLocal
import FurioLombardo.Discharge.SelmerBasis.GlobalCRT

/-!
# `K_v[T]/(fRev k)^σ ≅ F1 × F2` (lane selmer-v)

For an Eisenstein component `F1 = CF σ E` at `v` (`σ = M4Cert.σ : K21 →+* Kv`) with a model `M` of `ω`
and square root data `S` (PlaceUCert.lean), `F2 = UF σ E` is a `Kv`-algebra through `F1`, of dimension
`4`. The roots `τ1 = iL α` of `q^σ` and `τ2 = iNv β` of `h^σ` give, by `GlobalGen.crtEquiv` (`q^σ`
irreducible by `irreducible_q_v`, `h^σ` by `irr_Kv`, coprime, `2 + 4 = 6`), the isomorphism
`psiV : K_v[T]/(fRev k)^σ ≃ₐ[Kv] F1 × F2` with `psiV_mk`: the class of `P^σ` goes to
`(iL (P α), iNv (P β))`; and `evV`, the units map `(K_v[T]/(fRev k)^σ)ˣ ≃* F1ˣ × F2ˣ`.
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis.V

open Polynomial FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M4Cert
  FurioLombardo.Discharge.M3a.Bruin FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis
  FurioLombardo.Discharge.SelmerBasis.GlobalK21

variable {E : EisData} [Fact (∀ r : Kv, r ^ 2 ≠ σ (zkE E.A) + σ (zkE E.B) * r)]
  [Fact (∀ r : CF σ E, r ^ 2 ≠ -1 + 1 * r)]

/-- `F2` as a `Kv`-algebra, through `F1`. -/
noncomputable instance instAlgKvUF : Algebra Kv (UF σ E) :=
  ((algebraMap (CF σ E) (UF σ E)).comp (algebraMap Kv (CF σ E))).toAlgebra

instance instTowerKvUF : IsScalarTower Kv (CF σ E) (UF σ E) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_Kv_UF (x : Kv) :
    algebraMap Kv (UF σ E) x = algebraMap (CF σ E) (UF σ E) (algebraMap Kv (CF σ E) x) := rfl

theorem finrank_CF : Module.finrank Kv (CF σ E) = 2 := by
  exact QuadraticAlgebra.finrank_eq_two _ _

theorem finrank_UF : Module.finrank Kv (UF σ E) = 4 := by
  have h2 : Module.finrank (CF σ E) (UF σ E) = 2 := QuadraticAlgebra.finrank_eq_two _ _
  rw [← Module.finrank_mul_finrank Kv (CF σ E) (UF σ E), finrank_CF, h2]

instance instFinKvUF : FiniteDimensional Kv (UF σ E) := by
  exact Module.Finite.trans (CF σ E) (UF σ E)

/-- `fRev k = q · (c · h)` over `Kv`. -/
theorem fRev_map_eq (k : Fin 2) :
    (fRev k).map σ = (q k).map σ * (C (σ (c k)) * (h k).map σ) := by
  rw [fRev_eq_mul]
  simp only [Polynomial.map_mul, Polynomial.map_C]
  ring

theorem qh_coprime_v (k : Fin 2) : IsCoprime ((q k).map σ) ((h k).map σ) := by
  have hqd : ((q k).map σ).natDegree = 2 := by rw [natDegree_map, q_natDegree]
  have hhd : ((h k).map σ).natDegree = 4 := by rw [natDegree_map, h_natDegree]
  refine ((irreducible_q_v k).coprime_iff_not_dvd).mpr fun ⟨g, hg⟩ => ?_
  rcases (irr_Kv k).isUnit_or_isUnit hg with hu | hu
  · have h0 := natDegree_eq_zero_of_isUnit hu
    rw [hqd] at h0
    exact absurd h0 (by norm_num)
  · have hd := congrArg natDegree hg
    rw [natDegree_mul ((q_monic k).map σ).ne_zero hu.ne_zero, natDegree_eq_zero_of_isUnit hu, hhd,
      hqd] at hd
    exact absurd hd (by norm_num)

variable (M : LModel) (S : SqrtV) (hW : WPlace σ E) (hM : M.ok E = true) (hS : S.ok E M = true)

/-- `τ1 = iL α`, the root of `q^σ` in `F1`. -/
noncomputable def tau1 : CF σ E := iL σ E M hM alphaR

/-- `τ2 = iNv β`, the root of `h^σ` in `F2`. -/
noncomputable def tau2 : UF σ E := iNv σ E M hW hM S hS betaR

/-- `iNv` over `K21` is `σ` followed by `Kv → F2`. -/
theorem iNv_comp_algebraMap :
    (iNv σ E M hW hM S hS).comp (algebraMap K21 N84) = (algebraMap Kv (UF σ E)).comp σ := by
  exact RingHom.ext fun x => iNv_algebraMap hW hM hS x

/-- `P^σ (τ1) = iL (P α)`. -/
theorem aeval_tau1 (P : K21[X]) : aeval (tau1 M hM) (P.map σ) = iL σ E M hM (aeval alphaR P) := by
  rw [aeval_def, tau1, eval₂_map_eq_psi σ (iL σ E M hM) (iL_comp_algebraMap hM)]

/-- `P^σ (τ2) = iNv (P β)`. -/
theorem aeval_tau2 (P : K21[X]) :
    aeval (tau2 M S hW hM hS) (P.map σ) = iNv σ E M hW hM S hS (aeval betaR P) := by
  rw [aeval_def, tau2, eval₂_map_eq_psi σ (iNv σ E M hW hM S hS) (iNv_comp_algebraMap M S hW hM hS)]

theorem aeval_tau1_q (k : Fin 2) : aeval (tau1 M hM) ((q k).map σ) = 0 := by
  rw [aeval_tau1, aeval_alphaR, map_zero]

theorem aeval_tau2_h (k : Fin 2) : aeval (tau2 M S hW hM hS) ((h k).map σ) = 0 := by
  rw [aeval_tau2, aeval_betaR, map_zero]

theorem finrank_sum_v (k : Fin 2) :
    Module.finrank Kv (CF σ E) + Module.finrank Kv (UF σ E) = ((fRev k).map σ).natDegree := by
  rw [finrank_CF, finrank_UF, natDegree_map, fRev_natDegree]

theorem σ_c_ne_zero (k : Fin 2) : σ (c k) ≠ 0 := (map_ne_zero σ).mpr (c_ne_zero k)

/-- **`K_v[T]/(fRev k)^σ ≅ F1 × F2`**, `T ↦ (τ1, τ2)`. -/
noncomputable def psiV (k : Fin 2) : AdjoinRoot ((fRev k).map σ) ≃ₐ[Kv] CF σ E × UF σ E :=
  GlobalGen.crtEquiv (σ_c_ne_zero k) (fRev_map_eq k) ((q_monic k).map σ) ((h_monic k).map σ)
    (irreducible_q_v k) (irr_Kv k) (qh_coprime_v k) (aeval_tau1_q M hM k) (aeval_tau2_h M S hW hM hS k)
    (finrank_sum_v k)

theorem psiV_mk (k : Fin 2) (P : K21[X]) :
    psiV M S hW hM hS k (AdjoinRoot.mk _ (P.map σ)) =
      (iL σ E M hM (aeval alphaR P), iNv σ E M hW hM S hS (aeval betaR P)) := by
  rw [psiV, GlobalGen.crtEquiv_mk, aeval_tau1, aeval_tau2]

theorem psiV_algebraMap (k : Fin 2) (x : Kv) :
    psiV M S hW hM hS k (algebraMap Kv (AdjoinRoot ((fRev k).map σ)) x) =
      (algebraMap Kv (CF σ E) x, algebraMap Kv (UF σ E) x) :=
  (psiV M S hW hM hS k).commutes x

/-- **The units map** `(K_v[T]/(fRev k)^σ)ˣ ≃* F1ˣ × F2ˣ`. -/
noncomputable def evV (k : Fin 2) : (AdjoinRoot ((fRev k).map σ))ˣ ≃* (CF σ E)ˣ × (UF σ E)ˣ :=
  (Units.mapEquiv (psiV M S hW hM hS k).toRingEquiv.toMulEquiv).trans MulEquiv.prodUnits

theorem evV_fst (k : Fin 2) (u : (AdjoinRoot ((fRev k).map σ))ˣ) :
    (((evV M S hW hM hS k u).1 : (CF σ E)ˣ) : CF σ E) = (psiV M S hW hM hS k (u : AdjoinRoot _)).1 := by
  rfl

theorem evV_snd (k : Fin 2) (u : (AdjoinRoot ((fRev k).map σ))ˣ) :
    (((evV M S hW hM hS k u).2 : (UF σ E)ˣ) : UF σ E) = (psiV M S hW hM hS k (u : AdjoinRoot _)).2 := by
  rfl

end FurioLombardo.Discharge.SelmerBasis.V
