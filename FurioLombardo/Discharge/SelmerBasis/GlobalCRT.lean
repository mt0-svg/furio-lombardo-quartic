import FurioLombardo.Discharge.SelmerBasis.GlobalSpanGen
import FurioLombardo.Discharge.SelmerBasis.SUnitDefs
import FurioLombardo.Discharge.SelmerBasis.TowerFacts
import FurioLombardo.Discharge.SelmerBasis.MuTCert
import FurioLombardo.Discharge.SelmerBasis.SUnitMem
import FurioLombardo.Discharge.M3a.K1Concrete

/-!
# `K21[T]/(fRev k) ≅ L42 × N84`

`psi k : AdjoinRoot (fRev k) ≃ₐ[K21] L42 × N84`, `T ↦ (α, β)` with `α = alphaR`, `β = betaR`
(SUnitDefs.lean), from `GlobalGen.crtEquiv`: `fRev k = q k · (C (c k) · h k)`, `q k`, `h k` monic
irreducible of degrees 2 and 4 (hence coprime), `[L42 : K21] + [N84 : K21] = 2 + 4 = 6`.

Data facts, from the kernel checks on SUnitData.lean (TowerFacts.lean, MuTCert.lean, SUnitMem.lean): `aeval_alphaR`, `aeval_betaR`, the four
evaluations `Pgen_alphaR_left` .. `Pgen_betaR_right`, `gensL_ne_zero`, `gensN_ne_zero`, and the
certificate `muT_components` for `μ(T)`.
-/

namespace FurioLombardo.Discharge.SelmerBasis.GlobalK21

open Polynomial FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3a.Bruin FurioLombardo.Discharge.M3b
  FurioLombardo.Discharge.SelmerBasis FurioLombardo.Discharge.SelmerBasis.GlobalGen

/-! ## Data facts (SUnitData.lean) -/

theorem aeval_alphaR (k : Fin 2) : aeval alphaR (q k) = 0 := TowerFacts.aeval_alphaR_q k

theorem aeval_betaR (k : Fin 2) : aeval betaR (h k) = 0 := TowerFacts.aeval_betaR_h k

theorem Pgen_alphaR_left (i : Fin 29) : aeval alphaR (Pgen (Fin.castAdd 53 i)) = gensL i :=
  TowerFacts.Pgen_alphaR_left i

theorem Pgen_alphaR_right (j : Fin 53) : aeval alphaR (Pgen (Fin.natAdd 29 j)) = 1 :=
  TowerFacts.Pgen_alphaR_right j

theorem Pgen_betaR_left (i : Fin 29) : aeval betaR (Pgen (Fin.castAdd 53 i)) = 1 :=
  TowerFacts.Pgen_betaR_left i

theorem Pgen_betaR_right (j : Fin 53) : aeval betaR (Pgen (Fin.natAdd 29 j)) = gensN j :=
  TowerFacts.Pgen_betaR_right j

theorem gensL_ne_zero (i : Fin 29) : gensL i ≠ 0 := FurioLombardo.Discharge.SelmerBasis.gensL_ne_zero i

theorem gensN_ne_zero (j : Fin 53) : gensN j ≠ 0 := FurioLombardo.Discharge.SelmerBasis.gensN_ne_zero j

/-! ## The isomorphism -/

theorem finrank_K21_N84 : Module.finrank K21 N84 = 4 := by
  rw [← Module.finrank_mul_finrank K21 L42 N84, finrank_L42, finrank_N84]

instance finiteDimensional_K21_N84 : FiniteDimensional K21 N84 := Module.Finite.trans L42 N84

theorem q_irreducible (k : Fin 2) : Irreducible (q k) := by
  rw [(q_monic k).irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [q_natDegree])
    (by rw [q_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun a ha => ?_
  rw [mem_roots (q_monic k).ne_zero, IsRoot] at ha
  apply fRev_eval_ne_zero k a
  rw [fRev_eq_q_mul, eval_mul, ha, zero_mul]

theorem q_h_coprime (k : Fin 2) : IsCoprime (q k) (h k) := by
  refine ((q_irreducible k).coprime_iff_not_dvd).mpr fun ⟨g, hg⟩ => ?_
  rcases (h_irreducible k).isUnit_or_isUnit hg with hu | hu
  · have h0 := natDegree_eq_zero_of_isUnit hu
    rw [q_natDegree] at h0
    exact absurd h0 (by norm_num)
  · have hd := congrArg natDegree hg
    rw [natDegree_mul (q_monic k).ne_zero hu.ne_zero, natDegree_eq_zero_of_isUnit hu, h_natDegree,
      q_natDegree] at hd
    exact absurd hd (by norm_num)

theorem finrank_sum (k : Fin 2) :
    Module.finrank K21 L42 + Module.finrank K21 N84 = (fRev k).natDegree := by
  rw [finrank_L42, finrank_K21_N84, fRev_natDegree]

/-- **`K21[T]/(fRev k) ≅ L42 × N84`, `T ↦ (α, β)`.** -/
noncomputable def psi (k : Fin 2) : AdjoinRoot (fRev k) ≃ₐ[K21] L42 × N84 :=
  crtEquiv (c_ne_zero k) (fRev_eq_q_mul k) (q_monic k) (h_monic k) (q_irreducible k)
    (h_irreducible k) (q_h_coprime k) (aeval_alphaR k) (aeval_betaR k) (finrank_sum k)

theorem psi_mk (k : Fin 2) (P : K21[X]) :
    psi k (AdjoinRoot.mk (fRev k) P) = (aeval alphaR P, aeval betaR P) :=
  crtEquiv_mk _ _ _ _ _ _ _ _ _ _ P

theorem aeval_alphaR_fRev (k : Fin 2) : aeval alphaR (fRev k) = 0 := by
  rw [fRev_eq_q_mul, map_mul, aeval_alphaR, zero_mul]

theorem aeval_betaR_fRev (k : Fin 2) : aeval betaR (fRev k) = 0 := by
  rw [fRev_eq_q_mul, map_mul, map_mul, aeval_betaR, mul_zero, mul_zero]

theorem aeval_alphaR_Pgen_ne_zero (s : Fin 82) : aeval alphaR (Pgen s) ≠ 0 := by
  revert s
  show ∀ s : Fin (29 + 53), aeval alphaR (Pgen s) ≠ 0
  intro s
  refine Fin.addCases (fun i => ?_) (fun j => ?_) s
  · rw [Pgen_alphaR_left]
    exact gensL_ne_zero i
  · rw [Pgen_alphaR_right]
    exact one_ne_zero

theorem aeval_betaR_Pgen_ne_zero (s : Fin 82) : aeval betaR (Pgen s) ≠ 0 := by
  revert s
  show ∀ s : Fin (29 + 53), aeval betaR (Pgen s) ≠ 0
  intro s
  refine Fin.addCases (fun i => ?_) (fun j => ?_) s
  · rw [Pgen_betaR_left]
    exact one_ne_zero
  · rw [Pgen_betaR_right]
    exact gensN_ne_zero j

/-- `Pgen s (T)` is a unit of `K21[T]/(fRev k)`. -/
theorem isUnit_mk_Pgen (k : Fin 2) (s : Fin 82) : IsUnit (AdjoinRoot.mk (fRev k) (Pgen s)) :=
  isUnit_mk_of_equiv (psi k) (Pgen s) (by rw [psi_mk]; exact aeval_alphaR_Pgen_ne_zero s)
    (by rw [psi_mk]; exact aeval_betaR_Pgen_ne_zero s)

theorem aeval_ne_zero_of_isCoprime {A : Type*} [CommRing A] [Nontrivial A] [Algebra K21 A]
    {u f : K21[X]} {x : A} (h : IsCoprime u f) (hf : aeval x f = 0) : aeval x u ≠ 0 := by
  intro hu
  obtain ⟨a, b, hab⟩ := h
  have := congrArg (aeval x) hab
  rw [map_add, map_mul, map_mul, hu, hf, map_one, mul_zero, mul_zero, add_zero] at this
  exact zero_ne_one this

/-- The certificate for `μ(T)`: the two components of `(q - c h)(T)`, times one product of the
generators, are `κ y₁²` and `κ y₂²` (`CompCond`, GlobalSpanGen.lean). -/
theorem muT_components (k : Fin 2) :
    CompCond K21 (aeval alphaR (q k - C (c k) * h k)) (aeval betaR (q k - C (c k) * h k))
      (fun s : Fin 82 => aeval alphaR (Pgen s)) (fun s : Fin 82 => aeval betaR (Pgen s)) := by
  exact MuTCert.compCond_muT k (c_ne_zero k)
    (aeval_ne_zero_of_isCoprime (q_h_coprime k).symm (aeval_alphaR k))
    (aeval_ne_zero_of_isCoprime (q_h_coprime k) (aeval_betaR k)) gensL_ne_zero gensN_ne_zero

end FurioLombardo.Discharge.SelmerBasis.GlobalK21
