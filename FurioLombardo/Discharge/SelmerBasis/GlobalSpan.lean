import FurioLombardo.Discharge.SelmerBasis.GlobalGens
import FurioLombardo.Discharge.SelmerBasis.SchaeferGlobal
import FurioLombardo.Discharge.SelmerBasis.Interfaces
import FurioLombardo.Discharge.SelmerBasis.SUnitSpan

/-!
# `GlobalSpan (fRev k) (gK k)` from `SUnitSpan`

Every `Q ∈ A(K21)` is `1`, the 2-torsion point `T` of `q k` (the only monic quadratic divisor of
`fRev k`), or `[⟨u, Y - v⟩]` with `u` monic quadratic coprime to `fRev k`, where `μ(Q) = [u(T)]`.
In the last case `schaeferGlobal` gives `κ` with `u(α)/κ`, `u(β)/κ` of even valuation off 14, and
`SUnitSpan` for `L42` and `N84` turns them into squares times products of `gensL` and `gensN`;
`psi k` (GlobalCRT.lean) carries this back to `H (fRev k)`. The point `T` uses the certificate
`muT_components`. `globalSpan_gK` is the statement with SUnitSpan.lean.
-/

namespace FurioLombardo.Discharge.SelmerBasis.GlobalK21

open Polynomial FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.K1 FurioLombardo.Discharge.M3a.Bruin
  FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis FurioLombardo.Discharge.SelmerBasis.GlobalGen

theorem psi_gKu (k : Fin 2) (s : Fin 82) :
    psi k (gKu k s) = (aeval alphaR (Pgen s), aeval betaR (Pgen s)) := by
  rw [gKu_coe, psi_mk]

/-- One field of the reduced case: `SUnitSpan` applied to `u(θ) / κ`. -/
theorem sunit_component {F : Type} [Field F] [NumberField F] [Algebra K21 F] {m : ℕ}
    (gens : Fin m → F) (hS : SUnitSpan F gens) {u : K21[X]} {κ : K21} (hκ : κ ≠ 0) (θ : F)
    (hu : aeval θ u ≠ 0)
    (hev : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      (2 : NumberField.RingOfIntegers F) ∉ P.asIdeal →
      (7 : NumberField.RingOfIntegers F) ∉ P.asIdeal →
      Even (FractionalIdeal.count F P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers F))
        (u.eval₂ (algebraMap K21 F) θ / algebraMap K21 F κ)))) :
    ∃ a : Fin m → ℕ, IsSquare (aeval θ u / algebraMap K21 F κ * ∏ s, gens s ^ a s) := by
  have hκF : algebraMap K21 F κ ≠ 0 := (_root_.map_ne_zero _).mpr hκ
  rw [aeval_def]
  exact hS _ (div_ne_zero (by rwa [← aeval_def]) hκF) hev

/-- **`GlobalSpan (fRev k) (gK k)`**, given `SUnitSpan` for `L42` and `N84`. -/
theorem globalSpan_fRev (k : Fin 2) (hL : SUnitSpan L42 gensL) (hN : SUnitSpan N84 gensN) :
    GlobalSpan (fRev k) (gK k) := by
  show GlobalSpan (fRev k) (m := 29 + 53) (gK k)
  refine globalSpan_of_components (fRev k) (psi k) (gKu k) fun Q => ?_
  simp only [psi_gKu]
  rcases jac_eq_one_or_reduced (fRev k) Q with rfl | ⟨u, v, w, hu, h2, hv, hw, hQu⟩
  · refine ⟨1, by rw [map_one, QuotientGroup.mk_one], 1, one_ne_zero, 0, 1, 1, one_ne_zero,
      one_ne_zero, ?_, ?_⟩ <;> simp
  by_cases huf : IsCoprime u (fRev k)
  · refine ⟨(isUnit_mk_of_isCoprime huf).unit, ?_, ?_⟩
    · have hmu := mu_mumford_of_coprime (fRev k) hu hw huf
      change mu (fRev k) (Q : Pic (fRev k)) = _
      rw [hQu, hmu]
    have hv1 : v.natDegree ≤ 1 := by
      by_cases hv0 : v = 0
      · simp [hv0]
      · have : v.natDegree < 2 := (natDegree_lt_iff_degree_lt hv0).mpr (by exact_mod_cast hv)
        omega
    obtain ⟨κ, hκ, hS⟩ := schaeferGlobal k hu h2 hv1 hw
    have hα : aeval alphaR (fRev k) = 0 := aeval_alphaR_fRev k
    have hβ : aeval betaR (fRev k) = 0 := aeval_betaR_fRev k
    have huα := aeval_ne_zero_of_isCoprime huf hα
    have huβ := aeval_ne_zero_of_isCoprime huf hβ
    obtain ⟨a1, h1⟩ := sunit_component gensL hL hκ alphaR huα
      (hS L42 alphaR (by rw [← aeval_def]; exact hα))
    obtain ⟨a2, h2'⟩ := sunit_component gensN hN hκ betaR huβ
      (hS N84 betaR (by rw [← aeval_def]; exact hβ))
    rw [IsUnit.unit_spec, psi_mk]
    exact components_of_isSquare κ hκ (aeval alphaR u) (aeval betaR u) huα huβ gensL gensN
      gensL_ne_zero gensN_ne_zero _ _ Pgen_alphaR_left Pgen_alphaR_right Pgen_betaR_left
      Pgen_betaR_right a1 a2 h1 h2'
  · have hdvd := dvd_of_not_isCoprime hu h2 (fRev_eval_ne_zero k) huf
    have hv0 := v_eq_zero_of_dvd h2 hdvd GoodSextic.squarefree hw hv
    subst hv0
    have hirr : Irreducible (C (c k) * h k) :=
      (associated_unit_mul_left (h k) (C (c k)) (isUnit_C.mpr (Ne.isUnit (c_ne_zero k)))).symm.irreducible
        (h_irreducible k)
    have hdeg4 : 2 < (C (c k) * h k).natDegree := by
      rw [natDegree_C_mul (c_ne_zero k), h_natDegree]; norm_num
    have huq := eq_of_monic_quadratic_dvd (fRev_eq_q_mul k) (q_monic k) (q_natDegree k) hirr hdeg4
      u hu h2 hdvd
    subst huq
    have hQT : Q = Tpt (fRev k) hu hdvd h2 := Subtype.ext (by rw [hQu, coe_Tpt])
    refine ⟨(isUnit_mk_sub (fRev_eq_q_mul k) GoodSextic.squarefree).unit, ?_, ?_⟩
    · rw [hQT, muJ_Tpt (fRev k) hu hdvd h2 (fRev_eq_q_mul k)]
    rw [IsUnit.unit_spec, psi_mk]
    exact muT_components k

/-- **`GlobalSpan (fRev k) (gK k)`**, with `SUnitSpan` for `L42` and `N84` (SUnitSpan.lean).
Lemma 5.5 of the paper. -/
theorem globalSpan_gK (k : Fin 2) : GlobalSpan (fRev k) (gK k) :=
  globalSpan_fRev k sUnitSpan_L42 sUnitSpan_N84

end FurioLombardo.Discharge.SelmerBasis.GlobalK21
