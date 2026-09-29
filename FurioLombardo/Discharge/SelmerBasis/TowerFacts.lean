import FurioLombardo.Discharge.SelmerBasis.TowerChecks
import FurioLombardo.Discharge.SelmerBasis.SUnitDefs

/-!
# The tower data facts, from the kernel checks of TowerChecks.lean

`α = alphaR ∈ L42` is a root of `q k`, `β = betaR ∈ N84` a root of `h k`, and `Pgen s` takes the
values `(gensL s, 1)` for `s < 29` and `(1, gensN (s - 29))` for `s ≥ 29` at `(α, β)`.
-/

namespace FurioLombardo.Discharge.SelmerBasis.TowerFacts

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3a.Bruin FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis
  FurioLombardo.Discharge.SelmerBasis.Tower FurioLombardo.Discharge.SelmerBasis.TowerChecks

theorem alphaDen_ne_zero : SUnitData.alphaDen ≠ 0 := by decide

theorem betaPowDen_ne_zero : SUnitData.betaPowDen ≠ 0 := by decide

/-- `A = alphaDen α`. -/
theorem evL_alphaL :
    evL (ofL SUnitData.alphaL) = algebraMap K21 L42 (SUnitData.alphaDen : K21) * alphaR := by
  have hD : (SUnitData.alphaDen : K21) ≠ 0 := natCast_ne_zero alphaDen_ne_zero
  apply QuadraticAlgebra.ext
  · simp only [evL, ofL, evK_lin, alphaR, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_eq]
    field_simp
    ring
  · simp only [evL, ofL, evK_lin, alphaR, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.algebraMap_eq]
    field_simp
    ring

/-- `B = betaPowDen β = 2 betaDen β`. -/
theorem evN_twoBetaN :
    evN twoBetaN = algebraMap K21 N84 (SUnitData.betaPowDen : K21) * betaR := by
  have h368 : (SUnitData.betaPowDen : K21) = 2 * (SUnitData.betaDen : K21) := by
    rw [show SUnitData.betaPowDen = 2 * SUnitData.betaDen by decide]
    push_cast
    ring
  have hD : (SUnitData.betaDen : K21) ≠ 0 := natCast_ne_zero (by decide)
  rw [h368, algebraMap_N84]
  apply QuadraticAlgebra.ext
  · simp only [evN, evL, twoBetaN, evK_lin, evK_mul, evK_int, betaR, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_eq]
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_add,
        QuadraticAlgebra.im_add, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, mul_zero,
        zero_mul, add_zero]
      field_simp
      push_cast
      ring
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_add,
        QuadraticAlgebra.im_add, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, mul_zero,
        zero_mul, add_zero]
      field_simp
      push_cast
      ring
  · simp only [evN, evL, twoBetaN, evK_lin, evK_mul, evK_int, betaR, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_eq]
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_add,
        QuadraticAlgebra.im_add, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, mul_zero,
        zero_mul, add_zero]
      field_simp
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_add,
        QuadraticAlgebra.im_add, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, mul_zero,
        zero_mul, add_zero]
      field_simp

theorem tabA_spec : ∀ i, i < 6 →
    evL (tabA.getD i zeroLC) = (algebraMap K21 L42 (SUnitData.alphaDen : K21) * alphaR) ^ i := by
  set A := algebraMap K21 L42 (SUnitData.alphaDen : K21) * alphaR
  have p0 : evL (ofL SUnitData.alphaPow_0) = 1 := (evL_eq_of_checkLC ck_tabA_0).trans evL_one
  have p1 : evL (ofL SUnitData.alphaPow_1) = A := (evL_eq_of_checkLC ck_tabA_1).trans evL_alphaL
  have p2 : evL (ofL SUnitData.alphaPow_2) = A ^ 2 := by
    rw [evL_eq_of_checkLC ck_tabA_2, evL_mulLC, p1]; ring
  have p3 : evL (ofL SUnitData.alphaPow_3) = A ^ 3 := by
    rw [evL_eq_of_checkLC ck_tabA_3, evL_mulLC, p2, p1]; ring
  have p4 : evL (ofL SUnitData.alphaPow_4) = A ^ 4 := by
    rw [evL_eq_of_checkLC ck_tabA_4, evL_mulLC, p3, p1]; ring
  have p5 : evL (ofL SUnitData.alphaPow_5) = A ^ 5 := by
    rw [evL_eq_of_checkLC ck_tabA_5, evL_mulLC, p4, p1]; ring
  intro i hi
  interval_cases i
  · exact p0.trans (pow_zero A).symm
  · exact p1.trans (pow_one A).symm
  · exact p2
  · exact p3
  · exact p4
  · exact p5

theorem tabB_spec : ∀ i, i < 6 →
    evN (tabB.getD i zeroNC) = (algebraMap K21 N84 (SUnitData.betaPowDen : K21) * betaR) ^ i := by
  set B := algebraMap K21 N84 (SUnitData.betaPowDen : K21) * betaR
  have p0 : evN (ofN SUnitData.betaPow_0) = 1 := (evN_eq_of_checkNC ck_tabB_0).trans evN_one
  have p1 : evN (ofN SUnitData.betaPow_1) = B := (evN_eq_of_checkNC ck_tabB_1).trans evN_twoBetaN
  have p2 : evN (ofN SUnitData.betaPow_2) = B ^ 2 := by
    rw [evN_eq_of_checkNC ck_tabB_2, evN_mulNC, p1]; ring
  have p3 : evN (ofN SUnitData.betaPow_3) = B ^ 3 := by
    rw [evN_eq_of_checkNC ck_tabB_3, evN_mulNC, p2, p1]; ring
  have p4 : evN (ofN SUnitData.betaPow_4) = B ^ 4 := by
    rw [evN_eq_of_checkNC ck_tabB_4, evN_mulNC, p3, p1]; ring
  have p5 : evN (ofN SUnitData.betaPow_5) = B ^ 5 := by
    rw [evN_eq_of_checkNC ck_tabB_5, evN_mulNC, p4, p1]; ring
  intro i hi
  interval_cases i
  · exact p0.trans (pow_zero B).symm
  · exact p1.trans (pow_one B).symm
  · exact p2
  · exact p3
  · exact p4
  · exact p5

/-! ## Values of polynomials at `α` and `β` -/

theorem aeval_alphaR_pQ {m n : ℕ} (hm : m ≠ 0) {cs : List KE} (hn : cs.length ≤ n + 1)
    (h6 : cs.length ≤ 6) {t : LC}
    (h : checkLC 1024 (sumPL SUnitData.alphaDen n cs tabA)
      (smulLC (.int ((SUnitData.alphaDen ^ n * m : ℕ) : ℤ)) t) = true) :
    aeval alphaR (pQ m cs) = evL t :=
  aeval_pQ_of_checkL alphaDen_ne_zero hm hn (h6.trans (by decide))
    (fun i hi => tabA_spec i (by omega)) h

theorem aeval_betaR_pQ {m n : ℕ} (hm : m ≠ 0) {cs : List KE} (hn : cs.length ≤ n + 1)
    (h6 : cs.length ≤ 6) {t : NC}
    (h : checkNC 1024 (sumPN SUnitData.betaPowDen n cs tabB)
      (smulNC (.int ((SUnitData.betaPowDen ^ n * m : ℕ) : ℤ)) t) = true) :
    aeval betaR (pQ m cs) = evN t :=
  aeval_pQ_of_checkN betaPowDen_ne_zero hm hn (h6.trans (by decide))
    (fun i hi => tabB_spec i (by omega)) h

theorem aeval_alphaR_q (k : Fin 2) : aeval alphaR (q k) = 0 := by
  fin_cases k
  · exact (aeval_alphaR_pQ (by decide) (by decide) (by decide) ck_qA_0).trans evL_zero
  · exact (aeval_alphaR_pQ (by decide) (by decide) (by decide) ck_qA_1).trans evL_zero

theorem aeval_betaR_h (k : Fin 2) : aeval betaR (h k) = 0 := by
  fin_cases k
  · exact (aeval_betaR_pQ (by decide) (by decide) (by decide) ck_hB_0).trans evN_zero
  · exact (aeval_betaR_pQ (by decide) (by decide) (by decide) ck_hB_1).trans evN_zero

theorem pgen_map_length (s : ℕ) (hs : s < 82) :
    ((SUnitData.pgen.getD s []).map KE.lin).length = 6 := by
  rw [List.length_map, pgen_length s hs]

theorem Pgen_alphaR_left (i : Fin 29) : aeval alphaR (Pgen (Fin.castAdd 53 i)) = gensL i :=
  aeval_alphaR_pQ (pgenDen_ne_zero i (by omega)) (by rw [pgen_map_length i (by omega)])
    (by rw [pgen_map_length i (by omega)]) (ck_pA_left i i.isLt)

theorem Pgen_alphaR_right (j : Fin 53) : aeval alphaR (Pgen (Fin.natAdd 29 j)) = 1 :=
  (aeval_alphaR_pQ (pgenDen_ne_zero (29 + j) (by omega))
    (by rw [pgen_map_length (29 + j) (by omega)]) (by rw [pgen_map_length (29 + j) (by omega)])
    (ck_pA_right j j.isLt)).trans evL_one

theorem Pgen_betaR_left (i : Fin 29) : aeval betaR (Pgen (Fin.castAdd 53 i)) = 1 :=
  (aeval_betaR_pQ (pgenDen_ne_zero i (by omega)) (by rw [pgen_map_length i (by omega)])
    (by rw [pgen_map_length i (by omega)]) (ck_pB_left i i.isLt)).trans evN_one

theorem Pgen_betaR_right (j : Fin 53) : aeval betaR (Pgen (Fin.natAdd 29 j)) = gensN j :=
  aeval_betaR_pQ (pgenDen_ne_zero (29 + j) (by omega))
    (by rw [pgen_map_length (29 + j) (by omega)]) (by rw [pgen_map_length (29 + j) (by omega)])
    (ck_pB_right j j.isLt)

end FurioLombardo.Discharge.SelmerBasis.TowerFacts
