import FurioLombardo.Discharge.SelmerBasis.Count.AtPlace
import FurioLombardo.Discharge.SelmerBasis.Count.Cert
import FurioLombardo.Discharge.SelmerBasis.Count.KE
import FurioLombardo.Discharge.SelmerBasis.Count.CertData
import FurioLombardo.Discharge.SelmerBasis.AdicPlace

/-!
# Count lane: `CountBound` at `w3` (both twists)

At `w3 = (al3)` (`e = 6`, residue field `𝔽₂`, AdicPlace.lean), `σ = adicCoe w3`:

* base abscissas `x = 0` (twist 0) and `x = 1 + al3⁵` (twist 1, `w3k1x`): `4 fRev_k(x)` is a square
  (`ck_isSquare`, depths 13 and 13 > 2e), `nAt k x ≠ 0` (one Kronecker test each);
* `4 c_k` has odd depth 7, 5 and `46² d` odd depth 11 (`ck_not_isSquare_depth`), so `σ(c k)` and
  `σ(d k)` are not squares and `#A(K_w3)[2] ≤ 4` (`tors_noRoot`);
* `O² / 2 O²` has at most `2^12` representatives (`reps_dyadic`), so
  `countBound_w3 k : CountBound ((fRev k).map (adicCoe w3)) 14`.

Data: Count/CertData.lean (code/selmer-local-conditions/count_certs.gp).
-/

set_option autoImplicit false

open Polynomial NumberField
open scoped FurioLombardo.Discharge.SelmerBasis.Adic
open FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M3a.Bruin (fRev FE c d dnL)
open FurioLombardo.Discharge.SelmerBasis.Count.Data
open FurioLombardo.M2.Special (al3)

namespace FurioLombardo.Discharge.SelmerBasis.Count

/-! ## Kronecker tests -/

theorem ck_w3k0sq1 : checkK 4096 (.sub (.sub (gE 0 (.int 0) 0) (.mul (.lin w3k0sqT) (.lin w3k0sqT)))
    (.mul ((KE.lin al3).pow w3k0sqn) (.lin w3k0sqA))) = true := by
  decide +kernel

theorem ck_w3k0sq2 : checkK 1024 (.sub (.mul (.lin w3k0sqT) (.lin w3k0sqT))
    (.mul ((KE.lin al3).pow w3k0sqm) (.lin w3k0sqB))) = true := by
  decide +kernel

theorem ck_w3k0sq3 : checkK 256 (.sub (.mul (.lin w3k0sqB) (.lin w3k0sqBi))
    (.add (.int 1) (.mul (.lin al3) (.lin w3k0sqCb)))) = true := by
  decide +kernel

theorem ck_w3k1sq1 : checkK 2048 (.sub (.sub (gE 1 (.lin w3k1x) 0) (.mul (.lin w3k1sqT) (.lin w3k1sqT)))
    (.mul ((KE.lin al3).pow w3k1sqn) (.lin w3k1sqA))) = true := by
  decide +kernel

theorem ck_w3k1sq2 : checkK 512 (.sub (.mul (.lin w3k1sqT) (.lin w3k1sqT))
    (.mul ((KE.lin al3).pow w3k1sqm) (.lin w3k1sqB))) = true := by
  decide +kernel

theorem ck_w3k1sq3 : checkK 256 (.sub (.mul (.lin w3k1sqB) (.lin w3k1sqBi))
    (.add (.int 1) (.mul (.lin al3) (.lin w3k1sqCb)))) = true := by
  decide +kernel

theorem ck_w3k0N : checkK 2048 (.sub (.mul (nE 0 (.int 0)) (.lin w3k0Nu)) (.int w3k0D)) = true := by
  decide +kernel

theorem ck_w3k1N : checkK 4096 (.sub (.mul (nE 1 (.lin w3k1x)) (.lin w3k1Nu)) (.int w3k1D)) = true := by
  decide +kernel

theorem ck_w3k0d1 : checkK 2048 (.sub (.sub (.lin (dnL 0)) (.mul (.lin w3k0dT) (.lin w3k0dT)))
    (.mul ((KE.lin al3).pow w3k0dn) (.lin w3k0dA))) = true := by
  decide +kernel

theorem ck_w3k0d2 : checkK 256 (.sub (.mul (.lin w3k0dA) (.lin w3k0dAi))
    (.add (.int 1) (.mul (.lin al3) (.lin w3k0dCa)))) = true := by
  decide +kernel

theorem ck_w3k0d3 : checkK 1024 (.sub (.mul (.lin w3k0dT) (.lin w3k0dT))
    (.mul ((KE.lin al3).pow w3k0dm) (.lin w3k0dB))) = true := by
  decide +kernel

theorem ck_w3k0d4 : checkK 256 (.sub (.mul (.lin w3k0dB) (.lin w3k0dBi))
    (.add (.int 1) (.mul (.lin al3) (.lin w3k0dCb)))) = true := by
  decide +kernel

theorem ck_w3k1d1 : checkK 2048 (.sub (.sub (.lin (dnL 1)) (.mul (.lin w3k1dT) (.lin w3k1dT)))
    (.mul ((KE.lin al3).pow w3k1dn) (.lin w3k1dA))) = true := by
  decide +kernel

theorem ck_w3k1d2 : checkK 256 (.sub (.mul (.lin w3k1dA) (.lin w3k1dAi))
    (.add (.int 1) (.mul (.lin al3) (.lin w3k1dCa)))) = true := by
  decide +kernel

theorem ck_w3k1d3 : checkK 1024 (.sub (.mul (.lin w3k1dT) (.lin w3k1dT))
    (.mul ((KE.lin al3).pow w3k1dm) (.lin w3k1dB))) = true := by
  decide +kernel

theorem ck_w3k1d4 : checkK 256 (.sub (.mul (.lin w3k1dB) (.lin w3k1dBi))
    (.add (.int 1) (.mul (.lin al3) (.lin w3k1dCb)))) = true := by
  decide +kernel

theorem ck_w3k0c1 : checkK 2048 (.sub (.sub (FE 0 0) (.mul (.lin w3k0cT) (.lin w3k0cT)))
    (.mul ((KE.lin al3).pow w3k0cn) (.lin w3k0cA))) = true := by
  decide +kernel

theorem ck_w3k0c2 : checkK 256 (.sub (.mul (.lin w3k0cA) (.lin w3k0cAi))
    (.add (.int 1) (.mul (.lin al3) (.lin w3k0cCa)))) = true := by
  decide +kernel

theorem ck_w3k0c3 : checkK 1024 (.sub (.mul (.lin w3k0cT) (.lin w3k0cT))
    (.mul ((KE.lin al3).pow w3k0cm) (.lin w3k0cB))) = true := by
  decide +kernel

theorem ck_w3k0c4 : checkK 256 (.sub (.mul (.lin w3k0cB) (.lin w3k0cBi))
    (.add (.int 1) (.mul (.lin al3) (.lin w3k0cCb)))) = true := by
  decide +kernel

theorem ck_w3k1c1 : checkK 2048 (.sub (.sub (FE 1 0) (.mul (.lin w3k1cT) (.lin w3k1cT)))
    (.mul ((KE.lin al3).pow w3k1cn) (.lin w3k1cA))) = true := by
  decide +kernel

theorem ck_w3k1c2 : checkK 256 (.sub (.mul (.lin w3k1cA) (.lin w3k1cAi))
    (.add (.int 1) (.mul (.lin al3) (.lin w3k1cCa)))) = true := by
  decide +kernel

theorem ck_w3k1c3 : checkK 1024 (.sub (.mul (.lin w3k1cT) (.lin w3k1cT))
    (.mul ((KE.lin al3).pow w3k1cm) (.lin w3k1cB))) = true := by
  decide +kernel

theorem ck_w3k1c4 : checkK 256 (.sub (.mul (.lin w3k1cB) (.lin w3k1cBi))
    (.add (.int 1) (.mul (.lin al3) (.lin w3k1cCb)))) = true := by
  decide +kernel

/-! ## The inputs at `w3` -/

theorem isPrime_w3 : (Ideal.span {eltO al3} : Ideal (𝓞 K21)).IsPrime :=
  isPrime_of_absNorm_two absNorm_eltO_al3

theorem ne_zero_w3 : eltO al3 ≠ 0 := elt_ne_zero_of_absNorm absNorm_eltO_al3 two_ne_zero

/-- `σ(c k)` is not a square at `w3` (odd depths 7, 5 of `4 c_k`). -/
theorem not_isSquare_c_w3 (k : Fin 2) : ¬ IsSquare (adicCoe w3 (c k)) := by
  have h : ¬ IsSquare (adicCoe w3 (evK (FE k 0))) := by
    fin_cases k
    · exact ck_not_isSquare_depth norm_two_w3 _ _ _ _ _ _ _ _ _ _ ck_w3k0c1 ck_w3k0c2 ck_w3k0c3
        ck_w3k0c4 (by decide) (by decide) (by decide)
    · exact ck_not_isSquare_depth norm_two_w3 _ _ _ _ _ _ _ _ _ _ ck_w3k1c1 ck_w3k1c2 ck_w3k1c3
        ck_w3k1c4 (by decide) (by decide) (by decide)
  refine not_isSquare_of_sq_mul (u := (2 : w3.adicCompletion K21)) ?_ h
  rw [← four_mul_c, map_mul, map_ofNat]; norm_num

/-- `σ(d k)` is not a square at `w3` (odd depth 11 of `46² d`). -/
theorem not_isSquare_d_w3 (k : Fin 2) : ¬ IsSquare (adicCoe w3 (d k)) := by
  have h : ¬ IsSquare (adicCoe w3 (evK (.lin (dnL k)))) := by
    fin_cases k
    · exact ck_not_isSquare_depth norm_two_w3 _ _ _ _ _ _ _ _ _ _ ck_w3k0d1 ck_w3k0d2 ck_w3k0d3
        ck_w3k0d4 (by decide) (by decide) (by decide)
    · exact ck_not_isSquare_depth norm_two_w3 _ _ _ _ _ _ _ _ _ _ ck_w3k1d1 ck_w3k1d2 ck_w3k1d3
        ck_w3k1d4 (by decide) (by decide) (by decide)
  refine not_isSquare_of_sq_mul (u := (46 : w3.adicCompletion K21)) ?_ h
  rw [evK_lin, ← d_mul, map_mul, map_pow, map_ofNat]

/-- `CountBound` at `w3` from the data at a base abscissa `evK xE`. -/
theorem countBound_w3_of (k : Fin 2) [GoodSextic ((fRev k).map (adicCoe w3))] (xE : KE)
    (hsq : IsSquare (adicCoe w3 (evK (gE k xE 0)))) (hne : evK (gE k xE 0) ≠ 0)
    (hN : nAt k (evK xE) ≠ 0) : CountBound ((fRev k).map (adicCoe w3)) 14 := by
  have hsq' : IsSquare (adicCoe w3 ((fRev k).eval (evK xE))) := by
    refine isSquare_of_sq_mul (u := (2 : w3.adicCompletion K21)) two_ne_zero ?_ hsq
    rw [← fRev_eval_eq, map_mul, map_ofNat]; norm_num
  have hx0 : (fRev k).eval (evK xE) ≠ 0 := fun h => hne (by rw [← fRev_eval_eq, h, mul_zero])
  exact countBound_dyadic (adicCoe w3) isUniformizer_w3 res_w3 (by norm_num)
    two_eq_pow_mul_unit_w3 k (evK xE) hsq' hx0 (not_isSquare_c_w3 k) hN
    (tors_noRoot _ k (not_isSquare_d_w3 k))

/-- **`CountBound` at `w3`, twist 0** (base abscissa `0`). -/
theorem countBound_w3_zero [GoodSextic ((fRev 0).map (adicCoe w3))] :
    CountBound ((fRev 0).map (adicCoe w3)) 14 :=
  countBound_w3_of 0 (.int 0)
    (ck_isSquare norm_two_w3 _ _ _ _ _ _ _ _ ck_w3k0sq1 ck_w3k0sq2 ck_w3k0sq3 (by decide))
    (ck_sq_ne_zero isPrime_w3 ne_zero_w3 _ _ _ _ _ _ _ _ ck_w3k0sq1 ck_w3k0sq2 ck_w3k0sq3
      (by decide))
    (nAt_ne_zero_of_check 0 _ _ _ (by decide) _ ck_w3k0N)

/-- **`CountBound` at `w3`, twist 1** (base abscissa `1 + al3⁵`). -/
theorem countBound_w3_one [GoodSextic ((fRev 1).map (adicCoe w3))] :
    CountBound ((fRev 1).map (adicCoe w3)) 14 :=
  countBound_w3_of 1 (.lin w3k1x)
    (ck_isSquare norm_two_w3 _ _ _ _ _ _ _ _ ck_w3k1sq1 ck_w3k1sq2 ck_w3k1sq3 (by decide))
    (ck_sq_ne_zero isPrime_w3 ne_zero_w3 _ _ _ _ _ _ _ _ ck_w3k1sq1 ck_w3k1sq2 ck_w3k1sq3
      (by decide))
    (nAt_ne_zero_of_check 1 _ _ _ (by decide) _ ck_w3k1N)

/-- **`CountBound` at `w3`** for both twists. -/
theorem countBound_w3 (k : Fin 2) [GoodSextic ((fRev k).map (adicCoe w3))] :
    CountBound ((fRev k).map (adicCoe w3)) 14 := by
  fin_cases k
  · exact @countBound_w3_zero (by assumption)
  · exact @countBound_w3_one (by assumption)

end FurioLombardo.Discharge.SelmerBasis.Count
