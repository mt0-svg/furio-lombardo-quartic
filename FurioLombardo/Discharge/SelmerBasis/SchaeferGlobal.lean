import FurioLombardo.Discharge.SelmerBasis.SchaeferModel
import FurioLombardo.Discharge.M3a.ConcreteDefs
import FurioLombardo.M2.ZimmertProved
import FurioLombardo.Discharge.SelmerBasis.SchaeferCertGlue

/-!
# Schaefer's lemma for the reversed Prym sextics over K21

For a class `[U, V]` on
`Y² = fRev k` there is one `c ∈ K21ˣ` such that, for every number field `F` over K21, every root
`θ` of `fRev k` in `F` and every prime `P` of `𝓞 F` not above 2 or 7, the multiplicity of
`U(θ) / c` at `P` is even. From `schaefer_global_of_certs` (SchaeferModel.lean) with `D = 14`, the
certificates of SchaeferCertDefs.lean (kernel checked in SchaeferCertCheck.lean, turned into
polynomial identities in SchaeferCertGlue.lean) and `h(K21) = 1` (lane M2).
-/

open Polynomial NumberField FurioLombardo.M1 FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin
open scoped nonZeroDivisors

namespace FurioLombardo.Discharge.SelmerBasis

open Cert

/-- **Global Schaefer lemma for `fRev k`.** Proposition 5.3 of the paper. -/
theorem schaeferGlobal (k : Fin 2) {U V W : K21[X]} (hU : U.Monic) (hU2 : U.natDegree = 2)
    (hV : V.natDegree ≤ 1) (hw : V ^ 2 - fRev k = U * W) :
    ∃ c : K21, c ≠ 0 ∧ ∀ (F : Type) [Field F] [NumberField F] [Algebra K21 F] (θ : F),
      (fRev k).eval₂ (algebraMap K21 F) θ = 0 →
      ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∉ P.asIdeal →
      (7 : 𝓞 F) ∉ P.asIdeal →
      Even (FractionalIdeal.count F P (FractionalIdeal.spanSingleton (𝓞 F)⁰
        (U.eval₂ (algebraMap K21 F) θ / algebraMap K21 F c))) := by
  haveI := FurioLombardo.M2.Proved.isPrincipalIdealRing_M1K21
  have haff := affModel_fRev k
  obtain ⟨c, hc, hall⟩ := schaefer_global_of_certs (K := K21) (f := fRev k)
    (A1 := pK (AL k)) (B1 := pK (BL k)) (π := piK) (a := -469) (e1 := zkE (e1L k))
    (A2 := fun i => pK (A2L k i)) (B2 := fun i => pK (B2L k i))
    (r2 := fun i => zkE (R2L k i) / 4) (y := fun i => zkE (yL k i)) (z := fun i => zkE (zL k i))
    14 31 piK_ne_zero
    (by rw [haff]; exact isIntegral_scaled_pQ _)
    (by rw [haff]; exact natDegree_f1 k)
    (by rw [haff]; exact bez1_f1 k)
    (isIntegral_scaled_pK _)
    (isIntegral_zkE _)
    ⟨zkE (eL k), isIntegral_zkE _, by
      have h := evK_eq_of_check _ _ _ (e_ok k)
      simp only [evK_mul, evK_lin, evK_int] at h
      rw [h, expN]
      push_cast
      ring⟩
    (fun i hi => by rw [haff]; exact bez2_f1 k i hi)
    (fun i hi => isIntegral_scaled_pK _)
    (fun i hi => by
      rw [show (((14 : ℕ) : K21)) ^ 31 * (zkE (R2L ↑k i) / 4) =
        (49 * 14 ^ 29 : K21) * zkE (R2L ↑k i) by
          rw [Nat.cast_ofNat, mul_div_assoc', div_eq_mul_inv, mul_right_comm,
            fourteen_pow_mul_inv]]
      exact IsIntegral.mul (IsIntegral.mul (by exact_mod_cast isIntegral_algebraMap (x := (49 : ℤ)))
        (IsIntegral.pow (by exact_mod_cast isIntegral_algebraMap (x := (14 : ℤ))) _))
        (isIntegral_zkE _))
    (fun i hi => ⟨isIntegral_zkE _, isIntegral_zkE _, by rw [haff]; exact yz_f1 k i hi⟩)
    hU2 hV hw
  refine ⟨c, hc, fun F _ _ _ θ hθ P h2 h7 => hall F θ hθ P ?_⟩
  intro h14
  have e14 : ((14 : ℕ) : 𝓞 F) = 2 * 7 := by norm_num
  rw [e14] at h14
  rcases P.isPrime.mem_or_mem h14 with h | h
  exacts [h2 h, h7 h]

end FurioLombardo.Discharge.SelmerBasis
