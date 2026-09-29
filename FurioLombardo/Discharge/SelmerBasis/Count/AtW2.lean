import FurioLombardo.Discharge.SelmerBasis.Count.AtPlace
import FurioLombardo.Discharge.SelmerBasis.Count.Cert
import FurioLombardo.Discharge.SelmerBasis.Count.KE
import FurioLombardo.Discharge.SelmerBasis.Count.CertData
import FurioLombardo.Discharge.SelmerBasis.Count.AtW2Data
import FurioLombardo.Discharge.SelmerBasis.AdicPlace
import FurioLombardo.Discharge.SelmerBasis.SquareLemmas

/-!
# Count lane: `CountBound` at `w2` (both twists)

At `w2 = (al2)` (`e = 12`, residue field `𝔽₂`, AdicPlace.lean), `σ = adicCoe w2`:

* base abscissas `x = 0` (twist 0) and `x = w2k1x` (twist 1): `4 fRev_k(x)` is a square
  (`ck_isSquare`, depths 25 > 2e), `nAt k x ≠ 0` (one Kronecker test each);
* `4 c_1` has odd depth 11 (`ck_not_isSquare_depth`); `4 c_0` and `46² d` have depth exactly `2e = 24`
  (`ck_not_isSquare_depth_two_e`: `y / t² = 1 + 4 u` with `u` a unit is not a square when the residue
  field is `𝔽₂`), so `σ(c k)` and `σ(d k)` are not squares and `#A(K_w2)[2] ≤ 4` (`tors_noRoot`);
* `O² / 2 O²` has at most `2^24` representatives (`reps_dyadic`), so
  `countBound_w2 k : CountBound ((fRev k).map (adicCoe w2)) 26`.

Data: Count/CertData.lean (code/selmer-local-conditions/count_certs.gp) and Count/AtW2Data.lean
(code/selmer-local-conditions/count_certs_w12.gp, the two depth `2e` certificates).
-/

set_option autoImplicit false

open Polynomial NumberField
open scoped FurioLombardo.Discharge.SelmerBasis.Adic
open FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M3a.Bruin (fRev FE c d dnL)
open FurioLombardo.Discharge.SelmerBasis.Count.Data
open FurioLombardo.M2.Special (al2)

namespace FurioLombardo.Discharge.SelmerBasis.Count

/-! ## The depth `2e` test -/

/-- With residue field `𝔽₂`, `1 + 4 u` is not a square for a unit `u`: a square root gives
`u = y² + y` with `y` integral (`sb_eq_sq_add_self_of_sq`), and `y² + y = y ((y - 1) + 2)` lies in the
maximal ideal for both residues of `y`. -/
theorem not_isSquare_one_add_four_mul {F : Type*} [NormedField F] [IsUltrametricDist F]
    (h2 : (2 : F) ≠ 0) (hres : ∀ y : F, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) {u : F} (hu : ‖u‖ = 1) :
    ¬ IsSquare (1 + 4 * u) := by
  rintro ⟨ξ, hξ⟩
  obtain ⟨y, hy, hm⟩ := sb_eq_sq_add_self_of_sq h2 hu.le (by rw [sq]; exact hξ.symm)
  have h21 : ‖(2 : F)‖ < 1 := by
    have h2le : ‖(2 : F)‖ ≤ 1 := by
      rw [show (2 : F) = 1 + 1 by norm_num]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (by simp)
    rcases hres 2 h2le with h | h
    · exact h
    · exfalso; norm_num at h
  rcases hres y hy with h | h
  · have : ‖y ^ 2 + y‖ < 1 := by
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ h)
      rw [norm_pow]
      exact lt_of_le_of_lt (pow_le_of_le_one (norm_nonneg _) hy two_ne_zero) h
    rw [← hm, hu] at this
    exact lt_irrefl _ this
  · have hy2 : ‖(y - 1) + 2‖ < 1 :=
      lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h h21)
    have : ‖y ^ 2 + y‖ < 1 := by
      rw [show y ^ 2 + y = y * ((y - 1) + 2) by ring, norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hy) hy2
    rw [← hm, hu] at this
    exact lt_irrefl _ this

variable {K : Type*} [Field K] [NumberField K] {α : 𝓞 K}
  {hP : (Ideal.span {α} : Ideal (𝓞 K)).IsPrime} {hα : α ≠ 0}

/-- **Non-square from a depth `2e` certificate** at `primeOf α` with residue field `𝔽₂`:
`y - t² = α^n a`, `t² = α^m a'` with `a`, `a'` units modulo `α` and `n = m + 2e`, where `‖2‖ = ‖α‖^e`. -/
theorem cert_not_isSquare_depth_two_e {e : ℕ}
    (h2 : ‖(2 : (primeOf α hP hα).adicCompletion K)‖ =
      ‖((α : K) : (primeOf α hP hα).adicCompletion K)‖ ^ e)
    (hres : ∀ y : (primeOf α hP hα).adicCompletion K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1)
    {y t : K} {n m : ℕ} {a ai ca a' ai' ca' : 𝓞 K} (hy : y - t ^ 2 = (α : K) ^ n * (a : K))
    (ha : a * ai = 1 + α * ca) (hs : t ^ 2 = (α : K) ^ m * (a' : K))
    (ha' : a' * ai' = 1 + α * ca') (hnm : n = m + 2 * e) :
    ¬ IsSquare (y : (primeOf α hP hα).adicCompletion K) := by
  set w := primeOf α hP hα
  have hb : (1 : 𝓞 K) * 1 = 1 + α * 0 := by ring
  have hu : NormUnif ((α : K) : w.adicCompletion K) := primeOf_normUnif
  set r := ‖((α : K) : w.adicCompletion K)‖
  have hr0 : 0 < r := norm_pos_iff.mpr hu.ne_zero
  have h1 := primeOf_norm (hP := hP) (hα := hα) (x := y - t ^ 2) (n := (n : ℤ)) ha hb
    (by push_cast; rw [mul_one, zpow_natCast]; exact hy)
  have h3 := primeOf_norm (hP := hP) (hα := hα) (x := t ^ 2) (n := (m : ℤ)) ha' hb
    (by push_cast; rw [mul_one, zpow_natCast]; exact hs)
  have hcoe1 : ((y - t ^ 2 : K) : w.adicCompletion K) = (y : w.adicCompletion K) - (t : _) ^ 2 := by
    rw [adic_coe_sub]; congr 1; exact map_pow (adicCoe w) t 2
  have hcoe3 : ((t ^ 2 : K) : w.adicCompletion K) = (t : w.adicCompletion K) ^ 2 :=
    map_pow (adicCoe w) t 2
  rw [hcoe1] at h1
  rw [hcoe3] at h3
  have hs0 : (t : w.adicCompletion K) ^ 2 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h3; exact (zpow_pos hr0 _).ne' h3.symm
  have h20 : (2 : w.adicCompletion K) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h2; exact (pow_pos hr0 e).ne' h2.symm
  have h40 : (4 : w.adicCompletion K) ≠ 0 := by
    rw [show (4 : w.adicCompletion K) = 2 * 2 by norm_num]; exact mul_ne_zero h20 h20
  have hz : ‖(y : w.adicCompletion K) / (t : _) ^ 2 - 1‖ = r ^ (n - m) := by
    rw [div_sub_one hs0, norm_div, h1, h3, ← zpow_natCast, Nat.cast_sub (by omega : m ≤ n),
      zpow_sub₀ hr0.ne']
  have h4 : ‖(4 : w.adicCompletion K)‖ = r ^ (2 * e) := by
    rw [show (4 : w.adicCompletion K) = 2 ^ 2 by norm_num, norm_pow, h2, ← pow_mul, mul_comm]
  set u := ((y : w.adicCompletion K) / (t : _) ^ 2 - 1) / 4 with hudef
  have hu1 : ‖u‖ = 1 := by
    rw [hudef, norm_div, hz, h4, show n - m = 2 * e by omega, div_self (pow_pos hr0 _).ne']
  have ht0 : (t : w.adicCompletion K) ≠ 0 := fun h => hs0 (by rw [h]; ring)
  have hy' : (y : w.adicCompletion K) = (t : _) ^ 2 * (1 + 4 * u) := by
    rw [hudef]; field_simp; ring
  rintro ⟨z, hz⟩
  apply not_isSquare_one_add_four_mul h20 hres hu1
  refine ⟨z / (t : w.adicCompletion K), ?_⟩
  rw [div_mul_div_comm, ← hz, hy']
  field_simp

section Kron

variable {al : List ℤ} {hP' : (Ideal.span {eltO al} : Ideal (𝓞 K21)).IsPrime} {hα' : eltO al ≠ 0}

/-- A Kronecker test `Y = al^n a` with `al^n` read from a checked table entry. -/
theorem ck_eq_tab {Y : KE} {aL alN : List ℤ} {n N : ℕ} (hN : zkE alN = zkE al ^ n)
    (h : checkK N (.sub Y (.mul (.lin alN) (.lin aL))) = true) :
    evK Y = (((eltO al : 𝓞 K21) : K21)) ^ n * ((zkO aL : 𝓞 K21) : K21) := by
  have e := evK_eq_of_check _ _ _ h
  rw [evK_mul, evK_lin, evK_lin, hN] at e
  rw [e, coe_elt, coe_zkO]

/-- Non-square at `primeOf (eltO al)` from a depth `2e` certificate (four Kronecker tests). -/
theorem ck_not_isSquare_depth_two_e {e : ℕ}
    (h2 : ‖(2 : (primeOf (eltO al) hP' hα').adicCompletion K21)‖ =
      ‖(((eltO al : 𝓞 K21) : K21) : (primeOf (eltO al) hP' hα').adicCompletion K21)‖ ^ e)
    (hres : ∀ y : (primeOf (eltO al) hP' hα').adicCompletion K21, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1)
    (Y : KE) (tL aL aiL caL a'L ai'L ca'L alN alM : List ℤ) (n m : ℕ) {N1 N2 N3 N4 : ℕ}
    (hN : zkE alN = zkE al ^ n) (hM : zkE alM = zkE al ^ m)
    (c1 : checkK N1 (.sub (.sub Y (.mul (.lin tL) (.lin tL))) (.mul (.lin alN) (.lin aL))) = true)
    (c2 : checkK N2 (.sub (.mul (.lin aL) (.lin aiL)) (.add (.int 1) (.mul (.lin al) (.lin caL)))) =
      true)
    (c3 : checkK N3 (.sub (.mul (.lin tL) (.lin tL)) (.mul (.lin alM) (.lin a'L))) = true)
    (c4 : checkK N4 (.sub (.mul (.lin a'L) (.lin ai'L)) (.add (.int 1) (.mul (.lin al) (.lin ca'L)))) =
      true)
    (hnm : n = m + 2 * e) :
    ¬ IsSquare ((evK Y : K21) : (primeOf (eltO al) hP' hα').adicCompletion K21) := by
  have e1 := ck_eq_tab hN c1
  have e3 := ck_eq_tab hM c3
  simp only [evK_sub, evK_mul, evK_lin] at e1 e3
  have hy : evK Y - zkE tL ^ 2 = ((eltO al : 𝓞 K21) : K21) ^ n * ((zkO aL : 𝓞 K21) : K21) := by
    rw [sq, e1]
  have hs : zkE tL ^ 2 = ((eltO al : 𝓞 K21) : K21) ^ m * ((zkO a'L : 𝓞 K21) : K21) := by
    rw [sq, e3]
  exact cert_not_isSquare_depth_two_e h2 hres hy (ck_unit c2) hs (ck_unit c4) hnm

end Kron

/-! ## The power table of `al2` -/

/-- One step `al2^(d+1) = al2^d al2` of the table. -/
def w2alStep (d : ℕ) : Bool :=
  checkK w2alPrec (.sub (.lin (w2alPow.getD (d + 1) [])) (.mul (.lin (w2alPow.getD d [])) (.lin al2)))

theorem ck_w2al0 : checkK w2alPrec (.sub (.lin (w2alPow.getD 0 [])) (.int 1)) = true := by
  decide +kernel

theorem ck_w2alStep0 : ∀ d, d < 20 → w2alStep d = true := by
  decide +kernel

theorem ck_w2alStep1 : ∀ d, d < 20 → w2alStep (d + 20) = true := by
  decide +kernel

theorem ck_w2alStep2 : ∀ d, d < 20 → w2alStep (d + 40) = true := by
  decide +kernel

theorem ck_w2alStep3 : ∀ d, d < 20 → w2alStep (d + 60) = true := by
  decide +kernel

theorem w2alStep_all (d : ℕ) (hd : d < 80) : w2alStep d = true := by
  rcases (show d < 20 ∨ (20 ≤ d ∧ d < 40) ∨ (40 ≤ d ∧ d < 60) ∨ (60 ≤ d ∧ d < 80) by omega) with
    h | h | h | h
  · exact ck_w2alStep0 d h
  · have := ck_w2alStep1 (d - 20) (by omega); rwa [Nat.sub_add_cancel h.1] at this
  · have := ck_w2alStep2 (d - 40) (by omega); rwa [Nat.sub_add_cancel h.1] at this
  · have := ck_w2alStep3 (d - 60) (by omega); rwa [Nat.sub_add_cancel h.1] at this

/-- The table holds the powers of `al2`. -/
theorem w2alPow_spec : ∀ d, d ≤ 80 → zkE (w2alPow.getD d []) = zkE al2 ^ d
  | 0, _ => by simpa using evK_eq_of_check _ _ _ ck_w2al0
  | d + 1, h => by
    have e := evK_eq_of_check _ _ _ (w2alStep_all d (by omega))
    simp only [evK_lin, evK_mul] at e
    rw [e, w2alPow_spec d (by omega), pow_succ]

/-! ## Kronecker tests -/

theorem ck_w2k0sq1 : checkK 8192 (.sub (.sub (gE 0 (.int 0) 0) (.mul (.lin w2k0sqT) (.lin w2k0sqT)))
    (.mul ((KE.lin al2).pow w2k0sqn) (.lin w2k0sqA))) = true := by
  decide +kernel

theorem ck_w2k0sq2 : checkK 2048 (.sub (.mul (.lin w2k0sqT) (.lin w2k0sqT))
    (.mul ((KE.lin al2).pow w2k0sqm) (.lin w2k0sqB))) = true := by
  decide +kernel

theorem ck_w2k0sq3 : checkK 256 (.sub (.mul (.lin w2k0sqB) (.lin w2k0sqBi))
    (.add (.int 1) (.mul (.lin al2) (.lin w2k0sqCb)))) = true := by
  decide +kernel

theorem ck_w2k1sq1 : checkK 4096 (.sub (.sub (gE 1 (.lin w2k1x) 0) (.mul (.lin w2k1sqT) (.lin w2k1sqT)))
    (.mul ((KE.lin al2).pow w2k1sqn) (.lin w2k1sqA))) = true := by
  decide +kernel

theorem ck_w2k1sq2 : checkK 1024 (.sub (.mul (.lin w2k1sqT) (.lin w2k1sqT))
    (.mul ((KE.lin al2).pow w2k1sqm) (.lin w2k1sqB))) = true := by
  decide +kernel

theorem ck_w2k1sq3 : checkK 256 (.sub (.mul (.lin w2k1sqB) (.lin w2k1sqBi))
    (.add (.int 1) (.mul (.lin al2) (.lin w2k1sqCb)))) = true := by
  decide +kernel

theorem ck_w2k0N : checkK 2048 (.sub (.mul (nE 0 (.int 0)) (.lin w2k0Nu)) (.int w2k0D)) = true := by
  decide +kernel

theorem ck_w2k1N : checkK 8192 (.sub (.mul (nE 1 (.lin w2k1x)) (.lin w2k1Nu)) (.int w2k1D)) = true := by
  decide +kernel

theorem ck_w2k1c1 : checkK 4096 (.sub (.sub (FE 1 0) (.mul (.lin w2k1cT) (.lin w2k1cT)))
    (.mul ((KE.lin al2).pow w2k1cn) (.lin w2k1cA))) = true := by
  decide +kernel

theorem ck_w2k1c2 : checkK 512 (.sub (.mul (.lin w2k1cA) (.lin w2k1cAi))
    (.add (.int 1) (.mul (.lin al2) (.lin w2k1cCa)))) = true := by
  decide +kernel

theorem ck_w2k1c3 : checkK 2048 (.sub (.mul (.lin w2k1cT) (.lin w2k1cT))
    (.mul ((KE.lin al2).pow w2k1cm) (.lin w2k1cB))) = true := by
  decide +kernel

theorem ck_w2k1c4 : checkK 256 (.sub (.mul (.lin w2k1cB) (.lin w2k1cBi))
    (.add (.int 1) (.mul (.lin al2) (.lin w2k1cCb)))) = true := by
  decide +kernel

theorem ck_w2d1 : checkK 1090 (.sub (.sub (.lin (dnL 0)) (.mul (.lin w2dT) (.lin w2dT)))
    (.mul (.lin (w2alPow.getD w2dn [])) (.lin w2dA))) = true := by
  decide +kernel

theorem ck_w2d2 : checkK 833 (.sub (.mul (.lin w2dA) (.lin w2dAi))
    (.add (.int 1) (.mul (.lin al2) (.lin w2dCa)))) = true := by
  decide +kernel

theorem ck_w2d3 : checkK 436 (.sub (.mul (.lin w2dT) (.lin w2dT))
    (.mul (.lin (w2alPow.getD w2dm [])) (.lin w2dB))) = true := by
  decide +kernel

theorem ck_w2d4 : checkK 248 (.sub (.mul (.lin w2dB) (.lin w2dBi))
    (.add (.int 1) (.mul (.lin al2) (.lin w2dCb)))) = true := by
  decide +kernel

theorem ck_w2k0c1 : checkK 680 (.sub (.sub (FE 0 0) (.mul (.lin w2k0cT) (.lin w2k0cT)))
    (.mul (.lin (w2alPow.getD w2k0cn [])) (.lin w2k0cA))) = true := by
  decide +kernel

theorem ck_w2k0c2 : checkK 544 (.sub (.mul (.lin w2k0cA) (.lin w2k0cAi))
    (.add (.int 1) (.mul (.lin al2) (.lin w2k0cCa)))) = true := by
  decide +kernel

theorem ck_w2k0c3 : checkK 309 (.sub (.mul (.lin w2k0cT) (.lin w2k0cT))
    (.mul (.lin (w2alPow.getD w2k0cm [])) (.lin w2k0cB))) = true := by
  decide +kernel

theorem ck_w2k0c4 : checkK 241 (.sub (.mul (.lin w2k0cB) (.lin w2k0cBi))
    (.add (.int 1) (.mul (.lin al2) (.lin w2k0cCb)))) = true := by
  decide +kernel

theorem dnL_one : dnL 1 = dnL 0 := by decide

/-! ## The inputs at `w2` -/

theorem isPrime_w2 : (Ideal.span {eltO al2} : Ideal (𝓞 K21)).IsPrime :=
  isPrime_of_absNorm_two absNorm_eltO_al2

theorem ne_zero_w2 : eltO al2 ≠ 0 := elt_ne_zero_of_absNorm absNorm_eltO_al2 two_ne_zero

/-- `σ(c k)` is not a square at `w2` (`4 c_0` of depth `2e = 24`, `4 c_1` of odd depth 11). -/
theorem not_isSquare_c_w2 (k : Fin 2) : ¬ IsSquare (adicCoe w2 (c k)) := by
  have h : ¬ IsSquare (adicCoe w2 (evK (FE k 0))) := by
    fin_cases k
    · exact ck_not_isSquare_depth_two_e norm_two_w2 res_w2 _ _ _ _ _ _ _ _ _ _ _ _
        (w2alPow_spec _ (by decide)) (w2alPow_spec _ (by decide)) ck_w2k0c1 ck_w2k0c2
        ck_w2k0c3 ck_w2k0c4 (by decide)
    · exact ck_not_isSquare_depth norm_two_w2 _ _ _ _ _ _ _ _ _ _ ck_w2k1c1 ck_w2k1c2 ck_w2k1c3
        ck_w2k1c4 (by decide) (by decide) (by decide)
  refine not_isSquare_of_sq_mul (u := (2 : w2.adicCompletion K21)) ?_ h
  rw [← four_mul_c, map_mul, map_ofNat]; norm_num

/-- `σ(d k)` is not a square at `w2` (`46² d` of depth `2e = 24`). -/
theorem not_isSquare_d_w2 (k : Fin 2) : ¬ IsSquare (adicCoe w2 (d k)) := by
  have h0 : ¬ IsSquare (adicCoe w2 (evK (.lin (dnL 0)))) :=
    ck_not_isSquare_depth_two_e norm_two_w2 res_w2 _ _ _ _ _ _ _ _ _ _ _ _
      (w2alPow_spec _ (by decide)) (w2alPow_spec _ (by decide)) ck_w2d1 ck_w2d2 ck_w2d3
      ck_w2d4 (by decide)
  have h : ¬ IsSquare (adicCoe w2 (evK (.lin (dnL k)))) := by
    fin_cases k
    · exact h0
    · simpa [dnL_one] using h0
  refine not_isSquare_of_sq_mul (u := (46 : w2.adicCompletion K21)) ?_ h
  rw [evK_lin, ← d_mul, map_mul, map_pow, map_ofNat]

/-- `CountBound` at `w2` from the data at a base abscissa `evK xE`. -/
theorem countBound_w2_of (k : Fin 2) [GoodSextic ((fRev k).map (adicCoe w2))] (xE : KE)
    (hsq : IsSquare (adicCoe w2 (evK (gE k xE 0)))) (hne : evK (gE k xE 0) ≠ 0)
    (hN : nAt k (evK xE) ≠ 0) : CountBound ((fRev k).map (adicCoe w2)) 26 := by
  have hsq' : IsSquare (adicCoe w2 ((fRev k).eval (evK xE))) := by
    refine isSquare_of_sq_mul (u := (2 : w2.adicCompletion K21)) two_ne_zero ?_ hsq
    rw [← fRev_eval_eq, map_mul, map_ofNat]; norm_num
  have hx0 : (fRev k).eval (evK xE) ≠ 0 := fun h => hne (by rw [← fRev_eval_eq, h, mul_zero])
  exact countBound_dyadic (adicCoe w2) isUniformizer_w2 res_w2 (by norm_num)
    two_eq_pow_mul_unit_w2 k (evK xE) hsq' hx0 (not_isSquare_c_w2 k) hN
    (tors_noRoot _ k (not_isSquare_d_w2 k))

/-- **`CountBound` at `w2`, twist 0** (base abscissa `0`). -/
theorem countBound_w2_zero [GoodSextic ((fRev 0).map (adicCoe w2))] :
    CountBound ((fRev 0).map (adicCoe w2)) 26 :=
  countBound_w2_of 0 (.int 0)
    (ck_isSquare norm_two_w2 _ _ _ _ _ _ _ _ ck_w2k0sq1 ck_w2k0sq2 ck_w2k0sq3 (by decide))
    (ck_sq_ne_zero isPrime_w2 ne_zero_w2 _ _ _ _ _ _ _ _ ck_w2k0sq1 ck_w2k0sq2 ck_w2k0sq3
      (by decide))
    (nAt_ne_zero_of_check 0 _ _ _ (by decide) _ ck_w2k0N)

/-- **`CountBound` at `w2`, twist 1** (base abscissa `w2k1x`). -/
theorem countBound_w2_one [GoodSextic ((fRev 1).map (adicCoe w2))] :
    CountBound ((fRev 1).map (adicCoe w2)) 26 :=
  countBound_w2_of 1 (.lin w2k1x)
    (ck_isSquare norm_two_w2 _ _ _ _ _ _ _ _ ck_w2k1sq1 ck_w2k1sq2 ck_w2k1sq3 (by decide))
    (ck_sq_ne_zero isPrime_w2 ne_zero_w2 _ _ _ _ _ _ _ _ ck_w2k1sq1 ck_w2k1sq2 ck_w2k1sq3
      (by decide))
    (nAt_ne_zero_of_check 1 _ _ _ (by decide) _ ck_w2k1N)

/-- **`CountBound` at `w2`** for both twists. -/
theorem countBound_w2 (k : Fin 2) [GoodSextic ((fRev k).map (adicCoe w2))] :
    CountBound ((fRev k).map (adicCoe w2)) 26 := by
  fin_cases k
  · exact @countBound_w2_zero (by assumption)
  · exact @countBound_w2_one (by assumption)

end FurioLombardo.Discharge.SelmerBasis.Count
