import FurioLombardo.Discharge.SelmerBasis.SUnitCountGen
import FurioLombardo.Discharge.SelmerBasis.SUnitCountData
import FurioLombardo.Discharge.M3b.RamN
import FurioLombardo.Discharge.M3b.RamL
import FurioLombardo.M1.SSet

/-!
# The primes of `L42` and `N84` above 2 and 7 (piece (b))

`S27 F`: the primes of `𝓞 F` containing 2 or 7. Every such prime lies over `(la)`, `(lb)`, `(lc)`
or `(pi7)` of `K21` (lane M1's `eq_of_two_mem`, `eq_of_seven_mem`). With the generic counts of
SUnitCountGen.lean and five certificates (SUnitCountData.lean, code/selmer-global-bound/sunit_count_certs.gp):

* `L42 / K21`: `la`, `lc` ramified (Eisenstein elements `(x + ω) / l^k`), `lb` inert (`γL` of lane
  M3b is `≡ X² + X + 1` modulo `lb`), `pi7` at most two primes: `#S_L ≤ 5`.
* `N84 / L42`: the prime above `la` inert (`γN` of lane M3b, `1 + x_L` and `1 - n_L` lie in it
  because their traces and norms over `K21` lie in `(la)`), `(e')` ramified (`ω² = e'`), the primes
  above `lb`, `lc` and the other prime above `pi7` at most two each: `#S_N ≤ 1 + 2 + 2 + 1 + 2 = 8`.
-/

namespace FurioLombardo.Discharge.SelmerBasis

open NumberField IsDedekindDomain FurioLombardo.M1 FurioLombardo.M1.Kron
  FurioLombardo.Discharge.M3b QuadraticAlgebra SUnitCountData

/-- The primes of `F` above 2 or 7. -/
def S27 (F : Type*) [Field F] [NumberField F] : Set (HeightOneSpectrum (𝓞 F)) :=
  {P | (2 : 𝓞 F) ∈ P.asIdeal ∨ (7 : 𝓞 F) ∈ P.asIdeal}

/-! ### Generic glue -/

section Glue

set_option linter.unusedSectionVars false

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem isMaximal_of_mem_primesOver (p : Ideal (𝓞 K)) [p.IsMaximal] (P : Ideal (𝓞 L))
    (h : P ∈ p.primesOver (𝓞 L)) : P.IsMaximal := by
  obtain ⟨h1, h2⟩ := h
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap (𝓞 K) (𝓞 L))
    (fun x => Algebra.IsIntegral.isIntegral x) P
    (by rw [← Ideal.under_def, ← h2.over]; infer_instance)

theorem mem_primesOver_comap (P : Ideal (𝓞 L)) [hP : P.IsPrime] :
    P ∈ (P.comap (algebraMap (𝓞 K) (𝓞 L))).primesOver (𝓞 L) := ⟨hP, ⟨rfl⟩⟩

theorem comap_isMaximal (P : Ideal (𝓞 L)) [P.IsMaximal] :
    (P.comap (algebraMap (𝓞 K) (𝓞 L))).IsMaximal :=
  Ideal.isMaximal_under_of_isIntegral_of_isMaximal P

theorem ne_bot_of_isMaximal (p : Ideal (𝓞 K)) [hp : p.IsMaximal] : p ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)

/-- At most two primes above `p`. -/
theorem ncard_primesOver_le_two (h2 : Module.finrank K L = 2) (p : Ideal (𝓞 K)) [p.IsMaximal] :
    (p.primesOver (𝓞 L)).ncard ≤ 2 := by
  have h := ncard_primesOver_mul_le h2 p (ne_bot_of_isMaximal p) 1 (fun P hP => by
    have : P.IsPrime := hP.1
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Ideal.ramificationIdx_pos P (𝓞 K)).ne'
      (Ideal.inertiaDeg_pos P (𝓞 K)).ne'))
  simpa using h

/-- One prime above `p` when every prime above `p` has `e f ≥ 2`. -/
theorem ncard_primesOver_le_one (h2 : Module.finrank K L = 2) (p : Ideal (𝓞 K)) [p.IsMaximal]
    (hk : ∀ P ∈ p.primesOver (𝓞 L), 2 ≤ P.ramificationIdx (𝓞 K) * P.inertiaDeg (𝓞 K)) :
    (p.primesOver (𝓞 L)).ncard ≤ 1 := by
  have h := ncard_primesOver_mul_le h2 p (ne_bot_of_isMaximal p) 2 hk
  omega

/-- Eisenstein: one prime above `p`, of the same absolute norm. -/
theorem eisenstein_count (h2 : Module.finrank K L = 2) (p : Ideal (𝓞 K)) [p.IsMaximal]
    (g : 𝓞 K) (hg : p = Ideal.span {g}) (γ : 𝓞 L) (b c u : 𝓞 K)
    (hγ : γ ^ 2 + algebraMap (𝓞 K) (𝓞 L) b * γ + algebraMap (𝓞 K) (𝓞 L) c = 0)
    (hb : b ∈ p) (hc : c = g * u) (hu : u ∉ p) :
    (p.primesOver (𝓞 L)).ncard ≤ 1 ∧
      ∀ P ∈ p.primesOver (𝓞 L), Ideal.absNorm P = Ideal.absNorm p := by
  have hp := ne_bot_of_isMaximal p
  have he := fun P hP => two_le_ramificationIdx_of_eisenstein p hp g hg γ b c u hγ hb hc hu P hP
  refine ⟨ncard_primesOver_le_one h2 p fun P hP => ?_, fun P hP => ?_⟩
  · have : P.IsPrime := hP.1
    have := he P hP
    have := Ideal.inertiaDeg_pos P (𝓞 K)
    nlinarith
  · have hf := inertiaDeg_eq_one_of_two_le_ramificationIdx h2 p hp P hP (he P hP)
    have : P.IsPrime := hP.1
    have : P.LiesOver p := hP.2
    rw [← Ideal.absNorm_pow_inertiaDeg p P, hf, pow_one]

/-- Inert: one prime above `p`. -/
theorem inert_count (h2 : Module.finrank K L = 2) (p : Ideal (𝓞 K)) [p.IsMaximal]
    (hcard : Ideal.absNorm p = 2) (γ : 𝓞 L) (b c : 𝓞 K)
    (hγ : γ ^ 2 + algebraMap (𝓞 K) (𝓞 L) b * γ + algebraMap (𝓞 K) (𝓞 L) c = 0)
    (hb : 1 - b ∈ p) (hc : 1 - c ∈ p) : (p.primesOver (𝓞 L)).ncard ≤ 1 := by
  refine ncard_primesOver_le_one h2 p fun P hP => ?_
  have : P.IsPrime := hP.1
  have := two_le_inertiaDeg_of_inert p hcard γ b c hγ hb hc P hP
  have := Ideal.ramificationIdx_pos P (𝓞 K)
  nlinarith

end Glue

/-! ### Kernel certificates in `K21` -/

theorem ck_q1 : checkK 8192 (.sub (.add (.int 1) (.mul (.mul (eE 0) (.mul ((gE 12).pow 3)
    ((gE 14).pow 6))) (.lin xCL))) (.mul (gE 13) (.lin q1))) = true := by decide +kernel
theorem ck_q2 : checkK 8192 (.sub (.sub (.int 1) (.lin yCL)) (.mul (gE 13) (.lin q2))) = true := by
  decide +kernel
theorem ck_q3 : checkK 4096 (.sub (.add (.int 2) (.lin alL)) (.mul (gE 12) (.lin q3))) = true := by
  decide +kernel
theorem ck_q4 : checkK 4096 (.sub (.add (.add (.int 1) (.lin alL)) (.lin nxL))
    (.mul (gE 12) (.lin q4))) = true := by decide +kernel
theorem ck_q5 : checkK 4096 (.sub (.sub (.int 2) (.lin alnL)) (.mul (gE 12) (.lin q5))) = true := by
  decide +kernel
theorem ck_q6 : checkK 4096 (.sub (.add (.sub (.int 1) (.lin alnL)) (.lin nnL))
    (.mul (gE 12) (.lin q6))) = true := by decide +kernel

theorem ck_bA : checkK 4096 (.sub (.add (.add (.mul (.lin bA) ((gE 12).pow kA)) (.lin xA)) (.lin xA))
    (.int 0)) = true := by decide +kernel
theorem ck_cA : checkK 4096 (.sub (.mul (.lin cA) ((gE 12).pow (2 * kA)))
    (.sub (.mul (.lin xA) (.lin xA)) (.lin epsL))) = true := by decide +kernel
theorem ck_qbA : checkK 4096 (.sub (.lin bA) (.mul (gE 12) (.lin qbA))) = true := by decide +kernel
theorem ck_uA : checkK 4096 (.sub (.lin cA) (.mul (gE 12) (.lin uA))) = true := by decide +kernel
theorem ck_quA : checkK 4096 (.sub (.sub (.int 1) (.lin uA)) (.mul (gE 12) (.lin quA))) = true := by
  decide +kernel
theorem ck_bC : checkK 8192 (.sub (.add (.add (.mul (.lin bC) ((gE 14).pow kC)) (.lin xC)) (.lin xC))
    (.int 0)) = true := by decide +kernel
theorem ck_cC : checkK 8192 (.sub (.mul (.lin cC) ((gE 14).pow (2 * kC)))
    (.sub (.mul (.lin xC) (.lin xC)) (.lin epsL))) = true := by decide +kernel
theorem ck_qbC : checkK 4096 (.sub (.lin bC) (.mul (gE 14) (.lin qbC))) = true := by decide +kernel
theorem ck_uC : checkK 4096 (.sub (.lin cC) (.mul (gE 14) (.lin uC))) = true := by decide +kernel
theorem ck_quC : checkK 4096 (.sub (.sub (.int 1) (.lin uC)) (.mul (gE 14) (.lin quC))) = true := by
  decide +kernel


/-! ### The certificates in `𝓞 K21` -/

section Certs

/-- Read a kernel identity `e = f` in `𝓞 K21`. -/
theorem OK_eq_of_evK {x y : 𝓞 K21} {e f : KE} (hx : evK e = (x : K21)) (hy : evK f = (y : K21))
    (k : ℕ) (h : checkK k (.sub e f) = true) : x = y :=
  RingOfIntegers.coe_injective (hx.symm.trans ((evK_eq_of_check _ _ _ h).trans hy))

theorem coe_two_OK : ((2 : 𝓞 K21) : K21) = 2 := map_ofNat (algebraMap (𝓞 K21) K21) 2

theorem q1_eq : 1 + c0 * xO = gO 13 * zkO q1 :=
  OK_eq_of_evK (by simp only [evK_add, evK_mul, evK_int, evK_lin, evK_eE, evK_gE, evK_pow]; push_cast [c0, xO, coe_zkO]; ring) (by simp) _ ck_q1

theorem q2_eq : 1 - yO = gO 13 * zkO q2 := OK_eq_of_evK (by simp [yO]) (by simp) _ ck_q2

theorem q3_eq : 2 + zkO alL = gO 12 * zkO q3 := OK_eq_of_evK (by simp; exact (map_ofNat _ 2).symm) (by simp) _ ck_q3

theorem q4_eq : 1 + zkO alL + zkO nxL = gO 12 * zkO q4 := OK_eq_of_evK (by simp) (by simp) _ ck_q4

theorem q5_eq : 2 - zkO alnL = gO 12 * zkO q5 := OK_eq_of_evK (by simp; exact (map_ofNat _ 2).symm) (by simp) _ ck_q5

theorem q6_eq : 1 - zkO alnL + zkO nnL = gO 12 * zkO q6 :=
  OK_eq_of_evK (by simp) (by simp) _ ck_q6

theorem bA_eq : zkO bA * gO 12 ^ kA + zkO xA + zkO xA = 0 :=
  OK_eq_of_evK (by simp [evK_pow]) (by simp) _ ck_bA

theorem cA_eq : zkO cA * (gO 12 ^ kA) ^ 2 = zkO xA ^ 2 - epsO :=
  OK_eq_of_evK (by simp [evK_pow, ← pow_mul, mul_comm kA 2]) (by simp [epsO, sq]) _ ck_cA

theorem qbA_eq : zkO bA = gO 12 * zkO qbA := OK_eq_of_evK (by simp) (by simp) _ ck_qbA
theorem uA_eq : zkO cA = gO 12 * zkO uA := OK_eq_of_evK (by simp) (by simp) _ ck_uA
theorem quA_eq : 1 - zkO uA = gO 12 * zkO quA := OK_eq_of_evK (by simp) (by simp) _ ck_quA

theorem bC_eq : zkO bC * gO 14 ^ kC + zkO xC + zkO xC = 0 :=
  OK_eq_of_evK (by simp [evK_pow]) (by simp) _ ck_bC

theorem cC_eq : zkO cC * (gO 14 ^ kC) ^ 2 = zkO xC ^ 2 - epsO :=
  OK_eq_of_evK (by simp [evK_pow, ← pow_mul, mul_comm kC 2]) (by simp [epsO, sq]) _ ck_cC

theorem qbC_eq : zkO bC = gO 14 * zkO qbC := OK_eq_of_evK (by simp) (by simp) _ ck_qbC
theorem uC_eq : zkO cC = gO 14 * zkO uC := OK_eq_of_evK (by simp) (by simp) _ ck_uC
theorem quC_eq : 1 - zkO uC = gO 14 * zkO quC := OK_eq_of_evK (by simp) (by simp) _ ck_quC

end Certs


/-! ### Roots of quadratics in `𝓞 L42` and `𝓞 N84` -/

/-- `(x + ω) / λ` is an integral root of `X² + b X + c` when `b λ = -2x`, `c λ² = x² - ε`. -/
theorem eis_root (x lam b c : 𝓞 K21) (hlam : lam ≠ 0) (hb : b * lam + x + x = 0)
    (hc : c * lam ^ 2 = x ^ 2 - epsO) :
    ∃ γ : 𝓞 L42, γ ^ 2 + algebraMap (𝓞 K21) (𝓞 L42) b * γ + algebraMap (𝓞 K21) (𝓞 L42) c = 0 := by
  set ι := algebraMap K21 L42
  have hl : ι (lam : K21) ≠ 0 := by
    rw [_root_.map_ne_zero, Ne, RingOfIntegers.coe_eq_zero_iff]; exact hlam
  set γL : L42 := (ι (x : K21) + ω) * (ι (lam : K21))⁻¹
  have hγl : γL * ι (lam : K21) = ι (x : K21) + ω := by
    simp only [γL]; rw [mul_assoc, inv_mul_cancel₀ hl, mul_one]
  have hb' : ι (b : K21) * ι (lam : K21) + ι (x : K21) + ι (x : K21) = 0 := by
    have h := congrArg (fun z : 𝓞 K21 => ι (z : K21)) hb
    simpa [map_add, map_mul] using h
  have hc' : ι (c : K21) * ι (lam : K21) ^ 2 = ι (x : K21) ^ 2 - ι (epsO : K21) := by
    have h := congrArg (fun z : 𝓞 K21 => ι (z : K21)) hc
    simpa [map_sub, map_mul, map_pow] using h
  have e3 : (ω : L42) * ω = ι (epsO : K21) := omega_mul_omega_zero
  have heq : γL ^ 2 + ι (b : K21) * γL + ι (c : K21) = 0 := by
    have hne : ι (lam : K21) ^ 2 ≠ 0 := pow_ne_zero 2 hl
    apply (mul_left_inj' hne).mp
    linear_combination (γL * ι (lam : K21) + (ι (x : K21) + ω) - 2 * ι (x : K21)) * hγl +
      (γL * ι (lam : K21)) * hb' + hc' + e3
  have heq' : γL ^ 2 + algebraMap (𝓞 K21) L42 b * γL + algebraMap (𝓞 K21) L42 c = 0 := heq
  have hint : IsIntegral ℤ γL := isIntegral_of_quadratic γL b c heq'
  let γO : 𝓞 L42 := ⟨γL, hint⟩
  have hγ : algebraMap (𝓞 L42) L42 γO = γL := rfl
  refine ⟨γO, ?_⟩
  apply RingOfIntegers.coe_injective
  rw [map_add, map_add, map_mul, map_pow, map_zero, hγ]
  exact heq'

/-- `ω_N ∈ 𝓞 N84` is a root of `X² - e'`. -/
theorem omegaN_root : ∃ γ : 𝓞 N84,
    γ ^ 2 + algebraMap (𝓞 L42) (𝓞 N84) 0 * γ + algebraMap (𝓞 L42) (𝓞 N84) (-eNO) = 0 := by
  have heq : (ω : N84) ^ 2 + algebraMap (𝓞 L42) N84 0 * ω + algebraMap (𝓞 L42) N84 (-eNO) = 0 := by
    have e3 : (ω : N84) * ω = algebraMap L42 N84 eN := omega_mul_omega_zero
    have : algebraMap (𝓞 L42) N84 (-eNO) = -algebraMap L42 N84 eN := by
      rw [map_neg]; rfl
    rw [this, map_zero, zero_mul, add_zero, sq, e3, add_neg_cancel]
  have hint : IsIntegral ℤ (ω : N84) := isIntegral_of_quadratic (K := L42) (ω : N84) 0 (-eNO) heq
  let γO : 𝓞 N84 := ⟨ω, hint⟩
  have hγ : algebraMap (𝓞 N84) N84 γO = ω := rfl
  refine ⟨γO, ?_⟩
  apply RingOfIntegers.coe_injective
  rw [map_add, map_add, map_mul, map_pow, map_zero, hγ]
  exact heq

/-- `1 + x_L` is a root of `X² - (2 + al) X + (1 + al + nx)` in `𝓞 L42`. -/
theorem one_add_xLO_root : (1 + xLO) ^ 2 - algebraMap (𝓞 K21) (𝓞 L42) (2 + zkO alL) * (1 + xLO) +
    algebraMap (𝓞 K21) (𝓞 L42) (1 + zkO alL + zkO nxL) = 0 := by
  have h := mk_half_sq (a := epsK) (zkE alL) (zkE beL) (zkE nxL) (norm_ident ck_nx)
  apply RingOfIntegers.coe_injective
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, map_ofNat]
  have hx : algebraMap (𝓞 L42) L42 xLO = ⟨zkE alL / 2, zkE beL / 2⟩ := rfl
  have e1 : ∀ z : 𝓞 K21, algebraMap (𝓞 L42) L42 (algebraMap (𝓞 K21) (𝓞 L42) z) =
      algebraMap K21 L42 (algebraMap (𝓞 K21) K21 z) := fun _ => rfl
  rw [e1, e1, hx]
  simp only [coe_zkO]
  linear_combination h

/-- `1 - n_L` is a root of `X² - (2 - aln) X + (1 - aln + nn)` in `𝓞 L42`. -/
theorem one_sub_nLO_root : (1 - nLO) ^ 2 - algebraMap (𝓞 K21) (𝓞 L42) (2 - zkO alnL) * (1 - nLO) +
    algebraMap (𝓞 K21) (𝓞 L42) (1 - zkO alnL + zkO nnL) = 0 := by
  have h := mk_half_sq (a := epsK) (zkE alnL) (zkE benL) (zkE nnL) (norm_ident ck_nn)
  apply RingOfIntegers.coe_injective
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, map_ofNat]
  have hx : algebraMap (𝓞 L42) L42 nLO = ⟨zkE alnL / 2, zkE benL / 2⟩ := rfl
  have e1 : ∀ z : 𝓞 K21, algebraMap (𝓞 L42) L42 (algebraMap (𝓞 K21) (𝓞 L42) z) =
      algebraMap K21 L42 (algebraMap (𝓞 K21) K21 z) := fun _ => rfl
  rw [e1, e1, hx]
  simp only [coe_zkO]
  linear_combination h


/-! ### The four primes of `K21` and the primes of `L42` above them -/

/-- The primes of `L42` above `(gO i)`. -/
def PL (i : ℕ) : Set (Ideal (𝓞 L42)) := (Ideal.span {gO i} : Ideal (𝓞 K21)).primesOver (𝓞 L42)

theorem absNorm_span_gO13 : Ideal.absNorm (Ideal.span {gO 13} : Ideal (𝓞 K21)) = 2 := by
  rw [Ideal.absNorm_span_singleton]; exact natAbs_nZ_lb

theorem isMaximal_span_gO13 : (Ideal.span {gO 13} : Ideal (𝓞 K21)).IsMaximal :=
  isMaximal_of_absNorm_prime (by rw [absNorm_span_gO13]; exact Nat.prime_two)

theorem not_mem_of_one_sub {p : Ideal (𝓞 K21)} [hp : p.IsMaximal] {u q g : 𝓞 K21}
    (hg : p = Ideal.span {g}) (h : 1 - u = g * q) : u ∉ p := by
  intro hu
  have h1 : (1 : 𝓞 K21) ∈ p := by
    have : 1 - u ∈ p := by rw [h, hg]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)
    simpa using p.add_mem this hu
  exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr h1)

theorem mem_span_of_eq {g x q : 𝓞 K21} (h : x = g * q) : x ∈ (Ideal.span {g} : Ideal (𝓞 K21)) := by
  rw [h]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g)

theorem gO12_ne_zero : gO 12 ≠ 0 := by
  intro h; have h2 := two_eq; rw [h] at h2; simp at h2

theorem gO14_ne_zero : gO 14 ≠ 0 := by
  intro h; have h2 := two_eq; rw [h] at h2; simp at h2

/-- `la` is ramified in `L42`: one prime above it, of norm 2. -/
theorem PL12_count : (PL 12).ncard ≤ 1 ∧ ∀ P ∈ PL 12, Ideal.absNorm P = 2 := by
  have := isMaximal_span_gO12
  obtain ⟨γ, hγ⟩ := eis_root (zkO xA) (gO 12 ^ kA) (zkO bA) (zkO cA) (pow_ne_zero _ gO12_ne_zero)
    bA_eq cA_eq
  have h := eisenstein_count finrank_L42 _ (gO 12) rfl γ _ _ (zkO uA) hγ (mem_span_of_eq qbA_eq)
    uA_eq (not_mem_of_one_sub rfl quA_eq)
  exact ⟨h.1, fun P hP => (h.2 P hP).trans absNorm_span_gO12⟩

/-- `lc` is ramified in `L42`: one prime above it. -/
theorem PL14_count : (PL 14).ncard ≤ 1 := by
  have := isMaximal_span_gO14
  obtain ⟨γ, hγ⟩ := eis_root (zkO xC) (gO 14 ^ kC) (zkO bC) (zkO cC) (pow_ne_zero _ gO14_ne_zero)
    bC_eq cC_eq
  exact (eisenstein_count finrank_L42 _ (gO 14) rfl γ _ _ (zkO uC) hγ (mem_span_of_eq qbC_eq)
    uC_eq (not_mem_of_one_sub rfl quC_eq)).1

/-- `lb` is inert in `L42`. -/
theorem PL13_count : (PL 13).ncard ≤ 1 := by
  have := isMaximal_span_gO13
  refine inert_count finrank_L42 _ absNorm_span_gO13 γO _ _ γO_eq ?_ (mem_span_of_eq q2_eq)
  rw [sub_neg_eq_add]; exact mem_span_of_eq q1_eq

theorem PL15_count : (PL 15).ncard ≤ 2 := by
  have := isMaximal_span_gO15
  exact ncard_primesOver_le_two finrank_L42 _

/-- A maximal ideal of `𝓞 L42` containing 2 or 7 lies over one of the four primes. -/
theorem mem_PL (Q : Ideal (𝓞 L42)) [hQ : Q.IsMaximal]
    (h : (2 : 𝓞 L42) ∈ Q ∨ (7 : 𝓞 L42) ∈ Q) : Q ∈ PL 12 ∪ PL 13 ∪ PL 14 ∪ PL 15 := by
  set q := Q.comap (algebraMap (𝓞 K21) (𝓞 L42))
  haveI : q.IsMaximal := comap_isMaximal Q
  have hm : Q ∈ q.primesOver (𝓞 L42) := mem_primesOver_comap Q
  rcases h with h | h
  · have h2 : (2 : 𝓞 K21) ∈ q := by rw [Ideal.mem_comap, map_ofNat]; exact h
    rcases eq_of_two_mem q h2 with e | e | e <;> rw [e] at hm
    · exact Or.inl (Or.inl (Or.inl hm))
    · exact Or.inl (Or.inl (Or.inr hm))
    · exact Or.inl (Or.inr hm)
  · have h7 : (7 : 𝓞 K21) ∈ q := by rw [Ideal.mem_comap, map_ofNat]; exact h
    rw [eq_of_seven_mem q h7] at hm
    exact Or.inr hm

theorem PL_finite_of (i : ℕ) (h : (Ideal.span {gO i} : Ideal (𝓞 K21)).IsMaximal) :
    (PL i).Finite := by
  exact IsDedekindDomain.primesOver_finite _ (𝓞 L42)

theorem PL_finite (i : ℕ) (hi : i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) : (PL i).Finite := by
  rcases hi with rfl | rfl | rfl | rfl
  · exact PL_finite_of _ isMaximal_span_gO12
  · exact PL_finite_of _ isMaximal_span_gO13
  · exact PL_finite_of _ isMaximal_span_gO14
  · exact PL_finite_of _ isMaximal_span_gO15

theorem UL_finite : (PL 12 ∪ PL 13 ∪ PL 14 ∪ PL 15).Finite :=
  (((PL_finite 12 (by norm_num)).union (PL_finite 13 (by norm_num))).union
    (PL_finite 14 (by norm_num))).union (PL_finite 15 (by norm_num))

theorem UL_ncard : (PL 12 ∪ PL 13 ∪ PL 14 ∪ PL 15).ncard ≤ 5 := by
  have h1 := Set.ncard_union_le (PL 12 ∪ PL 13 ∪ PL 14) (PL 15)
  have h2 := Set.ncard_union_le (PL 12 ∪ PL 13) (PL 14)
  have h3 := Set.ncard_union_le (PL 12) (PL 13)
  have := PL12_count.1; have := PL13_count; have := PL14_count; have := PL15_count
  omega

theorem S27_L42_sub (v : HeightOneSpectrum (𝓞 L42)) (hv : v ∈ S27 L42) :
    v.asIdeal ∈ PL 12 ∪ PL 13 ∪ PL 14 ∪ PL 15 := by
  have := v.isMaximal
  exact mem_PL v.asIdeal hv

/-- **Piece (b), `L42`.** -/
theorem S27_L42_finite : (S27 L42).Finite :=
  (UL_finite.preimage HeightOneSpectrum.asIdeal_injective.injOn).subset S27_L42_sub

theorem ncard_S27_L42 : (S27 L42).ncard ≤ 5 :=
  (Set.ncard_le_ncard_of_injOn HeightOneSpectrum.asIdeal S27_L42_sub
    HeightOneSpectrum.asIdeal_injective.injOn UL_finite).trans UL_ncard


/-! ### The primes of `N84` above 2 and 7 -/

/-- The primes of `N84` above a prime `q` of `L42`. -/
def PN (q : Ideal (𝓞 L42)) : Set (Ideal (𝓞 N84)) := q.primesOver (𝓞 N84)

theorem PN_finite_le_two (q : Ideal (𝓞 L42)) [q.IsMaximal] : (PN q).Finite ∧ (PN q).ncard ≤ 2 :=
  ⟨IsDedekindDomain.primesOver_finite _ (𝓞 N84), ncard_primesOver_le_two finrank_N84 q⟩

theorem isMaximal_of_mem_PL {i : ℕ} (hi : (Ideal.span {gO i} : Ideal (𝓞 K21)).IsMaximal)
    {Q : Ideal (𝓞 L42)} (hQ : Q ∈ PL i) : Q.IsMaximal :=
  isMaximal_of_mem_primesOver _ Q hQ

/-- The prime above `la` is inert in `N84`. -/
theorem PN_PL12 (Q : Ideal (𝓞 L42)) (hQ : Q ∈ PL 12) : (PN Q).Finite ∧ (PN Q).ncard ≤ 1 := by
  have := isMaximal_span_gO12
  have := isMaximal_of_mem_PL isMaximal_span_gO12 hQ
  refine ⟨IsDedekindDomain.primesOver_finite _ (𝓞 N84), ?_⟩
  refine inert_count finrank_N84 Q (PL12_count.2 Q hQ) γNO _ _ γNO_eq ?_ ?_
  · rw [sub_neg_eq_add]
    exact mem_of_quadratic_mem _ _ _ _ one_add_xLO_root (mem_span_of_eq q3_eq)
      (mem_span_of_eq q4_eq) Q hQ
  · exact mem_of_quadratic_mem _ _ _ _ one_sub_nLO_root (mem_span_of_eq q5_eq)
      (mem_span_of_eq q6_eq) Q hQ

/-- The prime `(e')` of `L42` above `pi7`. -/
noncomputable def E7 : Ideal (𝓞 L42) := Ideal.span {eNO}

theorem isMaximal_E7 : E7.IsMaximal := by
  have hne : E7 ≠ ⊤ := by
    intro h
    have := absNorm_span_eNO
    rw [show Ideal.span {eNO} = E7 from rfl, h, Ideal.absNorm_top] at this
    norm_num at this
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal E7 hne
  have hmem : eNO ∈ M := hle (Ideal.mem_span_singleton_self eNO)
  have e := eq_span_of_eNO_mem M hmem
  rw [show E7 = Ideal.span {eNO} from rfl, ← e]
  exact hM

theorem E7_mem_PL15 : E7 ∈ PL 15 := by
  have := isMaximal_E7
  have h := mem_primesOver_comap (K := K21) E7
  rwa [comap_eq_of_eNO_mem E7 (Ideal.mem_span_singleton_self eNO)] at h

/-- `(e')` is ramified in `N84` (`ω_N² = e'`). -/
theorem PN_E7 : (PN E7).Finite ∧ (PN E7).ncard ≤ 1 := by
  have := isMaximal_E7
  refine ⟨IsDedekindDomain.primesOver_finite _ (𝓞 N84), ?_⟩
  obtain ⟨γ, hγ⟩ := omegaN_root
  refine (eisenstein_count finrank_N84 E7 eNO rfl γ 0 (-eNO) (-1) hγ E7.zero_mem
    (by ring) ?_).1
  intro h
  have h1 : (1 : 𝓞 L42) ∈ E7 := by simpa using E7.neg_mem h
  exact isMaximal_E7.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem PL15_diff : (PL 15 \ {E7}).Finite ∧ (PL 15 \ {E7}).ncard ≤ 1 := by
  refine ⟨(PL_finite 15 (by norm_num)).sdiff, ?_⟩
  rw [Set.ncard_sdiff_singleton_of_mem E7_mem_PL15]
  have := PL15_count
  omega

theorem PL1314 : (PL 13 ∪ PL 14).Finite ∧ (PL 13 ∪ PL 14).ncard ≤ 2 := by
  refine ⟨(PL_finite 13 (by norm_num)).union (PL_finite 14 (by norm_num)), ?_⟩
  have := Set.ncard_union_le (PL 13) (PL 14)
  have := PL13_count; have := PL14_count
  omega

/-- The four blocks of primes of `N84` above 2 and 7. -/
def UN : Set (Ideal (𝓞 N84)) :=
  ((⋃ Q ∈ PL 12, PN Q) ∪ (⋃ Q ∈ PL 13 ∪ PL 14, PN Q)) ∪ (PN E7 ∪ ⋃ Q ∈ PL 15 \ {E7}, PN Q)

theorem UN_bound : UN.Finite ∧ UN.ncard ≤ 8 := by
  have h1 := ncard_biUnion_le (PL 12) (PL_finite 12 (by norm_num)) 1 1 PL12_count.1 PN PN_PL12
  have h2 := ncard_biUnion_le (PL 13 ∪ PL 14) PL1314.1 2 2 PL1314.2 PN fun Q hQ => by
    rcases hQ with hQ | hQ
    · have := isMaximal_of_mem_PL isMaximal_span_gO13 hQ; exact PN_finite_le_two Q
    · have := isMaximal_of_mem_PL isMaximal_span_gO14 hQ; exact PN_finite_le_two Q
  have h4 := ncard_biUnion_le (PL 15 \ {E7}) PL15_diff.1 1 2 PL15_diff.2 PN fun Q hQ => by
    have := isMaximal_of_mem_PL isMaximal_span_gO15 hQ.1; exact PN_finite_le_two Q
  have h3 := PN_E7
  refine ⟨(h1.1.union h2.1).union (h3.1.union h4.1), ?_⟩
  have := Set.ncard_union_le ((⋃ Q ∈ PL 12, PN Q) ∪ (⋃ Q ∈ PL 13 ∪ PL 14, PN Q))
    (PN E7 ∪ ⋃ Q ∈ PL 15 \ {E7}, PN Q)
  have := Set.ncard_union_le (⋃ Q ∈ PL 12, PN Q) (⋃ Q ∈ PL 13 ∪ PL 14, PN Q)
  have := Set.ncard_union_le (PN E7) (⋃ Q ∈ PL 15 \ {E7}, PN Q)
  unfold UN
  omega

/-- A maximal ideal of `𝓞 N84` containing 2 or 7 is in `UN`. -/
theorem mem_UN (Q : Ideal (𝓞 N84)) [Q.IsMaximal]
    (h : (2 : 𝓞 N84) ∈ Q ∨ (7 : 𝓞 N84) ∈ Q) : Q ∈ UN := by
  set q := Q.comap (algebraMap (𝓞 L42) (𝓞 N84))
  have : q.IsMaximal := comap_isMaximal Q
  have hm : Q ∈ PN q := mem_primesOver_comap Q
  have hq : q ∈ PL 12 ∪ PL 13 ∪ PL 14 ∪ PL 15 := by
    refine mem_PL q ?_
    rcases h with h | h
    · left; rw [Ideal.mem_comap, map_ofNat]; exact h
    · right; rw [Ideal.mem_comap, map_ofNat]; exact h
  have hB : ∀ (T : Set (Ideal (𝓞 L42))), q ∈ T → Q ∈ ⋃ Q' ∈ T, PN Q' := fun T hT =>
    Set.mem_biUnion hT hm
  rcases hq with ((h12 | h13) | h14) | h15
  · exact Or.inl (Or.inl (hB _ h12))
  · exact Or.inl (Or.inr (hB _ (Or.inl h13)))
  · exact Or.inl (Or.inr (hB _ (Or.inr h14)))
  · by_cases hE : q = E7
    · rw [hE] at hm; exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (hB _ ⟨h15, hE⟩))

theorem S27_N84_sub (v : HeightOneSpectrum (𝓞 N84)) (hv : v ∈ S27 N84) : v.asIdeal ∈ UN := by
  have := v.isMaximal
  exact mem_UN v.asIdeal hv

/-- **Piece (b), `N84`.** -/
theorem S27_N84_finite : (S27 N84).Finite :=
  (UN_bound.1.preimage HeightOneSpectrum.asIdeal_injective.injOn).subset S27_N84_sub

theorem ncard_S27_N84 : (S27 N84).ncard ≤ 8 :=
  (Set.ncard_le_ncard_of_injOn HeightOneSpectrum.asIdeal S27_N84_sub
    HeightOneSpectrum.asIdeal_injective.injOn UN_bound.1).trans UN_bound.2

end FurioLombardo.Discharge.SelmerBasis
