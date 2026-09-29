import Mathlib
import FurioLombardo.Discharge.M3a.K1Norm
import FurioLombardo.Discharge.M3a.K1Quad
import FurioLombardo.Discharge.M3a.Reduction

/-!
# The halving construction of Cassels and Flynn (lane K1, bricks E2, E4, E6)

Setting: `f` with `GoodSextic f` and no root in `K`,
a Mumford pair `(u, v)` (`u` monic quadratic coprime to `f`, `v² - f = u w₀`), and a square root
`u(Θ) = η ρ²` in `A = K[X]/(f)`, `ρ = r(Θ)`, with the **good sign**
`f₆ η³ N(ρ) = -N_u(v)` (G). Then `[⟨u, Y - v⟩]` is a square in `Jac f`
(`exists_half_of_good_sign`):

* Step 4 (`exists_L`, `exists_W`): `L ≠ 0` of degree `≤ 2` with `M = L r mod f₀` of degree `≤ 3`,
  and `η M² - u L² = w f`, `w ∈ K`;
* Step 5 (`false_of_w_eq_zero`, E6): `w = 0` is impossible, by (G) and the absence of roots;
* Step 6: `L` is coprime to `f`, and the norm formula (N) (K1Norm.lean);
* Step 7 (`exists_s`): `w/η = s²` and `M ≡ s v mod u`;
* Step 8 (`exists_half_of_M`): with `M' = M/s`, `⟨u, Y - v⟩ ⟨L₀, Y - M'⟩² = (Y - M')`.
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.M3a.K1

variable {K : Type*} [Field K]

/-! ### Polynomial lemmas -/

theorem exists_L {f : K[X]} (hf : f.Monic) (h6 : f.natDegree = 6) (r : K[X]) :
    ∃ L : K[X], L ≠ 0 ∧ L.natDegree ≤ 2 ∧ ((L * r) %ₘ f).natDegree ≤ 3 := by
  classical
  have hf1 : f ≠ 1 := by
    rintro rfl
    simp at h6
  let ψ : degreeLT K 3 →ₗ[K] (Fin 2 → K) :=
    (LinearMap.pi fun j : Fin 2 => lcoeff K (j + 4)) ∘ₗ
      ((modByMonicHom f).restrictScalars K ∘ₗ LinearMap.mulRight K r) ∘ₗ (degreeLT K 3).subtype
  have hfin : Module.finrank K (degreeLT K 3) = 3 := by
    rw [(degreeLTEquiv K 3).finrank_eq, Module.finrank_fin_fun]
  have : FiniteDimensional K (degreeLT K 3) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv K 3).symm
  have hker : LinearMap.ker ψ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [hfin, Module.finrank_fin_fun]; norm_num)
  obtain ⟨L, hLker, hL0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hLmem := L.2
  rw [mem_degreeLT] at hLmem
  refine ⟨L, fun h => hL0 (Subtype.ext h), ?_, ?_⟩
  · by_cases h0 : (L : K[X]) = 0
    · rw [h0, natDegree_zero]; omega
    · rw [degree_eq_natDegree h0] at hLmem
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hLmem)
  · rw [LinearMap.mem_ker] at hLker
    have h4 : (((L : K[X]) * r) %ₘ f).coeff 4 = 0 := by
      have := congrFun hLker 0
      simpa [ψ] using this
    have h5 : (((L : K[X]) * r) %ₘ f).coeff 5 = 0 := by
      have := congrFun hLker 1
      simpa [ψ] using this
    have hlt : (((L : K[X]) * r) %ₘ f).natDegree < 6 := h6 ▸ natDegree_modByMonic_lt _ hf hf1
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rcases (by omega : n = 4 ∨ n = 5 ∨ 6 ≤ n) with rfl | rfl | h
    · exact h4
    · exact h5
    · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem exists_W {f P : K[X]} (hf : f.natDegree = 6) (hP : P.natDegree ≤ 6)
    (hdvd : f ∣ P) : ∃ w : K, P = C w * f := by
  have hf_ne_zero : f ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hf
    linarith
  rcases hdvd with ⟨q, hq⟩
  by_cases hq_zero : q = 0
  · refine ⟨0, ?_⟩
    rw [hq_zero, mul_zero] at hq
    rw [hq]
    simp
  · have h_natDegree_q : q.natDegree = 0 := by
      have h_natDegree_mul : (f * q).natDegree = f.natDegree + q.natDegree :=
        natDegree_mul hf_ne_zero hq_zero
      have hP_eq : P.natDegree = 6 + q.natDegree := by
        rw [hq, h_natDegree_mul, hf]
      have hle : 6 + q.natDegree ≤ 6 := by
        rw [← hP_eq]
        exact hP
      omega
    have hq_const : q = C (q.coeff 0) :=
      eq_C_of_natDegree_eq_zero h_natDegree_q
    refine ⟨q.coeff 0, ?_⟩
    rw [hq_const] at hq
    rw [hq]
    ring

theorem isCoprime_of_sq_comb {f A B : K[X]} (hf : Squarefree f) (α β : K[X])
    (h : f = α * A ^ 2 + β * B ^ 2) : IsCoprime A B := by
  have h_relprime : IsRelPrime A B := by
    intro d hdA hdB
    have hd_sq : d * d ∣ f := by
      rw [h]
      have hA2 : d * d ∣ A ^ 2 := by
        have : A ^ 2 = A * A := by ring
        rw [this]
        exact mul_dvd_mul hdA hdA
      have hB2 : d * d ∣ B ^ 2 := by
        have : B ^ 2 = B * B := by ring
        rw [this]
        exact mul_dvd_mul hdB hdB
      have hα : d * d ∣ α * A ^ 2 := by
        simpa [mul_comm] using dvd_mul_of_dvd_right hA2 α
      have hβ : d * d ∣ β * B ^ 2 := by
        simpa [mul_comm] using dvd_mul_of_dvd_right hB2 β
      exact dvd_add hα hβ
    exact hf d hd_sq
  exact h_relprime.isCoprime

theorem isCoprime_L_f {f u L M : K[X]} (hf : Squarefree f) {η w : K}
    (hη : η ≠ 0) (hw : w ≠ 0) (hW : C η * M ^ 2 - u * L ^ 2 = C w * f) : IsCoprime L f := by
  have hrel : IsRelPrime L f := by
    intro d hdL hdf
    by_contra hd
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact not_squarefree_zero hf
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hf0 (zero_dvd_iff.mp hdf)
    obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hd hd0
    have hpL : p ∣ L := hpd.trans hdL
    have hpf : p ∣ f := hpd.trans hdf
    have hpr : Prime p := hp.prime
    have hηu : IsUnit (C η) := isUnit_C.mpr (Ne.isUnit hη)
    have hwu : IsUnit (C w) := isUnit_C.mpr (Ne.isUnit hw)
    have hpM2 : p ∣ C η * M ^ 2 := by
      rw [show C η * M ^ 2 = C w * f + u * L ^ 2 by linear_combination hW]
      exact dvd_add (dvd_mul_of_dvd_right hpf _) (dvd_mul_of_dvd_right (dvd_pow hpL two_ne_zero) _)
    have hpM : p ∣ M := hpr.dvd_of_dvd_pow ((hηu.dvd_mul_left).mp hpM2)
    have hpp : p * p ∣ C w * f := by
      rw [← hW]
      refine dvd_sub (dvd_mul_of_dvd_right ?_ _) (dvd_mul_of_dvd_right ?_ _)
      · rw [sq]; exact mul_dvd_mul hpM hpM
      · rw [sq]; exact mul_dvd_mul hpL hpL
    exact hp.not_isUnit (hf p ((hwu.dvd_mul_left).mp hpp))
  exact hrel.isCoprime

theorem sq_decomp {u L M : K[X]} (hu : u.Monic) (h2 : u.natDegree = 2)
    (hL : L ≠ 0) {η : K} (h : C η * M ^ 2 = u * L ^ 2) :
    ∃ e : K, η = e ^ 2 ∧ ∃ s : K[X], s.Monic ∧ s.natDegree = 1 ∧ u = s ^ 2 ∧ C e * M = L * s := by
  have hu0 : u ≠ 0 := hu.ne_zero
  have hM : M ≠ 0 := by
    rintro rfl
    have h0 : u * L ^ 2 = 0 := by rw [← h]; simp
    exact mul_ne_zero hu0 (pow_ne_zero 2 hL) h0
  have hlcM : M.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hM
  have hlcL : L.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hL
  have hlc := congrArg leadingCoeff h
  rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow, leadingCoeff_pow,
    hu.leadingCoeff, one_mul] at hlc
  have hηe : η = (L.leadingCoeff / M.leadingCoeff) ^ 2 := by
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hlcM), hlc]
  refine ⟨L.leadingCoeff / M.leadingCoeff, hηe, ?_⟩
  have hsq : (C (L.leadingCoeff / M.leadingCoeff) * M) ^ 2 = u * L ^ 2 := by
    rw [mul_pow, ← C_pow, ← hηe, h]
  have hdvd : L ∣ C (L.leadingCoeff / M.leadingCoeff) * M := by
    have h' : L ^ 2 ∣ (C (L.leadingCoeff / M.leadingCoeff) * M) ^ 2 := ⟨u, by rw [hsq, mul_comm]⟩
    exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).mp h'
  obtain ⟨s, hs⟩ := hdvd
  have hus : u = s ^ 2 := by
    have h' : L ^ 2 * s ^ 2 = L ^ 2 * u := by
      rw [← mul_pow, ← hs, hsq, mul_comm]
    exact (mul_left_cancel₀ (pow_ne_zero 2 hL) h').symm
  have hlcs : s.leadingCoeff = 1 := by
    have h' := congrArg leadingCoeff hs
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, div_mul_cancel₀ _ hlcM] at h'
    exact (mul_left_cancel₀ hlcL (h'.symm.trans (mul_one _).symm))
  have hdeg : s.natDegree = 1 := by
    have h' := congrArg natDegree hus
    rw [natDegree_pow, h2] at h'
    omega
  exact ⟨s, hlcs, hdeg, hus, hs⟩

theorem involution_root (h2K : (2 : K) ≠ 0) {f L P : K[X]} (hf : f.Monic)
    (hsq : f ∣ P ^ 2 - 1) (hN : Algebra.norm K (AdjoinRoot.mk f P) = -1) (hL : L ≠ 0)
    (hL2 : L.natDegree ≤ 2) (hLP : f ∣ L * (P - 1)) : ∃ a : K, f.eval a = 0 := by
  classical
  have hf0 : f ≠ 0 := hf.ne_zero
  have hcop : IsCoprime (P + 1) (P - 1) := by
    refine ⟨C (2⁻¹), -C (2⁻¹), ?_⟩
    have h2 : (C (2⁻¹) : K[X]) * 2 = 1 := by
      rw [← map_ofNat C 2, ← C_mul, inv_mul_cancel₀ h2K, C_1]
    linear_combination h2
  have hG0 : gcd f (P + 1) ≠ 0 := fun h => hf0 ((gcd_eq_zero_iff _ _).mp h).1
  have hH0 : gcd f (P - 1) ≠ 0 := fun h => hf0 ((gcd_eq_zero_iff _ _).mp h).1
  have hGm : (gcd f (P + 1)).Monic := by
    rw [← normalize_gcd]; exact monic_normalize hG0
  have hHm : (gcd f (P - 1)).Monic := by
    rw [← normalize_gcd]; exact monic_normalize hH0
  have hGcop : IsCoprime (gcd f (P + 1)) (P - 1) :=
    hcop.of_isCoprime_of_dvd_left (gcd_dvd_right _ _)
  have hGH : IsCoprime (gcd f (P + 1)) (gcd f (P - 1)) :=
    hGcop.of_isCoprime_of_dvd_right (gcd_dvd_right _ _)
  have hGHf : gcd f (P + 1) * gcd f (P - 1) ∣ f := hGH.mul_dvd (gcd_dvd_left _ _) (gcd_dvd_left _ _)
  have hfGH : f ∣ gcd f (P + 1) * gcd f (P - 1) := by
    have h1 : f ∣ gcd f ((P + 1) * (P - 1)) :=
      dvd_gcd dvd_rfl (by rw [show (P + 1) * (P - 1) = P ^ 2 - 1 by ring]; exact hsq)
    exact h1.trans (gcd_mul_dvd_mul_gcd f (P + 1) (P - 1))
  have hfeq : f = gcd f (P + 1) * gcd f (P - 1) :=
    eq_of_monic_of_associated hf (hGm.mul hHm) (associated_of_dvd_dvd hfGH hGHf)
  have hGL : gcd f (P + 1) ∣ L := hGcop.dvd_of_dvd_mul_right ((gcd_dvd_left f (P + 1)).trans hLP)
  have hNGH : Algebra.norm K (AdjoinRoot.mk f P) =
      Algebra.norm K (AdjoinRoot.mk (gcd f (P + 1)) P) *
        Algebra.norm K (AdjoinRoot.mk (gcd f (P - 1)) P) := by
    rw [norm_mk_eq_resultant_of_le hf le_rfl, norm_mk_eq_resultant_of_le hGm le_rfl,
      norm_mk_eq_resultant_of_le hHm le_rfl]
    conv_lhs => rw [hfeq]
    rw [natDegree_mul hG0 hH0, resultant_mul_left _ _ _ _ le_rfl]
  have hNG : Algebra.norm K (AdjoinRoot.mk (gcd f (P + 1)) P) = (-1) ^ (gcd f (P + 1)).natDegree := by
    rw [show AdjoinRoot.mk (gcd f (P + 1)) P = algebraMap K _ (-1) from ?_,
      norm_algebraMap_adjoinRoot hGm]
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_mk, C_neg, C_1,
      sub_neg_eq_add]
    exact gcd_dvd_right _ _
  have hNH : Algebra.norm K (AdjoinRoot.mk (gcd f (P - 1)) P) = 1 := by
    rw [show AdjoinRoot.mk (gcd f (P - 1)) P = 1 from ?_, map_one]
    rw [← map_one (AdjoinRoot.mk (gcd f (P - 1))), AdjoinRoot.mk_eq_mk]
    exact gcd_dvd_right _ _
  rw [hNGH, hNG, hNH, mul_one] at hN
  have hodd : Odd (gcd f (P + 1)).natDegree := by
    rcases Nat.even_or_odd (gcd f (P + 1)).natDegree with he | ho
    · rw [he.neg_one_pow] at hN
      exact absurd (by linear_combination hN : (2 : K) = 0) h2K
    · exact ho
  have hGdeg : (gcd f (P + 1)).natDegree ≤ 2 := (natDegree_le_of_dvd hGL hL).trans hL2
  have hG1 : (gcd f (P + 1)).natDegree = 1 := by
    obtain ⟨m, hm⟩ := hodd
    omega
  obtain ⟨a, ha⟩ := exists_root_of_degree_eq_one
    (by rw [degree_eq_natDegree hG0, hG1]; rfl : (gcd f (P + 1)).degree = 1)
  exact ⟨a, eval_eq_zero_of_dvd_of_eval_eq_zero (gcd_dvd_left f (P + 1)) ha⟩

theorem norm_sq_linear {f s v : K[X]} (hf : f.natDegree = 6) (hs : s.Monic)
    (h1 : s.natDegree = 1) (hsv : s ^ 2 ∣ v ^ 2 - f) :
    Algebra.norm K (AdjoinRoot.mk (s ^ 2) v) =
      f.leadingCoeff * Algebra.norm K (AdjoinRoot.mk f s) := by
  have hf0 : f ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hf
    linarith
  have hs2 : (s ^ 2).Monic := hs.pow 2
  have hnat_sq : (s ^ 2).natDegree = 2 := by
    rw [hs.natDegree_pow, h1, mul_one]
  have h_s_dvd : s ∣ v ^ 2 - f :=
    dvd_trans (by rw [sq]; exact dvd_mul_right s s) hsv
  -- Step 1: N_{s²}(v) = N_s(v)²
  have h_step1 : Algebra.norm K (AdjoinRoot.mk (s ^ 2) v) = (Algebra.norm K (AdjoinRoot.mk s v)) ^ 2 := by
    have hnorm_sq : Algebra.norm K (AdjoinRoot.mk (s ^ 2) v) = resultant (s ^ 2) v (s ^ 2).natDegree v.natDegree :=
      norm_mk_eq_resultant_of_le hs2 (le_refl _)
    have hnorm_s : Algebra.norm K (AdjoinRoot.mk s v) = resultant s v s.natDegree v.natDegree :=
      norm_mk_eq_resultant_of_le hs (le_refl _)
    have hresultant : resultant (s ^ 2) v 2 v.natDegree = (resultant s v 1 v.natDegree) ^ 2 := by
      calc
        resultant (s ^ 2) v 2 v.natDegree = resultant (s * s) v (s.natDegree + s.natDegree) v.natDegree := by
          rw [sq, show s.natDegree + s.natDegree = 2 by rw [h1]]
        _ = resultant s v s.natDegree v.natDegree * resultant s v s.natDegree v.natDegree := by
          rw [resultant_mul_left s s v v.natDegree (le_refl _)]
        _ = (resultant s v s.natDegree v.natDegree) ^ 2 := by ring
        _ = (resultant s v 1 v.natDegree) ^ 2 := by rw [h1]
    calc
      Algebra.norm K (AdjoinRoot.mk (s ^ 2) v) = resultant (s ^ 2) v (s ^ 2).natDegree v.natDegree := hnorm_sq
      _ = resultant (s ^ 2) v 2 v.natDegree := by rw [hnat_sq]
      _ = (resultant s v 1 v.natDegree) ^ 2 := hresultant
      _ = (resultant s v s.natDegree v.natDegree) ^ 2 := by rw [h1]
      _ = (Algebra.norm K (AdjoinRoot.mk s v)) ^ 2 := by rw [hnorm_s]
  -- Step 2: N_s(v)² = N_s(v²) = N_s(f)
  have h_step2 : (Algebra.norm K (AdjoinRoot.mk s v)) ^ 2 = Algebra.norm K (AdjoinRoot.mk s f) := by
    have hnorm_pow : Algebra.norm K (AdjoinRoot.mk s (v ^ 2)) = (Algebra.norm K (AdjoinRoot.mk s v)) ^ 2 := by
      calc
        Algebra.norm K (AdjoinRoot.mk s (v ^ 2)) = Algebra.norm K ((AdjoinRoot.mk s v) ^ 2) := by
          rw [map_pow (AdjoinRoot.mk s) v 2]
        _ = (Algebra.norm K (AdjoinRoot.mk s v)) ^ 2 := by rw [map_pow (Algebra.norm K) (AdjoinRoot.mk s v) 2]
    have hmk_eq : AdjoinRoot.mk s (v ^ 2) = AdjoinRoot.mk s f := by
      rw [AdjoinRoot.mk_eq_mk]
      exact h_s_dvd
    calc
      (Algebra.norm K (AdjoinRoot.mk s v)) ^ 2 = Algebra.norm K (AdjoinRoot.mk s (v ^ 2)) := by rw [hnorm_pow]
      _ = Algebra.norm K (AdjoinRoot.mk s f) := by rw [hmk_eq]
  -- Step 3: norm_mk_swap
  have hswap := norm_mk_swap hf0 hs
  rw [h1, hf] at hswap
  norm_num at hswap
  calc
    Algebra.norm K (AdjoinRoot.mk (s ^ 2) v) = (Algebra.norm K (AdjoinRoot.mk s v)) ^ 2 := h_step1
    _ = Algebra.norm K (AdjoinRoot.mk s f) := h_step2
    _ = f.leadingCoeff * Algebra.norm K (AdjoinRoot.mk f s) := by rw [hswap]

theorem natDegree_L_eq_two {f u L M : K[X]} (hlc : ¬ IsSquare f.leadingCoeff)
    (hf : f.natDegree = 6) (hu : u.Monic) (h2 : u.natDegree = 2) {c : K} (hc : c ≠ 0)
    (hL2 : L.natDegree ≤ 2) (hM : M ^ 2 - f = u * (C c * L ^ 2)) : L.natDegree = 2 := by
  have h_ineq : 6 ≤ (M ^ 2 - (1 : K[X]) ^ 2 * f).natDegree :=
    six_le_natDegree_sq_sub_sq_mul hlc hf (r := 1) one_ne_zero (p := M)
  have h_eq : (M ^ 2 - (1 : K[X]) ^ 2 * f) = u * (C c * L ^ 2) := by
    simpa using hM
  have h_ineq' : 6 ≤ (u * (C c * L ^ 2)).natDegree := by
    rwa [h_eq] at h_ineq
  by_cases hL0 : L = 0
  · subst hL0
    simp at h_ineq'
  · have hu_ne_zero : u ≠ 0 := hu.ne_zero
    have hc_ne_zero : C c ≠ 0 := by
      intro hzero
      apply hc
      simpa using (C_eq_zero.mp hzero)
    have hLsq_ne_zero : L ^ 2 ≠ 0 := pow_ne_zero 2 hL0
    have hprod_ne_zero : C c * L ^ 2 ≠ 0 := mul_ne_zero hc_ne_zero hLsq_ne_zero
    have h_total : (u * (C c * L ^ 2)).natDegree = u.natDegree + (C c * L ^ 2).natDegree :=
      natDegree_mul hu_ne_zero hprod_ne_zero
    have h_inner : (C c * L ^ 2).natDegree = (C c).natDegree + (L ^ 2).natDegree :=
      natDegree_mul hc_ne_zero hLsq_ne_zero
    have h_natDegree_C : (C c).natDegree = 0 := natDegree_C _
    have h_natDegree_Lsq : (L ^ 2).natDegree = 2 * L.natDegree := by
      rw [Polynomial.natDegree_pow, Nat.mul_comm]
    have h_total_val : (u * (C c * L ^ 2)).natDegree = 2 + 2 * L.natDegree := by
      rw [h_total, h2, h_inner, h_natDegree_C, h_natDegree_Lsq]
      omega
    rw [h_total_val] at h_ineq'
    have h_ineq2 : 2 ≤ L.natDegree := by
      omega
    omega

theorem dvd_of_not_isCoprime {u f : K[X]} (hu : u.Monic) (h2 : u.natDegree = 2)
    (hroot : ∀ a : K, f.eval a ≠ 0) (h : ¬ IsCoprime u f) : u ∣ f := by
  classical
  have hgu : gcd u f ∣ u := gcd_dvd_left u f
  have hgf : gcd u f ∣ f := gcd_dvd_right u f
  have hng : ¬ IsUnit (gcd u f) := fun h' => h ((gcd_isUnit_iff u f).mp h')
  have hg0 : gcd u f ≠ 0 := fun h0 => hu.ne_zero ((gcd_eq_zero_iff _ _).mp h0).1
  have hgdeg : (gcd u f).natDegree ≤ 2 := h2 ▸ natDegree_le_of_dvd hgu hu.ne_zero
  have hgpos : 0 < (gcd u f).natDegree := by
    by_contra h0
    apply hng
    rw [eq_C_of_natDegree_eq_zero (by omega : (gcd u f).natDegree = 0)]
    refine isUnit_C.mpr (IsUnit.mk0 _ ?_)
    intro hc
    apply hg0
    rw [eq_C_of_natDegree_eq_zero (by omega : (gcd u f).natDegree = 0), hc, C_0]
  rcases (by omega : (gcd u f).natDegree = 1 ∨ (gcd u f).natDegree = 2) with h1 | h2g
  · obtain ⟨a, ha⟩ := exists_root_of_degree_eq_one
      (by rw [degree_eq_natDegree hg0, h1]; rfl : (gcd u f).degree = 1)
    exact absurd (eval_eq_zero_of_dvd_of_eval_eq_zero hgf ha) (hroot a)
  · obtain ⟨c, hc⟩ := hgu
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact hu.ne_zero hc
    have hcdeg : c.natDegree = 0 := by
      have := congrArg natDegree hc
      rw [natDegree_mul hg0 hc0] at this
      omega
    have hc00 : c.coeff 0 ≠ 0 := by
      intro h0
      apply hc0
      rw [eq_C_of_natDegree_eq_zero hcdeg, h0, C_0]
    rw [eq_C_of_natDegree_eq_zero hcdeg] at hc
    refine dvd_trans ⟨C (c.coeff 0)⁻¹, ?_⟩ hgf
    conv_rhs => rw [hc]
    rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hc00, C_1, mul_one]

theorem v_eq_zero_of_dvd {u f v w : K[X]} (h2 : u.natDegree = 2)
    (huf : u ∣ f) (hf : Squarefree f) (hw : v ^ 2 - f = u * w) (hv : v.degree < 2) : v = 0 := by
  have hu_nz : u ≠ 0 := by
    intro hzero
    rw [hzero] at h2
    have hzero_nd : (0 : K[X]).natDegree = 0 := by simp
    rw [hzero_nd] at h2
    norm_num at h2
  have h_deg_u : u.degree = (2 : ℕ) := by
    rw [Polynomial.degree_eq_natDegree hu_nz, h2]
  have hu_sqfree : Squarefree u :=
    Squarefree.squarefree_of_dvd huf hf
  have hu_dvd_vsq : u ∣ v ^ 2 := by
    have hvsq_eq : v ^ 2 = f + u * w := by
      calc
        v ^ 2 = (v ^ 2 - f) + f := by ring
        _ = u * w + f := by rw [hw]
        _ = f + u * w := add_comm _ _
    rw [hvsq_eq]
    exact dvd_add huf (dvd_mul_right u w)
  have hu_dvd_v : u ∣ v := by
    have hpos : (2 : ℕ) ≠ 0 := by norm_num
    exact ((Squarefree.dvd_pow_iff_dvd hu_sqfree hpos).mp hu_dvd_vsq)
  have h_deg_lt : v.degree < u.degree := by
    rw [h_deg_u]
    exact hv
  exact Polynomial.eq_zero_of_dvd_of_degree_lt hu_dvd_v h_deg_lt

theorem mumford_sq {f L m : K[X]} (h2 : (2 : K) ≠ 0) (hL : L ^ 2 ∣ m ^ 2 - f)
    (hc : IsCoprime L m) : mumford f L m ^ 2 = mumford f (L ^ 2) m := by
  obtain ⟨a, b, hab⟩ := hc
  obtain ⟨k, hk⟩ := hL
  set φ := algebraMap K[X] (CoordRing f) with hφ
  have hY : Yc f ^ 2 = φ f := Yc_sq f
  have hk' : φ L * φ L * φ k = φ m ^ 2 - φ f := by
    rw [← map_mul, ← map_mul, ← map_pow, ← map_sub, hk, sq]
  have hL1 : φ L ∈ mumford f L m := Ideal.subset_span (Set.mem_insert _ _)
  have hZ1 : Yc f - φ m ∈ mumford f L m := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  rw [sq]
  apply le_antisymm
  · have hA : φ (L ^ 2) ∈ mumford f (L ^ 2) m := Ideal.subset_span (Set.mem_insert _ _)
    have hB : Yc f - φ m ∈ mumford f (L ^ 2) m := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    show Ideal.span {φ L, Yc f - φ m} * Ideal.span {φ L, Yc f - φ m} ≤ mumford f (L ^ 2) m
    rw [Ideal.span_mul_span, Ideal.span_le]
    rintro x ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rw [SetLike.mem_coe]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · dsimp only; rw [← map_mul, ← sq]; exact hA
    · exact Ideal.mul_mem_left _ _ hB
    · exact Ideal.mul_mem_right _ _ hB
    · exact Ideal.mul_mem_left _ _ hB
  · show Ideal.span {φ (L ^ 2), Yc f - φ m} ≤ _
    rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      SetLike.mem_coe]
    refine ⟨?_, ?_⟩
    · rw [map_pow, sq]; exact Ideal.mul_mem_mul hL1 hL1
    · have h2R : algebraMap K (CoordRing f) 2⁻¹ * 2 = 1 := by
        rw [← map_ofNat (algebraMap K (CoordRing f)) 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
      have habc' : φ a * φ L + φ b * φ m = 1 := by
        rw [← map_mul, ← map_mul, ← map_add, hab, map_one]
      have key : Yc f - φ m = φ a * (φ L * (Yc f - φ m)) -
          φ b * algebraMap K (CoordRing f) 2⁻¹ *
            ((Yc f - φ m) * (Yc f - φ m) + φ k * (φ L * φ L)) := by
        linear_combination (-(Yc f - φ m)) * habc' + (φ b * algebraMap K (CoordRing f) 2⁻¹) * hY +
          (φ b * algebraMap K (CoordRing f) 2⁻¹) * hk' -
          (φ b * φ m * (Yc f - φ m)) * h2R
      rw [key]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hL1 hZ1))
        (Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.mul_mem_mul hZ1 hZ1)
          (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hL1 hL1))))

/-! ### Small facts -/

/-- A polynomial coprime to `g` is a unit modulo `g`. -/
theorem isUnit_mk_of_isCoprime {g p : K[X]} (h : IsCoprime p g) : IsUnit (AdjoinRoot.mk g p) := by
  obtain ⟨a, b, hab⟩ := h
  refine IsUnit.of_mul_eq_one_right (AdjoinRoot.mk g a) ?_
  have := congrArg (AdjoinRoot.mk g) hab
  rwa [map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, map_one] at this

/-- `u` coprime to `f` and `v² - f = u w₀` give `u` coprime to `v`. -/
theorem isCoprime_u_v {f u v w₀ : K[X]} (hw₀ : v ^ 2 - f = u * w₀) (huf : IsCoprime u f) :
    IsCoprime u v := by
  have h : IsCoprime u (f + u * w₀) := huf.add_mul_left_right w₀
  rw [show f + u * w₀ = v * v by linear_combination -hw₀] at h
  exact h.of_mul_right_left

/-- The monic associate `f₀ = f / lc f`. -/
theorem monic_assoc {f : K[X]} (hf : f ≠ 0) :
    (C f.leadingCoeff⁻¹ * f).Monic ∧ (C f.leadingCoeff⁻¹ * f).natDegree = f.natDegree ∧
      f = C f.leadingCoeff * (C f.leadingCoeff⁻¹ * f) := by
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  refine ⟨?_, natDegree_C_mul (inv_ne_zero hlc), ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc]
  · rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]

/-! ### Step 5: `w = 0` is impossible under the good sign -/

/-- **Step 5 (E6).** Under the good sign (G), `η M² = u L²` with `L ≠ 0` of degree `≤ 2` and
`M(Θ) = L(Θ) ρ` forces a root of `f`. -/
theorem false_of_w_eq_zero (f : K[X]) [GoodSextic f] (hroot : ∀ a : K, f.eval a ≠ 0)
    {u v w₀ : K[X]} (hu : u.Monic) (h2 : u.natDegree = 2) (hw₀ : v ^ 2 - f = u * w₀)
    (huf : IsCoprime u f) {η : K} (hη : η ≠ 0) {r : K[X]}
    (hρ : AdjoinRoot.mk f u = algebraMap K (AdjoinRoot f) η * AdjoinRoot.mk f r ^ 2)
    (hG : f.leadingCoeff * η ^ 3 * Algebra.norm K (AdjoinRoot.mk f r) =
      -Algebra.norm K (AdjoinRoot.mk u v))
    {L M : K[X]} (hL : L ≠ 0) (hL2 : L.natDegree ≤ 2)
    (hLM : AdjoinRoot.mk f M = AdjoinRoot.mk f L * AdjoinRoot.mk f r)
    (hW0 : C η * M ^ 2 = u * L ^ 2) : False := by
  have h2K : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  have h6 : f.natDegree = 6 := GoodSextic.natDegree_eq
  have hf0 : f ≠ 0 := by rintro rfl; simp at h6
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  obtain ⟨e, rfl, s, hs, hs1, rfl, heM⟩ := sq_decomp hu h2 hL hW0
  have hsf : IsCoprime s f := by
    rw [sq] at huf
    exact huf.of_mul_left_left
  have hsu : IsUnit (AdjoinRoot.mk f s) := isUnit_mk_of_isCoprime hsf
  set ms := AdjoinRoot.mk f s with hms
  set mr := AdjoinRoot.mk f r with hmr
  set mL := AdjoinRoot.mk f L with hmL
  set ae := algebraMap K (AdjoinRoot f) e with hae
  set σi : AdjoinRoot f := ↑hsu.unit⁻¹ with hσi
  have hσ : ms * σi = 1 := hsu.mul_val_inv
  have hρ' : ms ^ 2 = ae ^ 2 * mr ^ 2 := by
    rw [← map_pow, hρ, map_pow]
  have heM' : ae * AdjoinRoot.mk f M = mL * ms := by
    rw [hae, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, ← map_mul, heM, map_mul]
  -- the involution τ = e ρ / s(Θ)
  have hτsq : (ae * mr * σi) ^ 2 = 1 := by
    linear_combination (-(σi ^ 2)) * hρ' + (ms * σi + 1) * hσ
  have hLτ : mL * (ae * mr * σi) = mL := by
    linear_combination (-(ae * σi)) * hLM + σi * heM' + mL * hσ
  -- its norm
  have hNs : Algebra.norm K (AdjoinRoot.mk (s ^ 2) v) = f.leadingCoeff * Algebra.norm K ms :=
    norm_sq_linear h6 hs hs1 ⟨w₀, hw₀⟩
  have hNσ : Algebra.norm K ms * Algebra.norm K σi = 1 := by
    rw [← map_mul, hσ, map_one]
  have hNe : Algebra.norm K ae = e ^ 6 := by
    rw [hae, norm_algebraMap_adjoinRoot_of_ne_zero hf0, h6]
  have hG' : e ^ 6 * Algebra.norm K mr = -Algebra.norm K ms := by
    apply mul_left_cancel₀ hlc
    rw [hNs] at hG
    linear_combination hG
  have hNτ : Algebra.norm K (ae * mr * σi) = -1 := by
    rw [map_mul, map_mul, hNe]
    linear_combination Algebra.norm K σi * hG' - hNσ
  -- a lift P of τ, and the monic associate f₀ of f
  obtain ⟨P, hP⟩ := AdjoinRoot.mk_surjective (ae * mr * σi)
  obtain ⟨hmon, hdeg0, hff⟩ := monic_assoc hf0
  set f0 := C f.leadingCoeff⁻¹ * f with hf0def
  have hf0f : f0 ∣ f := ⟨C f.leadingCoeff, by rw [mul_comm]; exact hff⟩
  have hsqP : f0 ∣ P ^ 2 - 1 := by
    refine hf0f.trans ((AdjoinRoot.mk_eq_zero).mp ?_)
    rw [map_sub, map_pow, hP, hτsq, map_one, sub_self]
  have hLP : f0 ∣ L * (P - 1) := by
    refine hf0f.trans ((AdjoinRoot.mk_eq_zero).mp ?_)
    rw [map_mul, map_sub, hP, map_one, mul_sub, mul_one, hLτ, sub_self]
  have hNP : Algebra.norm K (AdjoinRoot.mk f0 P) = -1 := by
    rw [hf0def, ← norm_mk_eq_norm_mk_monic hf0, hP, hNτ]
  obtain ⟨a, ha⟩ := involution_root h2K hmon hsqP hNP hL hL2 hLP
  apply hroot a
  rw [hff, eval_mul, ha, mul_zero]

/-! ### Step 7 -/

/-- **Step 7.** From `η M² ≡ w v² mod u` and `η N_u(M) = w N_u(v)`: `w/η = s²` and
`M ≡ s v mod u`. -/
theorem exists_s (h2K : (2 : K) ≠ 0) {f u v L M : K[X]} (hu : u.Monic) (h2 : u.natDegree = 2)
    (huv : IsCoprime u v) (huf : u ∣ v ^ 2 - f) {η w : K} (hη : η ≠ 0) (hw : w ≠ 0)
    (hW : C η * M ^ 2 - u * L ^ 2 = C w * f)
    (hNN : η * Algebra.norm K (AdjoinRoot.mk u M) = w * Algebra.norm K (AdjoinRoot.mk u v)) :
    ∃ s : K, s ≠ 0 ∧ η * s ^ 2 = w ∧ u ∣ M - C s * v := by
  have hdeg : u.degree ≠ 0 := by
    rw [degree_eq_natDegree hu.ne_zero, h2]; exact two_ne_zero ∘ (by exact_mod_cast ·)
  have : Nontrivial (AdjoinRoot u) := AdjoinRoot.nontrivial u hdeg
  have hvu : IsUnit (AdjoinRoot.mk u v) := isUnit_mk_of_isCoprime huv.symm
  set mv := AdjoinRoot.mk u v with hmv
  set mM := AdjoinRoot.mk u M with hmM
  set Vi : AdjoinRoot u := ↑hvu.unit⁻¹ with hVi
  have hV : mv * Vi = 1 := hvu.mul_val_inv
  set aη := algebraMap K (AdjoinRoot u) η
  set aw := algebraMap K (AdjoinRoot u) w
  set ai := algebraMap K (AdjoinRoot u) η⁻¹
  have hinv : ai * aη = 1 := by rw [← map_mul, inv_mul_cancel₀ hη, map_one]
  have hM2 : aη * mM ^ 2 = aw * mv ^ 2 := by
    have h1 := congrArg (AdjoinRoot.mk u) hW
    rw [map_sub, map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero, map_mul,
      AdjoinRoot.mk_C, AdjoinRoot.mk_C, map_pow,
      show AdjoinRoot.mk u f = mv ^ 2 from by
        rw [hmv, ← map_pow]; exact (AdjoinRoot.mk_eq_mk.mpr (by rw [← neg_sub, dvd_neg]; exact huf))] at h1
    rw [← AdjoinRoot.algebraMap_eq] at h1
    exact h1
  set t := mM * Vi with ht
  have hwη : algebraMap K (AdjoinRoot u) (w / η) = aw * ai := by
    rw [div_eq_mul_inv, map_mul]
  have ht2 : t ^ 2 = algebraMap K (AdjoinRoot u) (w / η) := by
    rw [hwη]
    linear_combination (Vi ^ 2 * ai) * hM2 + (aw * ai * (mv * Vi + 1)) * hV - (mM ^ 2 * Vi ^ 2) * hinv
  have hNV : Algebra.norm K mv * Algebra.norm K Vi = 1 := by
    rw [← map_mul, hV, map_one]
  have hNt : Algebra.norm K t = w / η := by
    rw [eq_div_iff hη, ht, map_mul]
    linear_combination Algebra.norm K Vi * hNN + w * hNV
  obtain ⟨s, hs⟩ := exists_const_of_sq_eq_norm h2K hu h2 (div_ne_zero hw hη) ht2 hNt
  have hs2 : s ^ 2 = w / η := by
    apply (algebraMap K (AdjoinRoot u)).injective
    rw [map_pow, ← hs, ht2]
  refine ⟨s, ?_, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, div_eq_zero_iff] at hs2
    exact hs2.elim hw hη
  · rw [hs2, mul_div_cancel₀ _ hη]
  · rw [← AdjoinRoot.mk_eq_mk, map_mul, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, ← hs, ht,
      mul_assoc, mul_comm Vi, hV, mul_one]

/-! ### Step 8 -/

/-- **Step 8.** `M' ≡ v mod u` and `M'² - f = u (L²/w)` give `[⟨u, Y - v⟩] = R²` with
`R = [⟨L₀, Y - M'⟩]⁻¹ ∈ Jac f`. -/
theorem exists_half_of_M (f : K[X]) [GoodSextic f] {u v L M' : K[X]} (hu : u.Monic)
    (h2 : u.natDegree = 2) (huv : IsCoprime u v) {w : K} (hw : w ≠ 0) (hL2 : L.natDegree ≤ 2)
    (hM'v : u ∣ M' - v) (hM' : M' ^ 2 - f = u * (C w⁻¹ * L ^ 2)) :
    ∃ R : Jac f, ClassGroup.mk0 (mumford0 f hu.ne_zero v) = (R : Pic f) ^ 2 := by
  have h2K : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  have h6 : f.natDegree = 6 := GoodSextic.natDegree_eq
  have hsq : Squarefree f := GoodSextic.squarefree
  have hlc : ¬ IsSquare f.leadingCoeff := GoodSextic.not_isSquare_leadingCoeff
  have hL2' : L.natDegree = 2 := natDegree_L_eq_two hlc h6 hu h2 (inv_ne_zero hw) hL2 hM'
  have hL0 : L ≠ 0 := by rintro rfl; simp at hL2'
  have hlcL : L.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hL0
  obtain ⟨hmon, hdeg0, hLL⟩ := monic_assoc hL0
  set L0 := C L.leadingCoeff⁻¹ * L with hL0def
  -- coprimality
  have hcopLM : IsCoprime L M' :=
    (isCoprime_of_sq_comb hsq 1 (-(u * C w⁻¹)) (by linear_combination -hM')).symm
  have hcopL0 : IsCoprime L0 M' :=
    (isCoprime_mul_unit_left_left (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero hlcL))) L M').mpr hcopLM
  obtain ⟨k, hk⟩ := hM'v
  have hM'eq : M' = v + u * k := by linear_combination hk
  have hcopuM : IsCoprime u M' := by rw [hM'eq]; exact huv.add_mul_left_right k
  -- the Mumford data of ⟨L₀, Y - M'⟩ and of ⟨L²/w, Y - M'⟩
  set wL := L0 * (u * C (w⁻¹ * L.leadingCoeff ^ 2)) with hwLdef
  have hwL : M' ^ 2 - f = L0 * wL := by
    rw [hM', hwLdef]
    conv_lhs => rw [hLL]
    simp only [C_mul, C_pow]
    ring
  have hcL : ∃ a b c : K[X], a * L0 + b * M' + c * wL = 1 := by
    obtain ⟨a, b, hab⟩ := hcopL0
    exact ⟨a, b, 0, by rw [zero_mul, add_zero]; exact hab⟩
  have hcM : ∃ a b c : K[X], a * u + b * M' + c * (C w⁻¹ * L ^ 2) = 1 := by
    obtain ⟨a, b, hab⟩ := hcopuM
    exact ⟨a, b, 0, by rw [zero_mul, add_zero]; exact hab⟩
  have hL0sq : L0 ^ 2 ∣ M' ^ 2 - f := ⟨u * C (w⁻¹ * L.leadingCoeff ^ 2), by rw [hwL, hwLdef]; ring⟩
  have hassoc : Associated (L0 ^ 2) (C w⁻¹ * L ^ 2) := by
    refine ⟨(isUnit_C.mpr (IsUnit.mk0 (w⁻¹ * L.leadingCoeff ^ 2)
      (mul_ne_zero (inv_ne_zero hw) (pow_ne_zero 2 hlcL)))).unit, ?_⟩
    rw [IsUnit.unit_spec]
    conv_rhs => rw [hLL]
    simp only [C_mul, C_pow]
    ring
  -- the ideal identity ⟨u, Y - v⟩ ⟨L₀, Y - M'⟩² = (Y - M')
  have key : mumford f u v * mumford f L0 M' ^ 2 =
      Ideal.span {Yc f - algebraMap K[X] (CoordRing f) M'} := by
    rw [mumford_sq h2K hL0sq hcopL0, mumford_eq_of_associated f hassoc M',
      show mumford f u v = mumford f u M' by rw [hM'eq, mumford_add_mul]]
    exact mumford_mul_mumford_eq_span h2K hM' hcM
  have hprin : ((mumford0 f hu.ne_zero v * mumford0 f hmon.ne_zero M' ^ 2 :
      (Ideal (CoordRing f))⁰) : Ideal (CoordRing f)).IsPrincipal := by
    rw [Submonoid.coe_mul, SubmonoidClass.coe_pow]
    change (mumford f u v * mumford f L0 M' ^ 2).IsPrincipal
    rw [key]
    exact ⟨⟨_, rfl⟩⟩
  have hprod : ClassGroup.mk0 (mumford0 f hu.ne_zero v) *
      ClassGroup.mk0 (mumford0 f hmon.ne_zero M') ^ 2 = 1 := by
    rw [← map_pow, ← map_mul]
    exact (ClassGroup.mk0_eq_one_iff _).mpr hprin
  have heven : Even L0.natDegree := by rw [hdeg0, hL2']; exact even_two
  refine ⟨(mumfordJac f hmon heven hwL hcL)⁻¹, ?_⟩
  rw [InvMemClass.coe_inv, inv_pow]
  exact eq_inv_of_mul_eq_one_left hprod

/-! ### Steps 4 to 8 -/

/-- **Steps 4 to 8.** Under the good sign (G), the class `[⟨u, Y - v⟩]` is a square in `Jac f`. -/
theorem exists_half_of_good_sign (f : K[X]) [GoodSextic f] (hroot : ∀ a : K, f.eval a ≠ 0)
    {u v w₀ : K[X]} (hu : u.Monic) (h2 : u.natDegree = 2) (hw₀ : v ^ 2 - f = u * w₀)
    (huf : IsCoprime u f) {η : K} (hη : η ≠ 0) {r : K[X]}
    (hρ : AdjoinRoot.mk f u = algebraMap K (AdjoinRoot f) η * AdjoinRoot.mk f r ^ 2)
    (hG : f.leadingCoeff * η ^ 3 * Algebra.norm K (AdjoinRoot.mk f r) =
      -Algebra.norm K (AdjoinRoot.mk u v)) :
    ∃ R : Jac f, ClassGroup.mk0 (mumford0 f hu.ne_zero v) = (R : Pic f) ^ 2 := by
  have h2K : (2 : K) ≠ 0 := GoodSextic.two_ne_zero (f := f)
  have h6 : f.natDegree = 6 := GoodSextic.natDegree_eq
  have hsq : Squarefree f := GoodSextic.squarefree
  have hf0 : f ≠ 0 := by rintro rfl; simp at h6
  obtain ⟨hmon, hdeg0, hff⟩ := monic_assoc hf0
  set f0 := C f.leadingCoeff⁻¹ * f with hf0def
  have hdvd_of : ∀ g : K[X], f0 ∣ g → f ∣ g := fun g ⟨k, hk⟩ =>
    ⟨C f.leadingCoeff⁻¹ * k, by rw [hk, hf0def]; ring⟩
  -- Step 4: L, M and (W)
  obtain ⟨L, hL, hL2, hM3⟩ := exists_L hmon (hdeg0.trans h6) r
  set M := (L * r) %ₘ f0 with hMdef
  have hLM : AdjoinRoot.mk f M = AdjoinRoot.mk f L * AdjoinRoot.mk f r := by
    rw [← map_mul, AdjoinRoot.mk_eq_mk]
    apply hdvd_of
    rw [hMdef, modByMonic_eq_sub_mul_div (L * r) f0]
    exact ⟨-(L * r /ₘ f0), by ring⟩
  have hdvd : f ∣ C η * M ^ 2 - u * L ^ 2 := by
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_mul, map_mul, map_pow, map_pow, AdjoinRoot.mk_C,
      hLM, hρ, ← AdjoinRoot.algebraMap_eq]
    ring
  have hdegP : (C η * M ^ 2 - u * L ^ 2).natDegree ≤ 6 := by
    have h1 : (C η * M ^ 2).natDegree ≤ 6 :=
      (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans (by omega))
    have h1' : (L ^ 2).natDegree ≤ 4 := natDegree_pow_le.trans (by omega)
    have h2' : (u * L ^ 2).natDegree ≤ 6 := natDegree_mul_le.trans (by omega)
    exact (natDegree_sub_le _ _).trans (max_le h1 h2')
  obtain ⟨w, hW⟩ := exists_W h6 hdegP hdvd
  -- Step 5: w ≠ 0
  have hw : w ≠ 0 := by
    rintro rfl
    refine false_of_w_eq_zero f hroot hu h2 hw₀ huf hη hρ hG hL hL2 hLM ?_
    rwa [C_0, zero_mul, sub_eq_zero] at hW
  -- Step 6: the norm formula
  have hLf : IsCoprime L f := isCoprime_L_f hsq hη hw hW
  have hNL : Algebra.norm K (AdjoinRoot.mk f L) ≠ 0 :=
    ((isUnit_mk_of_isCoprime hLf).map (Algebra.norm K)).ne_zero
  have hN := norm_formula h6 hu h2 hL hL2 hM3 hη hw hW
  rw [hLM, map_mul] at hN
  have hN' : f.leadingCoeff * w * η ^ 2 * Algebra.norm K (AdjoinRoot.mk f r) =
      -Algebra.norm K (AdjoinRoot.mk u M) := by
    apply mul_right_cancel₀ hNL
    linear_combination hN
  have hNN : η * Algebra.norm K (AdjoinRoot.mk u M) = w * Algebra.norm K (AdjoinRoot.mk u v) := by
    linear_combination η * hN' - w * hG
  -- Step 7
  have huv := isCoprime_u_v hw₀ huf
  obtain ⟨s, hs0, hηs, hMs⟩ := exists_s h2K hu h2 huv ⟨w₀, hw₀⟩ hη hw hW hNN
  -- Step 8
  refine exists_half_of_M f hu h2 huv hw hL2 (M' := C s⁻¹ * M) ?_ ?_
  · have h : C s⁻¹ * M - v = C s⁻¹ * (M - C s * v) := by
      rw [mul_sub, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hs0, C_1, one_mul]
    rw [h]
    exact dvd_mul_of_dvd_right hMs _
  · apply mul_left_cancel₀ (C_ne_zero.mpr hw : C w ≠ 0)
    have hCw : C w * C w⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hw, C_1]
    have hCs : C w * C s⁻¹ ^ 2 = C η := by
      rw [← C_pow, ← C_mul, ← hηs]
      congr 1
      field_simp
    linear_combination M ^ 2 * hCs + hW - u * L ^ 2 * hCw

end FurioLombardo.Discharge.M3a.K1
