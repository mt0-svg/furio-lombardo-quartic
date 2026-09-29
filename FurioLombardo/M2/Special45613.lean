import FurioLombardo.M2.Special

/-!
# The special prime 45613 (lane M2)

`γ = Σ gam_j w_j` has characteristic polynomial `χ = X^21 + chiG` (kernel check `chi_gam`) and
`M θ = H(γ)` with `M = MG`, `H = HG` (kernel check `H_gam`). Hence `ℚ⟮γ⟯ = K21`, the minimal
polynomial of `γ` is `χ`, and `|N(γ)| = |χ(0)| = 45613`. A prime `P` above 45613 with
`45613 ^ f(P) ≤ Bnd` has `f(P) = 1`; the factor certificate `fac45` (the only root of `χ` modulo
45613 is `0`) puts `γ` in `P`, so `P = (γ)`.
-/

namespace FurioLombardo.M2

open Polynomial NumberField Ideal IntermediateField Special

theorem evalZ_mem_intermediateField (S : IntermediateField ℚ K21) (y : K21) (hy : y ∈ S) :
    ∀ l : List ℤ, evalZ y l ∈ S
  | [] => by rw [evalZ_nil]; exact S.zero_mem
  | a :: l => by
    rw [evalZ_cons]
    exact S.add_mem (intCast_mem S a) (S.mul_mem hy (evalZ_mem_intermediateField S y hy l))

theorem DD_mul_gam : (DD : 𝓞 K21) * elt gam = evalZ θ gamW := by
  have h := evalZ_eq_zero_of_forall θ _ ((allZero_iff _).mp gamW_eq)
  rw [evalZ_addZ, evalZ_smulZ, comboK_eq, ← DD_mul_elt] at h
  push_cast at h
  linear_combination h

theorem gam_root : elt gam ^ 21 + evalZ (elt gam) chiG = 0 := by
  have key := evalZ_homogL θ (elt gam) fLow gamW DD (root_fLow θ evalZ_θ_fL) DD_mul_gam
    (chiG ++ [1])
  rw [evalZ_eq_zero_of_forall _ _ ((allZero_iff _).mp chi_gam), mul_zero, evalZ_append,
    chiG_len.1] at key
  have h0 := (mul_eq_zero.mp key.symm).resolve_left (pow_ne_zero _ DD_ne_zero_O)
  simp only [evalZ_cons, evalZ_nil, mul_zero, add_zero, Int.cast_one, mul_one] at h0
  linear_combination h0

theorem gam_H : evalZ (elt gam) HG = (MG : 𝓞 K21) * θ := by
  have key := evalZ_homogL θ (elt gam) fLow gamW DD (root_fLow θ evalZ_θ_fL) DD_mul_gam HG
  rw [chiG_len.2] at key
  have h := evalZ_eq_zero_of_forall θ _ ((allZero_iff _).mp H_gam)
  rw [evalZ_addZ] at h
  simp only [evalZ_cons, evalZ_nil, mul_zero, add_zero] at h
  push_cast at h
  have h2 : (DD : 𝓞 K21) ^ 21 * (evalZ (elt gam) HG - MG * θ) = 0 := by
    linear_combination -key + (DD : 𝓞 K21) * h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ DD_ne_zero_O))

theorem adjoin_gam_eq_top : ℚ⟮((elt gam : 𝓞 K21) : K21)⟯ = ⊤ := by
  have hH : evalZ ((elt gam : 𝓞 K21) : K21) HG = (MG : K21) * AdjoinRoot.root fQ := by
    rw [← evalZ_coe_O, gam_H, RingOfIntegers.coe_eq_algebraMap, map_mul, map_intCast,
      ← RingOfIntegers.coe_eq_algebraMap, coe_θ]
  have hMG : (MG : K21) ≠ 0 := by
    have : MG ≠ 0 := by unfold MG; norm_num
    exact_mod_cast this
  have hroot : AdjoinRoot.root fQ ∈ ℚ⟮((elt gam : 𝓞 K21) : K21)⟯ := by
    have hmem := evalZ_mem_intermediateField ℚ⟮((elt gam : 𝓞 K21) : K21)⟯ _
      (mem_adjoin_simple_self ℚ ((elt gam : 𝓞 K21) : K21)) HG
    rw [hH] at hmem
    have := IntermediateField.mul_mem _ (IntermediateField.inv_mem _ (intCast_mem _ MG)) hmem
    rwa [← mul_assoc, inv_mul_cancel₀ hMG, one_mul] at this
  have htop : ℚ⟮AdjoinRoot.root fQ⟯ = (⊤ : IntermediateField ℚ K21) := adjoin_root_eq_top fQ
  rw [eq_top_iff, ← htop, adjoin_simple_le_iff]
  exact hroot

theorem natDegree_minpoly_gam : (minpoly ℚ ((elt gam : 𝓞 K21) : K21)).natDegree = 21 := by
  have hint : IsIntegral ℚ ((elt gam : 𝓞 K21) : K21) := Algebra.IsIntegral.isIntegral _
  rw [← adjoin.finrank hint, adjoin_gam_eq_top, IntermediateField.finrank_top', finrank_K21]

theorem minpoly_gam : minpoly ℚ ((elt gam : 𝓞 K21) : K21) = toPoly ℚ (chiG ++ [1]) := by
  have hint : IsIntegral ℚ ((elt gam : 𝓞 K21) : K21) := Algebra.IsIntegral.isIntegral _
  have hmon := monic_toPoly (R := ℚ) (chiG ++ [1]) (by simp)
  have haev : aeval ((elt gam : 𝓞 K21) : K21) (toPoly ℚ (chiG ++ [1])) = 0 := by
    rw [aeval_toPoly, evalZ_append, chiG_len.1]
    have h := congrArg (algebraMap (𝓞 K21) K21) gam_root
    rw [map_add, map_pow, map_zero, evalZ_map, ← RingOfIntegers.coe_eq_algebraMap] at h
    simp only [evalZ_cons, evalZ_nil, mul_zero, add_zero, Int.cast_one, mul_one]
    linear_combination h
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon.1
    (minpoly.dvd ℚ _ haev) ?_).symm
  rw [hmon.2, natDegree_minpoly_gam]
  simp [chiG_len.1]

theorem absNorm_gam : absNorm (span {elt gam}) = 45613 := by
  have h := absNorm_span_eq (elt gam)
  rw [norm_eq_of_natDegree _ natDegree_minpoly_gam, minpoly_gam, coeff_toPoly] at h
  have hv : ((chiG ++ [1]).getD 0 0 : ℤ) = -45613 := by decide
  have hv2 : |-(((-45613 : ℤ) : ℚ))| = 45613 := by norm_num
  rw [hv, hv2] at h
  exact_mod_cast h

instance fact_prime_45613 : Fact (Nat.Prime 45613) := ⟨by norm_num⟩

theorem special_45613 (P : Ideal (𝓞 K21)) (hP : P ∈ primesOver (span {(45613 : ℤ)}) (𝓞 K21))
    (hPB : 45613 ^ P.inertiaDeg ℤ ≤ Bnd) : Submodule.IsPrincipal P := by
  have hp : Nat.Prime 45613 := fact_prime_45613.out
  have hPp : P.IsPrime := hP.1
  have hf : P.inertiaDeg ℤ = 1 := by
    have hpos : 0 < P.inertiaDeg ℤ := by
      have : P.LiesOver (span {((45613 : ℕ) : ℤ)}) := hP.2
      have : (span {((45613 : ℕ) : ℤ)}).IsMaximal :=
        Int.ideal_span_isMaximal_of_prime 45613
      exact inertiaDeg_pos ..
    by_contra hc
    have h2 : 45613 ^ 2 ≤ 45613 ^ P.inertiaDeg ℤ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 := h2.trans hPB
    unfold Bnd at h3
    norm_num at h3
  have hlt : 45613 ^ P.inertiaDeg ℤ < 2 ^ 64 := by rw [hf]; norm_num
  have hfacs : ∀ fac ∈ [facX], fac.L.length = fac.deg + 1 ∧ ∀ z ∈ fac.L, z < 45613 := by
    decide
  obtain ⟨fac, hfac, _, hmem⟩ := residue_factor hp (by norm_num) hP hlt (elt gam) chiG
    chiG_len.1 gam_root [facX] hfacs s45 (by rw [hf]; exact fac45)
  rw [List.mem_singleton] at hfac
  subst hfac
  have hx : elt gam ∈ P := by simpa [facX, evalZ] using hmem
  exact ⟨⟨_, eq_span_of_absNorm_prime P _ hx (by rw [absNorm_gam]; exact hp)⟩⟩

end FurioLombardo.M2
