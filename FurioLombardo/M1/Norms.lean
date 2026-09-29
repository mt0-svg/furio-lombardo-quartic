import FurioLombardo.M1.Gens

/-!
# Norms in K21 and the primes (la), (lb), (lc), (pi7)

* `norm_algebraMap_sub_θ`: `N(r - θ) = f(r)` for `r ∈ ℚ` (characteristic polynomial of the power
  basis), so `N(θ) = 4`, `N(θ - 1) = 128`.
* Norm bookkeeping with the kernel identities of Gens.lean: `|N la| = |N lb| = |N lc| = 2`,
  `|N pi7| = 343`.
-/

namespace FurioLombardo.M1

open Polynomial NumberField

theorem fQ_monic : fQ.Monic := fZ_monic.map _

theorem fQ_ne_zero : fQ ≠ 0 := fQ_monic.ne_zero

theorem fQ_natDegree : fQ.natDegree = 21 := by
  rw [fQ, natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)), fZ_natDegree]

theorem finrank_K21 : Module.finrank ℚ K21 = 21 := by
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis fQ_ne_zero), AdjoinRoot.powerBasis_dim,
    fQ_natDegree]

theorem minpoly_θ : minpoly ℚ θ = fQ :=
  (minpoly.eq_of_irreducible_of_monic fQ_irreducible
    ((AdjoinRoot.aeval_eq fQ).trans AdjoinRoot.mk_self) fQ_monic).symm

/-- `N(r - θ) = f(r)`. -/
theorem norm_algebraMap_sub_θ (r : ℚ) : Algebra.norm ℚ (algebraMap ℚ K21 r - θ) = fQ.eval r := by
  let pb := AdjoinRoot.powerBasis fQ_ne_zero
  have hgen : pb.gen = θ := AdjoinRoot.powerBasis_gen fQ_ne_zero
  refine (Algebra.norm_eq_matrix_det pb.basis (algebraMap ℚ K21 r - θ)).trans ?_
  have hc : Algebra.leftMulMatrix pb.basis (algebraMap ℚ K21 r) = Matrix.scalar _ r := by
    have := (Algebra.leftMulMatrix pb.basis).commutes r
    refine this.trans ?_
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
    rfl
  rw [map_sub, hc]
  have h1 : (Algebra.leftMulMatrix pb.basis θ).charpoly = fQ := by
    have h := charpoly_leftMulMatrix pb
    rw [hgen] at h
    exact h.trans minpoly_θ
  calc _ = (Algebra.leftMulMatrix pb.basis θ).charpoly.eval r := (Matrix.eval_charpoly _ r).symm
    _ = fQ.eval r := by rw [h1]

theorem fQ_eval_int (n : ℤ) : fQ.eval (n : ℚ) = ((fZ.eval n : ℤ) : ℚ) := by
  rw [fQ, eval_map, eval₂_at_intCast]; rfl

/-! ## Norms of elements of `𝓞 K21` -/

/-- The norm `𝓞 K21 → ℤ`. -/
noncomputable def nZ (x : 𝓞 K21) : ℤ := Algebra.norm ℤ x

theorem nZ_cast (x : 𝓞 K21) : (nZ x : ℚ) = Algebra.norm ℚ (x : K21) := Algebra.coe_norm_int x

theorem nZ_mul (x y : 𝓞 K21) : nZ (x * y) = nZ x * nZ y := map_mul _ _ _

theorem nZ_pow (x : 𝓞 K21) (n : ℕ) : nZ (x ^ n) = nZ x ^ n := map_pow _ _ _

theorem nZ_one : nZ 1 = 1 := map_one _

theorem normQ_algebraMap (q : ℚ) : Algebra.norm ℚ (algebraMap ℚ K21 q) = q ^ 21 := by
  rw [Algebra.norm_algebraMap, finrank_K21]

theorem nZ_intCast (n : ℤ) : nZ (n : 𝓞 K21) = n ^ 21 := by
  have h := nZ_cast (n : 𝓞 K21)
  rw [show ((n : 𝓞 K21) : K21) = algebraMap ℚ K21 (n : ℚ) by simp, normQ_algebraMap] at h
  exact_mod_cast h

theorem nZ_θO_sub (n : ℤ) : nZ (θO - (n : 𝓞 K21)) = -(fZ.eval n) := by
  have h := nZ_cast (θO - (n : 𝓞 K21))
  have h2 : ((θO - (n : 𝓞 K21) : 𝓞 K21) : K21) =
      algebraMap ℚ K21 (-1) * (algebraMap ℚ K21 (n : ℚ) - θ) := by
    simp
  rw [h2, map_mul, normQ_algebraMap, norm_algebraMap_sub_θ, fQ_eval_int] at h
  have : ((nZ (θO - (n : 𝓞 K21)) : ℤ) : ℚ) = ((-(fZ.eval n) : ℤ) : ℚ) := by
    rw [h]; push_cast; ring
  exact_mod_cast this

theorem fZ_eval_zero : fZ.eval 0 = -4 := by simp [fZ]
theorem fZ_eval_one : fZ.eval 1 = -128 := by simp [fZ]

theorem nZ_θO : nZ θO = 4 := by
  have := nZ_θO_sub 0
  simpa [fZ_eval_zero] using this

theorem nZ_θO_sub_one : nZ (θO - 1) = 128 := by
  have := nZ_θO_sub 1
  simpa [fZ_eval_one] using this

theorem nZ_unit {x y : 𝓞 K21} (h : x * y = 1) : nZ x = 1 ∨ nZ x = -1 := by
  have := congrArg nZ h
  rw [nZ_mul, nZ_one] at this
  exact Int.eq_one_or_neg_one_of_mul_eq_one this

theorem natAbs_nZ_unit {x y : 𝓞 K21} (h : x * y = 1) : (nZ x).natAbs = 1 := by
  rcases nZ_unit h with h1 | h1 <;> simp [h1]

/-! ## The bookkeeping -/

theorem natAbs_nZ_eO (i : ℕ) (hi : i < 4) : (nZ (eO i)).natAbs = 1 :=
  natAbs_nZ_unit (eO_mul_eIO i hi)

/-- `|N la| = 2`, `|N lb| = 2`, `|N lc| = 2`. -/
theorem natAbs_nZ_lb : (nZ (gO 13)).natAbs = 2 := by
  have h := congrArg (fun x => (nZ x).natAbs) θO_eq
  simp only [nZ_mul, nZ_pow, Int.natAbs_mul, Int.natAbs_pow, natAbs_nZ_eO 1 (by norm_num),
    nZ_θO, one_mul] at h
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [show (Int.natAbs 4) = 2 ^ 2 by norm_num] at h
  exact (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h).symm

theorem natAbs_nZ_la_lc : (nZ (gO 12)).natAbs = 2 ∧ (nZ (gO 14)).natAbs = 2 := by
  have h1 := congrArg (fun x => (nZ x).natAbs) two_eq
  have h2 := congrArg (fun x => (nZ x).natAbs) θO_sub_one_eq
  simp only [nZ_mul, nZ_pow, Int.natAbs_mul, Int.natAbs_pow, natAbs_nZ_eO 0 (by norm_num),
    natAbs_nZ_eO 2 (by norm_num), natAbs_nZ_lb, one_mul, nZ_θO_sub_one] at h1 h2
  have h1' : (2 : ℕ) ^ 21 = (nZ (gO 12)).natAbs ^ 3 * 2 ^ 12 * (nZ (gO 14)).natAbs ^ 6 := by
    rw [← h1]
    have := nZ_intCast 2
    simp only [Int.cast_ofNat] at this
    rw [this]; norm_num
  have h2' : (128 : ℕ) = (nZ (gO 12)).natAbs ^ 4 * (nZ (gO 14)).natAbs ^ 3 := by
    rw [← h2]; norm_num
  generalize (nZ (gO 12)).natAbs = a at h1' h2' ⊢
  generalize (nZ (gO 14)).natAbs = c at h1' h2' ⊢
  have ha : a ≤ 3 := by
    by_contra h; push Not at h
    have : 4 ^ 4 ≤ a ^ 4 := Nat.pow_le_pow_left h 4
    have hc : 1 ≤ c ^ 3 := by
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · simp at h2'
      · exact Nat.one_le_pow _ _ hc
    nlinarith
  have hc : c ≤ 5 := by
    by_contra h; push Not at h
    have : 6 ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left h 3
    have ha1 : 1 ≤ a ^ 4 := by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp at h2'
      · exact Nat.one_le_pow _ _ ha
    nlinarith
  interval_cases a <;> interval_cases c <;> revert h1' h2' <;> decide

theorem natAbs_nZ_la : (nZ (gO 12)).natAbs = 2 := natAbs_nZ_la_lc.1

theorem natAbs_nZ_lc : (nZ (gO 14)).natAbs = 2 := natAbs_nZ_la_lc.2

/-- `|N pi7| = 343`. -/
theorem natAbs_nZ_pi7 : (nZ (gO 15)).natAbs = 343 := by
  have h := congrArg (fun x => (nZ x).natAbs) seven_eq
  simp only [nZ_mul, nZ_pow, Int.natAbs_mul, Int.natAbs_pow, natAbs_nZ_eO 3 (by norm_num),
    one_mul] at h
  have h7 := nZ_intCast 7
  simp only [Int.cast_ofNat] at h7
  rw [h7] at h
  have : (343 : ℕ) ^ 7 = (nZ (gO 15)).natAbs ^ 7 := by rw [← h]; norm_num
  exact (Nat.pow_left_injective (by norm_num : (7 : ℕ) ≠ 0) this).symm

end FurioLombardo.M1
