import FurioLombardo.M2.Mul

/-!
# Norms in K21 (lane M2)

For `x ∈ K21` whose minimal polynomial over `ℚ` has degree 21, `N(x) = -χ(0)`
(`norm_eq_of_natDegree`, through `Algebra.norm_eq_norm_adjoin` and the power basis of `ℚ⟮x⟯`).
Hence `|N(θ)| = 4`, `|N(θ - 1)| = 128`, and `absNorm (n) = n ^ 21` for `n ∈ ℕ`.
-/

namespace FurioLombardo.M2

open Polynomial NumberField Ideal IntermediateField

theorem fQ_monic : fQ.Monic := fZ_monic.map _

theorem fQ_natDegree : fQ.natDegree = 21 := by
  rw [fQ, fZ_monic.natDegree_map, fZ_natDegree]

theorem fQ_ne_zero : fQ ≠ 0 := fQ_monic.ne_zero

theorem finrank_K21 : Module.finrank ℚ K21 = 21 := by
  rw [(AdjoinRoot.powerBasis fQ_ne_zero).finrank, AdjoinRoot.powerBasis_dim, fQ_natDegree]

theorem finrank_O : Module.finrank ℤ (𝓞 K21) = 21 := by
  rw [RingOfIntegers.rank, finrank_K21]

theorem norm_eq_of_natDegree (x : K21) (hx : (minpoly ℚ x).natDegree = 21) :
    Algebra.norm ℚ x = -(minpoly ℚ x).coeff 0 := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  rw [Algebra.norm_eq_norm_adjoin ℚ x]
  have h1 : Module.finrank ℚ ℚ⟮x⟯ = 21 := by rw [adjoin.finrank hint, hx]
  have h2 : Module.finrank ℚ⟮x⟯ K21 = 1 := by
    have := Module.finrank_mul_finrank ℚ ℚ⟮x⟯ K21
    rw [h1, finrank_K21] at this; omega
  have h3 := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hint)
  rw [adjoin.powerBasis_gen, adjoin.powerBasis_dim, minpoly_gen, hx] at h3
  rw [h2, pow_one, h3]
  norm_num

theorem absNorm_span_eq (y : 𝓞 K21) :
    ((absNorm (span {y}) : ℕ) : ℚ) = |Algebra.norm ℚ (y : K21)| := by
  rw [absNorm_span_singleton, Nat.cast_natAbs, ← Algebra.coe_norm_int, Int.cast_abs]

theorem aeval_root_fQ : aeval (AdjoinRoot.root fQ) fQ = 0 := by
  show aeval (AdjoinRoot.root fQ) (fZ.map (Int.castRingHom ℚ)) = 0
  rw [← algebraMap_int_eq, aeval_map_algebraMap]; exact aeval_root_fZ

theorem minpoly_root : minpoly ℚ (AdjoinRoot.root fQ) = fQ :=
  (minpoly.eq_of_irreducible_of_monic fQ_irreducible aeval_root_fQ fQ_monic).symm

theorem eval_fQ (c : ℚ) : fQ.eval c = evalZ c fL := by
  rw [fQ, eval_map, ← algebraMap_int_eq, ← aeval_def, aeval_fZ_eq]

theorem absNorm_θ : absNorm (span {θ}) = 4 := by
  have h := absNorm_span_eq θ
  rw [coe_θ, norm_eq_of_natDegree _ (by rw [minpoly_root, fQ_natDegree]), minpoly_root,
    coeff_zero_eq_eval_zero, eval_fQ] at h
  have hv : |-evalZ (0 : ℚ) fL| = 4 := by norm_num [evalZ, fL]
  rw [hv] at h
  exact_mod_cast h

theorem absNorm_θ_sub_one : absNorm (span {θ - 1}) = 128 := by
  have hmin : minpoly ℚ (AdjoinRoot.root fQ - 1) = fQ.comp (X + C 1) := by
    have := minpoly.sub_algebraMap (A := ℚ) (AdjoinRoot.root fQ) 1
    rwa [map_one, minpoly_root] at this
  have hdeg : (fQ.comp (X + C 1)).natDegree = 21 := by
    rw [natDegree_comp, fQ_natDegree, natDegree_X_add_C]
  have h := absNorm_span_eq (θ - 1)
  rw [show ((θ - 1 : 𝓞 K21) : K21) = AdjoinRoot.root fQ - 1 by rw [← coe_θ]; push_cast; rfl,
    norm_eq_of_natDegree _ (by rw [hmin, hdeg]), hmin, coeff_zero_eq_eval_zero, eval_comp] at h
  simp only [eval_add, eval_X, eval_C, zero_add, eval_fQ] at h
  have hv : |-evalZ (1 : ℚ) fL| = 128 := by norm_num [evalZ, fL]
  rw [hv] at h
  exact_mod_cast h

theorem absNorm_natCast (m : ℕ) : absNorm (span {(m : 𝓞 K21)}) = m ^ 21 := by
  rw [absNorm_span_singleton, show (m : 𝓞 K21) = algebraMap ℤ (𝓞 K21) m by simp,
    Algebra.norm_algebraMap, finrank_O]
  simp [Int.natAbs_pow]

theorem absNorm_mul (x y : 𝓞 K21) :
    absNorm (span {x * y}) = absNorm (span {x}) * absNorm (span {y}) := by
  rw [← span_singleton_mul_span_singleton, map_mul]

theorem absNorm_pow (x : 𝓞 K21) (k : ℕ) : absNorm (span {x ^ k}) = absNorm (span {x}) ^ k := by
  rw [← span_singleton_pow, map_pow]

theorem absNorm_of_mul_eq_one (u v : 𝓞 K21) (h : u * v = 1) : absNorm (span {u}) = 1 := by
  have := absNorm_mul u v
  rw [h, span_singleton_one, absNorm_top] at this
  exact Nat.eq_one_of_mul_eq_one_right this.symm

end FurioLombardo.M2
