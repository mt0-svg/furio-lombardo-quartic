import FurioLombardo.Discharge.M3a.AbelPrym

/-!
# The ruling identity from the isotropy of the tangent plane (WP4 of the M3a discharge)

General algebra behind Bruin's construction, over any commutative ring `R`:

* `hodge_blk`: for the block matrix `G = diag(m, g)` (`m` a symmetric `3 × 3` matrix) and an
  antisymmetric `A`, `G ⋆(G A G) G = (g det m) ⋆A` (`⋆` = `hodge`);
* `cramer`: if `Ω` is antisymmetric with zero diagonal, `Ω a = Ω b = 0`, and one of the minors
  `A₁₂, A₂₀, A₀₁` of `A = plucker a b` is a unit, then `Ω = y ⋆A` for some `y`;
* `ruling_exists`: for `Ω = G A G` with `Ω a = Ω b = 0` (the plane spanned by `a, b` is totally
  isotropic for `G`) and a unit minor, `G A G = y ⋆A` with `y² = g det m`.

For Bruin's data (`gram M1 M2 M3 δ = blk (pencil M1 M2 M3) (-C δ)`): `bil_self`, `two_bil` compute
`plk P ⬝ G plk W` in terms of `quadD`, `polarD`; at a point `x` with a tangent vector `T`, the plane
spanned by `plk x`, `plk T` is totally isotropic modulo `U = bruinU T` (`gram_mulVec_pt`,
`gram_mulVec_T`). Applied in `L[X] ⧸ (U)` this gives the whole ruling identity and `U ∣ V² - f`
from one entry (`Cert.ofEntry`), and the existence of `V` (`exists_V`).
-/

open Polynomial Matrix
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.M3a.AbelPrym

section Algebra

variable {R : Type*} [CommRing R]

/-- The block matrix `diag(m, g)`. -/
def blk (m : Matrix (Fin 3) (Fin 3) R) (g : R) : Matrix (Fin 4) (Fin 4) R :=
  !![m 0 0, m 0 1, m 0 2, 0; m 1 0, m 1 1, m 1 2, 0; m 2 0, m 2 1, m 2 2, 0; 0, 0, 0, g]

/-- The antisymmetric matrix with upper entries `a01, a02, a03, a12, a13, a23`. -/
def asym (a01 a02 a03 a12 a13 a23 : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, a01, a02, a03; -a01, 0, a12, a13; -a02, -a12, 0, a23; -a03, -a13, -a23, 0]

theorem hodge_blk_asym (m00 m01 m02 m11 m12 m22 g a01 a02 a03 a12 a13 a23 : R) :
    blk !![m00, m01, m02; m01, m11, m12; m02, m12, m22] g * hodge (blk
      !![m00, m01, m02; m01, m11, m12; m02, m12, m22] g * asym a01 a02 a03 a12 a13 a23 * blk
      !![m00, m01, m02; m01, m11, m12; m02, m12, m22] g) *
      blk !![m00, m01, m02; m01, m11, m12; m02, m12, m22] g =
    (g * (m00 * (m11 * m22 - m12 * m12) - m01 * (m01 * m22 - m12 * m02) +
      m02 * (m01 * m12 - m11 * m02))) • hodge (asym a01 a02 a03 a12 a13 a23) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, asym, hodge, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

omit [CommRing R] in
theorem eq_sym3 (m : Matrix (Fin 3) (Fin 3) R) (hm : ∀ i j, m j i = m i j) :
    m = !![m 0 0, m 0 1, m 0 2; m 0 1, m 1 1, m 1 2; m 0 2, m 1 2, m 2 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> exact hm _ _

theorem det_sym3 (m : Matrix (Fin 3) (Fin 3) R) (hm : ∀ i j, m j i = m i j) :
    m.det = m 0 0 * (m 1 1 * m 2 2 - m 1 2 * m 1 2) - m 0 1 * (m 0 1 * m 2 2 - m 1 2 * m 0 2) +
      m 0 2 * (m 0 1 * m 1 2 - m 1 1 * m 0 2) := by
  rw [det_fin_three, hm 1 0, hm 2 0, hm 2 1]; ring

theorem plucker_eq_asym (a b : Fin 4 → R) :
    plucker a b = asym (a 0 * b 1 - a 1 * b 0) (a 0 * b 2 - a 2 * b 0) (a 0 * b 3 - a 3 * b 0)
      (a 1 * b 2 - a 2 * b 1) (a 1 * b 3 - a 3 * b 1) (a 2 * b 3 - a 3 * b 2) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [plucker, asym, vecMulVec_apply] <;> ring

/-- **The square of the ruling operator.** `G ⋆(G A G) G = (g det m) ⋆A` for `G = diag(m, g)`,
`m` symmetric, `A = a bᵀ - b aᵀ`. -/
theorem hodge_blk (m : Matrix (Fin 3) (Fin 3) R) (hm : ∀ i j, m j i = m i j) (g : R)
    (a b : Fin 4 → R) :
    blk m g * hodge (blk m g * plucker a b * blk m g) * blk m g =
      (g * m.det) • hodge (plucker a b) := by
  rw [det_sym3 m hm, eq_sym3 m hm, plucker_eq_asym]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.head_fin_const]
  exact hodge_blk_asym _ _ _ _ _ _ _ _ _ _ _ _ _

theorem hodge_hodge_plucker (a b : Fin 4 → R) : hodge (hodge (plucker a b)) = plucker a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hodge, plucker, vecMulVec_apply] <;> ring

theorem hodge_smul' (r : R) (A : Matrix (Fin 4) (Fin 4) R) : hodge (r • A) = r • hodge A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hodge]

/-- `(G A G) w = (b ⬝ G w) G a - (a ⬝ G w) G b` for `A = a bᵀ - b aᵀ`. -/
theorem mul_plucker_mul_mulVec (G : Matrix (Fin 4) (Fin 4) R) (a b w : Fin 4 → R) :
    (G * plucker a b * G) *ᵥ w = (b ⬝ᵥ (G *ᵥ w)) • (G *ᵥ a) - (a ⬝ᵥ (G *ᵥ w)) • (G *ᵥ b) := by
  ext i
  simp only [mulVec, dotProduct, Fin.sum_univ_four, plucker, Matrix.sub_apply, vecMulVec_apply,
    Matrix.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring


/-- Cramer's rule for the kernel condition, with the unit minor `a₁ b₂ - a₂ b₁`, in scalars:
`Ω = asym w01 w02 w03 w12 w13 w23` kills `a` and `b` (rows 0, 1, 3 of `Ω a = Ω b = 0`). -/
theorem cramer_scalar (a0 a1 a2 a3 b0 b1 b2 b3 w01 w02 w03 w12 w13 w23 : R)
    (r0a : w01 * a1 + w02 * a2 + w03 * a3 = 0) (r1a : -w01 * a0 + w12 * a2 + w13 * a3 = 0)
    (r3a : -w03 * a0 - w13 * a1 - w23 * a2 = 0)
    (r0b : w01 * b1 + w02 * b2 + w03 * b3 = 0) (r1b : -w01 * b0 + w12 * b2 + w13 * b3 = 0)
    (r3b : -w03 * b0 - w13 * b1 - w23 * b2 = 0) (hu : IsUnit (a1 * b2 - a2 * b1)) :
    (a1 * b2 - a2 * b1) * w01 = w03 * (a2 * b3 - a3 * b2) ∧
    (a1 * b2 - a2 * b1) * w02 = w03 * (a3 * b1 - a1 * b3) ∧
    (a1 * b2 - a2 * b1) * w12 = w03 * (a0 * b3 - a3 * b0) ∧
    (a1 * b2 - a2 * b1) * w13 = w03 * (a2 * b0 - a0 * b2) ∧
    (a1 * b2 - a2 * b1) * w23 = w03 * (a0 * b1 - a1 * b0) := by
  have e01 : (a1 * b2 - a2 * b1) * w01 = w03 * (a2 * b3 - a3 * b2) := by
    linear_combination b2 * r0a - a2 * r0b
  have e02 : (a1 * b2 - a2 * b1) * w02 = w03 * (a3 * b1 - a1 * b3) := by
    linear_combination a1 * r0b - b1 * r0a
  have e13 : (a1 * b2 - a2 * b1) * w13 = w03 * (a2 * b0 - a0 * b2) := by
    linear_combination a2 * r3b - b2 * r3a
  have e23 : (a1 * b2 - a2 * b1) * w23 = w03 * (a0 * b1 - a1 * b0) := by
    linear_combination b1 * r3a - a1 * r3b
  have e12 : (a1 * b2 - a2 * b1) * ((a1 * b2 - a2 * b1) * w12) =
      (a1 * b2 - a2 * b1) * (w03 * (a0 * b3 - a3 * b0)) := by
    linear_combination a1 * (a1 * b2 - a2 * b1) * r1b - b1 * (a1 * b2 - a2 * b1) * r1a -
      (a0 * b1 - a1 * b0) * e01 - (a1 * b3 - a3 * b1) * e13
  exact ⟨e01, e02, hu.mul_left_cancel e12, e13, e23⟩

/-- An antisymmetric matrix with zero diagonal is `asym` of its upper entries. -/
theorem eq_asym (Ω : Matrix (Fin 4) (Fin 4) R) (hdiag : ∀ i, Ω i i = 0)
    (hanti : ∀ i j, Ω j i = -Ω i j) :
    Ω = asym (Ω 0 1) (Ω 0 2) (Ω 0 3) (Ω 1 2) (Ω 1 3) (Ω 2 3) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [asym, hdiag] <;> exact hanti _ _

theorem mulVec_asym (a01 a02 a03 a12 a13 a23 : R) (a : Fin 4 → R) :
    asym a01 a02 a03 a12 a13 a23 *ᵥ a =
      ![a01 * a 1 + a02 * a 2 + a03 * a 3, -a01 * a 0 + a12 * a 2 + a13 * a 3,
        -a02 * a 0 - a12 * a 1 + a23 * a 3, -a03 * a 0 - a13 * a 1 - a23 * a 2] := by
  ext i; fin_cases i <;> simp [asym, mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem smul_asym_eq (c d a01 a02 a03 a12 a13 a23 h01 h02 h03 h12 h13 h23 : R)
    (e01 : c * a01 = d * h01) (e02 : c * a02 = d * h02) (e03 : c * a03 = d * h03)
    (e12 : c * a12 = d * h12) (e13 : c * a13 = d * h13) (e23 : c * a23 = d * h23) :
    c • asym a01 a02 a03 a12 a13 a23 = d • asym h01 h02 h03 h12 h13 h23 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [asym] <;>
    first
    | linear_combination e01 | linear_combination e02 | linear_combination e03
    | linear_combination e12 | linear_combination e13 | linear_combination e23

theorem hodge_plucker_eq (a b : Fin 4 → R) :
    hodge (plucker a b) = asym (a 2 * b 3 - a 3 * b 2) (a 3 * b 1 - a 1 * b 3)
      (a 1 * b 2 - a 2 * b 1) (a 0 * b 3 - a 3 * b 0) (a 2 * b 0 - a 0 * b 2)
      (a 0 * b 1 - a 1 * b 0) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hodge, plucker, asym, vecMulVec_apply] <;> ring


/-- **Cramer's rule**: an antisymmetric `Ω` with zero diagonal killing `a` and `b` is a multiple
of `⋆(a bᵀ - b aᵀ)`, as soon as one of the minors `A₁₂, A₂₀, A₀₁` is a unit. -/
theorem cramer (a b : Fin 4 → R) (Ω : Matrix (Fin 4) (Fin 4) R) (hdiag : ∀ i, Ω i i = 0)
    (hanti : ∀ i j, Ω j i = -Ω i j) (ha : Ω *ᵥ a = 0) (hb : Ω *ᵥ b = 0)
    (hu : IsUnit (a 1 * b 2 - a 2 * b 1) ∨ IsUnit (a 2 * b 0 - a 0 * b 2) ∨
      IsUnit (a 0 * b 1 - a 1 * b 0)) :
    ∃ y : R, Ω = y • hodge (plucker a b) := by
  rw [eq_asym Ω hdiag hanti, mulVec_asym] at ha hb
  have ha0 : Ω 0 1 * a 1 + Ω 0 2 * a 2 + Ω 0 3 * a 3 = 0 := congrFun ha 0
  have ha1 : -Ω 0 1 * a 0 + Ω 1 2 * a 2 + Ω 1 3 * a 3 = 0 := congrFun ha 1
  have ha2 : -Ω 0 2 * a 0 - Ω 1 2 * a 1 + Ω 2 3 * a 3 = 0 := congrFun ha 2
  have ha3 : -Ω 0 3 * a 0 - Ω 1 3 * a 1 - Ω 2 3 * a 2 = 0 := congrFun ha 3
  have hb0 : Ω 0 1 * b 1 + Ω 0 2 * b 2 + Ω 0 3 * b 3 = 0 := congrFun hb 0
  have hb1 : -Ω 0 1 * b 0 + Ω 1 2 * b 2 + Ω 1 3 * b 3 = 0 := congrFun hb 1
  have hb2 : -Ω 0 2 * b 0 - Ω 1 2 * b 1 + Ω 2 3 * b 3 = 0 := congrFun hb 2
  have hb3 : -Ω 0 3 * b 0 - Ω 1 3 * b 1 - Ω 2 3 * b 2 = 0 := congrFun hb 3
  rw [eq_asym Ω hdiag hanti, hodge_plucker_eq]
  rcases hu with hu | hu | hu
  · obtain ⟨e01, e02, e12, e13, e23⟩ := cramer_scalar (a 0) (a 1) (a 2) (a 3) (b 0) (b 1) (b 2)
      (b 3) (Ω 0 1) (Ω 0 2) (Ω 0 3) (Ω 1 2) (Ω 1 3) (Ω 2 3) ha0 ha1 ha3 hb0 hb1 hb3 hu
    refine ⟨↑hu.unit⁻¹ * Ω 0 3, ?_⟩
    have h := smul_asym_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ e01 e02 (mul_comm _ _) e12 e13 e23
    rw [mul_smul, ← h, ← mul_smul, Units.inv_mul_of_eq hu.unit_spec, one_smul]
  · obtain ⟨c01, c02, c12, c13, c23⟩ := cramer_scalar (a 1) (a 2) (a 0) (a 3) (b 1) (b 2) (b 0)
      (b 3) (Ω 1 2) (-Ω 0 1) (Ω 1 3) (-Ω 0 2) (Ω 2 3) (Ω 0 3) (by linear_combination ha1)
      (by linear_combination ha2) (by linear_combination ha3) (by linear_combination hb1)
      (by linear_combination hb2) (by linear_combination hb3) hu
    refine ⟨↑hu.unit⁻¹ * Ω 1 3, ?_⟩
    have h := smul_asym_eq (a 2 * b 0 - a 0 * b 2) (Ω 1 3) (Ω 0 1) (Ω 0 2) (Ω 0 3) (Ω 1 2) (Ω 1 3)
      (Ω 2 3) (a 2 * b 3 - a 3 * b 2) (a 3 * b 1 - a 1 * b 3) (a 1 * b 2 - a 2 * b 1)
      (a 0 * b 3 - a 3 * b 0) (a 2 * b 0 - a 0 * b 2) (a 0 * b 1 - a 1 * b 0)
      (by linear_combination -c02) (by linear_combination -c12) (by linear_combination c23)
      (by linear_combination c01) (by ring) (by linear_combination c13)
    rw [mul_smul, ← h, ← mul_smul, Units.inv_mul_of_eq hu.unit_spec, one_smul]
  · obtain ⟨c01, c02, c12, c13, c23⟩ := cramer_scalar (a 2) (a 0) (a 1) (a 3) (b 2) (b 0) (b 1)
      (b 3) (-Ω 0 2) (-Ω 1 2) (Ω 2 3) (Ω 0 1) (Ω 0 3) (Ω 1 3) (by linear_combination ha2)
      (by linear_combination ha0) (by linear_combination ha3) (by linear_combination hb2)
      (by linear_combination hb0) (by linear_combination hb3) hu
    refine ⟨↑hu.unit⁻¹ * Ω 2 3, ?_⟩
    have h := smul_asym_eq (a 0 * b 1 - a 1 * b 0) (Ω 2 3) (Ω 0 1) (Ω 0 2) (Ω 0 3) (Ω 1 2) (Ω 1 3)
      (Ω 2 3) (a 2 * b 3 - a 3 * b 2) (a 3 * b 1 - a 1 * b 3) (a 1 * b 2 - a 2 * b 1)
      (a 0 * b 3 - a 3 * b 0) (a 2 * b 0 - a 0 * b 2) (a 0 * b 1 - a 1 * b 0)
      (by linear_combination c12) (by linear_combination -c01) (by linear_combination c13)
      (by linear_combination -c02) (by linear_combination c23) (by ring)
    rw [mul_smul, ← h, ← mul_smul, Units.inv_mul_of_eq hu.unit_spec, one_smul]

theorem mul_vecMulVec_mul (G H : Matrix (Fin 4) (Fin 4) R) (a b : Fin 4 → R) :
    G * vecMulVec a b * H = vecMulVec (G *ᵥ a) (b ᵥ* H) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Fin.sum_univ_four]
  ring

/-- For symmetric `G`, `G (a bᵀ - b aᵀ) G = (G a)(G b)ᵀ - (G b)(G a)ᵀ`. -/
theorem mul_plucker_mul (G : Matrix (Fin 4) (Fin 4) R) (hG : Gᵀ = G) (a b : Fin 4 → R) :
    G * plucker a b * G = plucker (G *ᵥ a) (G *ᵥ b) := by
  have e : ∀ w : Fin 4 → R, w ᵥ* G = G *ᵥ w := fun w => by
    conv_lhs => rw [← hG]
    exact vecMul_transpose G w
  rw [plucker, Matrix.mul_sub, Matrix.sub_mul, mul_vecMulVec_mul, mul_vecMulVec_mul, e, e]
  rfl

theorem blk_transpose (m : Matrix (Fin 3) (Fin 3) R) (hm : ∀ i j, m j i = m i j) (g : R) :
    (blk m g)ᵀ = blk m g := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blk, hm]

theorem hodge_plucker_03 (a b : Fin 4 → R) : hodge (plucker a b) 0 3 = a 1 * b 2 - a 2 * b 1 := by
  simp [hodge, plucker, vecMulVec_apply]; ring

theorem hodge_plucker_13 (a b : Fin 4 → R) : hodge (plucker a b) 1 3 = a 2 * b 0 - a 0 * b 2 := by
  simp [hodge, plucker, vecMulVec_apply]; ring

theorem hodge_plucker_23 (a b : Fin 4 → R) : hodge (plucker a b) 2 3 = a 0 * b 1 - a 1 * b 0 := by
  simp [hodge, plucker, vecMulVec_apply]; ring

/-- **The ruling coordinate.** If the plane spanned by `a, b` is totally isotropic for
`G = diag(m, g)` in the sense `G A G a = G A G b = 0`, and a minor is a unit, then
`G A G = y ⋆A` with `y² = g det m = det G`. -/
theorem ruling_exists (m : Matrix (Fin 3) (Fin 3) R) (hm : ∀ i j, m j i = m i j) (g : R)
    (a b : Fin 4 → R) (ha : (blk m g * plucker a b * blk m g) *ᵥ a = 0)
    (hb : (blk m g * plucker a b * blk m g) *ᵥ b = 0)
    (hu : IsUnit (a 1 * b 2 - a 2 * b 1) ∨ IsUnit (a 2 * b 0 - a 0 * b 2) ∨
      IsUnit (a 0 * b 1 - a 1 * b 0)) :
    ∃ y : R, blk m g * plucker a b * blk m g = y • hodge (plucker a b) ∧ y ^ 2 = g * m.det := by
  have hΩ := mul_plucker_mul (blk m g) (blk_transpose m hm g) a b
  obtain ⟨y, hy⟩ := cramer a b _ (fun i => by rw [hΩ]; simp [plucker, vecMulVec_apply]; ring)
    (fun i j => by rw [hΩ]; simp [plucker, vecMulVec_apply]; ring) ha hb hu
  refine ⟨y, hy, ?_⟩
  have h1 := hodge_blk m hm g a b
  rw [hy, hodge_smul', hodge_hodge_plucker, Matrix.mul_smul, Matrix.smul_mul, hy, smul_smul] at h1
  have key : ∀ i j, y * y * hodge (plucker a b) i j = g * m.det * hodge (plucker a b) i j :=
    fun i j => by simpa using congrFun (congrFun h1 i) j
  rcases hu with hu | hu | hu
  · have := key 0 3
    rw [hodge_plucker_03] at this
    rw [pow_two]; exact hu.mul_right_cancel this
  · have := key 1 3
    rw [hodge_plucker_13] at this
    rw [pow_two]; exact hu.mul_right_cancel this
  · have := key 2 3
    rw [hodge_plucker_23] at this
    rw [pow_two]; exact hu.mul_right_cancel this

end Algebra

/-! ## Bruin's data -/

section Bruin

variable {L : Type*} [Field L] {M1 M2 M3 : Matrix (Fin 3) (Fin 3) L} {δ : L}

theorem gram_eq_blk : gram M1 M2 M3 δ = blk (pencil M1 M2 M3) (-C δ) := rfl

theorem symm_apply {M : Matrix (Fin 3) (Fin 3) L} (h : Mᵀ = M) (a b : Fin 3) : M b a = M a b := by
  rw [← Matrix.transpose_apply M a b, h]

theorem pencil_symm (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (a b : Fin 3) :
    pencil M1 M2 M3 b a = pencil M1 M2 M3 a b := by
  simp only [pencil, Matrix.of_apply, symm_apply h1, symm_apply h2, symm_apply h3]

theorem gram_transpose (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) :
    (gram M1 M2 M3 δ)ᵀ = gram M1 M2 M3 δ :=
  blk_transpose _ (pencil_symm h1 h2 h3) _

/-- The bilinear form `plk W ⬝ G plk P` of the pencil, coefficientwise in `t`. -/
theorem bil_eq (P W : V5 L) :
    plk W ⬝ᵥ (gram M1 M2 M3 δ *ᵥ plk P) =
      C (W.1 ⬝ᵥ (M1 *ᵥ P.1) - δ * (W.2.1 * P.2.1)) +
      X * C (2 * (W.1 ⬝ᵥ (M2 *ᵥ P.1)) - δ * (W.2.1 * P.2.2 + W.2.2 * P.2.1)) +
      X ^ 2 * C (W.1 ⬝ᵥ (M3 *ᵥ P.1) - δ * (W.2.2 * P.2.2)) := by
  simp [plk, gram, pencil, dotProduct, mulVec, Fin.sum_univ_four, Fin.sum_univ_three, map_ofNat]
  ring

theorem bil_self (P : V5 L) :
    plk P ⬝ᵥ (gram M1 M2 M3 δ *ᵥ plk P) = C (quadD ![M1, M2, M3] δ 0 P) +
      X * C (2 * quadD ![M1, M2, M3] δ 1 P) + X ^ 2 * C (quadD ![M1, M2, M3] δ 2 P) := by
  rw [bil_eq]
  simp only [quadD, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  congr 3 <;> ring

theorem polarD_symm {M : Fin 3 → Matrix (Fin 3) (Fin 3) L} (hM : ∀ i, (M i)ᵀ = M i) (i : Fin 3)
    (P W : V5 L) : polarD M δ i P W = 2 * (W.1 ⬝ᵥ (M i *ᵥ P.1)) -
      δ * ![2 * (P.2.1 * W.2.1), P.2.1 * W.2.2 + P.2.2 * W.2.1, 2 * (P.2.2 * W.2.2)] i := by
  unfold polarD
  rw [dotProduct_mulVec, ← mulVec_transpose, hM i, dotProduct_comm]
  ring

omit [Field L] in
theorem symm_fun (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) :
    ∀ i, (![M1, M2, M3] i)ᵀ = ![M1, M2, M3] i := by
  intro i; fin_cases i <;> simpa

theorem bil_comm {R : Type*} [CommRing R] {G : Matrix (Fin 4) (Fin 4) R} (hG : Gᵀ = G)
    (u v : Fin 4 → R) : u ⬝ᵥ (G *ᵥ v) = v ⬝ᵥ (G *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hG, dotProduct_comm]

/-- At a tangent vector, `plk T ⬝ G plk P = 0` identically in `t`. -/
theorem bil_T_pt (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (h2ne : (2 : L) ≠ 0)
    {P T : V5 L} (hT : ∀ i, polarD ![M1, M2, M3] δ i P T = 0) :
    plk T ⬝ᵥ (gram M1 M2 M3 δ *ᵥ plk P) = 0 := by
  have e0 := hT 0
  have e1 := hT 1
  have e2 := hT 2
  rw [polarD_symm (symm_fun h1 h2 h3)] at e0 e1 e2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at e0 e1 e2
  have c0 : T.1 ⬝ᵥ (M1 *ᵥ P.1) - δ * (T.2.1 * P.2.1) = 0 := by
    have : (2 : L) * (T.1 ⬝ᵥ (M1 *ᵥ P.1) - δ * (T.2.1 * P.2.1)) = 0 := by
      linear_combination e0
    exact (mul_eq_zero.mp this).resolve_left h2ne
  have c1 : 2 * (T.1 ⬝ᵥ (M2 *ᵥ P.1)) - δ * (T.2.1 * P.2.2 + T.2.2 * P.2.1) = 0 := by
    linear_combination e1
  have c2 : T.1 ⬝ᵥ (M3 *ᵥ P.1) - δ * (T.2.2 * P.2.2) = 0 := by
    have : (2 : L) * (T.1 ⬝ᵥ (M3 *ᵥ P.1) - δ * (T.2.2 * P.2.2)) = 0 := by
      linear_combination e2
    exact (mul_eq_zero.mp this).resolve_left h2ne
  rw [bil_eq, c0, c1, c2]
  simp

theorem bil_T_T {T : V5 L} (ha3 : quadD ![M1, M2, M3] δ 2 T ≠ 0) :
    plk T ⬝ᵥ (gram M1 M2 M3 δ *ᵥ plk T) =
      C (quadD ![M1, M2, M3] δ 2 T) * bruinU M1 M2 M3 δ T := by
  rw [bil_self, C_mul_bruinU ha3]; ring

/-- The plane spanned by `plk x` and `plk T` is isotropic: `G A G (plk x) = 0`. -/
theorem gram_mulVec_pt (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (h2ne : (2 : L) ≠ 0)
    (x : DPoint L M1 M2 M3 δ) {T : V5 L} (hT : ∀ i, polarD ![M1, M2, M3] δ i (pt x) T = 0) :
    (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) *ᵥ plk (pt x) = 0 := by
  rw [mul_plucker_mul_mulVec, bil_T_pt h1 h2 h3 h2ne hT, bil_self, quadD_pt, quadD_pt, quadD_pt]
  simp

/-- `G A G (plk T) = a₃ U · G (plk x)`. -/
theorem gram_mulVec_T (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (h2ne : (2 : L) ≠ 0)
    (x : DPoint L M1 M2 M3 δ) {T : V5 L} (hT : ∀ i, polarD ![M1, M2, M3] δ i (pt x) T = 0)
    (ha3 : quadD ![M1, M2, M3] δ 2 T ≠ 0) :
    (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) *ᵥ plk T =
      (C (quadD ![M1, M2, M3] δ 2 T) * bruinU M1 M2 M3 δ T) • (gram M1 M2 M3 δ *ᵥ plk (pt x)) := by
  rw [mul_plucker_mul_mulVec, bil_T_T ha3,
    bil_comm (gram_transpose h1 h2 h3) (plk (pt x)) (plk T), bil_T_pt h1 h2 h3 h2ne hT]
  simp


/-! ## Modulo `U` -/

theorem blk_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (m : Matrix (Fin 3) (Fin 3) R) (g : R) : (blk m g).map φ = blk (m.map φ) (φ g) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blk]

theorem plucker_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : Fin 4 → R) :
    (plucker a b).map φ = plucker (φ ∘ a) (φ ∘ b) := by
  ext i j; simp [plucker, vecMulVec_apply]

theorem hodge_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : Matrix (Fin 4) (Fin 4) R) : (hodge A).map φ = hodge (A.map φ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hodge]

theorem mulVec_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : Matrix (Fin 4) (Fin 4) R) (v : Fin 4 → R) : A.map φ *ᵥ (φ ∘ v) = φ ∘ (A *ᵥ v) := by
  funext i; exact (RingHom.map_mulVec φ A v i).symm

theorem hodge_plk_03 (P T : V5 L) :
    hodge (plucker (plk P) (plk T)) 0 3 = C (P.1 1 * T.1 2 - P.1 2 * T.1 1) := by
  rw [hodge_plucker_03]; simp [plk]

theorem hodge_plk_13 (P T : V5 L) :
    hodge (plucker (plk P) (plk T)) 1 3 = C (P.1 2 * T.1 0 - P.1 0 * T.1 2) := by
  rw [hodge_plucker_13]; simp [plk]

theorem hodge_plk_23 (P T : V5 L) :
    hodge (plucker (plk P) (plk T)) 2 3 = C (P.1 0 * T.1 1 - P.1 1 * T.1 0) := by
  rw [hodge_plucker_23]; simp [plk]

/-- **The ruling identity and `V² = f` modulo `U`.** At a point `x` with a tangent vector `T`,
`a₃ ≠ 0`, and a nonzero constant entry `(⋆A)_{l3} = C c` (a minor of `(p, T_p)`), there is
`y ∈ L[X]/(U)` with `G A G ≡ y ⋆A` and `y² ≡ f`, where `f = -δ det(M1 + 2t M2 + t² M3)`. -/
theorem ruling_mod (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (h2ne : (2 : L) ≠ 0)
    {f : L[X]} (hf : f = -C δ * (pencil M1 M2 M3).det) (x : DPoint L M1 M2 M3 δ) {T : V5 L}
    (hT : ∀ i, polarD ![M1, M2, M3] δ i (pt x) T = 0) (ha3 : quadD ![M1, M2, M3] δ 2 T ≠ 0)
    (l : Fin 4) (hl3 : l ≠ 3) {c : L} (hc : c ≠ 0)
    (hl : hodge (plucker (plk (pt x)) (plk T)) l 3 = C c) :
    ∃ y : L[X] ⧸ Ideal.span {bruinU M1 M2 M3 δ T},
      (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ).map
          (Ideal.Quotient.mk (Ideal.span {bruinU M1 M2 M3 δ T})) =
        y • (hodge (plucker (plk (pt x)) (plk T))).map (Ideal.Quotient.mk (Ideal.span {bruinU M1 M2 M3 δ T})) ∧
      y ^ 2 = Ideal.Quotient.mk (Ideal.span {bruinU M1 M2 M3 δ T}) f := by
  set π := Ideal.Quotient.mk (Ideal.span {bruinU M1 M2 M3 δ T})
  have hU : π (bruinU M1 M2 M3 δ T) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hG : (gram M1 M2 M3 δ).map π = blk ((pencil M1 M2 M3).map π) (π (-C δ)) := by
    rw [gram_eq_blk, blk_map]
  have hsym : ∀ i j, ((pencil M1 M2 M3).map π) j i = ((pencil M1 M2 M3).map π) i j := by
    intro i j; simp [pencil_symm h1 h2 h3]
  have hΩ : (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ).map π =
      blk ((pencil M1 M2 M3).map π) (π (-C δ)) * plucker (π ∘ plk (pt x)) (π ∘ plk T) *
        blk ((pencil M1 M2 M3).map π) (π (-C δ)) := by
    rw [Matrix.map_mul, Matrix.map_mul, hG, plucker_map]
  have ha : (blk ((pencil M1 M2 M3).map π) (π (-C δ)) * plucker (π ∘ plk (pt x)) (π ∘ plk T) *
      blk ((pencil M1 M2 M3).map π) (π (-C δ))) *ᵥ (π ∘ plk (pt x)) = 0 := by
    rw [← hΩ, mulVec_map, gram_mulVec_pt h1 h2 h3 h2ne x hT]
    funext i; simp
  have hb : (blk ((pencil M1 M2 M3).map π) (π (-C δ)) * plucker (π ∘ plk (pt x)) (π ∘ plk T) *
      blk ((pencil M1 M2 M3).map π) (π (-C δ))) *ᵥ (π ∘ plk T) = 0 := by
    rw [← hΩ, mulVec_map, gram_mulVec_T h1 h2 h3 h2ne x hT ha3]
    funext i; simp [hU]
  have hcu : IsUnit (π (C c)) := (isUnit_C.mpr (Ne.isUnit hc)).map π
  have hu : IsUnit ((π ∘ plk (pt x)) 1 * (π ∘ plk T) 2 - (π ∘ plk (pt x)) 2 * (π ∘ plk T) 1) ∨
      IsUnit ((π ∘ plk (pt x)) 2 * (π ∘ plk T) 0 - (π ∘ plk (pt x)) 0 * (π ∘ plk T) 2) ∨
      IsUnit ((π ∘ plk (pt x)) 0 * (π ∘ plk T) 1 - (π ∘ plk (pt x)) 1 * (π ∘ plk T) 0) := by
    simp only [Function.comp_apply, ← map_mul, ← map_sub]
    fin_cases l
    · left
      have hl0 : hodge (plucker (plk (pt x)) (plk T)) 0 3 = C c := hl
      rw [← hodge_plucker_03, hl0]; exact hcu
    · right; left
      have hl0 : hodge (plucker (plk (pt x)) (plk T)) 1 3 = C c := hl
      rw [← hodge_plucker_13, hl0]; exact hcu
    · right; right
      have hl0 : hodge (plucker (plk (pt x)) (plk T)) 2 3 = C c := hl
      rw [← hodge_plucker_23, hl0]; exact hcu
    · exact absurd rfl hl3
  obtain ⟨y, hy, hy2⟩ := ruling_exists _ hsym _ _ _ ha hb hu
  refine ⟨y, ?_, ?_⟩
  · rw [hΩ, hy, hodge_map, plucker_map]
  · rw [hy2, hf, map_mul, RingHom.map_det, RingHom.mapMatrix_apply]


theorem dvd_iff_mk_eq_zero (U p : L[X]) :
    U ∣ p ↔ Ideal.Quotient.mk (Ideal.span {U}) p = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- **From one entry to the whole ruling identity and `U ∣ V² - f`.** -/
theorem ruling_of_entry (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (h2ne : (2 : L) ≠ 0)
    {f : L[X]} (hf : f = -C δ * (pencil M1 M2 M3).det) (x : DPoint L M1 M2 M3 δ) {T : V5 L}
    (hT : ∀ i, polarD ![M1, M2, M3] δ i (pt x) T = 0) (ha3 : quadD ![M1, M2, M3] δ 2 T ≠ 0)
    (l : Fin 4) (hl3 : l ≠ 3) {c : L} (hc : c ≠ 0)
    (hl : hodge (plucker (plk (pt x)) (plk T)) l 3 = C c) (V : L[X])
    (hent : bruinU M1 M2 M3 δ T ∣
      (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) l 3 -
        V * hodge (plucker (plk (pt x)) (plk T)) l 3) :
    (∀ i j, bruinU M1 M2 M3 δ T ∣
      (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) i j -
        V * hodge (plucker (plk (pt x)) (plk T)) i j) ∧ bruinU M1 M2 M3 δ T ∣ V ^ 2 - f := by
  obtain ⟨y, hy, hy2⟩ := ruling_mod h1 h2 h3 h2ne hf x hT ha3 l hl3 hc hl
  set π := Ideal.Quotient.mk (Ideal.span {bruinU M1 M2 M3 δ T})
  have hent' := (dvd_iff_mk_eq_zero _ _).mp hent
  have key := congrFun (congrFun hy l) 3
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at key
  rw [map_sub, map_mul, key, hl] at hent'
  have hcu : IsUnit (π (C c)) := (isUnit_C.mpr (Ne.isUnit hc)).map π
  have hyV : y = π V := by
    have : (y - π V) * π (C c) = 0 := by rw [sub_mul]; exact hent'
    exact sub_eq_zero.mp ((hcu.mul_left_eq_zero).mp this)
  refine ⟨fun i j => ?_, ?_⟩
  · rw [dvd_iff_mk_eq_zero, map_sub, map_mul]
    have := congrFun (congrFun hy i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
    rw [this, hyV, sub_self]
  · rw [dvd_iff_mk_eq_zero, map_sub, map_pow, ← hyV, hy2, sub_self]

/-- **Existence of `V`.** -/
theorem exists_V (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (h2ne : (2 : L) ≠ 0)
    {f : L[X]} (hf : f = -C δ * (pencil M1 M2 M3).det) (x : DPoint L M1 M2 M3 δ) {T : V5 L}
    (hT : ∀ i, polarD ![M1, M2, M3] δ i (pt x) T = 0) (ha3 : quadD ![M1, M2, M3] δ 2 T ≠ 0)
    (l : Fin 4) (hl3 : l ≠ 3) {c : L} (hc : c ≠ 0)
    (hl : hodge (plucker (plk (pt x)) (plk T)) l 3 = C c) :
    ∃ V : L[X], V.degree < 2 ∧ bruinU M1 M2 M3 δ T ∣
      (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) l 3 -
        V * hodge (plucker (plk (pt x)) (plk T)) l 3 := by
  obtain ⟨y, hy, -⟩ := ruling_mod h1 h2 h3 h2ne hf x hT ha3 l hl3 hc hl
  obtain ⟨V0, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hU := bruinU_monic M1 M2 M3 δ T
  refine ⟨V0 %ₘ bruinU M1 M2 M3 δ T, ?_, ?_⟩
  · rw [← bruinU_degree M1 M2 M3 δ T]; exact degree_modByMonic_lt _ hU
  · rw [dvd_iff_mk_eq_zero, map_sub, map_mul]
    have := congrFun (congrFun hy l) 3
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
    rw [this, sub_eq_zero]
    congr 1
    rw [eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton]
    exact ⟨-(V0 /ₘ bruinU M1 M2 M3 δ T), by
      have := modByMonic_add_div V0 (bruinU M1 M2 M3 δ T)
      linear_combination this⟩

/-- **A certificate from the tangent data and one entry of the ruling identity**: the ruling
identity at every entry, the unit entry and `U ∣ V² - f` follow (`ruling_of_entry`). -/
noncomputable def Cert.ofEntry (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3)
    (h2ne : (2 : L) ≠ 0) {f : L[X]} (hf : f = -C δ * (pencil M1 M2 M3).det)
    (x : DPoint L M1 M2 M3 δ) (T : V5 L) (hT : ∀ i, polarD ![M1, M2, M3] δ i (pt x) T = 0)
    (hrank : Function.Surjective (tangentMap ![M1, M2, M3] δ (pt x)))
    (hind : LinearIndependent L ![T, pt x]) (ha3 : quadD ![M1, M2, M3] δ 2 T ≠ 0)
    (l : Fin 4) (hl3 : l ≠ 3) {c : L} (hc : c ≠ 0)
    (hl : hodge (plucker (plk (pt x)) (plk T)) l 3 = C c) (V : L[X]) (hV : V.degree < 2)
    (hent : bruinU M1 M2 M3 δ T ∣
      (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) l 3 -
        V * hodge (plucker (plk (pt x)) (plk T)) l 3) : Cert M1 M2 M3 δ f x where
  T := T
  tangent := hT
  rank := hrank
  indep := hind
  a3_ne := ha3
  V := V
  degree_V := hV
  ruling := (ruling_of_entry h1 h2 h3 h2ne hf x hT ha3 l hl3 hc hl V hent).1
  unit := ⟨l, 3, C c⁻¹, by
    rw [hl, ← map_mul, inv_mul_cancel₀ hc, map_one, sub_self]; exact dvd_zero _⟩
  sq := (ruling_of_entry h1 h2 h3 h2ne hf x hT ha3 l hl3 hc hl V hent).2

theorem Cert.ofEntry_T (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3)
    (h2ne : (2 : L) ≠ 0) {f : L[X]} (hf : f = -C δ * (pencil M1 M2 M3).det)
    (x : DPoint L M1 M2 M3 δ) (T : V5 L) (hT : ∀ i, polarD ![M1, M2, M3] δ i (pt x) T = 0)
    (hrank : Function.Surjective (tangentMap ![M1, M2, M3] δ (pt x)))
    (hind : LinearIndependent L ![T, pt x]) (ha3 : quadD ![M1, M2, M3] δ 2 T ≠ 0)
    (l : Fin 4) (hl3 : l ≠ 3) {c : L} (hc : c ≠ 0)
    (hl : hodge (plucker (plk (pt x)) (plk T)) l 3 = C c) (V : L[X]) (hV : V.degree < 2)
    (hent : bruinU M1 M2 M3 δ T ∣
      (gram M1 M2 M3 δ * plucker (plk (pt x)) (plk T) * gram M1 M2 M3 δ) l 3 -
        V * hodge (plucker (plk (pt x)) (plk T)) l 3) :
    (Cert.ofEntry h1 h2 h3 h2ne hf x T hT hrank hind ha3 l hl3 hc hl V hV hent).T = T ∧
    (Cert.ofEntry h1 h2 h3 h2ne hf x T hT hrank hind ha3 l hl3 hc hl V hV hent).V = V :=
  ⟨rfl, rfl⟩


/-! ## The rank condition, independence and `a₃ ≠ 0` -/

/-- **Rank 3.** If `(r, s) ≠ 0` and `(s² M1 - 2rs M2 + r² M3) p ≠ 0` (for a point of `D_δ` this
is `∇(Q1 Q3 - Q2²)(p) ≠ 0`, smoothness of `C`), the tangent map at `P = (p, r, s)` is onto. -/
theorem rank_of {M : Fin 3 → Matrix (Fin 3) (Fin 3) L} (hM : ∀ i, (M i)ᵀ = M i) (hδ : δ ≠ 0)
    (h2ne : (2 : L) ≠ 0) (P : V5 L) (hrs : P.2.1 ≠ 0 ∨ P.2.2 ≠ 0)
    (hN : (P.2.2 ^ 2 • M 0 - (2 * P.2.1 * P.2.2) • M 1 + P.2.1 ^ 2 • M 2) *ᵥ P.1 ≠ 0) :
    Function.Surjective (tangentMap M δ P) := by
  by_contra hns
  have hlt : LinearMap.range (tangentMap M δ P) < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hns (LinearMap.range_eq_top.mp h)
  obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  set c : Fin 3 → L := fun i => φ fun j => if i = j then 1 else 0
  have hφv : ∀ v, φ v = ∑ i, v i * c i := fun v => by
    rw [LinearMap.pi_apply_eq_sum_univ φ v]; rfl
  have hW : ∀ W, ∑ i, polarD M δ i P W * c i = 0 := fun W => by
    have hmem : φ (tangentMap M δ P W) ∈ (LinearMap.range (tangentMap M δ P)).map φ :=
      ⟨_, ⟨W, rfl⟩, rfl⟩
    rw [hmap, Submodule.mem_bot, hφv] at hmem
    simpa [tangentMap_apply] using hmem
  have er := hW (0, 1, 0)
  have es := hW (0, 0, 1)
  simp only [Fin.sum_univ_three, polarD, Prod.fst_zero, dotProduct_zero, mulVec_zero,
    zero_dotProduct, add_zero, zero_sub, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_one, mul_zero, zero_add] at er es
  have er' : 2 * P.2.1 * c 0 + P.2.2 * c 1 = 0 := by
    have : δ * (2 * P.2.1 * c 0 + P.2.2 * c 1) = 0 := by linear_combination -er
    exact (mul_eq_zero.mp this).resolve_left hδ
  have es' : P.2.1 * c 1 + 2 * P.2.2 * c 2 = 0 := by
    have : δ * (P.2.1 * c 1 + 2 * P.2.2 * c 2) = 0 := by linear_combination -es
    exact (mul_eq_zero.mp this).resolve_left hδ
  -- the `p` directions
  have ej : ∀ j, ∑ i, c i * (M i *ᵥ P.1) j = 0 := fun j => by
    have h := hW (Pi.single j 1, 0, 0)
    have e : ∀ i, polarD M δ i P (Pi.single j 1, 0, 0) = 2 * (M i *ᵥ P.1) j := fun i => by
      rw [polarD_symm hM]
      fin_cases i <;> simp [dotProduct_single]
    simp only [e] at h
    have : (2 : L) * ∑ i, c i * (M i *ᵥ P.1) j = 0 := by
      rw [Finset.mul_sum]; rw [← h]; congr 1; funext i; ring
    exact (mul_eq_zero.mp this).resolve_left h2ne
  have hNj : ∀ j, ((P.2.2 ^ 2 • M 0 - (2 * P.2.1 * P.2.2) • M 1 + P.2.1 ^ 2 • M 2) *ᵥ P.1) j =
      P.2.2 ^ 2 * (M 0 *ᵥ P.1) j - 2 * P.2.1 * P.2.2 * (M 1 *ᵥ P.1) j +
        P.2.1 ^ 2 * (M 2 *ᵥ P.1) j := fun j => by
    simp [add_mulVec, sub_mulVec, smul_mulVec]
  -- `r² w = c₂ N p` and `s² w = c₀ N p`
  have hc2 : c 2 = 0 := by
    by_contra h
    apply hN
    funext j
    have hj := ej j
    simp only [Fin.sum_univ_three] at hj
    rw [hNj, Pi.zero_apply]
    have : c 2 * (P.2.2 ^ 2 * (M 0 *ᵥ P.1) j - 2 * P.2.1 * P.2.2 * (M 1 *ᵥ P.1) j +
        P.2.1 ^ 2 * (M 2 *ᵥ P.1) j) = 0 := by
      have e1 : P.2.1 ^ 2 * c 0 = P.2.2 ^ 2 * c 2 := by
        have : 2 * (P.2.1 ^ 2 * c 0 - P.2.2 ^ 2 * c 2) = 0 := by
          linear_combination P.2.1 * er' - P.2.2 * es'
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2ne)
      linear_combination P.2.1 ^ 2 * hj - (M 0 *ᵥ P.1) j * e1 +
        -(P.2.1 * (M 1 *ᵥ P.1) j * es')
    exact (mul_eq_zero.mp this).resolve_left h
  have hc0 : c 0 = 0 := by
    by_contra h
    apply hN
    funext j
    have hj := ej j
    simp only [Fin.sum_univ_three] at hj
    rw [hNj, Pi.zero_apply]
    have : c 0 * (P.2.2 ^ 2 * (M 0 *ᵥ P.1) j - 2 * P.2.1 * P.2.2 * (M 1 *ᵥ P.1) j +
        P.2.1 ^ 2 * (M 2 *ᵥ P.1) j) = 0 := by
      have e1 : P.2.2 ^ 2 * c 2 = P.2.1 ^ 2 * c 0 := by
        have : 2 * (P.2.2 ^ 2 * c 2 - P.2.1 ^ 2 * c 0) = 0 := by
          linear_combination P.2.2 * es' - P.2.1 * er'
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2ne)
      linear_combination P.2.2 ^ 2 * hj - (M 2 *ᵥ P.1) j * e1 +
        -(P.2.2 * (M 1 *ᵥ P.1) j * er')
    exact (mul_eq_zero.mp this).resolve_left h
  have hc1 : c 1 = 0 := by
    rcases hrs with h | h
    · have : P.2.1 * c 1 = 0 := by linear_combination es' - 2 * P.2.2 * hc2
      exact (mul_eq_zero.mp this).resolve_left h
    · have : P.2.2 * c 1 = 0 := by linear_combination er' - 2 * P.2.1 * hc0
      exact (mul_eq_zero.mp this).resolve_left h
  apply hφ
  refine LinearMap.ext fun v => ?_
  rw [hφv, Fin.sum_univ_three, hc0, hc1, hc2]
  simp

/-- The pair `(T, P)` is independent as soon as `p ≠ 0` and a minor of `(p, T_p)` is nonzero. -/
theorem indep_of_minor {P T : V5 L} (hp : P.1 ≠ 0)
    (h : P.1 1 * T.1 2 - P.1 2 * T.1 1 ≠ 0 ∨ P.1 2 * T.1 0 - P.1 0 * T.1 2 ≠ 0 ∨
      P.1 0 * T.1 1 - P.1 1 * T.1 0 ≠ 0) : LinearIndependent L ![T, P] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h0 : a * T.1 0 + b * P.1 0 = 0 := by
    have := congrArg (fun W : V5 L => W.1 0) hab; simpa using this
  have h1 : a * T.1 1 + b * P.1 1 = 0 := by
    have := congrArg (fun W : V5 L => W.1 1) hab; simpa using this
  have h2 : a * T.1 2 + b * P.1 2 = 0 := by
    have := congrArg (fun W : V5 L => W.1 2) hab; simpa using this
  have ha : a = 0 := by
    rcases h with h | h | h
    · have : a * (P.1 1 * T.1 2 - P.1 2 * T.1 1) = 0 := by
        linear_combination P.1 1 * h2 - P.1 2 * h1
      exact (mul_eq_zero.mp this).resolve_right h
    · have : a * (P.1 2 * T.1 0 - P.1 0 * T.1 2) = 0 := by
        linear_combination P.1 2 * h0 - P.1 0 * h2
      exact (mul_eq_zero.mp this).resolve_right h
    · have : a * (P.1 0 * T.1 1 - P.1 1 * T.1 0) = 0 := by
        linear_combination P.1 0 * h1 - P.1 1 * h0
      exact (mul_eq_zero.mp this).resolve_right h
  refine ⟨ha, ?_⟩
  by_contra hb
  apply hp
  funext j
  have := congrArg (fun W : V5 L => W.1 j) hab
  simp [ha] at this
  exact this.resolve_left hb


/-- The projection `(x, y, z, s)` of a vector from the vertex `(0 : 0 : 0 : 1 : 0)` of the quadric
`Q3 - δ s²` (the point `t = ∞` of the pencil). -/
def plkInf (W : V5 L) : Fin 4 → L := ![W.1 0, W.1 1, W.1 2, W.2.2]

theorem bilInf (P W : V5 L) :
    plkInf W ⬝ᵥ (blk M3 (-δ) *ᵥ plkInf P) = W.1 ⬝ᵥ (M3 *ᵥ P.1) - δ * (W.2.2 * P.2.2) := by
  simp [plkInf, blk, dotProduct, mulVec, Fin.sum_univ_four, Fin.sum_univ_three]
  ring

/-- **`a₃ ≠ 0` at every point.** If `-δ det M3` (the leading coefficient of
`f = -δ det(M1 + 2t M2 + t² M3)`) is not a square, the tangent line at a point of `D_δ(L)` never
lies in the quadric `Q3 = δ s²`: otherwise the plane it spans with the vertex would be a totally
isotropic plane of `diag(M3, -δ)`, and `ruling_exists` would give `y² = -δ det M3`. -/
theorem a3_ne_of (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (h2ne : (2 : L) ≠ 0)
    (hlc : ¬ IsSquare (-δ * M3.det))
    (x : DPoint L M1 M2 M3 δ) {T : V5 L} (hT : ∀ i, polarD ![M1, M2, M3] δ i (pt x) T = 0)
    (hmin : x.p 1 * T.1 2 - x.p 2 * T.1 1 ≠ 0 ∨ x.p 2 * T.1 0 - x.p 0 * T.1 2 ≠ 0 ∨
      x.p 0 * T.1 1 - x.p 1 * T.1 0 ≠ 0) : quadD ![M1, M2, M3] δ 2 T ≠ 0 := by
  intro ha3
  have hG : (blk M3 (-δ))ᵀ = blk M3 (-δ) := blk_transpose M3 (symm_apply h3) (-δ)
  have hPP : plkInf (pt x) ⬝ᵥ (blk M3 (-δ) *ᵥ plkInf (pt x)) = 0 := by
    have := quadD_pt x 2
    simp only [quadD, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
    rw [bilInf]; linear_combination this
  have hTP : plkInf T ⬝ᵥ (blk M3 (-δ) *ᵥ plkInf (pt x)) = 0 := by
    have := hT 2
    rw [polarD_symm (symm_fun h1 h2 h3)] at this
    simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
    rw [bilInf]
    have h' : (2 : L) * (T.1 ⬝ᵥ (M3 *ᵥ (pt x).1) - δ * (T.2.2 * (pt x).2.2)) = 0 := by
      linear_combination this
    exact (mul_eq_zero.mp h').resolve_left h2ne
  have hPT : plkInf (pt x) ⬝ᵥ (blk M3 (-δ) *ᵥ plkInf T) = 0 := by
    rw [bil_comm hG]; exact hTP
  have hTT : plkInf T ⬝ᵥ (blk M3 (-δ) *ᵥ plkInf T) = 0 := by
    simp only [quadD, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at ha3
    rw [bilInf]; linear_combination ha3
  have ha : (blk M3 (-δ) * plucker (plkInf (pt x)) (plkInf T) * blk M3 (-δ)) *ᵥ plkInf (pt x) =
      0 := by
    rw [mul_plucker_mul_mulVec, hTP, hPP]; simp
  have hb : (blk M3 (-δ) * plucker (plkInf (pt x)) (plkInf T) * blk M3 (-δ)) *ᵥ plkInf T = 0 := by
    rw [mul_plucker_mul_mulVec, hTT, hPT]; simp
  have hu : IsUnit (plkInf (pt x) 1 * plkInf T 2 - plkInf (pt x) 2 * plkInf T 1) ∨
      IsUnit (plkInf (pt x) 2 * plkInf T 0 - plkInf (pt x) 0 * plkInf T 2) ∨
      IsUnit (plkInf (pt x) 0 * plkInf T 1 - plkInf (pt x) 1 * plkInf T 0) := by
    simp only [plkInf, pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rcases hmin with h | h | h
    · exact Or.inl (Ne.isUnit h)
    · exact Or.inr (Or.inl (Ne.isUnit h))
    · exact Or.inr (Or.inr (Ne.isUnit h))
  obtain ⟨y, -, hy⟩ := ruling_exists M3 (symm_apply h3) (-δ) _ _ ha hb hu
  exact hlc ⟨y, by rw [← hy]; ring⟩

end Bruin

end FurioLombardo.Discharge.M3a.AbelPrym
