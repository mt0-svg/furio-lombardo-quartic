import FurioLombardo.Discharge.M3a.MuT
import FurioLombardo.Discharge.M3a.Reduction

/-!
# Mumford points with a quadratic `u` and their `x - T` images (lane SelmerSpan)

Generic algebra over a field `F` with `2 ≠ 0`, used to define the local divisors `D_i` at `v`:

* `muJ_mumfordJac`: for a Mumford triple `(u, v, w)` (`u` monic of even degree,
  `v² - f = u w`) with `u` coprime to `f`, the `x - T` image of the point `[⟨u, Y - v⟩]` is the class
  of `u(T)` in `H f = L^× / K^× (L^×)²` (mirror of M3a's `muJ_Tpt`).
* `quad p r = X² + p X + r`; `sextic_eq`: division of a polynomial of degree `≤ 6` by `quad p r`
  with explicit quotient and remainder `z1 X + z0` (the recurrence `divW`, `divR1`, `divR0`).
* `sq_sub_eq`: the square root of `z1 X + z0` modulo `quad p r` from two square roots in `F`,
  in the scaled form used by the certificates (`n² = Z0² - p Z1 Z0 + r Z1²`,
  `a² = 2 Z0 - p Z1 + 2 n`, `a ≠ 0`; `Z1 = 4 z1`, `Z0 = 4 z0`).
* `isCoprime_quad_lin`: `quad p r` is coprime to `z1 X + z0` when `z0² - p z1 z0 + r z1² ≠ 0`.
-/

open Polynomial
open scoped nonZeroDivisors
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.SelmerSpan

variable {F : Type*} [Field F]

/-! ## The `x - T` image of a Mumford point with `u` coprime to `f` -/

/-- `u(T)` is a unit of `F[T]/(f)` when `u` and `f` are coprime. -/
theorem isUnit_mk_of_isCoprime {f u : F[X]} (h : IsCoprime u f) : IsUnit (AdjoinRoot.mk f u) := by
  obtain ⟨a, b, hab⟩ := h
  refine IsUnit.of_mul_eq_one (AdjoinRoot.mk f a) ?_
  have := congrArg (AdjoinRoot.mk f) hab
  rwa [map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero, map_one, mul_comm] at this

/-- **`μ([⟨u, Y - v⟩]) = [u(T)]` for `u` coprime to `f`.** -/
theorem muJ_mumfordJac (f : F[X]) [GoodSextic f] {u v w : F[X]} (hu : u.Monic)
    (hdeg : Even u.natDegree) (hw : v ^ 2 - f = u * w)
    (hc : ∃ a b c : F[X], a * u + b * v + c * w = 1) (hcop : IsCoprime u f) :
    muJ f (mumfordJac f hu hdeg hw hc) =
      (QuotientGroup.mk (isUnit_mk_of_isCoprime hcop).unit : H f) := by
  classical
  set φ := algebraMap F[X] (CoordRing f) with hφ
  -- the Mumford ideal is coprime to `(Y)`
  have hJY : mumford f u v ⊔ Ideal.span {Yc f} = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    obtain ⟨a, b, hab⟩ := hcop
    have hu_mem : φ u ∈ mumford f u v ⊔ Ideal.span {Yc f} :=
      Ideal.mem_sup_left (Ideal.subset_span (Set.mem_insert _ _))
    have hY_mem : Yc f ^ 2 ∈ mumford f u v ⊔ Ideal.span {Yc f} := by
      rw [sq]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have e1 : (1 : CoordRing f) = φ a * φ u + φ b * Yc f ^ 2 := by
      rw [Yc_sq, ← map_mul, ← map_mul, ← map_add, hab, map_one]
    rw [e1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hu_mem) (Ideal.mul_mem_left _ _ hY_mem)
  have hN : Ideal.relNorm F[X] (mumford f u v) = Ideal.span {u} := relNorm_mumford f hu hw hc
  change mu f (ClassGroup.mk0 (mumford0 f hu.ne_zero v)) = _
  rw [mu_mk0 f (mumford0 f hu.ne_zero v) hJY]
  have hunit : IsUnit (AdjoinRoot.mk f (Submodule.IsPrincipal.generator (Ideal.relNorm F[X]
      ((mumford0 f hu.ne_zero v : (Ideal (CoordRing f))⁰) : Ideal (CoordRing f))))) :=
    isUnit_mk_generator f _ hJY
  unfold muIdeal
  rw [dite_eq_left_of_eq_true (eq_true hunit), QuotientGroup.eq]
  set g := Submodule.IsPrincipal.generator (Ideal.relNorm F[X]
    ((mumford0 f hu.ne_zero v : (Ideal (CoordRing f))⁰) : Ideal (CoordRing f))) with hg
  have hassoc : Associated g u := by
    rw [← Ideal.span_singleton_eq_span_singleton, hg, Ideal.span_singleton_generator]
    exact hN
  obtain ⟨e, he⟩ := hassoc
  obtain ⟨c, hc0, hce⟩ := Polynomial.isUnit_iff.mp e.isUnit
  have hkey : AdjoinRoot.mk f u = AdjoinRoot.mk f g * algebraMap F (AdjoinRoot f) c := by
    rw [← he, map_mul, ← hce, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  apply Subgroup.mem_sup_left
  refine ⟨hc0.unit, ?_⟩
  ext
  simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, Units.val_mul,
    IsUnit.unit_spec]
  rw [hkey, ← mul_assoc, Units.inv_mul_of_eq hunit.unit_spec, one_mul]

/-! ## Monic quadratics -/

/-- `X² + p X + r`. -/
noncomputable def quad (p r : F) : F[X] := X ^ 2 + C p * X + C r

theorem quad_natDegree (p r : F) : (quad p r).natDegree = 2 := by
  unfold quad; compute_degree!

theorem quad_monic (p r : F) : (quad p r).Monic := by
  unfold quad; monicity!

theorem quad_even (p r : F) : Even (quad p r).natDegree := by
  rw [quad_natDegree]; exact even_two

theorem quad_map {F' : Type*} [Field F'] (φ : F →+* F') (p r : F) :
    (quad p r).map φ = quad (φ p) (φ r) := by
  simp [quad, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

/-! ## Division of a sextic by `X² + p X + r` -/

set_option linter.unusedVariables false in
/-- The coefficients `w4, w3, w2, w1, w0` of the quotient of `Σ g_j X^j` (`j ≤ 6`) by
`X² + p X + r`. -/
def divW (p r g0 g1 g2 g3 g4 g5 g6 : F) : F × F × F × F × F :=
  let w4 := g6
  let w3 := g5 - p * w4
  let w2 := g4 - p * w3 - r * w4
  let w1 := g3 - p * w2 - r * w3
  let w0 := g2 - p * w1 - r * w2
  (w4, w3, w2, w1, w0)

/-- The coefficient of `X` of the remainder. -/
def divR1 (p r g0 g1 g2 g3 g4 g5 g6 : F) : F :=
  let w := divW p r g0 g1 g2 g3 g4 g5 g6
  g1 - p * w.2.2.2.2 - r * w.2.2.2.1

/-- The constant coefficient of the remainder. -/
def divR0 (p r g0 g1 g2 g3 g4 g5 g6 : F) : F :=
  let w := divW p r g0 g1 g2 g3 g4 g5 g6
  g0 - r * w.2.2.2.2

/-- The quotient polynomial. -/
noncomputable def divQ (p r g0 g1 g2 g3 g4 g5 g6 : F) : F[X] :=
  let w := divW p r g0 g1 g2 g3 g4 g5 g6
  C w.1 * X ^ 4 + C w.2.1 * X ^ 3 + C w.2.2.1 * X ^ 2 + C w.2.2.2.1 * X + C w.2.2.2.2

theorem sextic_eq (p r g0 g1 g2 g3 g4 g5 g6 : F) :
    C g6 * X ^ 6 + C g5 * X ^ 5 + C g4 * X ^ 4 + C g3 * X ^ 3 + C g2 * X ^ 2 + C g1 * X + C g0 =
      quad p r * divQ p r g0 g1 g2 g3 g4 g5 g6 +
        (C (divR1 p r g0 g1 g2 g3 g4 g5 g6) * X + C (divR0 p r g0 g1 g2 g3 g4 g5 g6)) := by
  simp only [quad, divQ, divR1, divR0, divW, C_sub, C_mul]
  ring

/-- A polynomial of degree `≤ 6` as the sum of its seven monomials. -/
theorem eq_sextic_of_natDegree_le {g : F[X]} (hg : g.natDegree ≤ 6) :
    g = C (g.coeff 6) * X ^ 6 + C (g.coeff 5) * X ^ 5 + C (g.coeff 4) * X ^ 4 +
      C (g.coeff 3) * X ^ 3 + C (g.coeff 2) * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
  conv_lhs => rw [g.as_sum_range' 7 (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ← C_mul_X_pow_eq_monomial]
  ring

/-! ## The square root of `z1 X + z0` modulo `X² + p X + r` -/

/-- The linear coefficient `b = Z1 / (2 a)` of the square root. -/
def sqB (Z1 a : F) : F := Z1 / (2 * a)

/-- The constant coefficient `a / 4 + b p / 2` of the square root. -/
def sqC (p Z1 a : F) : F := a / 4 + sqB Z1 a * p / 2

/-- **Square root modulo a monic quadratic.** With `n² = Z0² - p Z1 Z0 + r Z1²`,
`a² = 2 Z0 - p Z1 + 2 n` and `a ≠ 0`, the polynomial `V = b X + c` (`b = Z1 / (2a)`,
`c = a/4 + b p/2`) satisfies `V² - (Z1/4 X + Z0/4) = b² (X² + p X + r)`. -/
theorem sq_sub_eq (h2 : (2 : F) ≠ 0) {p r Z0 Z1 n a : F}
    (hn : n ^ 2 = Z0 ^ 2 - p * Z1 * Z0 + r * Z1 ^ 2) (ha : a ^ 2 = 2 * Z0 - p * Z1 + 2 * n)
    (ha0 : a ≠ 0) :
    (C (sqB Z1 a) * X + C (sqC p Z1 a)) ^ 2 - (C (Z1 / 4) * X + C (Z0 / 4)) =
      C (sqB Z1 a ^ 2) * quad p r := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have h16 : (16 : F) ≠ 0 := by
    have : (16 : F) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  have e1 : 2 * sqB Z1 a * sqC p Z1 a - sqB Z1 a ^ 2 * p - Z1 / 4 = 0 := by
    unfold sqC sqB; field_simp; ring
  have hnum : a ^ 4 - 2 * a ^ 2 * (2 * Z0 - p * Z1) + Z1 ^ 2 * (p ^ 2 - 4 * r) = 0 := by
    linear_combination 4 * hn + (a ^ 2 - (2 * Z0 - p * Z1) + 2 * n) * ha
  have e0 : sqC p Z1 a ^ 2 - sqB Z1 a ^ 2 * r - Z0 / 4 = 0 := by
    have : sqC p Z1 a ^ 2 - sqB Z1 a ^ 2 * r - Z0 / 4 =
        (a ^ 4 - 2 * a ^ 2 * (2 * Z0 - p * Z1) + Z1 ^ 2 * (p ^ 2 - 4 * r)) / (16 * a ^ 2) := by
      unfold sqC sqB; field_simp; ring
    rw [this, hnum, zero_div]
  have : (C (sqB Z1 a) * X + C (sqC p Z1 a)) ^ 2 - (C (Z1 / 4) * X + C (Z0 / 4)) -
      C (sqB Z1 a ^ 2) * quad p r =
      C (2 * sqB Z1 a * sqC p Z1 a - sqB Z1 a ^ 2 * p - Z1 / 4) * X +
        C (sqC p Z1 a ^ 2 - sqB Z1 a ^ 2 * r - Z0 / 4) := by
    simp only [quad, C_sub, C_mul, C_pow, C_ofNat]; ring
  rw [e1, e0, C_0, zero_mul, zero_add] at this
  exact sub_eq_zero.mp this

/-! ## Coprimality -/

/-- `X² + p X + r` is coprime to `z1 X + z0` when `ρ = z0² - p z1 z0 + r z1² ≠ 0`:
`z1² (X² + p X + r) - (z1 X + p z1 - z0) (z1 X + z0) = ρ`. -/
theorem isCoprime_quad_lin {p r z1 z0 : F} (hρ : z0 ^ 2 - p * z1 * z0 + r * z1 ^ 2 ≠ 0) :
    IsCoprime (quad p r) (C z1 * X + C z0) := by
  set ρ := z0 ^ 2 - p * z1 * z0 + r * z1 ^ 2 with hρdef
  have key : C (z1 ^ 2) * quad p r - (C z1 * X + C (p * z1 - z0)) * (C z1 * X + C z0) = C ρ := by
    simp only [hρdef, quad, C_sub, C_mul, C_add, C_pow]; ring
  refine ⟨C (ρ⁻¹ * z1 ^ 2), -(C ρ⁻¹ * (C z1 * X + C (p * z1 - z0))), ?_⟩
  have e : C (ρ⁻¹ * z1 ^ 2) * quad p r + -(C ρ⁻¹ * (C z1 * X + C (p * z1 - z0))) * (C z1 * X + C z0) =
      C ρ⁻¹ * (C (z1 ^ 2) * quad p r - (C z1 * X + C (p * z1 - z0)) * (C z1 * X + C z0)) := by
    rw [C_mul]; ring
  rw [e, key, ← C_mul, inv_mul_cancel₀ hρ, C_1]

end FurioLombardo.Discharge.SelmerSpan
