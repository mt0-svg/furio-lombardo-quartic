import Mathlib
import FurioLombardo.Discharge.M4Log.Defs

/-!
# The point of a disc: one root `Y` for every `X` (lane lean-m4box, D3)

For a disc `d ∈ {1, ..., 5}` of lane M4 and `X ∈ ℤ_[2]`, the equation `F(discPt d X Y) = 0` has exactly one
root `Y ∈ ℤ_[2]` (`existsUnique_root`), so lane lean-m4log's choice `discY d X` is that root (`discY_spec`),
and `X ≡ X' mod 2^s` gives `discY d X ≡ discY d X' mod 2^s` (`discY_sub_dvd`).

The certificate (code/covering/disc_root_data.gp, .out; the same as part 2 of
code/covering/log_branch.gp): `F(discPt d X Y) = 2^m G1(X, Y)` and
`G1(X, Y) - G1(X, Y') = (Y - Y') H(X, Y, Y')` with integer polynomials `G1`, `H` (`ring`), and `H` odd at
the 8 residues (`decide` in `ZMod 2`), so `H` takes unit values on `ℤ_[2]³`. Then two roots are equal,
`G1(X, 0)` or `G1(X, 1)` is even (their difference `H(X, 1, 0)` is odd), and Hensel's lemma
(`∂G1/∂Y = H(X, Y, Y)` a unit) gives the root.
-/

open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.M4Log Polynomial

namespace FurioLombardo.Discharge.M4Box

/-! ## The certificate data -/

/-- `F(discPt d x y) = 2^(mD d) G1 d x y`. -/
def mD : ℕ → ℕ
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 1
  | _ => 0

/-- `F(discPt d x y) / 2^(mD d)`. -/
def G1 {R : Type*} [CommRing R] : ℕ → R → R → R
  | 1, x, y => 8*x^4 + 24*y*x^3 + (-12*y - 6)*x^2 + (48*y^3 - 24*y^2 + 6*y - 2)*x + (32*y^4 + 8*y^3 - 5*y)
  | 2, x, y => 4*x^4 + (12*y + 8)*x^3 + (12*y + 3)*x^2 + (24*y^3 - 12*y^2 + 6*y - 2)*x +
      (16*y^4 + 16*y^3 - 6*y^2 - y - 1)
  | 3, x, y => 4*x^4 + (12*y + 14)*x^3 + (12*y + 9)*x^2 + (24*y^3 + 24*y^2 + 12*y + 1)*x +
      (16*y^4 + 48*y^3 + 42*y^2 + 13*y)
  | 4, x, y => 4*x^4 + 6*x^3 + (-12*y^2 - 6*y)*x^2 + (-8*y^3 + 6*y^2 - 6*y + 3)*x + (-10*y^3 + y + 1)
  | 5, x, y => 8*x^4 + 28*x^3 + (-24*y^2 - 12*y + 30)*x^2 + (-16*y^3 - 12*y^2 - 24*y + 19)*x +
      (-28*y^3 - 7*y + 7)
  | _, _, _ => 0

/-- The divided difference `(G1 d x y - G1 d x y2) / (y - y2)`. -/
def Hd {R : Type*} [CommRing R] : ℕ → R → R → R → R
  | 1, x, y, y2 => 24*x^3 - 12*x^2 + (48*y^2 + (48*y2 - 24)*y + (48*y2^2 - 24*y2 + 6))*x +
      (32*y^3 + (32*y2 + 8)*y^2 + (32*y2^2 + 8*y2)*y + (32*y2^3 + 8*y2^2 - 5))
  | 2, x, y, y2 => 12*x^3 + 12*x^2 + (24*y^2 + (24*y2 - 12)*y + (24*y2^2 - 12*y2 + 6))*x +
      (16*y^3 + (16*y2 + 16)*y^2 + (16*y2^2 + 16*y2 - 6)*y + (16*y2^3 + 16*y2^2 - 6*y2 - 1))
  | 3, x, y, y2 => 12*x^3 + 12*x^2 + (24*y^2 + (24*y2 + 24)*y + (24*y2^2 + 24*y2 + 12))*x +
      (16*y^3 + (16*y2 + 48)*y^2 + (16*y2^2 + 48*y2 + 42)*y + (16*y2^3 + 48*y2^2 + 42*y2 + 13))
  | 4, x, y, y2 => (-12*y + (-12*y2 - 6))*x^2 + (-8*y^2 + (-8*y2 + 6)*y + (-8*y2^2 + 6*y2 - 6))*x +
      (-10*y^2 - 10*y2*y + (-10*y2^2 + 1))
  | 5, x, y, y2 => (-24*y + (-24*y2 - 12))*x^2 + (-16*y^2 + (-16*y2 - 12)*y + (-16*y2^2 - 12*y2 - 24))*x +
      (-28*y^2 - 28*y2*y + (-28*y2^2 - 7))
  | _, _, _, _ => 0

/-- `G1 d x` as a polynomial in `y`. -/
noncomputable def Pd (d : ℕ) (x : ℤ_[2]) : ℤ_[2][X] :=
  match d with
  | 1 => C (8*x^4 - 6*x^2 - 2*x) + C (24*x^3 - 12*x^2 + 6*x - 5) * X + C (-24*x) * X^2 +
      C (48*x + 8) * X^3 + C 32 * X^4
  | 2 => C (4*x^4 + 8*x^3 + 3*x^2 - 2*x - 1) + C (12*x^3 + 12*x^2 + 6*x - 1) * X + C (-12*x - 6) * X^2 +
      C (24*x + 16) * X^3 + C 16 * X^4
  | 3 => C (4*x^4 + 14*x^3 + 9*x^2 + x) + C (12*x^3 + 12*x^2 + 12*x + 13) * X + C (24*x + 42) * X^2 +
      C (24*x + 48) * X^3 + C 16 * X^4
  | 4 => C (4*x^4 + 6*x^3 + 3*x + 1) + C (-6*x^2 - 6*x + 1) * X + C (-12*x^2 + 6*x) * X^2 +
      C (-8*x - 10) * X^3
  | 5 => C (8*x^4 + 28*x^3 + 30*x^2 + 19*x + 7) + C (-12*x^2 - 24*x - 7) * X + C (-24*x^2 - 12*x) * X^2 +
      C (-16*x - 28) * X^3
  | _ => 0

/-- The discs of lane M4. -/
def IsDisc (d : ℕ) : Prop := d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5

/-! ## The certificate checks -/

theorem F_discPt {R : Type*} [CommRing R] {d : ℕ} (hd : IsDisc d) (x y : R) :
    FurioLombardo.F (discPt d x y 0) (discPt d x y 1) (discPt d x y 2) = 2 ^ mD d * G1 d x y := by
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp [discPt, FurioLombardo.F, G1, mD] <;> ring

theorem G1_sub {R : Type*} [CommRing R] {d : ℕ} (hd : IsDisc d) (x y y2 : R) :
    G1 d x y - G1 d x y2 = (y - y2) * Hd d x y y2 := by
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp only [G1, Hd] <;> ring

theorem map_G1 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ} (hd : IsDisc d) (x y : R) :
    φ (G1 d x y) = G1 d (φ x) (φ y) := by
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp [G1, map_ofNat]

theorem map_Hd {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ} (hd : IsDisc d)
    (x y y2 : R) : φ (Hd d x y y2) = Hd d (φ x) (φ y) (φ y2) := by
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp [Hd, map_ofNat]

/-- **Kernel check**: `H` is odd at the 8 residues. -/
theorem Hd_zmod {d : ℕ} (hd : IsDisc d) (a b c : ZMod 2) : Hd d a b c ≠ 0 := by
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> revert a b c <;> decide

theorem Pd_eval {d : ℕ} (hd : IsDisc d) (x y : ℤ_[2]) : (Pd d x).eval y = G1 d x y := by
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp [Pd, G1] <;> ring

theorem Pd_derivative_eval {d : ℕ} (hd : IsDisc d) (x y : ℤ_[2]) :
    (Pd d x).derivative.eval y = Hd d x y y := by
  rcases hd with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Pd, Hd, derivative_add, derivative_C, derivative_C_mul_X, derivative_C_mul_X_pow, eval_add,
    eval_C, eval_mul, eval_X, eval_pow, zero_add, Nat.cast_ofNat] <;> ring

/-! ## Units of `ℤ_[2]` modulo 2 -/

theorem isUnit_iff_toZMod_ne_zero (z : ℤ_[2]) : IsUnit z ↔ PadicInt.toZMod z ≠ 0 := by
  rw [Ne, ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

theorem isUnit_Hd {d : ℕ} (hd : IsDisc d) (x y y2 : ℤ_[2]) : IsUnit (Hd d x y y2) := by
  rw [isUnit_iff_toZMod_ne_zero, map_Hd _ hd]
  exact Hd_zmod hd _ _ _

/-! ## One root for every `X` -/

theorem G1_eq_zero_iff {d : ℕ} (hd : IsDisc d) (x y : ℤ_[2]) :
    FurioLombardo.F (discPt d x y 0) (discPt d x y 1) (discPt d x y 2) = 0 ↔ G1 d x y = 0 := by
  rw [F_discPt hd, mul_eq_zero, or_iff_right (pow_ne_zero _ two_ne_zero)]

/-- **At most one root**. -/
theorem root_unique {d : ℕ} (hd : IsDisc d) {x y y2 : ℤ_[2]}
    (h : FurioLombardo.F (discPt d x y 0) (discPt d x y 1) (discPt d x y 2) = 0)
    (h2 : FurioLombardo.F (discPt d x y2 0) (discPt d x y2 1) (discPt d x y2 2) = 0) : y = y2 := by
  rw [G1_eq_zero_iff hd] at h h2
  have e := G1_sub hd x y y2
  rw [h, h2, sub_zero, zero_eq_mul] at e
  rcases e with e | e
  · exact sub_eq_zero.mp e
  · exact absurd e (isUnit_Hd hd x y y2).ne_zero

/-- **A root exists** (Hensel's lemma at `Y = 0` or `Y = 1`). -/
theorem exists_root {d : ℕ} (hd : IsDisc d) (x : ℤ_[2]) :
    ∃ y : ℤ_[2], FurioLombardo.F (discPt d x y 0) (discPt d x y 1) (discPt d x y 2) = 0 := by
  -- one of `G1 x 0`, `G1 x 1` is even
  have ha : ∃ a : ℤ_[2], ‖G1 d x a‖ < 1 := by
    by_contra hc
    push Not at hc
    have h0 : IsUnit (G1 d x 0) := PadicInt.isUnit_iff.mpr (le_antisymm (PadicInt.norm_le_one _) (hc 0))
    have h1 : IsUnit (G1 d x 1) := PadicInt.isUnit_iff.mpr (le_antisymm (PadicInt.norm_le_one _) (hc 1))
    have hu := isUnit_Hd hd x 1 0
    rw [isUnit_iff_toZMod_ne_zero] at h0 h1 hu
    have e := G1_sub hd x 1 0
    rw [sub_zero, one_mul] at e
    apply hu
    rw [← e, map_sub]
    generalize PadicInt.toZMod (G1 d x 1) = a at h1
    generalize PadicInt.toZMod (G1 d x 0) = b at h0
    revert a b
    decide
  obtain ⟨a, ha⟩ := ha
  have hder : ‖(Pd d x).derivative.aeval a‖ = 1 := by
    rw [coe_aeval_eq_eval, Pd_derivative_eval hd]
    exact PadicInt.isUnit_iff.mp (isUnit_Hd hd x a a)
  have hnorm : ‖(Pd d x).aeval a‖ < ‖(Pd d x).derivative.aeval a‖ ^ 2 := by
    rw [hder, one_pow, coe_aeval_eq_eval, Pd_eval hd]
    exact ha
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, (G1_eq_zero_iff hd x z).mpr ?_⟩
  rw [coe_aeval_eq_eval, Pd_eval hd] at hz
  exact hz

theorem existsUnique_root {d : ℕ} (hd : IsDisc d) (x : ℤ_[2]) :
    ∃! y : ℤ_[2], FurioLombardo.F (discPt d x y 0) (discPt d x y 1) (discPt d x y 2) = 0 := by
  obtain ⟨y, hy⟩ := exists_root hd x
  exact ⟨y, hy, fun y2 hy2 => root_unique hd hy2 hy⟩

/-- **Lane lean-m4log's `discY` is the root.** -/
theorem discY_spec {d : ℕ} (hd : IsDisc d) (x : ℤ_[2]) :
    FurioLombardo.F (discPt d x (discY d x) 0) (discPt d x (discY d x) 1) (discPt d x (discY d x) 2) = 0 ∧
      ∀ y : ℤ_[2], FurioLombardo.F (discPt d x y 0) (discPt d x y 1) (discPt d x y 2) = 0 →
        y = discY d x := by
  have hex := exists_root hd x
  have h : FurioLombardo.F (discPt d x (discY d x) 0) (discPt d x (discY d x) 1)
      (discPt d x (discY d x) 2) = 0 := by
    unfold discY
    rw [dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec
  exact ⟨h, fun y hy => root_unique hd hy h⟩

/-- **The root is 2-adically continuous**: `X ≡ X' mod 2^s` gives `discY d X ≡ discY d X' mod 2^s`. -/
theorem discY_sub_dvd {d : ℕ} (hd : IsDisc d) {x x2 : ℤ_[2]} {s : ℕ} (h : (2 : ℤ_[2]) ^ s ∣ x - x2) :
    (2 : ℤ_[2]) ^ s ∣ discY d x - discY d x2 := by
  set y := discY d x
  set y2 := discY d x2
  have hy := (G1_eq_zero_iff hd x y).mp (discY_spec hd x).1
  have hy2 := (G1_eq_zero_iff hd x2 y2).mp (discY_spec hd x2).1
  -- `G1 x y2 ≡ G1 x2 y2 = 0 mod 2^s`
  have hc : (2 : ℤ_[2]) ^ s ∣ G1 d x y2 := by
    have hI : Ideal.Quotient.mk (Ideal.span {(2 : ℤ_[2]) ^ s}) x =
        Ideal.Quotient.mk (Ideal.span {(2 : ℤ_[2]) ^ s}) x2 :=
      Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)
    have e : Ideal.Quotient.mk (Ideal.span {(2 : ℤ_[2]) ^ s}) (G1 d x y2) =
        Ideal.Quotient.mk (Ideal.span {(2 : ℤ_[2]) ^ s}) (G1 d x2 y2) := by
      rw [map_G1 _ hd, map_G1 _ hd, hI]
    rw [hy2, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at e
    exact e
  have e := G1_sub hd x y y2
  rw [hy, zero_sub] at e
  have hd2 : (2 : ℤ_[2]) ^ s ∣ (y - y2) * Hd d x y y2 := by
    rw [← e]
    exact (dvd_neg).mpr hc
  obtain ⟨u, hu⟩ := isUnit_Hd hd x y y2
  rw [← hu] at hd2
  exact (Units.dvd_mul_right).mp hd2

end FurioLombardo.Discharge.M4Box
