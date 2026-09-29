import FurioLombardo.Discharge.M3b.Fields
import FurioLombardo.Discharge.M3a.PolyK

/-!
# Kernel arithmetic in `L42` and `N84`

Elements of the tower `K21 ⊂ L42 = K21(ω) ⊂ N84 = L42(ω_N)` in coordinates that are `KE`
expressions (lane M1's Kronecker checks):

* `LC`: `(x0, x1)` for `x0 + x1 ω ∈ L42` (`evL`);
* `NC`: `((x0, x1), (x2, x3))` for `x0 + x1 ω + (x2 + x3 ω) (2 ω_N) ∈ N84` (`evN`, the convention
  of `mkN`: with `Ω = 2 ω_N`, `Ω² = 4 e' = 2 ea + 2 eb ω`, so the coordinates of an algebraic
  integer are zk-integral in practice).

Products (`mulLC`, `mulNC`), sums and scalings are formal, with `evL`, `evN` multiplicative and
additive (`evL_mulLC`, `evN_mulNC`, ...); an identity is checked by one `checkK` per coordinate
(`evL_eq_of_checkLC`, `evN_eq_of_checkNC`). Values of polynomials read off a table of powers are in
TowerEval.lean (`aeval_pQ_of_checkL`, `aeval_pQ_of_checkN`), the tables and the checks of the tower
data in TowerChecks.lean and TowerFacts.lean, products of generators selected by a bitmask in
MuTCert.lean (`evL_selProdL`, `evN_selProdN`).
-/

namespace FurioLombardo.Discharge.SelmerBasis.Tower

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3b

/-! ## Coordinates -/

/-- Coordinates `(x0, x1)` of `x0 + x1 ω ∈ L42`. -/
abbrev LC : Type := KE × KE

/-- Coordinates `((x0, x1), (x2, x3))` of `x0 + x1 ω + (x2 + x3 ω) (2 ω_N) ∈ N84`. -/
abbrev NC : Type := LC × LC

/-- The element of `L42` with coordinates `x`. -/
noncomputable def evL (x : LC) : L42 := ⟨evK x.1, evK x.2⟩

/-- The element of `N84` with coordinates `x` (`Ω = 2 ω_N`). -/
noncomputable def evN (x : NC) : N84 := ⟨evL x.1, ⟨2 * evK x.2.1, 2 * evK x.2.2⟩⟩

def zeroLC : LC := (.int 0, .int 0)
def oneLC : LC := (.int 1, .int 0)
def zeroNC : NC := (zeroLC, zeroLC)
def oneNC : NC := (oneLC, zeroLC)

def addLC (x y : LC) : LC := (.add x.1 y.1, .add x.2 y.2)
def smulLC (c : KE) (x : LC) : LC := (.mul c x.1, .mul c x.2)
/-- `(x0 + x1 ω)(y0 + y1 ω) = (x0 y0 + ε x1 y1) + (x0 y1 + x1 y0) ω`. -/
def mulLC (x y : LC) : LC :=
  (.add (.mul x.1 y.1) (.mul (.lin epsL) (.mul x.2 y.2)), .add (.mul x.1 y.2) (.mul x.2 y.1))
/-- `Ω² = 4 e' = 2 ea + 2 eb ω`. -/
def e4LC : LC := (.mul (.int 2) (.lin eaL), .mul (.int 2) (.lin ebL))

def addNC (x y : NC) : NC := (addLC x.1 y.1, addLC x.2 y.2)
def smulNC (c : KE) (x : NC) : NC := (smulLC c x.1, smulLC c x.2)
/-- `(X + X' Ω)(Y + Y' Ω) = (X Y + Ω² X' Y') + (X Y' + X' Y) Ω`. -/
def mulNC (x y : NC) : NC :=
  (addLC (mulLC x.1 y.1) (mulLC e4LC (mulLC x.2 y.2)), addLC (mulLC x.1 y.2) (mulLC x.2 y.1))

/-- Coordinates from zk lists `[x0, x1]`. -/
def ofL (a : List (List ℤ)) : LC := (.lin (a.getD 0 []), .lin (a.getD 1 []))
/-- Coordinates from zk lists `[x0, x1, x2, x3]`. -/
def ofN (a : List (List ℤ)) : NC :=
  ((.lin (a.getD 0 []), .lin (a.getD 1 [])), (.lin (a.getD 2 []), .lin (a.getD 3 [])))

theorem evL_ext {x y : LC} (h1 : evK x.1 = evK y.1) (h2 : evK x.2 = evK y.2) : evL x = evL y := by
  simp only [evL, h1, h2]

@[simp] theorem evL_zero : evL zeroLC = 0 := by
  ext <;> simp [evL, zeroLC]

@[simp] theorem evL_one : evL oneLC = 1 := by
  ext <;> simp [evL, oneLC, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

@[simp] theorem evN_zero : evN zeroNC = 0 := by
  ext <;> simp [evN, evL, zeroNC, zeroLC]

@[simp] theorem evN_one : evN oneNC = 1 := by
  ext <;> simp [evN, evL, oneNC, oneLC, zeroLC, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

@[simp] theorem evL_addLC (x y : LC) : evL (addLC x y) = evL x + evL y := by
  ext <;> simp [evL, addLC]

@[simp] theorem evL_smulLC (c : KE) (x : LC) :
    evL (smulLC c x) = algebraMap K21 L42 (evK c) * evL x := by
  ext <;> simp [evL, smulLC, QuadraticAlgebra.algebraMap_eq]

@[simp] theorem evL_mulLC (x y : LC) : evL (mulLC x y) = evL x * evL y := by
  ext <;> simp [evL, mulLC, ← epsK_eq] <;> ring

theorem four_mul_half (a : K21) : 4 * (a / 2) = 2 * a := by
  rw [show (4 : K21) = 2 * 2 by norm_num, mul_assoc, mul_div_cancel₀ _ two_ne_zero]

theorem L42_re_mul (z w : L42) : (z * w).re = z.re * w.re + epsK * z.im * w.im := rfl
theorem L42_im_mul (z w : L42) : (z * w).im = z.re * w.im + z.im * w.re + 0 * z.im * w.im := rfl
theorem N84_re_mul (z w : N84) : (z * w).re = z.re * w.re + eN * z.im * w.im := rfl
theorem N84_im_mul (z w : N84) : (z * w).im = z.re * w.im + z.im * w.re + 0 * z.im * w.im := rfl

theorem evL_e4LC : evL e4LC = 4 * eN := by
  ext <;> simp [evL, e4LC, eN, eaK, ebK, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat,
    four_mul_half]

theorem algebraMap_N84 (c : K21) : algebraMap K21 N84 c = ⟨algebraMap K21 L42 c, 0⟩ := rfl

@[simp] theorem evN_addNC (x y : NC) : evN (addNC x y) = evN x + evN y := by
  ext <;> simp [evN, evL, addNC, addLC] <;> ring

@[simp] theorem evN_smulNC (c : KE) (x : NC) :
    evN (smulNC c x) = algebraMap K21 N84 (evK c) * evN x := by
  ext <;> simp [evN, evL, smulNC, smulLC, algebraMap_N84, QuadraticAlgebra.algebraMap_eq] <;> ring

@[simp] theorem evN_mulNC (x y : NC) : evN (mulNC x y) = evN x * evN y := by
  have hre : (evN x * evN y).re = (evN x).re * (evN y).re + eN * (evN x).im * (evN y).im :=
    N84_re_mul _ _
  have him : (evN x * evN y).im = (evN x).re * (evN y).im + (evN x).im * (evN y).re +
      0 * (evN x).im * (evN y).im := N84_im_mul _ _
  apply QuadraticAlgebra.ext
  · rw [hre]
    ext <;> simp only [evN, evL, mulNC, mulLC, addLC, e4LC, evK_add, evK_mul, evK_lin, evK_int,
      ← epsK_eq, L42_re_mul, L42_im_mul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
      zero_mul, add_zero, eN, eaK, ebK] <;> push_cast <;> ring
  · rw [him]
    ext <;> simp only [evN, evL, mulNC, mulLC, addLC, e4LC, evK_add, evK_mul, evK_lin, evK_int,
      ← epsK_eq, L42_re_mul, L42_im_mul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
      zero_mul, add_zero, eN, eaK, ebK] <;> push_cast <;> ring

/-! ## Checks -/

/-- Both coordinates of `x - y` vanish (one Kronecker check each). -/
def checkLC (k : ℕ) (x y : LC) : Bool := checkK k (.sub x.1 y.1) && checkK k (.sub x.2 y.2)

/-- The four coordinates of `x - y` vanish. -/
def checkNC (k : ℕ) (x y : NC) : Bool := checkLC k x.1 y.1 && checkLC k x.2 y.2

theorem evL_eq_of_checkLC {k : ℕ} {x y : LC} (h : checkLC k x y = true) : evL x = evL y := by
  simp only [checkLC, Bool.and_eq_true] at h
  exact evL_ext (evK_eq_of_check _ _ _ h.1) (evK_eq_of_check _ _ _ h.2)

theorem evN_eq_of_checkNC {k : ℕ} {x y : NC} (h : checkNC k x y = true) : evN x = evN y := by
  simp only [checkNC, checkLC, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  simp only [evN, evL, evK_eq_of_check _ _ _ h1, evK_eq_of_check _ _ _ h2,
    evK_eq_of_check _ _ _ h3, evK_eq_of_check _ _ _ h4]

end FurioLombardo.Discharge.SelmerBasis.Tower
