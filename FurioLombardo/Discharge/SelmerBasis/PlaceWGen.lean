import FurioLombardo.Discharge.SelmerBasis.QuadLocal
import FurioLombardo.Discharge.SelmerBasis.Bridge
import FurioLombardo.Discharge.M4Cert.Hensel

/-!
# Generic layer of the p-adic places w2, w3 and 7 (lane selmer-basis w-places)

Algebra and norm facts shared by the per place files:

* `qaLift φ u hu`: the ring hom `QuadraticAlgebra R a b →+* S` extending `φ` by `ω ↦ u`, `u² = φ a + φ b u`
  (the embeddings of `K21[Y]/(Y² - B Y - A)` and of `L42` into a component field);
* `isSquare_of_sub_sq_lt`: `x` is a square when `‖x - s²‖ < ‖4‖ ‖s‖²` (local square theorem);
* `isSquare_of_eisen_cert`: the square certificate at an Eisenstein component `QF K A B`: from
  `x = π^(2mh) Y^(2ep) S''² + π^n0 r0 + π^n1 r1 Y + t` with `S'' = (1 + π c0) + s1 Y`, all of norm at
  most `1`, `‖t‖ ≤ ‖π‖^n0` and `n0 > m + 2e`, `n1 ≥ m + 2e` (`m = 2 mh + ep`);
* `exists_sqrt_near`: a square root near an approximate one (Hensel, with its precision);
* `evTab`, `dpTab`: the expansion `∏_{j ∈ S} (1 + t^j y) = Σ_n (Σ_d c_{n,d} t^d) y^n` computed by a
  dynamic program on integer tables (`prod_eq_evTab`), and its truncation at `t^D` with an integral
  remainder (`evTab_trunc`, `norm_evTab_le_one`).
-/

namespace FurioLombardo.Discharge.SelmerBasis

/-! ## Ring homs out of a quadratic algebra -/

section Lift

open QuadraticAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] {a b : R}

/-- The ring hom `QuadraticAlgebra R a b →+* S` extending `φ` by `ω ↦ u` when `u * u = φ a + φ b * u`. -/
def qaLift (φ : R →+* S) (u : S) (hu : u * u = φ a + φ b * u) : QuadraticAlgebra R a b →+* S where
  toFun z := φ z.re + φ z.im * u
  map_one' := by simp [re_one, im_one]
  map_mul' z w := by
    simp only [re_mul, im_mul, map_add, map_mul]
    linear_combination (-(φ z.im * φ w.im)) * hu
  map_zero' := by simp
  map_add' z w := by simp only [re_add, im_add, map_add]; ring

theorem qaLift_apply (φ : R →+* S) (u : S) (hu : u * u = φ a + φ b * u)
    (z : QuadraticAlgebra R a b) : qaLift φ u hu z = φ z.re + φ z.im * u := rfl

@[simp] theorem qaLift_mk (φ : R →+* S) (u : S) (hu : u * u = φ a + φ b * u) (x y : R) :
    qaLift φ u hu (⟨x, y⟩ : QuadraticAlgebra R a b) = φ x + φ y * u := rfl

@[simp] theorem qaLift_algebraMap (φ : R →+* S) (u : S) (hu : u * u = φ a + φ b * u) (x : R) :
    qaLift φ u hu (algebraMap R (QuadraticAlgebra R a b) x) = φ x := by
  simp [qaLift_apply, algebraMap_eq]

@[simp] theorem qaLift_omega (φ : R →+* S) (u : S) (hu : u * u = φ a + φ b * u) :
    qaLift φ u hu (ω : QuadraticAlgebra R a b) = u := by
  simp [qaLift_apply]

end Lift

/-! ## Square certificates -/

section Square

/-- **Local square theorem, difference form**: `‖x - s²‖ < ‖4‖ ‖s‖²` makes `x` a square. -/
theorem isSquare_of_sub_sq_lt {F : Type*} [NormedField F] [IsUltrametricDist F] [ProperSpace F]
    {π : F} (hπ : NormUnif π) (h2 : (2 : F) ≠ 0) {x s : F} (hs : s ≠ 0)
    (h : ‖x - s ^ 2‖ < ‖(4 : F)‖ * ‖s‖ ^ 2) : IsSquare x := by
  refine isSquare_of_norm_div_sq_sub_one_lt hπ h2 hs ?_
  have hs2 : 0 < ‖s‖ ^ 2 := pow_pos (norm_pos_iff.mpr hs) 2
  have hs2' : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  rw [div_sub_one hs2', norm_div, norm_pow, div_lt_iff₀ hs2]
  exact h

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **The square certificate at an Eisenstein component.** With `Y = QF.mk K A B 0 1`, `m = 2 mh + ep`
and `S = π^mh Y^ep ((1 + π c0) + s1 Y)` (of norm `‖Y‖^m`), the element
`x = S² + π^n0 r0 + π^n1 r1 Y + t` is a square as soon as `c0, s1, r0, r1` are integral,
`‖t‖ ≤ ‖π‖^n0`, `n0 > m + 2e` and `n1 ≥ m + 2e` (then the three corrections are below `‖4‖ ‖S‖²`). -/
theorem isSquare_of_eisen_cert [ProperSpace K] {π A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)]
    (hπ : NormUnif π) (hA : ‖A‖ = ‖π‖) (hB : ‖B‖ < 1) {e : ℕ} (h2 : ‖(2 : K)‖ = ‖π‖ ^ e)
    {mh ep n0 n1 : ℕ} {c0 s1 r0 r1 : K} (hc0 : ‖c0‖ ≤ 1) (hs1 : ‖s1‖ ≤ 1) (hr0 : ‖r0‖ ≤ 1)
    (hr1 : ‖r1‖ ≤ 1) (hn0 : 2 * mh + ep + 2 * e < n0) (hn1 : 2 * mh + ep + 2 * e ≤ n1)
    {x t : QF K A B} (ht : ‖t‖ ≤ ‖π‖ ^ n0)
    (hx : x = (algebraMap K (QF K A B) π ^ mh * QF.mk K A B 0 1 ^ ep *
        QF.mk K A B (1 + π * c0) s1) ^ 2 + algebraMap K (QF K A B) (π ^ n0 * r0) +
        algebraMap K (QF K A B) (π ^ n1 * r1) * QF.mk K A B 0 1 + t) :
    IsSquare x := by
  set Y := QF.mk K A B 0 1 with hYdef
  have hY0 := qfE_Y_pos hπ hA hB
  have hY1 := qfE_Y_lt_one hπ hA hB
  have hYπ : ‖π‖ = ‖Y‖ ^ 2 := (qfE_norm_Y hπ hA hB).symm
  have hπ0 : 0 < ‖π‖ := norm_pos_iff.mpr hπ.ne_zero
  -- the norm of the unit `S''`
  have hπc : ‖π * c0‖ < 1 := by
    rw [norm_mul]
    calc ‖π‖ * ‖c0‖ ≤ ‖π‖ * 1 := mul_le_mul_of_nonneg_left hc0 hπ0.le
      _ < 1 := by rw [mul_one]; exact hπ.norm_lt_one
  have hu1 : ‖1 + π * c0‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hπc.ne'),
      norm_one, max_eq_left hπc.le]
  have hS'' : ‖QF.mk K A B (1 + π * c0) s1‖ = 1 := by
    rw [qfE_norm hπ hA hB, hu1]
    exact max_eq_left (by
      calc ‖s1‖ * ‖Y‖ ≤ 1 * 1 := mul_le_mul hs1 hY1.le (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1)
  set S := algebraMap K (QF K A B) π ^ mh * Y ^ ep * QF.mk K A B (1 + π * c0) s1 with hSdef
  have hSn : ‖S‖ = ‖Y‖ ^ (2 * mh + ep) := by
    rw [hSdef, norm_mul, norm_mul, norm_pow, norm_pow, QF.norm_algebraMap, hS'', mul_one, hYπ,
      ← pow_mul, ← pow_add]
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hSn
    exact (pow_pos hY0 _).ne' hSn.symm
  have h4 : ‖(4 : QF K A B)‖ = ‖Y‖ ^ (4 * e) := by
    have : (4 : QF K A B) = algebraMap K (QF K A B) 4 := (map_ofNat _ 4).symm
    rw [this, QF.norm_algebraMap, show (4 : K) = 2 * 2 by norm_num, norm_mul, h2, hYπ, ← pow_mul,
      ← pow_add]
    ring_nf
  have hbound : ‖(4 : QF K A B)‖ * ‖S‖ ^ 2 = ‖Y‖ ^ (4 * e + 2 * (2 * mh + ep)) := by
    rw [h4, hSn, ← pow_mul, ← pow_add]
    ring_nf
  have hlt : ∀ k : ℕ, 4 * e + 2 * (2 * mh + ep) < k → ‖Y‖ ^ k < ‖Y‖ ^ (4 * e + 2 * (2 * mh + ep)) :=
    fun k hk => pow_lt_pow_right_of_lt_one₀ hY0 hY1 hk
  have hπn : ∀ n : ℕ, ‖π‖ ^ n = ‖Y‖ ^ (2 * n) := fun n => by rw [hYπ, ← pow_mul]
  have h0 : ‖algebraMap K (QF K A B) (π ^ n0 * r0)‖ < ‖(4 : QF K A B)‖ * ‖S‖ ^ 2 := by
    rw [QF.norm_algebraMap, norm_mul, norm_pow, hbound]
    calc ‖π‖ ^ n0 * ‖r0‖ ≤ ‖π‖ ^ n0 * 1 := mul_le_mul_of_nonneg_left hr0 (pow_nonneg hπ0.le _)
      _ = ‖Y‖ ^ (2 * n0) := by rw [mul_one, hπn]
      _ < _ := hlt _ (by omega)
  have h1 : ‖algebraMap K (QF K A B) (π ^ n1 * r1) * Y‖ < ‖(4 : QF K A B)‖ * ‖S‖ ^ 2 := by
    rw [norm_mul, QF.norm_algebraMap, norm_mul, norm_pow, hbound]
    calc ‖π‖ ^ n1 * ‖r1‖ * ‖Y‖ ≤ ‖π‖ ^ n1 * 1 * ‖Y‖ := by gcongr
      _ = ‖Y‖ ^ (2 * n1 + 1) := by rw [mul_one, hπn, pow_succ]
      _ < _ := hlt _ (by omega)
  have htt : ‖t‖ < ‖(4 : QF K A B)‖ * ‖S‖ ^ 2 := by
    rw [hbound]
    calc ‖t‖ ≤ ‖π‖ ^ n0 := ht
      _ = ‖Y‖ ^ (2 * n0) := hπn n0
      _ < _ := hlt _ (by omega)
  have h2F : (2 : QF K A B) ≠ 0 := by
    intro h
    have := congrArg norm h
    rw [norm_zero, qfE_two hπ hA hB h2] at this
    exact (pow_pos hY0 _).ne' this
  refine isSquare_of_sub_sq_lt (qfE_normUnif hπ hA hB) h2F hS0 ?_
  have hd : x - S ^ 2 = (algebraMap K (QF K A B) (π ^ n0 * r0) +
      algebraMap K (QF K A B) (π ^ n1 * r1) * Y) + t := by
    rw [hx]; ring
  rw [hd]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ htt)
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h0 h1)

end Square

/-! ## Square roots near an approximation -/

section Sqrt

open Polynomial

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **A square root near `s0`** (Hensel's lemma for `X² - z`): if `‖s0² - z‖ < ‖2 s0‖²` with `z`
and `s0` integral, then `z = s²` with `‖s - s0‖ ≤ ‖s0² - z‖ / ‖2 s0‖`. -/
theorem exists_sqrt_near {z s0 : K} (hz : ‖z‖ ≤ 1) (hs0 : ‖s0‖ ≤ 1)
    (h : ‖s0 ^ 2 - z‖ < ‖2 * s0‖ ^ 2) :
    ∃ s : K, s ^ 2 = z ∧ ‖s - s0‖ ≤ ‖s0 ^ 2 - z‖ / ‖2 * s0‖ := by
  have hcoeff : ∀ i, ‖((X : K[X]) ^ 2 - C z).coeff i‖ ≤ 1 := by
    intro i
    rw [coeff_sub, coeff_X_pow, coeff_C]
    rcases eq_or_ne i 2 with rfl | h2
    · simp
    · rcases eq_or_ne i 0 with rfl | h0
      · simpa using hz
      · simp [h2, h0]
  have hev : ∀ y : K, ((X : K[X]) ^ 2 - C z).eval y = y ^ 2 - z := fun y => by simp
  have hder : ∀ y : K, (derivative ((X : K[X]) ^ 2 - C z)).eval y = 2 * y := fun y => by
    simp; norm_num
  obtain ⟨s, hs, hsn⟩ := FurioLombardo.Discharge.M4Cert.hensel_of_norm_lt ((X : K[X]) ^ 2 - C z)
    hcoeff s0 hs0 (by rw [hev, hder]; exact h)
  rw [hev] at hs hsn
  rw [hder] at hsn
  exact ⟨s, sub_eq_zero.mp hs, hsn⟩

end Sqrt

/-! ## Expansion of `∏ (1 + t^j y)` -/

section Expand

/-- `Σ_d r_d t^d`. -/
def evRow {R : Type*} [CommRing R] (t : R) : List ℤ → R
  | [] => 0
  | c :: l => c + t * evRow t l

/-- `Σ_n (Σ_d c_{n,d} t^d) y^n` for the table `c` (rows `n`). -/
def evTab {R : Type*} [CommRing R] (t y : R) : List (List ℤ) → R
  | [] => 0
  | r :: c => evRow t r + y * evTab t y c

/-- Entrywise sum of two rows, the longer one decides the length. -/
def addR : List ℤ → List ℤ → List ℤ
  | [], r => r
  | c :: r, [] => c :: r
  | c :: r, c' :: r' => (c + c') :: addR r r'

/-- Rows added entrywise, the longer table decides the length. -/
def addT : List (List ℤ) → List (List ℤ) → List (List ℤ)
  | [], c => c
  | r :: c, [] => r :: c
  | r :: c, r' :: c' => addR r r' :: addT c c'

/-- Multiplication of a row by `t^j`. -/
def shiftD (j : ℕ) (r : List ℤ) : List ℤ := List.replicate j 0 ++ r

/-- One step of the dynamic program: multiplication by `1 + t^j y`. -/
def dpStep (j : ℕ) (c : List (List ℤ)) : List (List ℤ) := addT c ([] :: c.map (shiftD j))

/-- The table of `∏_{j ∈ S} (1 + t^j y)`. -/
def dpTab (S : List ℕ) : List (List ℤ) := S.foldr dpStep [[1]]

variable {R : Type*} [CommRing R] (t y : R)

theorem evRow_addR : ∀ r r' : List ℤ, evRow t (addR r r') = evRow t r + evRow t r'
  | [], r' => by simp [addR, evRow]
  | c :: r, [] => by simp [addR, evRow]
  | c :: r, c' :: r' => by
    simp only [addR, evRow, evRow_addR r r', Int.cast_add]; ring

theorem evRow_shiftD (j : ℕ) (r : List ℤ) : evRow t (shiftD j r) = t ^ j * evRow t r := by
  induction j with
  | zero => simp [shiftD]
  | succ j ih =>
    simp only [shiftD, List.replicate_succ, List.cons_append, evRow, Int.cast_zero, zero_add] at ih ⊢
    rw [ih]; ring

theorem evTab_addT : ∀ c c' : List (List ℤ), evTab t y (addT c c') = evTab t y c + evTab t y c'
  | [], c' => by simp [addT, evTab]
  | r :: c, [] => by simp [addT, evTab]
  | r :: c, r' :: c' => by
    simp only [addT, evTab, evRow_addR, evTab_addT c c']; ring

theorem evTab_map_shiftD (j : ℕ) : ∀ c : List (List ℤ),
    evTab t y (c.map (shiftD j)) = t ^ j * evTab t y c
  | [] => by simp [evTab]
  | r :: c => by
    simp only [List.map_cons, evTab, evRow_shiftD, evTab_map_shiftD j c]; ring

theorem evTab_dpStep (j : ℕ) (c : List (List ℤ)) :
    evTab t y (dpStep j c) = (1 + t ^ j * y) * evTab t y c := by
  simp only [dpStep, evTab_addT, evTab, evRow, evTab_map_shiftD]
  ring

/-- **The expansion**: `∏_{j ∈ S} (1 + t^j y)` is the value of the table `dpTab S`. -/
theorem prod_eq_evTab (S : List ℕ) :
    (S.map fun j => 1 + t ^ j * y).prod = evTab t y (dpTab S) := by
  induction S with
  | nil => simp [dpTab, evTab, evRow]
  | cons j S ih =>
    rw [List.map_cons, List.prod_cons, ih]
    simp only [dpTab, List.foldr_cons]
    rw [evTab_dpStep]

/-- The truncation of every row at `t^D`. -/
def truncT (D : ℕ) (c : List (List ℤ)) : List (List ℤ) := c.map (List.take D)

/-- The rest of every row above `t^D`. -/
def restT (D : ℕ) (c : List (List ℤ)) : List (List ℤ) := c.map (List.drop D)

theorem evRow_take_drop (D : ℕ) : ∀ r : List ℤ,
    evRow t r = evRow t (r.take D) + t ^ D * evRow t (r.drop D) := by
  induction D with
  | zero => intro r; simp [evRow]
  | succ D ih =>
    intro r
    cases r with
    | nil => simp [evRow]
    | cons c r =>
      simp only [List.take_succ_cons, List.drop_succ_cons, evRow]
      rw [ih r]; ring

/-- **Truncation**: the table is its truncation at `t^D` plus `t^D` times the rest. -/
theorem evTab_trunc (D : ℕ) : ∀ c : List (List ℤ),
    evTab t y c = evTab t y (truncT D c) + t ^ D * evTab t y (restT D c)
  | [] => by simp [evTab, truncT, restT]
  | r :: c => by
    simp only [truncT, restT, List.map_cons] at *
    simp only [evTab]
    rw [evRow_take_drop t D r, evTab_trunc D c]
    simp only [truncT, restT]
    ring

theorem norm_evRow_le_one {F : Type*} [NormedField F] [IsUltrametricDist F] {t : F}
    (ht : ‖t‖ ≤ 1) : ∀ r : List ℤ, ‖evRow t r‖ ≤ 1
  | [] => by simp [evRow]
  | c :: r => by
    simp only [evRow]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
    · exact IsUltrametricDist.norm_intCast_le_one F c
    · rw [norm_mul]
      calc ‖t‖ * ‖evRow t r‖ ≤ 1 * 1 := mul_le_mul ht (norm_evRow_le_one ht r) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

/-- An integer table at integral `t`, `y` has an integral value. -/
theorem norm_evTab_le_one {F : Type*} [NormedField F] [IsUltrametricDist F] {t y : F}
    (ht : ‖t‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ∀ c : List (List ℤ), ‖evTab t y c‖ ≤ 1
  | [] => by simp [evTab]
  | r :: c => by
    simp only [evTab]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (norm_evRow_le_one ht r) ?_)
    rw [norm_mul]
    calc ‖y‖ * ‖evTab t y c‖ ≤ 1 * 1 :=
          mul_le_mul hy (norm_evTab_le_one ht hy c) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

end Expand

end FurioLombardo.Discharge.SelmerBasis
