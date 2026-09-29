import FurioLombardo.M1.Residue
import FurioLombardo.M3a.CoordRing

/-!
# Polynomials over K21 with kernel checked coefficients (WP2 of the M3a discharge)

`pK l` is the polynomial `Σ evK(l_i) X^i` over K21 for a list `l` of Kronecker expressions (lane
M1's `KE`, constant term first), and `pQ m l = m⁻¹ · pK l`. The symbolic list operations `addP`,
`smulP`, `subP`, `mulP`, `derivP` build the coefficient expressions of sums, products and
derivatives, and `pK` turns them into ring operations (`pK_addP`, `pK_mulP`, `pK_derivP`, ...).
An identity `pK l = pK l'` follows from one Kronecker test per coefficient (`pK_eq_of_eqCheck`,
`pK_eq_of_coefCheck`); the kernel never multiplies polynomials over K21, it only evaluates the
coefficient expressions at `N = 2 ^ k`.

Residues: `resHom_zkO` evaluates lane M1's residue homomorphism `𝓞 K21 → R` on `zkO a`, and
`not_isSquare_zkE_of_res` turns a non residue in `R` (for instance `ZMod p` at a root of `f`)
into a non square in K21 (a square root of an algebraic integer is an algebraic integer).

Finally `goodSextic_of` and `goodSextic_map` give lane M3a's `GoodSextic` for a separable sextic
and for its base change along any field homomorphism.
-/

namespace FurioLombardo.Discharge.M3a

open Polynomial NumberField FurioLombardo.M1 FurioLombardo.M1.Kron

/-! ## Polynomials with coefficient expressions -/

/-- `Σ evK(l_i) X^i` (constant term first). -/
noncomputable def pK : List KE → K21[X]
  | [] => 0
  | e :: l => C (evK e) + X * pK l

@[simp] theorem pK_nil : pK [] = 0 := rfl

@[simp] theorem pK_cons (e : KE) (l : List KE) : pK (e :: l) = C (evK e) + X * pK l := rfl

/-- Coefficientwise sum. -/
def addP : List KE → List KE → List KE
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => .add a b :: addP l m

/-- Multiplication by the constant `a`. -/
def smulP (a : KE) (l : List KE) : List KE := l.map (.mul a)

/-- Difference. -/
def subP (l m : List KE) : List KE := addP l (smulP (.int (-1)) m)

/-- Product. -/
def mulP : List KE → List KE → List KE
  | [], _ => []
  | a :: l, m => addP (smulP a m) (.int 0 :: mulP l m)

/-- Derivative. -/
def derivP : List KE → List KE
  | [] => []
  | _ :: l => addP l (.int 0 :: derivP l)

theorem pK_addP : ∀ l m : List KE, pK (addP l m) = pK l + pK m
  | [], m => by simp [addP]
  | a :: l, [] => by simp [addP]
  | a :: l, b :: m => by
    simp only [addP, pK_cons, evK_add, map_add, pK_addP l m]; ring

theorem pK_smulP (a : KE) : ∀ l : List KE, pK (smulP a l) = C (evK a) * pK l
  | [] => by simp [smulP]
  | e :: l => by
    have ih := pK_smulP a l
    simp only [smulP, List.map_cons, pK_cons, evK_mul, map_mul] at ih ⊢
    rw [ih]; ring

theorem pK_subP (l m : List KE) : pK (subP l m) = pK l - pK m := by
  rw [subP, pK_addP, pK_smulP]; simp; ring

theorem pK_mulP : ∀ l m : List KE, pK (mulP l m) = pK l * pK m
  | [], m => by simp [mulP]
  | a :: l, m => by
    simp only [mulP, pK_addP, pK_smulP, pK_cons, evK_int, pK_mulP l m]; simp; ring

theorem pK_derivP : ∀ l : List KE, pK (derivP l) = derivative (pK l)
  | [] => by simp [derivP]
  | e :: l => by
    simp only [derivP, pK_addP, pK_cons, evK_int, pK_derivP l, derivative_add, derivative_C,
      derivative_mul, derivative_X]
    simp

theorem coeff_pK : ∀ (l : List KE) (i : ℕ), (pK l).coeff i = evK (l.getD i (.int 0))
  | [], i => by simp
  | e :: l, 0 => by simp
  | e :: l, i + 1 => by simp [coeff_pK l i]

theorem pK_eq_of_coeff (l m : List KE)
    (h : ∀ i < max l.length m.length, evK (l.getD i (.int 0)) = evK (m.getD i (.int 0))) :
    pK l = pK m := by
  ext i
  rw [coeff_pK, coeff_pK]
  by_cases hi : i < max l.length m.length
  · exact h i hi
  · push Not at hi
    rw [List.getD_eq_default _ _ (le_of_max_le_left hi),
      List.getD_eq_default _ _ (le_of_max_le_right hi)]

/-! ## Kernel checks of polynomial identities -/

/-- The Kronecker test (at `N = 2 ^ k`) of coefficient `i` of `pK l - pK m`. -/
def coefCheck (k : ℕ) (l m : List KE) (i : ℕ) : Bool :=
  checkK k (.sub (l.getD i (.int 0)) (m.getD i (.int 0)))

/-- The Kronecker tests of all coefficients of `pK l - pK m`. -/
def eqCheck (k : ℕ) (l m : List KE) : Bool :=
  (List.range (max l.length m.length)).all (coefCheck k l m)

theorem pK_eq_of_coefCheck (k : ℕ) (l m : List KE)
    (h : ∀ i < max l.length m.length, coefCheck k l m i = true) : pK l = pK m :=
  pK_eq_of_coeff l m fun i hi => evK_eq_of_check k _ _ (h i hi)

theorem pK_eq_of_eqCheck (k : ℕ) (l m : List KE) (h : eqCheck k l m = true) : pK l = pK m :=
  pK_eq_of_coefCheck k l m fun i hi => List.all_eq_true.mp h i (List.mem_range.mpr hi)

/-! ## Polynomials with a denominator -/

/-- `m⁻¹ · pK l`. -/
noncomputable def pQ (m : ℕ) (l : List KE) : K21[X] := C ((m : K21)⁻¹) * pK l

theorem natCast_ne_zero {m : ℕ} (hm : m ≠ 0) : (m : K21) ≠ 0 := Nat.cast_ne_zero.mpr hm

theorem coeff_pQ (m : ℕ) (l : List KE) (i : ℕ) :
    (pQ m l).coeff i = (m : K21)⁻¹ * evK (l.getD i (.int 0)) := by
  rw [pQ, coeff_C_mul, coeff_pK]

theorem pQ_mul (m n : ℕ) (l l' : List KE) : pQ m l * pQ n l' = pQ (m * n) (mulP l l') := by
  simp only [pQ, pK_mulP, Nat.cast_mul, mul_inv, map_mul]; ring

theorem pQ_sq (m : ℕ) (l : List KE) : pQ m l ^ 2 = pQ (m * m) (mulP l l) := by
  rw [pow_two, pQ_mul]

theorem pQ_add {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (l l' : List KE) :
    pQ m l + pQ n l' = pQ (m * n) (addP (smulP (.int n) l) (smulP (.int m) l')) := by
  have hm' := natCast_ne_zero hm
  have hn' := natCast_ne_zero hn
  have e1 : ((m * n : ℕ) : K21)⁻¹ * (n : K21) = (m : K21)⁻¹ := by
    push_cast; field_simp
  have e2 : ((m * n : ℕ) : K21)⁻¹ * (m : K21) = (n : K21)⁻¹ := by
    push_cast; field_simp
  simp only [pQ, pK_addP, pK_smulP, evK_int, Int.cast_natCast, mul_add, ← mul_assoc, ← map_mul,
    e1, e2]

theorem pQ_sub {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (l l' : List KE) :
    pQ m l - pQ n l' = pQ (m * n) (subP (smulP (.int n) l) (smulP (.int m) l')) := by
  have hm' := natCast_ne_zero hm
  have hn' := natCast_ne_zero hn
  have e1 : ((m * n : ℕ) : K21)⁻¹ * (n : K21) = (m : K21)⁻¹ := by
    push_cast; field_simp
  have e2 : ((m * n : ℕ) : K21)⁻¹ * (m : K21) = (n : K21)⁻¹ := by
    push_cast; field_simp
  simp only [pQ, pK_subP, pK_smulP, evK_int, Int.cast_natCast, mul_sub, ← mul_assoc, ← map_mul,
    e1, e2]

/-- Clearing denominators: `pQ m l = pQ n l'` from `n · pK l = m · pK l'`. -/
theorem pQ_eq_of {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) {l l' : List KE}
    (h : pK (smulP (.int n) l) = pK (smulP (.int m) l')) : pQ m l = pQ n l' := by
  have hm' := natCast_ne_zero hm
  have hn' := natCast_ne_zero hn
  rw [pK_smulP, pK_smulP, evK_int, evK_int, Int.cast_natCast, Int.cast_natCast] at h
  calc C (m : K21)⁻¹ * pK l = C ((m : K21)⁻¹ * (n : K21)⁻¹) * (C (n : K21) * pK l) := by
        rw [← mul_assoc, ← map_mul]; congr 2; field_simp
    _ = C ((m : K21)⁻¹ * (n : K21)⁻¹) * (C (m : K21) * pK l') := by rw [h]
    _ = C (n : K21)⁻¹ * pK l' := by rw [← mul_assoc, ← map_mul]; congr 2; field_simp

theorem C_eq_pQ (m : ℕ) (e : KE) : C ((m : K21)⁻¹ * evK e) = pQ m [e] := by
  simp [pQ]

theorem derivative_pQ (m : ℕ) (l : List KE) : derivative (pQ m l) = pQ m (derivP l) := by
  rw [pQ, pQ, derivative_C_mul, pK_derivP]

theorem natDegree_pQ_le (m : ℕ) (l : List KE) : (pQ m l).natDegree ≤ l.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_pQ, List.getD_eq_default _ _ (by omega)]
  simp

theorem natDegree_pQ {m : ℕ} (hm : m ≠ 0) {l : List KE} {n : ℕ} (hl : l.length = n + 1)
    (hn : evK (l.getD n (.int 0)) ≠ 0) : (pQ m l).natDegree = n := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · have := natDegree_pQ_le m l; omega
  · rw [coeff_pQ]; exact mul_ne_zero (inv_ne_zero (natCast_ne_zero hm)) hn

theorem leadingCoeff_pQ {m : ℕ} (hm : m ≠ 0) {l : List KE} {n : ℕ} (hl : l.length = n + 1)
    (hn : evK (l.getD n (.int 0)) ≠ 0) :
    (pQ m l).leadingCoeff = (m : K21)⁻¹ * evK (l.getD n (.int 0)) := by
  rw [leadingCoeff, natDegree_pQ hm hl hn, coeff_pQ]

/-- A monic `pQ`: the top coefficient expression is the integer `m`. -/
theorem monic_pQ {m : ℕ} (hm : m ≠ 0) {l : List KE} {n : ℕ} (hl : l.length = n + 1)
    (htop : l.getD n (.int 0) = .int m) : (pQ m l).Monic ∧ (pQ m l).natDegree = n := by
  have hm' := natCast_ne_zero hm
  have hn : evK (l.getD n (.int 0)) ≠ 0 := by rw [htop, evK_int, Int.cast_natCast]; exact hm'
  refine ⟨?_, natDegree_pQ hm hl hn⟩
  rw [Monic, leadingCoeff_pQ hm hl hn, htop, evK_int, Int.cast_natCast, inv_mul_cancel₀ hm']

/-! ## Residues and non squares -/

theorem map_evalL {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (t : R) :
    ∀ l : List ℤ, φ (evalL t l) = evalL (φ t) l
  | [] => by simp [evalL]
  | a :: l => by simp [evalL, map_evalL φ t l]

theorem Dz_mul_zkO (a : List ℤ) : (Dz : 𝓞 K21) * zkO a = evalL θO (combo a zkNum) := by
  apply RingOfIntegers.coe_injective
  rw [map_mul, map_natCast, map_evalL]
  change (Dz : K21) * (dInv * evalL θ (combo a zkNum)) = evalL θ (combo a zkNum)
  rw [← mul_assoc, mul_comm (Dz : K21) dInv, dInv_mul, one_mul]

theorem aeval_fZ_of_evalL {R : Type*} [CommRing R] (r : R) (h : evalL r fL = 0) :
    aeval r fZ = 0 := by
  rw [← ofListL_fL, aeval_ofListL]; exact h

/-- Lane M1's residue homomorphism on `zkO a`. -/
theorem resHom_zkO {R : Type*} [CommRing R] (r : R) (hr : aeval r fZ = 0) (u : R)
    (hu : u * (DB : R) = 1) (w : R) (hw : w * (Dz : R) = 1) (a : List ℤ) :
    resHom r hr u hu (zkO a) = w * evalL r (combo a zkNum) := by
  have h := congrArg (resHom r hr u hu) (Dz_mul_zkO a)
  rw [map_mul, map_natCast, map_evalL, resHom_θO] at h
  rw [← h, ← mul_assoc, hw, one_mul]

/-- A non residue gives a non square: if `zkE a = y²` then `y` is integral, and its residue is a
square root of the residue of `zkO a`. -/
theorem not_isSquare_zkE_of_res {R : Type*} [CommRing R] (r : R) (hr : evalL r fL = 0) (u : R)
    (hu : u * (DB : R) = 1) (w : R) (hw : w * (Dz : R) = 1) (a : List ℤ)
    (h : ¬ IsSquare (w * evalL r (combo a zkNum))) : ¬ IsSquare (zkE a) := by
  rintro ⟨y, hy⟩
  have hint : IsIntegral ℤ y :=
    IsIntegral.of_pow two_pos (by rw [pow_two, ← hy]; exact isIntegral_zkE a)
  let Y : 𝓞 K21 := ⟨y, hint⟩
  have hY : zkO a = Y * Y := by
    apply RingOfIntegers.coe_injective
    rw [map_mul]
    exact hy
  apply h
  rw [← resHom_zkO r (aeval_fZ_of_evalL r hr) u hu w hw a, hY, map_mul]
  exact ⟨_, rfl⟩

/-- A nonzero residue gives a nonzero element. -/
theorem zkE_ne_zero_of_res {R : Type*} [CommRing R] (r : R) (hr : evalL r fL = 0) (u : R)
    (hu : u * (DB : R) = 1) (w : R) (hw : w * (Dz : R) = 1) (a : List ℤ)
    (h : w * evalL r (combo a zkNum) ≠ 0) : zkE a ≠ 0 := by
  intro h0
  apply h
  have : zkO a = 0 := RingOfIntegers.coe_injective (by rw [map_zero]; exact h0)
  rw [← resHom_zkO r (aeval_fZ_of_evalL r hr) u hu w hw a, this, map_zero]

theorem not_isSquare_inv_sq_mul {K : Type*} [Field K] {c x : K} (hc : c ≠ 0)
    (hx : ¬ IsSquare x) : ¬ IsSquare ((c ^ 2)⁻¹ * x) := by
  rintro ⟨y, hy⟩
  exact hx ⟨c * y, by rw [show x = c ^ 2 * ((c ^ 2)⁻¹ * x) by field_simp, hy]; ring⟩

/-! ## `GoodSextic` from separability -/

open FurioLombardo.M3a.Genus2 in
theorem goodSextic_of {K : Type*} [Field K] {f : K[X]} (hs : f.Separable) (hd : f.natDegree = 6)
    (hl : ¬ IsSquare f.leadingCoeff) (h2 : (2 : K) ≠ 0) : GoodSextic f :=
  ⟨hs.squarefree, hd, hl, h2⟩

open FurioLombardo.M3a.Genus2 in
/-- Base change of a separable sextic along a field homomorphism `σ`: squarefree (separability
survives), of degree 6 and with `2 ≠ 0` (`σ` is injective); the leading coefficient is `σ` of
the old one, so only its non squareness is a hypothesis. -/
theorem goodSextic_map {K L : Type*} [Field K] [Field L] (σ : K →+* L) {f : K[X]}
    (hs : f.Separable) (hd : f.natDegree = 6) (h2 : (2 : K) ≠ 0)
    (hl : ¬ IsSquare (σ f.leadingCoeff)) : GoodSextic (f.map σ) :=
  ⟨hs.map.squarefree, by rw [natDegree_map, hd], by rw [leadingCoeff_map]; exact hl,
    by rw [← map_ofNat σ 2]; exact (map_ne_zero σ).mpr h2⟩

end FurioLombardo.Discharge.M3a
