import FurioLombardo.Discharge.SelmerBasis.SquareLemmas

/-!
# Echelon certificates of independence modulo squares, coordinates, and an F₂ checker

1. `sb_echelon` (abstract) and `sb_indep_of_echelonOK`: a family `b : Fin r → G` in a commutative
   group is independent modulo squares when each row has a pivot position (checked by the Boolean
   `echelonOK`, for `decide +kernel`) and every position passes its test.
2. Component data: at a component field `F` (reached by `φ : G →* Fˣ`) with shape `Q : CShape`
   (`e` with `‖2‖ = ‖π‖ ^ e`, `f` residue digits, trace bitmask `τ`, `N` for odd residue
   characteristic), each element carries a valuation exponent and a unit datum `UDatum`; `DFact`
   is its analytic content, `CompOK` the field facts, and `comp_test` gives every test of that
   component (`admB`, `digB`).
3. Coordinates: `sb_coord` and `sb_mem_iff` (membership in `K ⊔ closure(range μ) ⊔ squares` is a
   linear condition over `ZMod 2`).
4. F₂ linear algebra on `ℕ` bitmasks for `decide +kernel`: `bitv` (the low `n` bits as a vector),
   `xorSel`, `dotB`, `allLt`; certificates `leftInvOK` (trivial kernel), `kerSpanOK` (kernel inside a
   span), `annOK` (an annihilator of a span), `dotRow` (rows of the product with a column family).
-/

namespace FurioLombardo.Discharge.SelmerBasis

open Finset

/-! ## Bitmask vectors and Boolean quantifiers -/

/-- The low `n` bits of `x` as a vector over `ZMod 2`. -/
def bitv (n x : ℕ) : Fin n → ZMod 2 := fun j => if x.testBit j then 1 else 0

/-- `allLt P n`: `P k` holds for every `k < n`. -/
def allLt (P : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allLt P n && P n

/-- `anyLt P n`: `P k` holds for some `k < n`. -/
def anyLt (P : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => anyLt P n || P n

/-- `xorSel R m c`: the xor of the rows `R k`, `k < m`, whose bit `k` is set in `c`. -/
def xorSel (R : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, c => if c.testBit m then xorSel R m c ^^^ R m else xorSel R m c

/-- The parity of the dot product of the low `n` bits of `x` and `y`. -/
def dotB : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | n + 1, x, y => xor (dotB n x y) (x.testBit n && y.testBit n)

theorem allLt_iff (P : ℕ → Bool) (n : ℕ) : allLt P n = true ↔ ∀ k < n, P k = true := by
  induction' n with n ih
  · simp [allLt]
  · simp [allLt, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ k hk
      rcases Nat.le_iff_lt_or_eq.mp hk with (hk_lt | hk_eq)
      · exact h k hk_lt
      · rw [hk_eq]; exact hn
    · intro h
      constructor
      · intro k hk
        exact h k (Nat.le_of_lt hk)
      · exact h n (le_refl n)

theorem anyLt_iff (P : ℕ → Bool) (n : ℕ) : anyLt P n = true ↔ ∃ k < n, P k = true := by
  induction n with
  | zero =>
      simp [anyLt]
  | succ n ih =>
      rw [anyLt, Bool.or_eq_true, ih]
      constructor
      · rintro (h | h)
        · rcases h with ⟨k, hk, hP⟩
          exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self n), hP⟩
        · exact ⟨n, Nat.lt_succ_self n, h⟩
      · rintro ⟨k, hk, hP⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with (hk' | rfl)
        · exact Or.inl ⟨k, hk', hP⟩
        · exact Or.inr hP

theorem bitv_xor (n x y : ℕ) : bitv n (x ^^^ y) = bitv n x + bitv n y := by
  funext j
  unfold bitv
  rw [Nat.testBit_xor]
  by_cases hx : x.testBit j
  · by_cases hy : y.testBit j
    · simp [hx, hy, Bool.xor_self]
      decide
    · simp [hx, hy, Bool.xor_true]
  · by_cases hy : y.testBit j
    · simp [hx, hy, Bool.xor_false]
    · simp [hx, hy, Bool.xor_false]

theorem bitv_xorSel (n : ℕ) (R : ℕ → ℕ) (m c : ℕ) :
    bitv n (xorSel R m c) = ∑ k : Fin m, bitv m c k • bitv n (R k) := by
  induction m with
  | zero =>
      simp [xorSel]
      ext j
      simp [bitv, Nat.zero_testBit]
  | succ m ih =>
      simp [xorSel]
      by_cases h : c.testBit m
      · simp [h]
        rw [bitv_xor]
        rw [ih]
        rw [Fin.sum_univ_castSucc]
        simp [bitv, Fin.val_castSucc, Fin.val_last, h]
      · simp [h]
        rw [ih]
        rw [Fin.sum_univ_castSucc]
        simp [bitv, Fin.val_castSucc, Fin.val_last, h]

theorem dotB_eq (n x y : ℕ) :
    (if dotB n x y then 1 else 0 : ZMod 2) = ∑ j : Fin n, bitv n x j * bitv n y j := by
  induction n with
  | zero => simp [dotB, bitv]
  | succ n ih =>
    rw [dotB, Fin.sum_univ_castSucc]
    -- Goal: (if (dotB n x y ^^ x.testBit n && y.testBit n) = true then 1 else 0) =
    --   (∑ j : Fin n, bitv (n+1) x (Fin.castSucc j) * bitv (n+1) y (Fin.castSucc j)) +
    --   bitv (n+1) x (Fin.last n) * bitv (n+1) y (Fin.last n)
    have hcast : ∀ j : Fin n, bitv (n + 1) x (Fin.castSucc j) = bitv n x j ∧
                                      bitv (n + 1) y (Fin.castSucc j) = bitv n y j := by
      intro j
      simp [bitv, Fin.val_castSucc]
    have hlast_x : bitv (n + 1) x (Fin.last n) = (if x.testBit n then 1 else 0 : ZMod 2) := by
      simp [bitv, Fin.val_last]
    have hlast_y : bitv (n + 1) y (Fin.last n) = (if y.testBit n then 1 else 0 : ZMod 2) := by
      simp [bitv, Fin.val_last]
    have hsum : (∑ j : Fin n, bitv (n + 1) x (Fin.castSucc j) * bitv (n + 1) y (Fin.castSucc j)) =
               (∑ j : Fin n, bitv n x j * bitv n y j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases hcast j with ⟨hxj, hyj⟩
      simp [hxj, hyj]
    rw [hsum, hlast_x, hlast_y, ← ih]
    -- Goal: (if (dotB n x y ^^ x.testBit n && y.testBit n) = true then 1 else 0) =
    --   (if dotB n x y = true then 1 else 0) + (if x.testBit n then 1 else 0) * (if y.testBit n then 1 else 0)
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    by_cases hA : dotB n x y
    · by_cases hx : x.testBit n
      · by_cases hy : y.testBit n
        · simp [hA, hx, hy, h11]
        · simp [hA, hx, hy]
      · simp [hA, hx]
    · by_cases hx : x.testBit n
      · by_cases hy : y.testBit n
        · simp [hA, hx, hy]
        · simp [hA, hx, hy]
      · simp [hA, hx]

/-- A product with exponents read off a bitmask is the product over the set bits. -/
theorem prod_pow_bitv {G : Type*} [CommMonoid G] {r : ℕ} (b : Fin r → G) (c : ℕ) :
    ∏ i, b i ^ (bitv r c i).val = ∏ i ∈ univ.filter (fun i : Fin r => c.testBit i), b i := by
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp [bitv]
  split_ifs with h
  · simp [ZMod.val_one, pow_one]
  · simp [ZMod.val_zero, pow_zero]

/-! ## The abstract echelon lemma -/

/-- Abstract echelon independence. Rows `i : Fin r` carry digits `dig i p : ZMod 2` at positions
`p` and admissibility flags `adm i p`; row `i` has a pivot position `piv i` where it is admissible
with digit `1`, and every later row is admissible there with digit `0`. If at every position the
digits of the admissible rows of any `IsSq` combination sum to `0`, no nonzero combination is `IsSq`. -/
theorem sb_echelon {r : ℕ} {P : Type*} (dig : Fin r → P → ZMod 2) (adm : Fin r → P → Bool)
    (piv : Fin r → P) (IsSq : (Fin r → ZMod 2) → Prop)
    (htest : ∀ (p : P) (ε : Fin r → ZMod 2), (∀ i, ε i = 1 → adm i p = true) → IsSq ε →
      ∑ i, ε i * dig i p = 0)
    (hech : ∀ i : Fin r, adm i (piv i) = true ∧ dig i (piv i) = 1 ∧
      ∀ i' : Fin r, i < i' → adm i' (piv i) = true ∧ dig i' (piv i) = 0)
    (ε : Fin r → ZMod 2) (hε : ε ≠ 0) : ¬ IsSq ε := by
  -- In ZMod 2, the only values are 0 and 1
  have hzmod2_ne_zero : ∀ (x : ZMod 2), x ≠ 0 → x = 1 := by
    intro x hx
    have h_cases : x = 0 ∨ x = 1 := by revert x; decide
    rcases h_cases with (h | h)
    · contradiction
    · exact h
  have hzmod2_ne_one : ∀ (x : ZMod 2), x ≠ 1 → x = 0 := by
    intro x hx
    have h_cases : x = 0 ∨ x = 1 := by revert x; decide
    rcases h_cases with (h | h)
    · exact h
    · contradiction
  -- Since ε ≠ 0, there exists i with ε i ≠ 0
  have h_exists : ∃ i : Fin r, ε i ≠ 0 := by
    contrapose! hε
    ext i
    exact hε i
  -- Let s be the set of indices where ε i = 1
  let s := Finset.filter (λ i => ε i = 1) Finset.univ
  have hs_nonempty : s.Nonempty := by
    rcases h_exists with ⟨i, hi⟩
    have hi1 : ε i = 1 := hzmod2_ne_zero (ε i) hi
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi1⟩⟩
  -- Let i0 be the minimal such index
  let i0 := s.min' hs_nonempty
  have hi0_mem : i0 ∈ s := Finset.min'_mem s hs_nonempty
  have hi0_eq_one : ε i0 = 1 := (Finset.mem_filter.mp hi0_mem).2
  have h_minimal : ∀ i, ε i = 1 → i0 ≤ i := by
    intro i hi
    have hi_mem_s : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    exact Finset.min'_le _ _ hi_mem_s
  have h_lt_min : ∀ i, i < i0 → ε i = 0 := by
    intro i hi_lt
    have h_not_one : ε i ≠ 1 := by
      intro h_eq_one
      have h_le := h_minimal i h_eq_one
      exact not_lt.mpr h_le hi_lt
    exact hzmod2_ne_one (ε i) h_not_one
  -- Let p = piv i0 and extract properties from hech
  let p := piv i0
  have hp_adm : adm i0 p = true := (hech i0).1
  have hp_dig : dig i0 p = 1 := (hech i0).2.1
  have hp_adm' : ∀ i', i0 < i' → adm i' p = true := by
    intro i' hi'
    exact ((hech i0).2.2 i' hi').1
  have hp_dig' : ∀ i', i0 < i' → dig i' p = 0 := by
    intro i' hi'
    exact ((hech i0).2.2 i' hi').2
  -- Assume IsSq ε and derive a contradiction
  intro h_sq
  have h_adm_all : ∀ i, ε i = 1 → adm i p = true := by
    intro i hi
    by_cases h_eq : i = i0
    · subst h_eq; exact hp_adm
    · have h_lt : i0 < i := by
        have h_le : i0 ≤ i := h_minimal i hi
        exact Ne.lt_of_le (Ne.symm h_eq) h_le
      exact hp_adm' i h_lt
  have hsum_zero : (∑ i : Fin r, ε i * dig i p) = 0 :=
    htest p ε h_adm_all h_sq
  have hsum_one : (∑ i : Fin r, ε i * dig i p) = 1 := by
    refine (Finset.sum_eq_single i0 (s := Finset.univ) (f := λ i => ε i * dig i p) ?_ ?_).trans ?_
    · intro b _ hb_ne
      by_cases hb_lt : b < i0
      · rw [h_lt_min b hb_lt]; simp
      · have h_lt : i0 < b := by
          have h_le : i0 ≤ b := not_lt.mp hb_lt
          exact Ne.lt_of_le (Ne.symm hb_ne) h_le
        rw [hp_dig' b h_lt]; simp
    · intro h; exfalso; exact h (Finset.mem_univ i0)
    · rw [hi0_eq_one, hp_dig]; simp
  rw [hsum_one] at hsum_zero
  -- 1 ≠ 0 in ZMod 2
  have h_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide
  exact h_one_ne_zero hsum_zero

/-- The pivot condition of `sb_echelon` as a Boolean check on `ℕ` indices. -/
def echelonOK {P : Type*} (adm dig : ℕ → P → Bool) (piv : ℕ → P) (r : ℕ) : Bool :=
  allLt (fun i => adm i (piv i) && dig i (piv i) &&
    allLt (fun i' => decide (i' ≤ i) || (adm i' (piv i) && !dig i' (piv i))) r) r

/-- **Echelon independence.** If every position passes its test and `echelonOK` holds, the family
`b` is independent modulo squares. -/
theorem sb_indep_of_echelonOK {G : Type*} [CommGroup G] {r : ℕ} (b : Fin r → G) {P : Type*}
    (adm dig : ℕ → P → Bool) (piv : ℕ → P)
    (htest : ∀ (p : P) (ε : Fin r → ZMod 2), (∀ i : Fin r, ε i = 1 → adm i p = true) →
      IsSquare (∏ i, b i ^ (ε i).val) → ∑ i : Fin r, ε i * (if dig i p then 1 else 0) = 0)
    (hech : echelonOK adm dig piv r = true)
    (ε : Fin r → ZMod 2) (hsq : IsSquare (∏ i, b i ^ (ε i).val)) : ε = 0 := by
  by_contra hε
  have h_all_iff := (allLt_iff (fun i : ℕ => adm i (piv i) && dig i (piv i) &&
    allLt (fun i' : ℕ => decide (i' ≤ i) || (adm i' (piv i) && !dig i' (piv i))) r) r).mp hech
  have htest' : ∀ (p : P) (ε' : Fin r → ZMod 2), (∀ i : Fin r, ε' i = 1 → adm (i.val) p = true) →
      IsSquare (∏ i, b i ^ (ε' i).val) → ∑ i : Fin r, ε' i * (if dig (i.val) p then (1 : ZMod 2) else (0 : ZMod 2)) = 0 := by
    intro p ε' h_adm h_sq
    simpa using htest p ε' h_adm h_sq
  have hech' : ∀ i : Fin r, adm (i.val) (piv (i.val)) = true ∧ (if dig (i.val) (piv (i.val)) then (1 : ZMod 2) else (0 : ZMod 2)) = 1 ∧
      ∀ i' : Fin r, i < i' → adm (i'.val) (piv (i.val)) = true ∧ (if dig (i'.val) (piv (i.val)) then (1 : ZMod 2) else (0 : ZMod 2)) = 0 := by
    intro i
    have hi_val_lt_r : (i.val : ℕ) < r := i.is_lt
    have h_i := h_all_iff (i.val) hi_val_lt_r
    rw [Bool.and_eq_true] at h_i
    rcases h_i with ⟨h_i12, h_alllt⟩
    rw [Bool.and_eq_true] at h_i12
    rcases h_i12 with ⟨h_adm_i, h_dig_i⟩
    have h_alllt_iff := (allLt_iff (fun i' : ℕ => decide (i' ≤ (i.val : ℕ)) || (adm i' (piv (i.val)) && !dig i' (piv (i.val)))) r).mp h_alllt
    refine ⟨h_adm_i, ?_, ?_⟩
    · simp [h_dig_i]
    · intro i' hi_lt'
      have hi'_val_lt_r : (i'.val : ℕ) < r := i'.is_lt
      have h_i' := h_alllt_iff (i'.val) hi'_val_lt_r
      have h_not_le : ¬ (i'.val ≤ (i.val : ℕ)) := Nat.not_le.mpr hi_lt'
      simp [h_not_le] at h_i'
      rcases h_i' with ⟨h_adm_i', h_dig_i'⟩
      refine ⟨h_adm_i', ?_⟩
      simp [h_dig_i']
  have h := sb_echelon (dig := fun (i : Fin r) (p : P) => if dig (i.val) p then (1 : ZMod 2) else (0 : ZMod 2))
    (adm := fun (i : Fin r) (p : P) => adm (i.val) p)
    (piv := fun (i : Fin r) => piv (i.val))
    (IsSq := fun (ε' : Fin r → ZMod 2) => IsSquare (∏ i, b i ^ (ε' i).val))
    (htest := htest') (hech := hech') (ε := ε) (hε := hε)
  exact h hsq

/-! ## Component data -/

/-- The shape of a component field: `e` with `‖2‖ = ‖π‖ ^ e` (`0` in odd residue characteristic),
`f` residue digits, the trace bitmask `τ` (bit `l` = trace of the residue of `w l`), and `N` with
`2 N + 1` the residue field cardinality in odd residue characteristic. -/
structure CShape where
  e : ℕ
  f : ℕ
  τ : ℕ
  N : ℕ

/-- The unit datum of an element `x` at a component, next to its valuation exponent. -/
inductive UDatum
  /-- Only the valuation is certified. -/
  | none
  /-- `x / s² = 1 + π ^ t · (lift of the digit bitset c) + (norm < ‖π‖ ^ t)`, `t` odd `< 2e`. -/
  | odd (t c : ℕ)
  /-- `x / s² = 1 + 4 · (lift of the digit bitset c) + (norm < ‖4‖)`. -/
  | four (c : ℕ)
  /-- Odd residue characteristic: `(x / s²) ^ N ≡ (-1) ^ b`. -/
  | chr (b : Bool)
  deriving DecidableEq

/-- Test positions at a component. -/
inductive CPos
  | val
  | odd (t l : ℕ)
  | four
  | chr
  deriving DecidableEq

/-- Admissibility of a unit datum at a position. -/
def admB (Q : CShape) (u : UDatum) : CPos → Bool
  | .val => true
  | .odd t l => decide (t % 2 = 1) && decide (t < 2 * Q.e) && decide (l < Q.f) &&
      match u with
      | .odd t' _ => decide (t ≤ t')
      | .four _ => true
      | _ => false
  | .four => decide (0 < Q.e) && match u with
      | .four _ => true
      | _ => false
  | .chr => decide (Q.e = 0) && match u with
      | .chr _ => true
      | _ => false

/-- The digit of a datum (valuation exponent `k`, unit datum `u`) at a position. -/
def digB (Q : CShape) (k : ℤ) (u : UDatum) : CPos → Bool
  | .val => decide (k % 2 = 1)
  | .odd t l => match u with
      | .odd t' c => decide (t = t') && c.testBit l
      | _ => false
  | .four => match u with
      | .four c => dotB Q.f c Q.τ
      | _ => false
  | .chr => match u with
      | .chr b => b
      | _ => false

/-- The lift `∑ l, c_l w l` of a digit bitset `c`. -/
def liftW {F : Type*} [NormedField F] {f : ℕ} (w : Fin f → F) (c : ℕ) : F :=
  ∑ l, ((bitv f c l).val : F) * w l

/-- The analytic content of a datum of `x` (with adjusting element `s`) at a component. -/
def DFact {F : Type*} [NormedField F] (Q : CShape) (π : F) (w : Fin Q.f → F) (x s : F) (k : ℤ) :
    UDatum → Prop
  | .none => ‖x‖ = ‖π‖ ^ k
  | .odd t c => ‖x‖ = ‖π‖ ^ k ∧ ‖x / s ^ 2 - 1 - π ^ t * liftW w c‖ < ‖π‖ ^ t
  | .four c => ‖x‖ = ‖π‖ ^ k ∧ ‖x / s ^ 2 - 1 - 4 * liftW w c‖ < ‖(4 : F)‖
  | .chr b => ‖x‖ = ‖π‖ ^ k ∧ ‖x / s ^ 2‖ = 1 ∧
      ‖(x / s ^ 2) ^ Q.N - (-1) ^ (if b then 1 else 0)‖ < 1

/-- The facts about a component field used by its tests. -/
structure CompOK {F : Type*} [NormedField F] (Q : CShape) (π : F) (w : Fin Q.f → F) : Prop where
  unif : NormUnif π
  two : ‖(2 : F)‖ = ‖π‖ ^ Q.e
  lift_le : ∀ l, ‖w l‖ ≤ 1
  lift_ind : ∀ C : Fin Q.f → ZMod 2, C ≠ 0 → ‖∑ l, ((C l).val : F) * w l‖ = 1
  trace : 0 < Q.e → ∀ (y : F) (C : Fin Q.f → ZMod 2), ‖y‖ ≤ 1 →
    ‖y ^ 2 + y - ∑ l, ((C l).val : F) * w l‖ < 1 → ∑ l, C l * bitv Q.f Q.τ l = 0
  fermat : Q.e = 0 → ∀ ξ : F, ‖ξ‖ = 1 → ‖ξ ^ (2 * Q.N) - 1‖ < 1

theorem ech_zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem norm_liftW_le {F : Type*} [NormedField F] [IsUltrametricDist F] {f : ℕ} (w : Fin f → F)
    (hw : ∀ l, ‖w l‖ ≤ 1) (c : ℕ) : ‖liftW w c‖ ≤ 1 := by
  unfold liftW
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l _ => ?_
  rw [norm_mul]
  calc _ ≤ 1 * 1 := mul_le_mul (IsUltrametricDist.norm_natCast_le_one F _) (hw l) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **All tests of one component.** For `b : Fin r → G` read in the component `F` through `φ`, with
a datum per row whose `DFact` holds, every position of the component passes its test. -/
theorem comp_test {G : Type*} [CommGroup G] {r : ℕ} (b : Fin r → G) {F : Type*} [NormedField F]
    [IsUltrametricDist F] (φ : G →* Fˣ) (Q : CShape) {π : F} {w : Fin Q.f → F}
    (hQ : CompOK Q π w) (s : Fin r → F) (k : Fin r → ℤ) (u : Fin r → UDatum)
    (hfact : ∀ i, DFact Q π w ((φ (b i) : Fˣ) : F) (s i) (k i) (u i))
    (p : CPos) (ε : Fin r → ZMod 2) (hadm : ∀ i, ε i = 1 → admB Q (u i) p = true)
    (hsq : IsSquare (∏ i, b i ^ (ε i).val)) :
    ∑ i, ε i * (if digB Q (k i) (u i) p then 1 else 0) = 0 := by
  classical
  set x : Fin r → F := fun i => ((φ (b i) : Fˣ) : F) with hxdef
  have hπ0 := hQ.unif.ne_zero
  have hπ1 := hQ.unif.norm_lt_one
  have hx_norm : ∀ i, ‖x i‖ = ‖π‖ ^ k i := fun i => by
    have h := hfact i
    cases hu : u i <;> rw [hu] at h
    · exact h
    all_goals exact h.1
  set S := univ.filter (fun i => ε i = 1) with hS
  have hsqS : IsSquare (∏ i ∈ S, x i) := by
    have h1 : IsSquare (∏ i, x i ^ (ε i).val) := by
      obtain ⟨y, hy⟩ := hsq
      refine ⟨((φ y : Fˣ) : F), ?_⟩
      have := congrArg (fun g => ((φ g : Fˣ) : F)) hy
      simpa [hxdef, map_prod, map_pow, Units.coe_prod] using this
    have h2 : ∏ i, x i ^ (ε i).val = ∏ i ∈ S, x i := by
      rw [hS, prod_filter]
      refine prod_congr rfl fun i _ => ?_
      rcases ech_zmod2_cases (ε i) with h | h <;> simp [h, show (1 : ZMod 2).val = 1 from rfl]
    rwa [h2] at h1
  have hsum : ∑ i, ε i * (if digB Q (k i) (u i) p then 1 else 0) =
      ∑ i ∈ S, (if digB Q (k i) (u i) p then (1 : ZMod 2) else 0) := by
    rw [hS, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    rcases ech_zmod2_cases (ε i) with h | h <;> simp [h]
  rw [hsum]
  have hadmS : ∀ i ∈ S, admB Q (u i) p = true := fun i hi => hadm i (mem_filter.mp hi).2
  rcases S.eq_empty_or_nonempty with hS0 | ⟨i0, hi0⟩
  · rw [hS0, sum_empty]
  cases p with
  | val =>
    have hd : ∀ i, (if digB Q (k i) (u i) .val then (1 : ZMod 2) else 0) = (k i : ZMod 2) := by
      intro i
      simp only [digB]
      rw [← ZMod.intCast_mod (k i) 2]
      rcases Int.emod_two_eq_zero_or_one (k i) with h | h <;> simp [h]
    simp only [hd]
    exact sb_test_val hπ0 hπ1 hQ.unif.disc S x k (fun i _ => hx_norm i) hsqS
  | odd t l =>
    have h0 := hadmS i0 hi0
    simp only [admB, Bool.and_eq_true, decide_eq_true_eq] at h0
    obtain ⟨⟨⟨ht, hte⟩, hl⟩, -⟩ := h0
    let V : Fin r → Fin Q.f → ZMod 2 := fun i =>
      match u i with
      | .odd t' c => if t = t' then bitv Q.f c else 0
      | _ => 0
    have h4 : ‖(4 : F)‖ < ‖π‖ ^ t := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this, norm_mul, hQ.two, ← pow_add]
      exact pow_lt_pow_right_of_lt_one₀ (norm_pos_iff.mpr hπ0) hπ1 (by omega)
    have hx : ∀ i ∈ S, ‖x i / s i ^ 2 - 1 - π ^ t * ∑ l, ((V i l).val : F) * w l‖ < ‖π‖ ^ t := by
      intro i hi
      have ha := hadmS i hi
      have hf := hfact i
      cases hu : u i with
      | none => simp [admB, hu] at ha
      | chr b => simp [admB, hu] at ha
      | odd t' c =>
        simp only [admB, hu, Bool.and_eq_true, decide_eq_true_eq] at ha
        rw [hu] at hf
        rcases (ha.2).lt_or_eq with htt | htt
        · have hV : V i = 0 := by simp [V, hu, htt.ne]
          rw [hV]
          simpa using sb_depth_mono hπ1 htt (norm_liftW_le w hQ.lift_le c) hf.2
        · subst htt
          have hV : V i = bitv Q.f c := by simp [V, hu]
          rw [hV]
          exact hf.2
      | four c =>
        rw [hu] at hf
        have hV : V i = 0 := by simp [V, hu]
        rw [hV]
        simpa using sb_depth_four h4 (norm_liftW_le w hQ.lift_le c) hf.2
    have hV0 := sb_test_odd hπ0 hπ1 hQ.unif.disc hQ.two (Nat.odd_iff.mpr ht) hte w hQ.lift_le
      hQ.lift_ind S x s V hx hsqS
    have hcoord := congrFun hV0 ⟨l, hl⟩
    rw [Finset.sum_apply, Pi.zero_apply] at hcoord
    refine (sum_congr rfl fun i _ => ?_).trans hcoord
    simp only [V, digB]
    cases u i with
    | odd t' c =>
      by_cases h : t = t' <;> simp [h, bitv]
    | _ => simp
  | four =>
    have h0 := hadmS i0 hi0
    simp only [admB, Bool.and_eq_true, decide_eq_true_eq] at h0
    have he := h0.1
    have h2pos : 0 < ‖(2 : F)‖ := by rw [hQ.two]; exact pow_pos (norm_pos_iff.mpr hπ0) _
    have h21 : ‖(2 : F)‖ < 1 := by rw [hQ.two]; exact pow_lt_one₀ (norm_nonneg _) hπ1 he.ne'
    let V : Fin r → Fin Q.f → ZMod 2 := fun i =>
      match u i with
      | .four c => bitv Q.f c
      | _ => 0
    have hfour : ∀ i ∈ S, ∃ c, u i = .four c := by
      intro i hi
      have ha := hadmS i hi
      cases hu : u i with
      | four c => exact ⟨c, rfl⟩
      | _ => simp [admB, hu] at ha
    have hx : ∀ i ∈ S, ‖x i / s i ^ 2 - 1 - 4 * ∑ l, ((V i l).val : F) * w l‖ < ‖(4 : F)‖ := by
      intro i hi
      obtain ⟨c, hc⟩ := hfour i hi
      have hf := hfact i
      rw [hc] at hf
      have hV : V i = bitv Q.f c := by simp [V, hc]
      rw [hV]
      exact hf.2
    have hT := sb_test_four (norm_pos_iff.mp h2pos) h21 w hQ.lift_le (bitv Q.f Q.τ) (hQ.trace he)
      S x s V hx hsqS
    refine (sum_congr rfl fun i hi => ?_).trans hT
    obtain ⟨c, hc⟩ := hfour i hi
    simp only [digB, hc, V]
    exact dotB_eq Q.f c Q.τ
  | chr =>
    have h0 := hadmS i0 hi0
    simp only [admB, Bool.and_eq_true, decide_eq_true_eq] at h0
    have he := h0.1
    have h2 : ‖(2 : F)‖ = 1 := by rw [hQ.two, he, pow_zero]
    have hchr : ∀ i ∈ S, ∃ bb, u i = .chr bb := by
      intro i hi
      have ha := hadmS i hi
      cases hu : u i with
      | chr bb => exact ⟨bb, rfl⟩
      | _ => simp [admB, hu] at ha
    let c : Fin r → ZMod 2 := fun i =>
      match u i with
      | .chr bb => if bb then 1 else 0
      | _ => 0
    have hx1 : ∀ i ∈ S, ‖x i / s i ^ 2‖ = 1 := by
      intro i hi
      obtain ⟨bb, hb⟩ := hchr i hi
      have hf := hfact i
      rw [hb] at hf
      exact hf.2.1
    have hx : ∀ i ∈ S, ‖(x i / s i ^ 2) ^ Q.N - (-1) ^ (c i).val‖ < 1 := by
      intro i hi
      obtain ⟨bb, hb⟩ := hchr i hi
      have hf := hfact i
      rw [hb] at hf
      have hc : (c i).val = if bb then 1 else 0 := by
        simp only [c, hb]
        cases bb <;> rfl
      rw [hc]
      exact hf.2.2
    have hT := sb_test_chr h2 (hQ.fermat he) S x s c hx1 hx hsqS
    refine (sum_congr rfl fun i hi => ?_).trans hT
    obtain ⟨bb, hb⟩ := hchr i hi
    simp only [digB, hb, c]


/-! ## Coordinates modulo squares -/

section SqQuot

variable {G : Type*} [CommGroup G]

/-- `G` modulo squares. -/
abbrev SqQ (G : Type*) [CommGroup G] := G ⧸ (powMonoidHom 2 : G →* G).range

theorem sqQ_sq (x : SqQ G) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨g, rfl⟩

theorem sqQ_mk_eq_one_iff (x : G) : ((x : SqQ G)) = 1 ↔ IsSquare x := by
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp [sq]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp [sq]⟩

theorem sqQ_inv (x : SqQ G) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, sqQ_sq])

theorem sqQ_pow_mod_two (x : SqQ G) (k : ℕ) : x ^ (k % 2) = x ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k 2, pow_add, pow_mul, sqQ_sq, one_pow, mul_one]

theorem sqQ_pow_val_add (x : SqQ G) (a c : ZMod 2) : x ^ (a + c).val = x ^ a.val * x ^ c.val := by
  rw [ZMod.val_add, sqQ_pow_mod_two, pow_add]

/-- The class of `∏ b i ^ v i` modulo squares. -/
noncomputable def sqPsi {r : ℕ} (b : Fin r → G) (v : Fin r → ZMod 2) : SqQ G :=
  ∏ i, ((b i : SqQ G)) ^ (v i).val

variable {r : ℕ} (b : Fin r → G)

theorem sqPsi_zero : sqPsi b 0 = 1 := by
  simp [sqPsi]

theorem sqPsi_add (v w : Fin r → ZMod 2) : sqPsi b (v + w) = sqPsi b v * sqPsi b w := by
  simp only [sqPsi, Pi.add_apply, sqQ_pow_val_add, prod_mul_distrib]

theorem sqPsi_smul (c : ZMod 2) (v : Fin r → ZMod 2) : sqPsi b (c • v) = sqPsi b v ^ c.val := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · rw [zero_smul, sqPsi_zero, ZMod.val_zero, pow_zero]
  · rw [one_smul, ZMod.val_one, pow_one]

theorem sqPsi_sum {ι : Type*} (S : Finset ι) (w : ι → Fin r → ZMod 2) :
    sqPsi b (∑ s ∈ S, w s) = ∏ s ∈ S, sqPsi b (w s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sqPsi_zero]
  | insert a S ha ih => rw [sum_insert ha, prod_insert ha, sqPsi_add, ih]

theorem sqQ_mk_prod_pow (v : Fin r → ZMod 2) :
    ((∏ i, b i ^ (v i).val : G) : SqQ G) = sqPsi b v := by
  simp [sqPsi, QuotientGroup.mk_prod, QuotientGroup.mk_pow]

theorem sqPsi_eq_one_iff (hind : ∀ ε : Fin r → ZMod 2, IsSquare (∏ i, b i ^ (ε i).val) → ε = 0)
    (v : Fin r → ZMod 2) : sqPsi b v = 1 ↔ v = 0 := by
  constructor
  · intro h
    exact hind v ((sqQ_mk_eq_one_iff _).1 (by rw [sqQ_mk_prod_pow, h]))
  · rintro rfl
    exact sqPsi_zero b

theorem sqPsi_inj (hind : ∀ ε : Fin r → ZMod 2, IsSquare (∏ i, b i ^ (ε i).val) → ε = 0)
    {v w : Fin r → ZMod 2} (h : sqPsi b v = sqPsi b w) : v = w := by
  have h1 : sqPsi b (v - w) = 1 := by
    have h2 : sqPsi b v = sqPsi b w * sqPsi b (v - w) := by
      rw [← sqPsi_add, add_sub_cancel]
    rw [h] at h2
    exact (mul_eq_left.1 h2.symm)
  exact sub_eq_zero.1 ((sqPsi_eq_one_iff b hind _).1 h1)

theorem sqQ_mk_of_coord {t : G} {A : Fin r → ZMod 2} (hA : IsSquare (t * ∏ i, b i ^ (A i).val)) :
    ((t : SqQ G)) = sqPsi b A := by
  have h := (sqQ_mk_eq_one_iff _).2 hA
  rw [QuotientGroup.mk_mul, sqQ_mk_prod_pow] at h
  rw [eq_inv_of_mul_eq_one_left h, sqQ_inv]

theorem sqQ_mk_prod_coord {n : ℕ} (t : Fin n → G) (A : Fin n → Fin r → ZMod 2)
    (hA : ∀ s, IsSquare (t s * ∏ i, b i ^ (A s i).val)) (c : Fin n → ZMod 2) :
    ((∏ s, t s ^ (c s).val : G) : SqQ G) = sqPsi b (∑ s, c s • A s) := by
  rw [sqPsi_sum, QuotientGroup.mk_prod]
  refine prod_congr rfl fun s _ => ?_
  rw [QuotientGroup.mk_pow, sqQ_mk_of_coord b (hA s), sqPsi_smul]

end SqQuot

/-- Coordinates modulo squares. If `b` is independent modulo squares in a commutative group and
each `e k` times `∏ b i ^ a k i` is a square, then a product `∏ e k ^ η k` is a square exactly
when `∑ η k • a k = 0` over `ZMod 2`. -/
theorem sb_coord {G : Type*} [CommGroup G] {r m : ℕ} (b : Fin r → G)
    (hind : ∀ ε : Fin r → ZMod 2, IsSquare (∏ i, b i ^ (ε i).val) → ε = 0)
    (e : Fin m → G) (a : Fin m → Fin r → ZMod 2)
    (ha : ∀ k, IsSquare (e k * ∏ i, b i ^ (a k i).val))
    (η : Fin m → ZMod 2) :
    IsSquare (∏ k, e k ^ (η k).val) ↔ ∑ k, η k • a k = 0 := by
  rw [← sqQ_mk_eq_one_iff, sqQ_mk_prod_coord b e a ha, sqPsi_eq_one_iff b hind]

/-- **Membership as a linear condition.** With `b` independent modulo squares, `κ` spanning the
subgroup `K` modulo squares, and coordinates `Aκ`, `Aμ`, `C` of `κ`, `μ`, `g` on `b`: the product
`∏ g s ^ a s` lies in `K · ⟨μ⟩ · G²` exactly when `∑ a s • C s` lies in the span of the coordinates of
the `κ` and the `μ`. -/
theorem sb_mem_iff {G : Type*} [CommGroup G] {r : ℕ} (b : Fin r → G)
    (hind : ∀ ε : Fin r → ZMod 2, IsSquare (∏ i, b i ^ (ε i).val) → ε = 0)
    (K : Subgroup G) {mκ : ℕ} (κ : Fin mκ → G) (hκK : ∀ l, κ l ∈ K)
    (hK : ∀ x ∈ K, ∃ c : Fin mκ → ZMod 2, IsSquare (x * ∏ l, κ l ^ (c l).val))
    (Aκ : Fin mκ → Fin r → ZMod 2) (hAκ : ∀ l, IsSquare (κ l * ∏ i, b i ^ (Aκ l i).val))
    {mμ : ℕ} (μ : Fin mμ → G) (Aμ : Fin mμ → Fin r → ZMod 2)
    (hAμ : ∀ l, IsSquare (μ l * ∏ i, b i ^ (Aμ l i).val))
    {n : ℕ} (g : Fin n → G) (C : Fin n → Fin r → ZMod 2)
    (hC : ∀ s, IsSquare (g s * ∏ i, b i ^ (C s i).val)) (a : Fin n → ZMod 2) :
    ∏ s, g s ^ (a s).val ∈ K ⊔ Subgroup.closure (Set.range μ) ⊔ (powMonoidHom 2 : G →* G).range ↔
      ∑ s, a s • C s ∈
        Submodule.span (ZMod 2) (Set.range Aκ) ⊔ Submodule.span (ZMod 2) (Set.range Aμ) := by
  have hg := sqQ_mk_prod_coord b g C hC a
  constructor
  · intro hx
    obtain ⟨yz, hyz, w, hw, hx⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨y, hy, z, hz, hyzeq⟩ := Subgroup.mem_sup.1 hyz
    -- the class of `y`
    obtain ⟨c, hc⟩ := hK y hy
    have hyq : ((y : SqQ G)) = sqPsi b (∑ l, c l • Aκ l) := by
      have h := (sqQ_mk_eq_one_iff _).2 hc
      rw [QuotientGroup.mk_mul, sqQ_mk_prod_coord b κ Aκ hAκ c] at h
      rw [eq_inv_of_mul_eq_one_left h, sqQ_inv]
    -- the class of `z`
    have hzq : ∀ z' ∈ Subgroup.closure (Set.range μ),
        ∃ v ∈ Submodule.span (ZMod 2) (Set.range Aμ), ((z' : SqQ G)) = sqPsi b v := by
      intro z' hz'
      induction hz' using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        exact ⟨Aμ l, Submodule.subset_span ⟨l, rfl⟩, sqQ_mk_of_coord b (hAμ l)⟩
      | one => exact ⟨0, Submodule.zero_mem _, by rw [QuotientGroup.mk_one, sqPsi_zero]⟩
      | mul x x' _ _ hx hx' =>
        obtain ⟨v, hv, hvq⟩ := hx
        obtain ⟨v', hv', hvq'⟩ := hx'
        exact ⟨v + v', Submodule.add_mem _ hv hv', by rw [QuotientGroup.mk_mul, hvq, hvq', sqPsi_add]⟩
      | inv x _ hx =>
        obtain ⟨v, hv, hvq⟩ := hx
        exact ⟨v, hv, by rw [QuotientGroup.mk_inv, hvq, sqQ_inv]⟩
    obtain ⟨v, hv, hvq⟩ := hzq z hz
    have hwq : ((w : SqQ G)) = 1 := by
      obtain ⟨w', rfl⟩ := hw
      exact (QuotientGroup.eq_one_iff _).2 ⟨w', rfl⟩
    have heq : sqPsi b (∑ s, a s • C s) = sqPsi b ((∑ l, c l • Aκ l) + v) := by
      rw [← hg, ← hx, ← hyzeq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hyq, hvq, hwq, mul_one, sqPsi_add]
    rw [sqPsi_inj b hind heq]
    refine Submodule.add_mem_sup ?_ hv
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hu
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hv
    set y := ∏ l, κ l ^ (c l).val
    set z := ∏ l, μ l ^ (d l).val
    have hy : y ∈ K := Subgroup.prod_mem _ fun l _ => Subgroup.pow_mem _ (hκK l) _
    have hz : z ∈ Subgroup.closure (Set.range μ) :=
      Subgroup.prod_mem _ fun l _ => Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self l)) _
    have hq : ((∏ s, g s ^ (a s).val : G) : SqQ G) = ((y * z : G) : SqQ G) := by
      rw [hg, ← huv, sqPsi_add, QuotientGroup.mk_mul, sqQ_mk_prod_coord b κ Aκ hAκ c,
        sqQ_mk_prod_coord b μ Aμ hAμ d]
    have hsq : (∏ s, g s ^ (a s).val) * (y * z)⁻¹ ∈ (powMonoidHom 2 : G →* G).range := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hq, mul_inv_cancel]
    have := Subgroup.mul_mem_sup (Subgroup.mul_mem_sup hy hz) hsq
    rwa [mul_comm (∏ s, g s ^ (a s).val), mul_inv_cancel_left] at this

/-! ## F₂ certificates on bitmasks -/

/-- Left inverse certificate: `xorSel R m (T k) = 2 ^ k` for `k < n` (rows `R` of `n` bits). -/
def leftInvOK (R : ℕ → ℕ) (m n : ℕ) (T : ℕ → ℕ) : Bool :=
  allLt (fun k => xorSel R m (T k) == 2 ^ k) n

lemma bitv_two_pow_eq_ite (n k : ℕ) (j : Fin n) : bitv n (2 ^ k) j = if (k : ℕ) = (j : ℕ) then 1 else 0 := by
  dsimp [bitv]
  have h := Nat.testBit_two_pow (n := k) (m := j)
  -- h : (2 ^ k).testBit (j : ℕ) = decide (k = (j : ℕ))
  rw [h]
  simp

lemma sum_bitv_two_pow_mul (n : ℕ) (a : Fin n → ZMod 2) (k : Fin n) :
    ∑ j : Fin n, bitv n (2 ^ (k : ℕ)) j * a j = a k := by
  calc
    ∑ j : Fin n, bitv n (2 ^ (k : ℕ)) j * a j
        = ∑ j : Fin n, (if (k : ℕ) = (j : ℕ) then 1 else 0) * a j := by
          simp [bitv_two_pow_eq_ite]
    _ = ∑ j : Fin n, (if (k : ℕ) = (j : ℕ) then a j else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : (k : ℕ) = (j : ℕ)
      · simp [h]
      · simp [h]
    _ = a k := by
      simpa [Finset.mem_univ, Fin.ext_iff] using Finset.sum_ite_eq (Finset.univ : Finset (Fin n)) k a


/-- **Trivial kernel.** A passing `leftInvOK` makes the rows `R 0, …, R (m-1)` (as linear forms on
`Fin n → ZMod 2`) have trivial common kernel. -/
theorem eq_zero_of_leftInvOK {R : ℕ → ℕ} {m n : ℕ} {T : ℕ → ℕ} (h : leftInvOK R m n T = true)
    (a : Fin n → ZMod 2) (ha : ∀ i : Fin m, ∑ j, bitv n (R i) j * a j = 0) : a = 0 := by
  have h_allLt := (allLt_iff (fun k => xorSel R m (T k) == 2 ^ k) n).mp h
  ext k
  have hk_lt_n : (k : ℕ) < n := k.is_lt
  have h_eq_check := h_allLt (k : ℕ) hk_lt_n
  -- h_eq_check : (xorSel R m (T (k : ℕ)) == 2 ^ (k : ℕ)) = true
  have h_xor_eq : xorSel R m (T (k : ℕ)) = 2 ^ (k : ℕ) := by
    -- from beq_iff_eq
    have := (beq_iff_eq (a := xorSel R m (T (k : ℕ))) (b := 2 ^ (k : ℕ))).mp h_eq_check
    exact this
  calc
    a k = ∑ j : Fin n, bitv n (2 ^ (k : ℕ)) j * a j := by
      symm; exact sum_bitv_two_pow_mul n a k
    _ = ∑ j : Fin n, bitv n (xorSel R m (T (k : ℕ))) j * a j := by simp [h_xor_eq]
    _ = ∑ j : Fin n, (∑ i : Fin m, bitv m (T (k : ℕ)) i • bitv n (R i)) j * a j := by
      rw [bitv_xorSel]
    _ = ∑ j : Fin n, (∑ i : Fin m, (bitv m (T (k : ℕ)) i • bitv n (R i)) j) * a j := by
      simp [Finset.sum_apply]
    _ = ∑ j : Fin n, (∑ i : Fin m, bitv m (T (k : ℕ)) i * bitv n (R i) j) * a j := by
      simp
    _ = ∑ i : Fin m, bitv m (T (k : ℕ)) i * (∑ j : Fin n, bitv n (R i) j * a j) := by
      simp [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [Finset.mul_sum, mul_comm, mul_left_comm]
    _ = ∑ i : Fin m, bitv m (T (k : ℕ)) i * 0 := by simp [ha]
    _ = 0 := by simp

/-- The kernel vector of a free column `j` for pivot rows `Rp` with pivots `piv`:
`e_j + ∑_{k < q, bit j of Rp k} e_(piv k)`. -/
def freeVec (Rp : ℕ → ℕ) (piv : ℕ → ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 2 ^ j
  | q + 1 => if (Rp q).testBit j then freeVec Rp piv j q ^^^ 2 ^ piv q else freeVec Rp piv j q

/-- Kernel inside a span: `Rp k = xorSel M m (T k)` (`k < q`) are reduced on distinct pivot columns
`piv k < n`, and for every non pivot column `j < n` the kernel vector `freeVec` is the combination
`U j` of the rows `W`. -/
def kerSpanOK (M : ℕ → ℕ) (m n : ℕ) (T : ℕ → ℕ) (piv : ℕ → ℕ) (q : ℕ) (W : ℕ → ℕ) (nw : ℕ)
    (U : ℕ → ℕ) : Bool :=
  allLt (fun k => decide (piv k < n) &&
    allLt (fun k' => (xorSel M m (T k)).testBit (piv k') == (k == k')) q) q &&
  allLt (fun j => anyLt (fun k => piv k == j) q ||
    xorSel W nw (U j) == freeVec (fun k => xorSel M m (T k)) piv j q) n

theorem ech_bitv_freeVec (n : ℕ) (Rp piv : ℕ → ℕ) (j q : ℕ) :
    bitv n (freeVec Rp piv j q) = bitv n (2 ^ j) +
      ∑ k ∈ range q, if (Rp k).testBit j then bitv n (2 ^ piv k) else 0 := by
  induction q with
  | zero => simp [freeVec]
  | succ q ih =>
    rw [sum_range_succ, freeVec]
    split_ifs with hb
    · rw [bitv_xor, ih, add_assoc]
    · rw [ih, add_zero]

theorem ech_bitv_freeVec_apply (n : ℕ) (Rp piv : ℕ → ℕ) (j q : ℕ) (i : Fin n) :
    bitv n (freeVec Rp piv j q) i = (if j = (i : ℕ) then 1 else 0) +
      ∑ k ∈ range q, if (Rp k).testBit j ∧ piv k = (i : ℕ) then 1 else 0 := by
  rw [ech_bitv_freeVec, Pi.add_apply, Finset.sum_apply, bitv_two_pow_eq_ite]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  by_cases hb : (Rp k).testBit j
  · simp [hb, bitv_two_pow_eq_ite]
  · simp [hb]

/-- **Kernel inside a span.** A passing `kerSpanOK` puts every common zero of the rows `M` in the span
of the rows `W`. -/
theorem mem_span_of_kerSpanOK {M : ℕ → ℕ} {m n : ℕ} {T piv : ℕ → ℕ} {q : ℕ} {W : ℕ → ℕ} {nw : ℕ}
    {U : ℕ → ℕ} (h : kerSpanOK M m n T piv q W nw U = true) (a : Fin n → ZMod 2)
    (ha : ∀ i : Fin m, ∑ j, bitv n (M i) j * a j = 0) :
    a ∈ Submodule.span (ZMod 2) (Set.range fun l : Fin nw => bitv n (W l)) := by
  classical
  unfold kerSpanOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h

  have h1' := (allLt_iff _ _).mp h1
  have h2' := (allLt_iff _ _).mp h2
  have hpivn : ∀ k < q, piv k < n := by
    intro k hk
    have := h1' k hk
    rw [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  have hbit : ∀ k < q, ∀ k' < q, ((xorSel M m (T k)).testBit (piv k') = true ↔ k = k') := by
    intro k hk k' hk'
    have := h1' k hk
    rw [Bool.and_eq_true] at this
    have := (allLt_iff _ _).mp this.2 k' hk'
    simp only [beq_iff_eq] at this
    rw [this]
    exact beq_iff_eq
  have hdist : ∀ k < q, ∀ k' < q, piv k = piv k' → k = k' := by
    intro k hk k' hk' he
    have h0 := (hbit k hk k hk).mpr rfl
    rw [he] at h0
    exact (hbit k hk k' hk').mp h0
  have hfree : ∀ j < n, (∀ k < q, piv k ≠ j) →
      xorSel W nw (U j) = freeVec (fun k => xorSel M m (T k)) piv j q := by
    intro j hj hjf
    have := h2' j hj
    rw [Bool.or_eq_true] at this
    rcases this with h | h
    · obtain ⟨k, hk, hkj⟩ := (anyLt_iff _ _).mp h
      exact absurd (beq_iff_eq.mp hkj) (hjf k hk)
    · exact beq_iff_eq.mp h
  have hann : ∀ k < q, ∑ j : Fin n, bitv n (xorSel M m (T k)) j * a j = 0 := by
    intro k _
    simp only [bitv_xorSel, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ha i, mul_zero]
  set free : Finset (Fin n) := univ.filter (fun j => ∀ k < q, piv k ≠ (j : ℕ)) with hfreedef
  have hmemfree : ∀ j : Fin n, j ∈ free ↔ ∀ k < q, piv k ≠ (j : ℕ) := fun j => by
    simp [hfreedef]
  set v : Fin n → ZMod 2 :=
    ∑ j ∈ free, a j • bitv n (freeVec (fun k => xorSel M m (T k)) piv j q) with hvdef
  have hv : v ∈ Submodule.span (ZMod 2) (Set.range fun l : Fin nw => bitv n (W l)) := by
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    rw [← hfree j j.is_lt ((hmemfree j).mp hj), bitv_xorSel]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hz2 : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
  suffices hav : a = v by rw [hav]; exact hv
  funext i
  simp only [hvdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ech_bitv_freeVec_apply]
  by_cases hi : i ∈ free
  · have hsum0 : ∀ j ∈ free, a j * ((if (j : ℕ) = (i : ℕ) then (1 : ZMod 2) else 0) +
        ∑ k ∈ range q, if (xorSel M m (T k)).testBit j ∧ piv k = (i : ℕ) then (1 : ZMod 2) else 0) =
        if j = i then a j else 0 := by
      intro j _
      have h0 : (∑ k ∈ range q, if (xorSel M m (T k)).testBit j ∧ piv k = (i : ℕ) then
          (1 : ZMod 2) else 0) = 0 := by
        refine sum_eq_zero fun k hk => ite_eq_right ?_
        rintro ⟨-, hk'⟩
        exact (hmemfree i).mp hi k (mem_range.mp hk) hk'
      rw [h0, add_zero]
      by_cases hji : j = i
      · simp [hji]
      · have : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
        simp [hji, this]
    rw [sum_congr rfl hsum0, sum_ite_eq' free i a, ite_eq_left hi]
  · have hi' : ¬ ∀ k < q, piv k ≠ (i : ℕ) := fun h => hi ((hmemfree i).mpr h)
    push Not at hi'
    obtain ⟨k0, hk0, hk0i⟩ := hi'
    have hsum1 : ∀ j ∈ free, a j * ((if (j : ℕ) = (i : ℕ) then (1 : ZMod 2) else 0) +
        ∑ k ∈ range q, if (xorSel M m (T k)).testBit j ∧ piv k = (i : ℕ) then (1 : ZMod 2) else 0) =
        bitv n (xorSel M m (T k0)) j * a j := by
      intro j hj
      have hji : (j : ℕ) ≠ (i : ℕ) := fun h => (hmemfree j).mp hj k0 hk0 (hk0i.trans h.symm)
      rw [ite_eq_right hji, zero_add, mul_comm]
      congr 1
      rw [sum_eq_single k0]
      · simp [bitv, hk0i]
      · intro k hk hkk0
        rw [ite_eq_right]
        rintro ⟨-, hk'⟩
        exact hkk0 (hdist k (mem_range.mp hk) k0 hk0 (hk'.trans hk0i.symm))
      · intro h; exact absurd (mem_range.mpr hk0) h
    rw [sum_congr rfl hsum1]
    have hsplit := sum_add_sum_compl free (fun j => bitv n (xorSel M m (T k0)) j * a j)
    rw [hann k0 hk0] at hsplit
    have hcompl : ∑ j ∈ freeᶜ, bitv n (xorSel M m (T k0)) j * a j = a i := by
      rw [sum_eq_single i]
      · have : (xorSel M m (T k0)).testBit (i : ℕ) = true := by
          rw [← hk0i]; exact (hbit k0 hk0 k0 hk0).mpr rfl
        simp [bitv, this]
      · intro j hj hji
        rw [mem_compl, hmemfree] at hj
        push Not at hj
        obtain ⟨k', hk', hk'j⟩ := hj
        have hne : k0 ≠ k' := by
          rintro rfl
          exact hji (Fin.ext (hk'j.symm.trans hk0i))
        have : (xorSel M m (T k0)).testBit (j : ℕ) = false := by
          rw [← hk'j, Bool.eq_false_iff]
          exact fun h => hne ((hbit k0 hk0 k' hk').mp h)
        simp [bitv, this]
      · intro h; exact absurd (mem_compl.mpr hi) h
    rw [hcompl] at hsplit
    exact hz2 _ _ hsplit

/-- Annihilator certificate: every row `Q i` (`i < nQ`) is orthogonal to every generator `A l`
(`l < nA`), on `r` bits. -/
def annOK (r : ℕ) (A : ℕ → ℕ) (nA : ℕ) (Q : ℕ → ℕ) (nQ : ℕ) : Bool :=
  allLt (fun i => allLt (fun l => !dotB r (Q i) (A l)) nA) nQ

/-- **Annihilator.** If the rows `Q` annihilate the generators `A1` and `A2`, every vector of the
sum of their spans is a common zero of the rows `Q`. -/
theorem ann_of_mem_sup {r : ℕ} {A1 A2 : ℕ → ℕ} {n1 n2 : ℕ} {Q : ℕ → ℕ} {nQ : ℕ}
    (h1 : annOK r A1 n1 Q nQ = true) (h2 : annOK r A2 n2 Q nQ = true) {v : Fin r → ZMod 2}
    (hv : v ∈ Submodule.span (ZMod 2) (Set.range fun l : Fin n1 => bitv r (A1 l)) ⊔
      Submodule.span (ZMod 2) (Set.range fun l : Fin n2 => bitv r (A2 l)))
    (i : Fin nQ) : ∑ j, bitv r (Q i) j * v j = 0 := by
  let f : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun v => ∑ j : Fin r, bitv r (Q i) j * v j
      map_add' := by
        intro x y
        simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring }
  have hA1 : ∀ l : Fin n1, f (bitv r (A1 l)) = 0 := by
    intro l
    dsimp [f]
    have h_allLt := (allLt_iff (fun i => allLt (fun l' => !dotB r (Q i) (A1 l')) n1) nQ).mp h1
    have hi : i.1 < nQ := i.2
    have h_allLt_i := h_allLt i.1 hi
    have h_allLt' := (allLt_iff (fun l' => !dotB r (Q i.1) (A1 l')) n1).mp h_allLt_i
    have hl : l.1 < n1 := l.2
    have h_dotB_not : (!dotB r (Q i.1) (A1 l.1)) = true := h_allLt' l.1 hl
    have h_dotB_false : dotB r (Q i.1) (A1 l.1) = false := by
      cases hb : dotB r (Q i.1) (A1 l.1)
      · rfl
      · exfalso
        rw [hb] at h_dotB_not
        simp at h_dotB_not
    have h_dot_eq := dotB_eq r (Q i.1) (A1 l.1)
    rw [h_dotB_false] at h_dot_eq
    simp at h_dot_eq
    simpa using h_dot_eq.symm
  have hA2 : ∀ l : Fin n2, f (bitv r (A2 l)) = 0 := by
    intro l
    dsimp [f]
    have h_allLt := (allLt_iff (fun i => allLt (fun l' => !dotB r (Q i) (A2 l')) n2) nQ).mp h2
    have hi : i.1 < nQ := i.2
    have h_allLt_i := h_allLt i.1 hi
    have h_allLt' := (allLt_iff (fun l' => !dotB r (Q i.1) (A2 l')) n2).mp h_allLt_i
    have hl : l.1 < n2 := l.2
    have h_dotB_not : (!dotB r (Q i.1) (A2 l.1)) = true := h_allLt' l.1 hl
    have h_dotB_false : dotB r (Q i.1) (A2 l.1) = false := by
      cases hb : dotB r (Q i.1) (A2 l.1)
      · rfl
      · exfalso
        rw [hb] at h_dotB_not
        simp at h_dotB_not
    have h_dot_eq := dotB_eq r (Q i.1) (A2 l.1)
    rw [h_dotB_false] at h_dot_eq
    simp at h_dot_eq
    simpa using h_dot_eq.symm
  have h_span_A1 : Submodule.span (ZMod 2) (Set.range fun l : Fin n1 => bitv r (A1 l)) ≤ LinearMap.ker f := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    rcases hx with ⟨l, rfl⟩
    exact LinearMap.mem_ker.mpr (hA1 l)
  have h_span_A2 : Submodule.span (ZMod 2) (Set.range fun l : Fin n2 => bitv r (A2 l)) ≤ LinearMap.ker f := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    rcases hx with ⟨l, rfl⟩
    exact LinearMap.mem_ker.mpr (hA2 l)
  have h_sup : Submodule.span (ZMod 2) (Set.range fun l : Fin n1 => bitv r (A1 l)) ⊔
      Submodule.span (ZMod 2) (Set.range fun l : Fin n2 => bitv r (A2 l)) ≤ LinearMap.ker f :=
    sup_le h_span_A1 h_span_A2
  have hv' : v ∈ LinearMap.ker f := h_sup hv
  rw [LinearMap.mem_ker] at hv'
  simpa [f] using hv'

/-- The row over `n` columns whose bit `s` is the dot product (on `r` bits) of `q` with the column
`Ccol s`. -/
def dotRow (r : ℕ) (Ccol : ℕ → ℕ) (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => dotRow r Ccol q n + if dotB r q (Ccol n) then 2 ^ n else 0

lemma dotRow_lt_two_pow (r : ℕ) (Ccol : ℕ → ℕ) (q n : ℕ) : dotRow r Ccol q n < 2 ^ n := by
  induction' n with n ih
  · simp [dotRow]
  · rw [dotRow]
    by_cases h : dotB r q (Ccol n)
    · simp [h]
      have hsum : dotRow r Ccol q n + 2 ^ n < 2 ^ n + 2 ^ n := by
        nlinarith
      have h2 : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
        ring
      rw [h2] at hsum
      exact hsum
    · simp [h]
      have hpow : 2 ^ n < 2 ^ (n + 1) := by
        simp [pow_succ]
      exact lt_of_lt_of_le ih (by simpa using hpow.le)

lemma testBit_add_two_pow_of_lt {a n s : ℕ} (_ha : a < 2 ^ n) (hs : s < n) : (a + 2 ^ n).testBit s = a.testBit s := by
  have h_mod : (a + 2 ^ n) % 2 ^ (s + 1) = a % 2 ^ (s + 1) := by
    rw [Nat.add_mod]
    have h : 2 ^ n % 2 ^ (s + 1) = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      apply Nat.pow_dvd_pow 2 (by omega : s + 1 ≤ n)
    rw [h, add_zero, Nat.mod_mod]
  have h1 : (a + 2 ^ n).testBit s = ((a + 2 ^ n) % 2 ^ (s + 1)).testBit s := by
    rw [Nat.testBit_mod_two_pow]
    simp
  have h2 : (a % 2 ^ (s + 1)).testBit s = a.testBit s := by
    rw [Nat.testBit_mod_two_pow]
    simp
  rw [h1, h_mod, h2]

lemma dotRow_testBit (r : ℕ) (Ccol : ℕ → ℕ) (q : ℕ) (n s : ℕ) (hs : s < n) : (dotRow r Ccol q n).testBit s = dotB r q (Ccol s) := by
  revert s
  induction' n with n ih
  · intro s hs
    exact (Nat.not_lt_zero _ hs).elim
  · intro s hs
    rw [dotRow]
    have hs_cases : s < n ∨ s = n := by
      have hle : s ≤ n := Nat.le_of_lt_succ hs
      rcases hle.eq_or_lt with (h_eq | h_lt)
      · right; exact h_eq
      · left; exact h_lt
    rcases hs_cases with (hs_lt_n | hs_eq_n)
    · -- s < n
      by_cases hb : dotB r q (Ccol n)
      · simp [hb]
        have ha : dotRow r Ccol q n < 2 ^ n := dotRow_lt_two_pow r Ccol q n
        rw [testBit_add_two_pow_of_lt ha hs_lt_n]
        exact ih s hs_lt_n
      · simp [hb]
        exact ih s hs_lt_n
    · -- s = n
      rw [hs_eq_n]
      by_cases hb : dotB r q (Ccol n)
      · simp [hb]
        have ha : dotRow r Ccol q n < 2 ^ n := dotRow_lt_two_pow r Ccol q n
        have hbit : (dotRow r Ccol q n).testBit n = false := Nat.testBit_lt_two_pow ha
        rw [add_comm, Nat.testBit_two_pow_add_eq]
        simp [hbit]
      · simp [hb]
        have ha : dotRow r Ccol q n < 2 ^ n := dotRow_lt_two_pow r Ccol q n
        have hbit : (dotRow r Ccol q n).testBit n = false := Nat.testBit_lt_two_pow ha
        simp [hbit]


/-- A linear form `q` applied to a combination of columns is the form `dotRow` applied to the
coefficients. -/
theorem dotRow_sound (r : ℕ) (Ccol : ℕ → ℕ) (q : ℕ) {n : ℕ} (a : Fin n → ZMod 2) :
    ∑ j : Fin r, bitv r q j * (∑ s : Fin n, a s • bitv r (Ccol s)) j =
      ∑ s : Fin n, bitv n (dotRow r Ccol q n) s * a s := by
  calc
    ∑ j : Fin r, bitv r q j * (∑ s : Fin n, a s • bitv r (Ccol s)) j
        = ∑ j : Fin r, bitv r q j * (∑ s : Fin n, a s * bitv r (Ccol s) j) := by
      simp
    _ = ∑ j : Fin r, ∑ s : Fin n, bitv r q j * (a s * bitv r (Ccol s) j) := by
      simp [Finset.mul_sum]
    _ = ∑ s : Fin n, ∑ j : Fin r, bitv r q j * (a s * bitv r (Ccol s) j) := by
      rw [Finset.sum_comm]
    _ = ∑ s : Fin n, a s * (∑ j : Fin r, bitv r q j * bitv r (Ccol s) j) := by
      simp [Finset.mul_sum, mul_left_comm]
    _ = ∑ s : Fin n, a s * (if dotB r q (Ccol s.val) then (1 : ZMod 2) else 0) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← dotB_eq r q (Ccol s)]
    _ = ∑ s : Fin n, (if dotB r q (Ccol s.val) then (1 : ZMod 2) else 0) * a s := by
      simp [mul_comm]
    _ = ∑ s : Fin n, bitv n (dotRow r Ccol q n) s * a s := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [bitv]
      have h := dotRow_testBit r Ccol q n s.val s.is_lt
      -- h : (dotRow r Ccol q n).testBit s.val = dotB r q (Ccol s.val)
      -- We need: (if (dotRow r Ccol q n).testBit s.val then 1 else 0) = (if dotB r q (Ccol s.val) then 1 else 0)
      -- This follows from h
      simp [h]

end FurioLombardo.Discharge.SelmerBasis
