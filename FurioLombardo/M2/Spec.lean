import Mathlib
import FurioLombardo.M2.Defs

/-!
# Semantics of the kernel checkers of lane M2: integer coefficient lists

`evalZ t l` is the value at `t` (in any commutative ring) of the polynomial with coefficient list
`l` (constant term first). The lemmas say that the list operations of `FurioLombardo.M2.Defs`
are ring operations under `evalZ`, bound the coefficients they produce, and give the Kronecker
uniqueness principle: a list with coefficients of absolute value below `2^k` whose value at
`2^k` is `0` has only zero entries.
-/

namespace FurioLombardo.M2

/-- Horner evaluation of an integer coefficient list (constant term first). -/
def evalZ {R : Type*} [CommRing R] (t : R) : List ℤ → R
  | [] => 0
  | a :: l => (a : R) + t * evalZ t l

/-- `Σ_j a_j W_j` for coefficient lists `W_j`. -/
def combo : List ℤ → List (List ℤ) → List ℤ
  | a :: l, W :: Ws => addZ (smulZ a W) (combo l Ws)
  | _, _ => []

section Eval

variable {R : Type*} [CommRing R]

@[simp] theorem evalZ_nil (t : R) : evalZ t [] = 0 := rfl

@[simp] theorem evalZ_cons (t : R) (a : ℤ) (l : List ℤ) :
    evalZ t (a :: l) = (a : R) + t * evalZ t l := rfl

theorem evalI_eq (t : ℤ) (l : List ℤ) : evalI t l = evalZ t l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [evalI, ih]

theorem evalZ_map {R' : Type*} [CommRing R'] (f : R →+* R') (t : R) :
    ∀ l : List ℤ, f (evalZ t l) = evalZ (f t) l
  | [] => by simp
  | a :: l => by simp [evalZ_map f t l]

theorem evalZ_addZ (t : R) : ∀ l m : List ℤ, evalZ t (addZ l m) = evalZ t l + evalZ t m
  | [], m => by simp [addZ]
  | a :: l, [] => by simp [addZ]
  | a :: l, b :: m => by
    simp only [addZ, evalZ_cons, evalZ_addZ t l m, Int.cast_add]; ring

theorem evalZ_smulZ (t : R) (c : ℤ) : ∀ l : List ℤ, evalZ t (smulZ c l) = c * evalZ t l
  | [] => by simp [smulZ]
  | a :: l => by
    simp only [smulZ, evalZ_cons, evalZ_smulZ t c l, Int.cast_mul]; ring

theorem evalZ_mulZ (t : R) : ∀ l m : List ℤ, evalZ t (mulZ l m) = evalZ t l * evalZ t m
  | [], m => by simp [mulZ]
  | a :: l, m => by
    simp only [mulZ, evalZ_addZ, evalZ_smulZ, evalZ_cons, evalZ_mulZ t l m, Int.cast_zero]; ring

theorem evalZ_append (t : R) : ∀ l m : List ℤ,
    evalZ t (l ++ m) = evalZ t l + t ^ l.length * evalZ t m
  | [], m => by simp
  | a :: l, m => by
    simp only [List.cons_append, evalZ_cons, evalZ_append t l m, List.length_cons]; ring

theorem evalZ_dropLast (t : R) : ∀ l : List ℤ, l ≠ [] →
    evalZ t l = evalZ t l.dropLast + (l.getLastD 0 : R) * t ^ (l.length - 1)
  | [], h => absurd rfl h
  | [a], _ => by simp
  | a :: b :: l, _ => by
    have ih := evalZ_dropLast t (b :: l) (List.cons_ne_nil b l)
    simp only [List.dropLast_cons_cons, evalZ_cons, List.getLastD_cons, List.length_cons] at ih ⊢
    rw [ih]
    simp only [Nat.add_sub_cancel, pow_succ]
    ring

theorem evalZ_mulXZ (t : R) (gl r : List ℤ) (hg : t ^ gl.length + evalZ t gl = 0) :
    evalZ t (mulXZ gl r) = t * evalZ t r := by
  unfold mulXZ
  split_ifs with hlen
  · by_cases hr : r = []
    · subst hr
      have : gl = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst this
      simp [addZ, smulZ]
    · rw [evalZ_addZ, evalZ_smulZ, evalZ_cons, evalZ_dropLast t r hr]
      have hpos : 0 < r.length := List.length_pos_of_ne_nil hr
      have hg' : evalZ t gl = -(t ^ r.length) := by rw [← hlen] at hg; linear_combination hg
      rw [hg']
      have : t ^ r.length = t * t ^ (r.length - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]; push_cast; ring
  · simp

theorem evalZ_redZ (t : R) (gl : List ℤ) (hg : t ^ gl.length + evalZ t gl = 0) :
    ∀ l : List ℤ, evalZ t (redZ gl l) = evalZ t l
  | [] => rfl
  | a :: l => by
    rw [redZ, evalZ_addZ, evalZ_mulXZ t gl _ hg, evalZ_redZ t gl hg l]
    simp

/-- `homogL` computes `Σ c_i D^(n-i) W^i` modulo the monic polynomial `X^gl.length + gl`:
at a root `t`, with `w` such that `D w = W(t)`, `D * homogL = D ^ n * cs(w)` (`n = cs.length`). -/
theorem evalZ_homogL (t w : R) (gl W : List ℤ) (D : ℤ) (hg : t ^ gl.length + evalZ t gl = 0)
    (hw : (D : R) * w = evalZ t W) :
    ∀ cs : List ℤ, (D : R) * evalZ t (homogL gl W D cs) = (D : R) ^ cs.length * evalZ w cs
  | [] => by simp [homogL]
  | c :: cs => by
    rw [homogL, evalZ_redZ t gl hg, evalZ_addZ, evalZ_mulZ, mul_add, List.length_cons]
    have ih := evalZ_homogL t w gl W D hg hw cs
    simp only [evalZ_cons, evalZ_nil, mul_zero, add_zero, Int.cast_mul, Int.cast_pow]
    rw [← hw]
    linear_combination (D : R) * w * ih

theorem evalZ_combo (t : R) : ∀ (a : List ℤ) (Ws : List (List ℤ)),
    evalZ t (combo a Ws) = ((a.zip Ws).map fun x => (x.1 : R) * evalZ t x.2).sum
  | [], _ => by simp [combo]
  | _ :: _, [] => by simp [combo]
  | a :: l, W :: Ws => by
    simp [combo, evalZ_addZ, evalZ_smulZ, evalZ_combo t l Ws]

theorem dotZ_map_evalZ (x : ℤ) : ∀ (a : List ℤ) (Ws : List (List ℤ)),
    dotZ a (Ws.map (evalZ x)) = evalZ x (combo a Ws)
  | [], _ => by simp [dotZ, combo]
  | _ :: _, [] => by simp [dotZ, combo]
  | a :: l, W :: Ws => by
    simp [dotZ, combo, evalZ_addZ, evalZ_smulZ, dotZ_map_evalZ x l Ws]

end Eval

/-! ## Coefficient bounds -/

theorem allBounded_iff (b : ℕ) : ∀ l : List ℤ, allBounded b l = true ↔ ∀ x ∈ l, x.natAbs ≤ b
  | [] => by simp [allBounded]
  | a :: l => by simp [allBounded, allBounded_iff b l]

theorem allDvd_iff (p : ℤ) : ∀ l : List ℤ, allDvd p l = true ↔ ∀ x ∈ l, p ∣ x
  | [] => by simp [allDvd]
  | a :: l => by
    simp only [allDvd, Bool.and_eq_true, beq_iff_eq, allDvd_iff p l, List.mem_cons,
      forall_eq_or_imp, Int.dvd_iff_emod_eq_zero]

theorem allZero_iff : ∀ l : List ℤ, allZero l = true ↔ ∀ x ∈ l, x = 0
  | [] => by simp [allZero]
  | a :: l => by simp [allZero, allZero_iff l]

theorem natAbs_addZ (A B : ℕ) : ∀ l m : List ℤ, (∀ x ∈ l, x.natAbs ≤ A) →
    (∀ x ∈ m, x.natAbs ≤ B) → ∀ x ∈ addZ l m, x.natAbs ≤ A + B
  | [], m, _, hm => fun x hx => (hm x hx).trans (Nat.le_add_left _ _)
  | a :: l, [], hl, _ => fun x hx => (hl x hx).trans (Nat.le_add_right _ _)
  | a :: l, b :: m, hl, hm => by
    intro x hx
    simp only [addZ, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact (Int.natAbs_add_le a b).trans
        (Nat.add_le_add (hl a (by simp)) (hm b (by simp)))
    · exact natAbs_addZ A B l m (fun y hy => hl y (by simp [hy]))
        (fun y hy => hm y (by simp [hy])) x hx

theorem natAbs_smulZ (c : ℤ) (A : ℕ) : ∀ l : List ℤ, (∀ x ∈ l, x.natAbs ≤ A) →
    ∀ x ∈ smulZ c l, x.natAbs ≤ c.natAbs * A
  | [], _ => by simp [smulZ]
  | a :: l, hl => by
    intro x hx
    simp only [smulZ, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ (hl a (by simp))
    · exact natAbs_smulZ c A l (fun y hy => hl y (by simp [hy])) x hx

theorem natAbs_mulZ (A B : ℕ) : ∀ l m : List ℤ, (∀ x ∈ l, x.natAbs ≤ A) →
    (∀ x ∈ m, x.natAbs ≤ B) → ∀ x ∈ mulZ l m, x.natAbs ≤ l.length * A * B
  | [], _, _, _ => by simp [mulZ]
  | a :: l, m, hl, hm => by
    intro x hx
    simp only [mulZ] at hx
    have h1 : ∀ y ∈ smulZ a m, y.natAbs ≤ A * B := fun y hy =>
      (natAbs_smulZ a B m hm y hy).trans (Nat.mul_le_mul_right _ (hl a (by simp)))
    have h2 : ∀ y ∈ (0 : ℤ) :: mulZ l m, y.natAbs ≤ l.length * A * B := by
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · simp
      · exact natAbs_mulZ A B l m (fun z hz => hl z (by simp [hz])) hm y hy
    have := natAbs_addZ _ _ _ _ h1 h2 x hx
    simp only [List.length_cons]
    nlinarith

theorem natAbs_combo (A Wm : ℕ) : ∀ (a : List ℤ) (Ws : List (List ℤ)), (∀ x ∈ a, x.natAbs ≤ A) →
    (∀ W ∈ Ws, ∀ x ∈ W, x.natAbs ≤ Wm) → ∀ x ∈ combo a Ws, x.natAbs ≤ a.length * A * Wm
  | [], _, _, _ => by simp [combo]
  | _ :: _, [], _, _ => by simp [combo]
  | a :: l, W :: Ws, ha, hW => by
    intro x hx
    simp only [combo] at hx
    have h1 : ∀ y ∈ smulZ a W, y.natAbs ≤ A * Wm := fun y hy =>
      (natAbs_smulZ a Wm W (hW W (by simp)) y hy).trans (Nat.mul_le_mul_right _ (ha a (by simp)))
    have h2 := natAbs_combo A Wm l Ws (fun y hy => ha y (by simp [hy]))
      (fun V hV => hW V (by simp [hV]))
    have := natAbs_addZ _ _ _ _ h1 h2 x hx
    simp only [List.length_cons]
    nlinarith

/-! ## Kronecker uniqueness -/

/-- A list with entries of absolute value below `2^k` and value `0` at `2^k` is zero. -/
theorem eq_zero_of_evalZ_two_pow (k : ℕ) : ∀ l : List ℤ, (∀ x ∈ l, x.natAbs < 2 ^ k) →
    evalZ ((2 : ℤ) ^ k) l = 0 → ∀ x ∈ l, x = 0
  | [], _, _ => by simp
  | a :: l, hl, h0 => by
    simp only [evalZ_cons, Int.cast_id] at h0
    have hv : evalZ ((2 : ℤ) ^ k) l = 0 := by
      by_contra hne
      have ha : a = -((2 : ℤ) ^ k * evalZ ((2 : ℤ) ^ k) l) := by linarith
      have hlt := hl a (by simp)
      rw [ha, Int.natAbs_neg, Int.natAbs_mul] at hlt
      have : 1 ≤ (evalZ ((2 : ℤ) ^ k) l).natAbs := Int.natAbs_pos.mpr hne
      have h2 : ((2 : ℤ) ^ k).natAbs = 2 ^ k := by simp [Int.natAbs_pow]
      rw [h2] at hlt
      have h3 : 2 ^ k * 1 ≤ 2 ^ k * (evalZ ((2 : ℤ) ^ k) l).natAbs := Nat.mul_le_mul_left _ this
      rw [mul_one] at h3
      linarith
    have ha : a = 0 := by rw [hv, mul_zero, add_zero] at h0; exact h0
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact eq_zero_of_evalZ_two_pow k l (fun y hy => hl y (by simp [hy])) hv x hx

theorem evalZ_eq_zero_of_forall {R : Type*} [CommRing R] (t : R) :
    ∀ l : List ℤ, (∀ x ∈ l, x = 0) → evalZ t l = 0
  | [], _ => rfl
  | a :: l, h => by
    rw [evalZ_cons, h a (by simp), evalZ_eq_zero_of_forall t l (fun y hy => h y (by simp [hy]))]
    simp

/-- Kronecker transfer: if `H(2^k) = g(2^k) Q(2^k)` and the coefficients of `H` and of `g Q` are
small, then `H = g Q` at every point of every commutative ring. -/
theorem kron_mul {R : Type*} [CommRing R] (k b b' : ℕ) (H g Q : List ℤ)
    (hH : ∀ x ∈ H, x.natAbs ≤ b) (hgQ : ∀ x ∈ mulZ g Q, x.natAbs ≤ b') (hk : b + b' < 2 ^ k)
    (hv : evalZ ((2 : ℤ) ^ k) H = evalZ ((2 : ℤ) ^ k) g * evalZ ((2 : ℤ) ^ k) Q) (t : R) :
    evalZ t H = evalZ t g * evalZ t Q := by
  set l := addZ H (smulZ (-1) (mulZ g Q))
  have hb : ∀ x ∈ l, x.natAbs < 2 ^ k := by
    intro x hx
    have h2 : ∀ y ∈ smulZ (-1) (mulZ g Q), y.natAbs ≤ b' := fun y hy => by
      simpa using natAbs_smulZ (-1) b' _ hgQ y hy
    exact lt_of_le_of_lt (natAbs_addZ b b' H _ hH h2 x hx) hk
  have h0 : evalZ ((2 : ℤ) ^ k) l = 0 := by
    simp only [l, evalZ_addZ, evalZ_smulZ, evalZ_mulZ, hv]; push_cast; ring
  have := evalZ_eq_zero_of_forall t l (eq_zero_of_evalZ_two_pow k l hb h0)
  simp only [l, evalZ_addZ, evalZ_smulZ, evalZ_mulZ] at this
  push_cast at this
  linear_combination this

/-- Kronecker transfer for two lists with the same value at `2^k`. -/
theorem kron_eq {R : Type*} [CommRing R] (k b b' : ℕ) (l m : List ℤ)
    (hl : ∀ x ∈ l, x.natAbs ≤ b) (hm : ∀ x ∈ m, x.natAbs ≤ b') (hk : b + b' < 2 ^ k)
    (hv : evalZ ((2 : ℤ) ^ k) l = evalZ ((2 : ℤ) ^ k) m) (t : R) :
    evalZ t l = evalZ t m := by
  set d := addZ l (smulZ (-1) m)
  have hb : ∀ x ∈ d, x.natAbs < 2 ^ k := by
    intro x hx
    have h2 : ∀ y ∈ smulZ (-1) m, y.natAbs ≤ b' := fun y hy => by
      simpa using natAbs_smulZ (-1) b' _ hm y hy
    exact lt_of_le_of_lt (natAbs_addZ b b' l _ hl h2 x hx) hk
  have h0 : evalZ ((2 : ℤ) ^ k) d = 0 := by
    simp only [d, evalZ_addZ, evalZ_smulZ, hv]; push_cast; ring
  have := evalZ_eq_zero_of_forall t d (eq_zero_of_evalZ_two_pow k d hb h0)
  simp only [d, evalZ_addZ, evalZ_smulZ] at this
  push_cast at this
  linear_combination this

/-! ## Divisibility and residues -/

theorem evalZ_of_allDvd {R : Type*} [CommRing R] (t : R) (p : ℤ) :
    ∀ l : List ℤ, allDvd p l = true → evalZ t l = (p : R) * evalZ t (l.map fun x => x / p)
  | [], _ => by simp
  | a :: l, h => by
    simp only [allDvd, Bool.and_eq_true, beq_iff_eq] at h
    rw [List.map_cons, evalZ_cons, evalZ_cons, evalZ_of_allDvd t p l h.2, mul_add]
    have : (a : R) = (p : R) * ((a / p : ℤ) : R) := by
      rw [← Int.cast_mul, Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h.1)]
    rw [this]; ring

theorem hornerMod_eq (p r : ℤ) : ∀ l : List ℤ, hornerMod p r l = evalZ r l % p
  | [] => by simp [hornerMod]
  | c :: l => by
    simp only [hornerMod, hornerMod_eq p r l, evalZ_cons, Int.cast_id]
    rw [Int.add_emod, Int.mul_emod, Int.emod_emod_of_dvd _ (dvd_refl p), ← Int.mul_emod,
      ← Int.add_emod]

/-- `l(x) - l(y)` is a multiple of `x - y`. -/
theorem sub_dvd_evalZ_sub {R : Type*} [CommRing R] (x y : R) :
    ∀ l : List ℤ, (x - y) ∣ evalZ x l - evalZ y l
  | [] => by simp
  | a :: l => by
    obtain ⟨c, hc⟩ := sub_dvd_evalZ_sub x y l
    refine ⟨evalZ x l + y * c, ?_⟩
    simp only [evalZ_cons]
    linear_combination y * hc

end FurioLombardo.M2
