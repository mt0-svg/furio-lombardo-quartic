import FurioLombardo.M1.ListPoly

/-!
# Kernel-checked ring identities by Kronecker substitution

Setting: a commutative ring `R`, an element `t : R` with `evalL t g = 0` for an integer coefficient
list `g`, a positive integer `Dz` with an inverse `d : R` (`d * Dz = 1`), and atoms
`x_j = d * evalL t A_j` for integer coefficient lists `A_j` (`As = [A_0, A_1, ...]`). For K21:
`g = fL`, `t = θ`, `d = Dz⁻¹` and `As = zkNum`, so the atoms are PARI's integral basis.

A `KE` is a ring expression in linear combinations of the atoms. `ev` is its value in `R`. The
numerator `num e ∈ ℤ[X]` satisfies `num e (t) = Dz ^ deg e * ev e`; the kernel computes the
integer `valN e = num e (N)` at `N = 2 ^ k` (one GMP operation per node), a bound `bnd e` on the
coefficients of `num e`, and a bound `len e` on its number of coefficients.

`check`: `num e (N) = g(N) q` for an integer `q` whose balanced base `N` digits `Q` are small,
with `2 (bnd e + #g · max|g| · max|Q|) < N`. Then `num e - g · Q` has coefficients below `N / 2`
and vanishes at `N`, so it is the zero polynomial: `num e = g · Q` in `ℤ[X]`, and `num e (t) = 0`,
whence `ev e = 0` (`ev_eq_zero_of_check`). No reduction modulo `g` and no polynomial product is
ever computed by the kernel; `g` need not be monic.
-/

namespace FurioLombardo.M1.Kron

open Polynomial

/-- Ring expressions in linear combinations of the atoms. -/
inductive KE : Type
  /-- `Σ a_j x_j` -/
  | lin (a : List ℤ)
  /-- an integer -/
  | int (m : ℤ)
  | add (e f : KE)
  | sub (e f : KE)
  | mul (e f : KE)
  deriving Inhabited

/-- `Σ a_i W_i` for coefficient lists (the shorter list decides the number of terms). -/
def combo : List ℤ → List (List ℤ) → List ℤ
  | c :: a, W :: Ws => addL (smulL c W) (combo a Ws)
  | _, _ => []

/-- `Σ a_i v_i` (the shorter list decides the number of terms). -/
def dot {R : Type*} [CommRing R] : List ℤ → List R → R
  | c :: a, v :: vs => (c : R) * v + dot a vs
  | _, _ => 0

/-- Sum of the absolute values. -/
def sumAbs : List ℤ → ℕ
  | [] => 0
  | c :: a => c.natAbs + sumAbs a

/-- Largest absolute value (`0` for the empty list). -/
def maxAbs : List ℤ → ℕ
  | [] => 0
  | c :: a => max c.natAbs (maxAbs a)

/-- `n` balanced digits in base `2 ^ k` (each in `(-2^k/2, 2^k/2]`), lowest first. Only used to
propose a quotient: `check` verifies that the digits reproduce it. -/
def digits (k : ℕ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | n + 1, x =>
    let r := x % 2 ^ k
    let r' := if 2 * r > 2 ^ k then r - 2 ^ k else r
    r' :: digits k n ((x - r') / 2 ^ k)

namespace KE

/-- Formal degree in the atoms, i.e. the power of `Dz` in the denominator. -/
def deg : KE → ℕ
  | lin _ => 1
  | int _ => 0
  | add e f => max e.deg f.deg
  | sub e f => max e.deg f.deg
  | mul e f => e.deg + f.deg

/-- `e ^ n` as a product chain (`int 1` for `n = 0`). -/
def pow (e : KE) : ℕ → KE
  | 0 => int 1
  | 1 => e
  | n + 2 => mul (pow e (n + 1)) e

/-- Product of a list of expressions. -/
def prod : List KE → KE
  | [] => int 1
  | [e] => e
  | e :: l => mul e (prod l)

/-- Sum of a list of expressions. -/
def sum : List KE → KE
  | [] => int 0
  | [e] => e
  | e :: l => add e (sum l)

variable (As : List (List ℤ)) (Dz : ℕ)

/-- The value of an expression, the atoms being `d * evalL t A_j`. -/
def ev {R : Type*} [CommRing R] (t d : R) : KE → R
  | lin a => d * evalL t (combo a As)
  | int m => m
  | add e f => ev t d e + ev t d f
  | sub e f => ev t d e - ev t d f
  | mul e f => ev t d e * ev t d f

/-- The numerator polynomial: `ev e = num e (t) / Dz ^ deg e`. -/
noncomputable def num : KE → ℤ[X]
  | lin a => ofListL (combo a As)
  | int m => C m
  | add e f => C ((Dz : ℤ) ^ (max e.deg f.deg - e.deg)) * num e
      + C ((Dz : ℤ) ^ (max e.deg f.deg - f.deg)) * num f
  | sub e f => C ((Dz : ℤ) ^ (max e.deg f.deg - e.deg)) * num e
      - C ((Dz : ℤ) ^ (max e.deg f.deg - f.deg)) * num f
  | mul e f => num e * num f

/-- The value of the numerator at the integer where the atoms' numerators take the values `WN`. -/
def valN (WN : List ℤ) : KE → ℤ
  | lin a => dot a WN
  | int m => m
  | add e f => (Dz : ℤ) ^ (max e.deg f.deg - e.deg) * valN WN e
      + (Dz : ℤ) ^ (max e.deg f.deg - f.deg) * valN WN f
  | sub e f => (Dz : ℤ) ^ (max e.deg f.deg - e.deg) * valN WN e
      - (Dz : ℤ) ^ (max e.deg f.deg - f.deg) * valN WN f
  | mul e f => valN WN e * valN WN f

/-- A bound on the number of coefficients of the numerator (`L` bounds the atoms' lengths). -/
def len (L : ℕ) : KE → ℕ
  | lin _ => L
  | int _ => 1
  | add e f => max (len L e) (len L f)
  | sub e f => max (len L e) (len L f)
  | mul e f => len L e + len L f - 1

/-- A bound on the absolute values of the coefficients of the numerator (`Wb` bounds the
coefficients of the atoms). -/
def bnd (L Wb : ℕ) : KE → ℕ
  | lin a => sumAbs a * Wb
  | int m => m.natAbs
  | add e f => Dz ^ (max e.deg f.deg - e.deg) * bnd L Wb e
      + Dz ^ (max e.deg f.deg - f.deg) * bnd L Wb f
  | sub e f => Dz ^ (max e.deg f.deg - e.deg) * bnd L Wb e
      + Dz ^ (max e.deg f.deg - f.deg) * bnd L Wb f
  | mul e f => len L e * bnd L Wb e * bnd L Wb f

/-- The Kronecker test at `N = 2 ^ k` (see the module docstring). -/
def check (g : List ℤ) (L Wb k : ℕ) (e : KE) : Bool :=
  let N : ℤ := 2 ^ k
  let v := valN Dz (As.map (evalL N)) e
  let gN := evalL N g
  let q := v / gN
  let Q := digits k (len L e) q
  v == gN * q && evalL N Q == q &&
    decide (2 * (bnd Dz L Wb e + g.length * maxAbs g * maxAbs Q) < 2 ^ k)

/-! ## Soundness -/

variable {As Dz}


theorem natAbs_coeff_mul_le (p q : ℤ[X]) (lp Bp Bq : ℕ) (hp : ∀ i, (p.coeff i).natAbs ≤ Bp)
    (hp0 : ∀ i, lp ≤ i → p.coeff i = 0) (hq : ∀ i, (q.coeff i).natAbs ≤ Bq) (k : ℕ) :
    ((p * q).coeff k).natAbs ≤ lp * Bp * Bq := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine (Int.natAbs_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range (k + 1), (p.coeff i * q.coeff (k - i)).natAbs
      ≤ ∑ i ∈ Finset.range (k + 1), (if i < lp then Bp * Bq else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Int.natAbs_mul]
        split_ifs with h
        · exact Nat.mul_le_mul (hp i) (hq _)
        · rw [hp0 i (by omega)]; simp
    _ = ((Finset.range (k + 1)).filter (· < lp)).card * (Bp * Bq) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    _ ≤ lp * (Bp * Bq) := by
        refine Nat.mul_le_mul_right _ ?_
        calc ((Finset.range (k + 1)).filter (· < lp)).card ≤ (Finset.range lp).card :=
              Finset.card_le_card fun i hi => by
                simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; exact hi.2
          _ = lp := Finset.card_range lp
    _ = lp * Bp * Bq := by ring

theorem coeff_mul_eq_zero (p q : ℤ[X]) (lp lq : ℕ) (hp0 : ∀ i, lp ≤ i → p.coeff i = 0)
    (hq0 : ∀ i, lq ≤ i → q.coeff i = 0) (k : ℕ) (hk : lp + lq - 1 ≤ k) : (p * q).coeff k = 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_eq_zero fun i hi => ?_
  simp only [Finset.mem_range] at hi
  by_cases h : lp ≤ i
  · rw [hp0 i h, zero_mul]
  · rcases Nat.eq_zero_or_pos lq with h0 | h0
    · rw [hq0 _ (by omega), mul_zero]
    · rw [hq0 _ (by omega), mul_zero]

theorem eval_ofListL (x : ℤ) : ∀ l : List ℤ, (ofListL l).eval x = evalL x l
  | [] => by simp [ofListL]
  | a :: l => by simp [ofListL, eval_ofListL x l]

theorem coeff_ofListL : ∀ (l : List ℤ) (i : ℕ), (ofListL l).coeff i = l.getD i 0
  | [], i => by simp [ofListL]
  | a :: l, 0 => by simp [ofListL]
  | a :: l, i + 1 => by
    simp only [ofListL, coeff_add, coeff_C, coeff_X_mul, coeff_ofListL l i]; simp

theorem natAbs_getD_le_maxAbs : ∀ (l : List ℤ) (i : ℕ), (l.getD i 0).natAbs ≤ maxAbs l
  | [], i => by simp [maxAbs]
  | a :: l, 0 => by simp [maxAbs]
  | a :: l, i + 1 => by
    simp only [List.getD_cons_succ, maxAbs]
    exact (natAbs_getD_le_maxAbs l i).trans (le_max_right _ _)

theorem getD_eq_zero_of_length_le (l : List ℤ) (i : ℕ) (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem getD_addL : ∀ (l m : List ℤ) (i : ℕ), (addL l m).getD i 0 = l.getD i 0 + m.getD i 0
  | [], m, i => by simp [addL]
  | a :: l, [], i => by simp [addL]
  | a :: l, b :: m, 0 => by simp [addL]
  | a :: l, b :: m, i + 1 => by simp only [addL, List.getD_cons_succ]; exact getD_addL l m i

theorem length_addL : ∀ (l m : List ℤ), (addL l m).length = max l.length m.length
  | [], m => by simp [addL]
  | a :: l, [] => by simp [addL]
  | a :: l, b :: m => by simp [addL, length_addL l m, Nat.succ_max_succ]

theorem getD_smulL (c : ℤ) (l : List ℤ) (i : ℕ) : (smulL c l).getD i 0 = c * l.getD i 0 := by
  unfold smulL
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

theorem combo_bound (L Wb : ℕ) : ∀ (a : List ℤ) (Ws : List (List ℤ)),
    (∀ W ∈ Ws, W.length ≤ L) → (∀ W ∈ Ws, ∀ x ∈ W, x.natAbs ≤ Wb) →
    (combo a Ws).length ≤ L ∧ ∀ i, ((combo a Ws).getD i 0).natAbs ≤ sumAbs a * Wb
  | c :: a, W :: Ws, hL, hW => by
    obtain ⟨ih1, ih2⟩ := combo_bound L Wb a Ws (fun V hV => hL V (List.mem_cons_of_mem _ hV))
      (fun V hV => hW V (List.mem_cons_of_mem _ hV))
    refine ⟨?_, fun i => ?_⟩
    · simp only [combo, length_addL, smulL, List.length_map]
      exact max_le (hL W List.mem_cons_self) ih1
    · simp only [combo, getD_addL, getD_smulL, sumAbs]
      refine (Int.natAbs_add_le _ _).trans ?_
      rw [Int.natAbs_mul, add_mul]
      refine Nat.add_le_add (Nat.mul_le_mul_left _ ?_) (ih2 i)
      rcases lt_or_ge i W.length with h | h
      · rw [List.getD_eq_getElem _ _ h]; exact hW W List.mem_cons_self _ (List.getElem_mem h)
      · rw [getD_eq_zero_of_length_le W i h]; simp
  | [], _, _, _ => by simp [combo]
  | _ :: _, [], _, _ => by simp [combo]

theorem evalL_combo {R : Type*} [CommRing R] (t : R) :
    ∀ (a : List ℤ) (Ws : List (List ℤ)), evalL t (combo a Ws) = dot a (Ws.map (evalL t))
  | c :: a, W :: Ws => by
    simp only [combo, dot, List.map_cons, evalL_addL, evalL_smulL, evalL_combo t a Ws]
  | [], _ => by simp [combo, dot]
  | _ :: _, [] => by simp [combo, dot]

theorem eval₂_num {R : Type*} [CommRing R] (t d : R) (hd : d * (Dz : R) = 1) :
    ∀ e : KE, (num As Dz e).eval₂ (Int.castRingHom R) t = (Dz : R) ^ e.deg * ev As t d e
  | lin a => by
    simp only [num, evalL_ofListL, deg, ev, pow_one]
    rw [← mul_assoc, mul_comm (Dz : R) d, hd, one_mul]
  | int m => by rw [num, eval₂_C]; simp [deg, ev]
  | add e f => by
    simp only [num, eval₂_add, eval₂_mul, eval₂_C, deg, ev, eval₂_num t d hd e, eval₂_num t d hd f]
    have h1 : max e.deg f.deg - e.deg + e.deg = max e.deg f.deg := Nat.sub_add_cancel (le_max_left _ _)
    have h2 : max e.deg f.deg - f.deg + f.deg = max e.deg f.deg := Nat.sub_add_cancel (le_max_right _ _)
    simp only [eq_intCast, Int.cast_pow, Int.cast_natCast]
    rw [← mul_assoc, ← pow_add, h1, ← mul_assoc, ← pow_add, h2]; ring
  | sub e f => by
    simp only [num, eval₂_sub, eval₂_mul, eval₂_C, deg, ev, eval₂_num t d hd e, eval₂_num t d hd f]
    have h1 : max e.deg f.deg - e.deg + e.deg = max e.deg f.deg := Nat.sub_add_cancel (le_max_left _ _)
    have h2 : max e.deg f.deg - f.deg + f.deg = max e.deg f.deg := Nat.sub_add_cancel (le_max_right _ _)
    simp only [eq_intCast, Int.cast_pow, Int.cast_natCast]
    rw [← mul_assoc, ← pow_add, h1, ← mul_assoc, ← pow_add, h2]; ring
  | mul e f => by
    simp only [num, eval₂_mul, deg, ev, eval₂_num t d hd e, eval₂_num t d hd f, pow_add]; ring


theorem eval_num (N : ℤ) :
    ∀ e : KE, (num As Dz e).eval N = valN Dz (As.map (evalL N)) e
  | lin a => by
    simp only [num, valN]
    rw [← evalL_combo, eval, ← evalL_ofListL]; rfl
  | int m => by simp [num, valN]
  | add e f => by simp [num, valN, eval_num N e, eval_num N f]
  | sub e f => by simp [num, valN, eval_num N e, eval_num N f]
  | mul e f => by simp [num, valN, eval_num N e, eval_num N f]

theorem coeff_num_le (L Wb : ℕ) (hL : ∀ W ∈ As, W.length ≤ L)
    (hWb : ∀ W ∈ As, ∀ x ∈ W, x.natAbs ≤ Wb) : ∀ e : KE,
    (∀ i, ((num As Dz e).coeff i).natAbs ≤ bnd Dz L Wb e) ∧
      (∀ i, len L e ≤ i → (num As Dz e).coeff i = 0)
  | lin a => by
    obtain ⟨h1, h2⟩ := combo_bound L Wb a As hL hWb
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · simp only [num, bnd, coeff_ofListL]; exact h2 i
    · simp only [num, len, coeff_ofListL] at hi ⊢
      exact getD_eq_zero_of_length_le _ _ (h1.trans hi)
  | int m => by
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · simp only [num, bnd, coeff_C]; split_ifs <;> simp
    · simp only [len] at hi; simp only [num, coeff_C]; exact ite_eq_right_iff.mpr (fun h => by omega)
  | add e f => by
    obtain ⟨he1, he2⟩ := coeff_num_le L Wb hL hWb e
    obtain ⟨hf1, hf2⟩ := coeff_num_le L Wb hL hWb f
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · simp only [num, bnd, coeff_add, coeff_C_mul]
      refine (Int.natAbs_add_le _ _).trans (Nat.add_le_add ?_ ?_) <;>
      · rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        exact Nat.mul_le_mul_left _ (by first | exact he1 i | exact hf1 i)
    · simp only [len] at hi
      simp only [num, coeff_add, coeff_C_mul, he2 i (le_of_max_le_left hi),
        hf2 i (le_of_max_le_right hi), mul_zero, add_zero]
  | sub e f => by
    obtain ⟨he1, he2⟩ := coeff_num_le L Wb hL hWb e
    obtain ⟨hf1, hf2⟩ := coeff_num_le L Wb hL hWb f
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · simp only [num, bnd, coeff_sub, coeff_C_mul]
      refine (Int.natAbs_sub_le _ _).trans (Nat.add_le_add ?_ ?_) <;>
      · rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        exact Nat.mul_le_mul_left _ (by first | exact he1 i | exact hf1 i)
    · simp only [len] at hi
      simp only [num, coeff_sub, coeff_C_mul, he2 i (le_of_max_le_left hi),
        hf2 i (le_of_max_le_right hi), mul_zero, sub_zero]
  | mul e f => by
    obtain ⟨he1, he2⟩ := coeff_num_le L Wb hL hWb e
    obtain ⟨hf1, hf2⟩ := coeff_num_le L Wb hL hWb f
    exact ⟨fun i => natAbs_coeff_mul_le _ _ _ _ _ he1 he2 hf1 i,
      fun i hi => coeff_mul_eq_zero _ _ _ _ he2 hf2 i hi⟩

theorem eq_zero_of_eval_eq_zero_aux (N : ℕ) : ∀ (n : ℕ) (p : ℤ[X]),
    (∀ i, 2 * (p.coeff i).natAbs < N) → (∀ i, n ≤ i → p.coeff i = 0) → p.eval (N : ℤ) = 0 → p = 0
  | 0, p, _, hn, _ => Polynomial.ext fun i => by simpa using hn i (Nat.zero_le i)
  | n + 1, p, hp, hn, h0 => by
    have hsplit := X_mul_divX_add p
    have hN : (0 : ℤ) < N := by have := hp 0; omega
    have hev : (N : ℤ) * (divX p).eval (N : ℤ) + p.coeff 0 = 0 := by
      rw [← h0]; conv_rhs => rw [← hsplit]
      simp
    have hdvd : (N : ℤ) ∣ p.coeff 0 := ⟨-(divX p).eval (N : ℤ), by linarith⟩
    have h00 : p.coeff 0 = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
      have := hp 0
      rw [Int.abs_eq_natAbs]; omega
    have hd0 : (divX p).eval (N : ℤ) = 0 := by
      rw [h00, add_zero] at hev
      rcases mul_eq_zero.mp hev with h | h
      · omega
      · exact h
    have hdiv : divX p = 0 := eq_zero_of_eval_eq_zero_aux N n (divX p)
      (fun i => by rw [coeff_divX]; exact hp _)
      (fun i hi => by rw [coeff_divX]; exact hn _ (by omega)) hd0
    rw [← hsplit, hdiv, h00]; simp

theorem eq_zero_of_eval_eq_zero (N : ℕ) (p : ℤ[X]) (hp : ∀ i, 2 * (p.coeff i).natAbs < N)
    (h0 : p.eval (N : ℤ) = 0) : p = 0 :=
  eq_zero_of_eval_eq_zero_aux N (p.natDegree + 1) p hp
    (fun i hi => coeff_eq_zero_of_natDegree_lt (by omega)) h0

theorem ev_eq_zero_of_check {R : Type*} [CommRing R] (g : List ℤ) (L Wb k : ℕ)
    (hL : ∀ W ∈ As, W.length ≤ L) (hWb : ∀ W ∈ As, ∀ x ∈ W, x.natAbs ≤ Wb)
    (t d : R) (hg : evalL t g = 0) (hd : d * (Dz : R) = 1) (e : KE)
    (h : check As Dz g L Wb k e = true) : ev As t d e = 0 := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  set N : ℤ := 2 ^ k with hNdef
  set Q := digits k (len L e) (valN Dz (As.map (evalL N)) e / evalL N g) with hQ
  set P : ℤ[X] := num As Dz e - ofListL g * ofListL Q with hP
  have hPN : P.eval ((2 ^ k : ℕ) : ℤ) = 0 := by
    have : ((2 ^ k : ℕ) : ℤ) = N := by push_cast; rfl
    rw [this, hP, eval_sub, eval_mul, eval_ofListL, eval_ofListL, eval_num, h2, ← h1, sub_self]
  obtain ⟨hb1, -⟩ := coeff_num_le (Dz := Dz) L Wb hL hWb e
  have hgQ : ∀ i, ((ofListL g * ofListL Q).coeff i).natAbs ≤ g.length * maxAbs g * maxAbs Q :=
    natAbs_coeff_mul_le _ _ _ _ _ (fun i => by rw [coeff_ofListL]; exact natAbs_getD_le_maxAbs _ _)
      (fun i hi => by rw [coeff_ofListL]; exact getD_eq_zero_of_length_le _ _ hi)
      (fun i => by rw [coeff_ofListL]; exact natAbs_getD_le_maxAbs _ _)
  have hP0 : P = 0 := eq_zero_of_eval_eq_zero (2 ^ k) P (fun i => by
    rw [hP, coeff_sub]
    have := (Int.natAbs_sub_le _ _).trans (Nat.add_le_add (hb1 i) (hgQ i))
    omega) hPN
  have hnum : num As Dz e = ofListL g * ofListL Q := sub_eq_zero.mp hP0
  have hev := eval₂_num (As := As) t d hd e
  rw [hnum, eval₂_mul, evalL_ofListL, hg, zero_mul] at hev
  have : (d * (Dz : R)) ^ e.deg * ev As t d e = 0 := by rw [mul_pow, mul_assoc, ← hev, mul_zero]
  rwa [hd, one_pow, one_mul] at this

theorem ev_pow {R : Type*} [CommRing R] (t d : R) (e : KE) :
    ∀ n : ℕ, ev As t d (pow e n) = ev As t d e ^ n
  | 0 => by simp [pow, ev]
  | 1 => by simp [pow]
  | n + 2 => by rw [pow, ev, ev_pow t d e (n + 1)]; ring

theorem ev_prod {R : Type*} [CommRing R] (t d : R) :
    ∀ l : List KE, ev As t d (prod l) = (l.map (ev As t d)).prod
  | [] => by simp [prod, ev]
  | [e] => by simp [prod]
  | e :: f :: l => by
    show ev As t d (mul e (prod (f :: l))) = _
    rw [ev, ev_prod t d (f :: l)]; simp

theorem ev_sum {R : Type*} [CommRing R] (t d : R) :
    ∀ l : List KE, ev As t d (sum l) = (l.map (ev As t d)).sum
  | [] => by simp [sum, ev]
  | [e] => by simp [sum]
  | e :: f :: l => by
    show ev As t d (add e (sum (f :: l))) = _
    rw [ev, ev_sum t d (f :: l)]; simp


/-- Identity form: `check (sub e f)` gives `ev e = ev f`. -/
theorem ev_eq_of_check {R : Type*} [CommRing R] (g : List ℤ) (L Wb k : ℕ)
    (hL : ∀ W ∈ As, W.length ≤ L) (hWb : ∀ W ∈ As, ∀ x ∈ W, x.natAbs ≤ Wb)
    (t d : R) (hg : evalL t g = 0) (hd : d * (Dz : R) = 1) (e f : KE)
    (h : check As Dz g L Wb k (sub e f) = true) : ev As t d e = ev As t d f := by
  have := ev_eq_zero_of_check g L Wb k hL hWb t d hg hd _ h
  simpa [ev, sub_eq_zero] using this

end KE

end FurioLombardo.M1.Kron
