import FurioLombardo.Discharge.SelmerBasis.SUnitTower
import FurioLombardo.Discharge.SelmerBasis.SUnitDefs

/-!
# Polynomial values in `L42` and `N84` from a table of powers (kernel checks)

For `A = D α` with a table `P` of coordinates of `B A^i` (`B = 1` in practice), the coordinates
`sumPL D n cs P = Σ_i c_i D^(n-i) P_i` evaluate to `B D^n · pK cs (α)` (`evL_sumPL`, and `evN_sumPN`
in `N84`), for `cs` of length at most `n + 1`. With `mkL`, `mkN` read as coordinates (`mkL_eq_evL`,
`mkN_eq_evN`), an identity `pK cs (α) = t` in `L42` reduces to one `checkLC` of
`sumPL D n cs P` against `D^n m · t` (`aeval_pQ_of_checkL`).
-/

namespace FurioLombardo.Discharge.SelmerBasis.Tower

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis

/-! ## Sums against a table -/

/-- `Σ_i c_i D^(n-i) P_i` in `L42` coordinates. -/
def sumPL (D : ℕ) : ℕ → List KE → List LC → LC
  | _, [], _ => zeroLC
  | _, _ :: _, [] => zeroLC
  | n, c :: cs, p :: P => addLC (smulLC (.mul c (.int ((D ^ n : ℕ) : ℤ))) p) (sumPL D (n - 1) cs P)

/-- `Σ_i c_i D^(n-i) P_i` in `N84` coordinates. -/
def sumPN (D : ℕ) : ℕ → List KE → List NC → NC
  | _, [], _ => zeroNC
  | _, _ :: _, [] => zeroNC
  | n, c :: cs, p :: P => addNC (smulNC (.mul c (.int ((D ^ n : ℕ) : ℤ))) p) (sumPN D (n - 1) cs P)

theorem evL_sumPL (D : ℕ) (α : L42) :
    ∀ (cs : List KE) (n : ℕ) (P : List LC) (B : L42), cs.length ≤ n + 1 →
      cs.length ≤ P.length →
      (∀ i, i < cs.length → evL (P.getD i zeroLC) = B * (algebraMap K21 L42 D * α) ^ i) →
      evL (sumPL D n cs P) = B * algebraMap K21 L42 ((D : K21) ^ n) * aeval α (pK cs)
  | [], n, P, B, _, _, _ => by
    cases P <;> simp [sumPL]
  | c :: cs, n, [], B, _, hP, _ => by simp at hP
  | c :: cs, n, p :: P, B, hn, hP, hT => by
    have h0 : evL p = B := by simpa using hT 0 (by simp)
    have hT' : ∀ i, i < cs.length →
        evL (P.getD i zeroLC) = (B * (algebraMap K21 L42 D * α)) * (algebraMap K21 L42 D * α) ^ i := by
      intro i hi
      have := hT (i + 1) (by simp only [List.length_cons]; omega)
      simp only [List.getD_cons_succ] at this
      rw [this, pow_succ]
      ring
    have ih := evL_sumPL D α cs (n - 1) P (B * (algebraMap K21 L42 D * α)) (by simp only [List.length_cons] at hn; omega)
      (by simp only [List.length_cons] at hP; omega) hT'
    simp only [sumPL, evL_addLC, evL_smulLC, evK_mul, evK_int, h0, ih, pK_cons, map_add, map_mul,
      aeval_C, aeval_X, Nat.cast_pow, Int.cast_pow, Int.cast_natCast]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hcs : cs = [] := by
        simp only [List.length_cons] at hn; exact List.eq_nil_of_length_eq_zero (by omega)
      subst hcs
      simp only [pK_nil, map_zero, mul_zero, add_zero, pow_zero, map_one, mul_one]
      ring
    · have hpow : (D : K21) ^ n = D * D ^ (n - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hpow, map_mul]
      ring

theorem evN_sumPN (D : ℕ) (β : N84) :
    ∀ (cs : List KE) (n : ℕ) (P : List NC) (B : N84), cs.length ≤ n + 1 →
      cs.length ≤ P.length →
      (∀ i, i < cs.length → evN (P.getD i zeroNC) = B * (algebraMap K21 N84 D * β) ^ i) →
      evN (sumPN D n cs P) = B * algebraMap K21 N84 ((D : K21) ^ n) * aeval β (pK cs)
  | [], n, P, B, _, _, _ => by
    cases P <;> simp [sumPN]
  | c :: cs, n, [], B, _, hP, _ => by simp at hP
  | c :: cs, n, p :: P, B, hn, hP, hT => by
    have h0 : evN p = B := by simpa using hT 0 (by simp)
    have hT' : ∀ i, i < cs.length →
        evN (P.getD i zeroNC) = (B * (algebraMap K21 N84 D * β)) * (algebraMap K21 N84 D * β) ^ i := by
      intro i hi
      have := hT (i + 1) (by simp only [List.length_cons]; omega)
      simp only [List.getD_cons_succ] at this
      rw [this, pow_succ]
      ring
    have ih := evN_sumPN D β cs (n - 1) P (B * (algebraMap K21 N84 D * β)) (by simp only [List.length_cons] at hn; omega)
      (by simp only [List.length_cons] at hP; omega) hT'
    simp only [sumPN, evN_addNC, evN_smulNC, evK_mul, evK_int, h0, ih, pK_cons, map_add, map_mul,
      aeval_C, aeval_X, Nat.cast_pow, Int.cast_pow, Int.cast_natCast]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hcs : cs = [] := by
        simp only [List.length_cons] at hn; exact List.eq_nil_of_length_eq_zero (by omega)
      subst hcs
      simp only [pK_nil, map_zero, mul_zero, add_zero, pow_zero, map_one, mul_one]
      ring
    · have hpow : (D : K21) ^ n = D * D ^ (n - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hpow, map_mul]
      ring

/-! ## From one check to a value of `pQ` -/

theorem aeval_pQ_of_evL {D m n : ℕ} (hD : D ≠ 0) (hm : m ≠ 0) {α : L42} {cs : List KE}
    {P : List LC} (hn : cs.length ≤ n + 1) (hP : cs.length ≤ P.length)
    (hT : ∀ i, i < cs.length → evL (P.getD i zeroLC) = (algebraMap K21 L42 D * α) ^ i) {t : L42}
    (h : evL (sumPL D n cs P) = algebraMap K21 L42 (((D ^ n * m : ℕ) : ℤ) : K21) * t) :
    aeval α (pQ m cs) = t := by
  have hs := evL_sumPL D α cs n P 1 hn hP (by simpa using hT)
  have e1 : (((D ^ n * m : ℕ) : ℤ) : K21) = (D : K21) ^ n * m := by push_cast; ring
  rw [h, e1, map_mul, one_mul, mul_assoc] at hs
  have hD' : algebraMap K21 L42 ((D : K21) ^ n) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (pow_ne_zero _ (natCast_ne_zero hD))
  have hm' : algebraMap K21 L42 (m : K21) ≠ 0 := (_root_.map_ne_zero _).mpr (natCast_ne_zero hm)
  have hs' : aeval α (pK cs) = algebraMap K21 L42 (m : K21) * t := (mul_left_cancel₀ hD' hs).symm
  rw [pQ, map_mul, aeval_C]
  rw [hs', ← mul_assoc, ← map_mul, inv_mul_cancel₀ (natCast_ne_zero hm), map_one, one_mul]

theorem aeval_pQ_of_evN {D m n : ℕ} (hD : D ≠ 0) (hm : m ≠ 0) {β : N84} {cs : List KE}
    {P : List NC} (hn : cs.length ≤ n + 1) (hP : cs.length ≤ P.length)
    (hT : ∀ i, i < cs.length → evN (P.getD i zeroNC) = (algebraMap K21 N84 D * β) ^ i) {t : N84}
    (h : evN (sumPN D n cs P) = algebraMap K21 N84 (((D ^ n * m : ℕ) : ℤ) : K21) * t) :
    aeval β (pQ m cs) = t := by
  have hs := evN_sumPN D β cs n P 1 hn hP (by simpa using hT)
  have e1 : (((D ^ n * m : ℕ) : ℤ) : K21) = (D : K21) ^ n * m := by push_cast; ring
  rw [h, e1, map_mul, one_mul, mul_assoc] at hs
  have hD' : algebraMap K21 N84 ((D : K21) ^ n) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (pow_ne_zero _ (natCast_ne_zero hD))
  have hm' : algebraMap K21 N84 (m : K21) ≠ 0 := (_root_.map_ne_zero _).mpr (natCast_ne_zero hm)
  have hs' : aeval β (pK cs) = algebraMap K21 N84 (m : K21) * t := (mul_left_cancel₀ hD' hs).symm
  rw [pQ, map_mul, aeval_C]
  rw [hs', ← mul_assoc, ← map_mul, inv_mul_cancel₀ (natCast_ne_zero hm), map_one, one_mul]

/-- The check form of `aeval_pQ_of_evL`: `sumPL` against `(D^n m) · t`. -/
theorem aeval_pQ_of_checkL {k D m n : ℕ} (hD : D ≠ 0) (hm : m ≠ 0) {α : L42} {cs : List KE}
    {P : List LC} (hn : cs.length ≤ n + 1) (hP : cs.length ≤ P.length)
    (hT : ∀ i, i < cs.length → evL (P.getD i zeroLC) = (algebraMap K21 L42 D * α) ^ i) {t : LC}
    (h : checkLC k (sumPL D n cs P) (smulLC (.int ((D ^ n * m : ℕ) : ℤ)) t) = true) :
    aeval α (pQ m cs) = evL t := by
  refine aeval_pQ_of_evL hD hm hn hP hT ?_
  rw [evL_eq_of_checkLC h, evL_smulLC, evK_int]

theorem aeval_pQ_of_checkN {k D m n : ℕ} (hD : D ≠ 0) (hm : m ≠ 0) {β : N84} {cs : List KE}
    {P : List NC} (hn : cs.length ≤ n + 1) (hP : cs.length ≤ P.length)
    (hT : ∀ i, i < cs.length → evN (P.getD i zeroNC) = (algebraMap K21 N84 D * β) ^ i) {t : NC}
    (h : checkNC k (sumPN D n cs P) (smulNC (.int ((D ^ n * m : ℕ) : ℤ)) t) = true) :
    aeval β (pQ m cs) = evN t := by
  refine aeval_pQ_of_evN hD hm hn hP hT ?_
  rw [evN_eq_of_checkNC h, evN_smulNC, evK_int]

/-! ## Reading `mkL`, `mkN` as coordinates -/

theorem mkL_eq_evL (l : List (List ℤ)) : mkL l = evL (ofL l) := rfl

theorem mkN_eq_evN (l : List (List ℤ)) : mkN l = evN (ofN l) := rfl

end FurioLombardo.Discharge.SelmerBasis.Tower
