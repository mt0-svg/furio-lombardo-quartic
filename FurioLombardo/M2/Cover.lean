import Mathlib.Data.Nat.Prime.Basic
import FurioLombardo.M2.Check

/-!
# Coverage of the blocks of integers (lane M2)

`coverCheck lo len ps = true` says that every integer of `[lo, lo + len)` is below 2, special
(2, 7, 45613), has a proper factor among the primes up to 337, or belongs to `ps`. Hence every
non-special prime of the block has a record, and `AllTrue recs` makes its check succeed.
-/

namespace FurioLombardo.M2

theorem coverCheck_spec : ∀ (len n : ℕ) (ps : List ℕ), coverCheck n len ps = true →
    ∀ m, n ≤ m → m < n + len →
      m < 2 ∨ isSpecial m = true ∨ hasSmallFactor m = true ∨ m ∈ ps
  | 0, n, ps, _, m, h1, h2 => by omega
  | len + 1, n, [], h, m, h1, h2 => by
    simp only [coverCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rcases h.1 with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact coverCheck_spec len (n + 1) [] h.2 m hlt (by omega)
  | len + 1, n, q :: qs, h, m, h1, h2 => by
    unfold coverCheck at h
    split_ifs at h with hq
    · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact Or.inr (Or.inr (Or.inr (by simp at hq; simp [hq])))
      · rcases coverCheck_spec len (n + 1) qs h m hlt (by omega) with h' | h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inr (Or.inr (List.mem_cons_of_mem q h')))
    · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · rcases h.1 with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · exact coverCheck_spec len (n + 1) (q :: qs) h.2 m hlt (by omega)

theorem smallPrimes_ge_two : ∀ q ∈ smallPrimes, 2 ≤ q := by decide

theorem not_hasSmallFactor {p : ℕ} (hp : p.Prime) : hasSmallFactor p = false := by
  unfold hasSmallFactor
  rw [List.any_eq_false]
  intro q hq h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hdvd : q ∣ p := Nat.dvd_of_mod_eq_zero h.2
  rcases hp.eq_one_or_self_of_dvd q hdvd with h1 | h1
  · have := smallPrimes_ge_two q hq; omega
  · omega

theorem AllTrue_mem : ∀ (recs : List (ℕ × ℕ)), AllTrue recs → ∀ x ∈ recs, checkPrime x.1 x.2 = true
  | [], _, _, hx => absurd hx (by simp)
  | y :: l, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact AllTrue_mem l h.2 x hx

/-- Every non-special prime of a covered block has a successful record. -/
theorem cover_sound (lo len : ℕ) (recs : List (ℕ × ℕ))
    (hcov : coverCheck lo len (recs.map Prod.fst) = true) (hok : AllTrue recs) (p : ℕ)
    (hp : p.Prime) (h1 : lo ≤ p) (h2 : p < lo + len) (hs : isSpecial p = false) :
    ∃ N, checkPrime p N = true := by
  rcases coverCheck_spec len lo _ hcov p h1 h2 with h | h | h | h
  · exact absurd h (by have := hp.two_le; omega)
  · rw [hs] at h; exact absurd h (by simp)
  · rw [not_hasSmallFactor hp] at h; exact absurd h (by simp)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    exact ⟨x.2, AllTrue_mem recs hok x hx⟩

end FurioLombardo.M2
