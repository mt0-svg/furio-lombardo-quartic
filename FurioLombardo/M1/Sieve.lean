import FurioLombardo.M1.SieveComb
import FurioLombardo.M1.SieveCheck0
import FurioLombardo.M1.SieveCheck1
import FurioLombardo.M1.SieveCheck2
import FurioLombardo.M1.SieveCheck3
import FurioLombardo.M1.SieveCheck4
import FurioLombardo.M1.SieveCheck5

/-!
# The good prime sieve

* `sieve_good`: if `SqCond a e` holds at a primitive integer point `a` of `C`, then `e` is one of
  the eight survivors `survE k`, `k < 8`.
* `gProd_eq_sq`: the eighteen generators are independent modulo squares.
* `exists_qO_ne_zero`: `Q1(a)` or `Q3(a)` is nonzero (from one ring above 5).

Each ring `r` of block `t` gives the row `(Mz e)_r = β_r`, where `β_r` is the character bit of the
chosen conic at the listed point `P_t` with `a ≡ λ P_t (mod p_t)` (`block_rows`); the bit vector of
`P_t` is one of `sieveV`, so `Mz e` is one of the 128 vectors `comboVec i`, and
`e = Lz (Mz e)` is a survivor by `comboOK`.
-/

namespace FurioLombardo.M1

open NumberField

theorem blockOK_of (t : ℕ) (ht : t < 6) : blockOK t = true := by
  interval_cases t
  exacts [blockOK_0, blockOK_1, blockOK_2, blockOK_3, blockOK_4, blockOK_5]

theorem fact_blkP (t : ℕ) (ht : t < 6) : Fact (blkP t).Prime :=
  ⟨by interval_cases t <;> norm_num [blkP]⟩

theorem blockOK_parts (t : ℕ) (ht : t < 6) (j : ℕ) (hj : j < blkCnt t) :
    ringOKt t j = true ∧ ∀ q < (ptsOf t).length, pointOKt t q j = true := by
  have hb := blockOK_of t ht
  simp only [blockOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hb
  exact hb j hj

/-- The exponent vector in `ZMod 2`. -/
def evz (e : Fin 18 → Bool) : Fin 18 → ZMod 2 := fun i => bz (e i)

theorem mulVec_Mz (e : Fin 18 → Bool) (r : Fin 32) :
    Mz.mulVec (evz e) r = ∑ i : Fin 18, bz ((rBits r).getD i false) * bz (e i) := by
  simp [Matrix.mulVec, dotProduct, Mz, rBits, evz]

theorem bz_injective : Function.Injective bz := by
  intro a b h
  cases a <;> cases b <;> simp_all [bz]

/-- **The rows of one block.** -/
theorem block_rows (t : ℕ) (ht : t < 6) (a r : Fin 3 → ℤ) (hr : ∑ j, r j * a j = 1)
    (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0) (e : Fin 18 → Bool) (hsq : SqCond a e) :
    ∃ q < (ptsOf t).length, ∀ j < blkCnt t,
      ∑ i : Fin 18, bz ((rBits (blkOff t + j)).getD i false) * bz (e i) =
        bz (choice t q j).2 := by
  haveI := fact_blkP t ht
  obtain ⟨q, hq, lam, hlam, ha⟩ := exists_pt (blkP t) (ptsOf t) (ptsOKp_of t ht) a r hr hF
  refine ⟨q, hq, fun j hj => ?_⟩
  obtain ⟨hring, hpts⟩ := blockOK_parts t ht j hj
  have hpt := hpts q hq
  simp only [pointOKt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hpt
  obtain ⟨hci, hsqok⟩ := hpt
  have h := ring_row hring a e hsq (ptL t q) lam hlam ha (choice t q j).1 (choice t q j).2 hci
    _ _ hsqok
  exact sum_bz_of_even _ (fun i => (rBits (blkOff t + j)).getD i false) e h

theorem getD_vecOf (t q j : ℕ) : (vecOf t q).getD j false = (choice t q j).2 := by
  rw [vecOf, choice, show false = (Prod.snd (0, false) : Bool) from rfl, List.getD_map]

/-- The index of the bit vector of the point of block `t`. -/
theorem block_vec (t : ℕ) (ht : t < 6) (a r : Fin 3 → ℤ) (hr : ∑ j, r j * a j = 1)
    (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0) (e : Fin 18 → Bool) (hsq : SqCond a e) :
    ∃ i < nV t, ∀ j < blkCnt t,
      ∑ i' : Fin 18, bz ((rBits (blkOff t + j)).getD i' false) * bz (e i') =
        bz (((sieveV.getD t []).getD i []).getD j false) := by
  obtain ⟨q, hq, hrow⟩ := block_rows t ht a r hr hF e hsq
  obtain ⟨i, hi, hv⟩ := vec_mem t q ht hq
  exact ⟨i, hi, fun j hj => by rw [hrow j hj, hv, getD_vecOf]⟩

/-- `Mz e` from the rows, block by block. -/
theorem mulVec_eq_comboVec (e : Fin 18 → Bool) (i : ℕ → ℕ)
    (h : ∀ t < 6, ∀ j < blkCnt t,
      ∑ i' : Fin 18, bz ((rBits (blkOff t + j)).getD i' false) * bz (e i') =
        bz (((sieveV.getD t []).getD (i t) []).getD j false)) :
    Mz.mulVec (evz e) = comboVec i := by
  funext r
  obtain ⟨h1, h2, h3⟩ := blkOf_spec r
  have e1 : blkOff (blkOf r) + ((r : ℕ) - blkOff (blkOf r)) = r := Nat.add_sub_cancel' h2
  rw [mulVec_Mz, comboVec, ← h _ h1 _ h3, e1]

theorem evz_eq (e : Fin 18 → Bool) : evz e = Lz.mulVec (Mz.mulVec (evz e)) := by
  rw [Matrix.mulVec_mulVec, hLM, Matrix.one_mulVec]

/-- **The good prime sieve.** -/
theorem sieve_good (a r : Fin 3 → ℤ) (hr : ∑ j, r j * a j = 1)
    (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0) (e : Fin 18 → Bool) (hsq : SqCond a e) :
    ∃ k < 8, e = survE k := by
  have H := fun t (ht : t < 6) => block_vec t ht a r hr hF e hsq
  classical
  let i : ℕ → ℕ := fun t => if ht : t < 6 then (H t ht).choose else 0
  have hi : ∀ t < 6, i t < nV t := fun t ht => by
    simp only [i, dif_pos ht]; exact (H t ht).choose_spec.1
  have hrow : ∀ t < 6, ∀ j < blkCnt t,
      ∑ i' : Fin 18, bz ((rBits (blkOff t + j)).getD i' false) * bz (e i') =
        bz (((sieveV.getD t []).getD (i t) []).getD j false) := fun t ht => by
    simp only [i, dif_pos ht]; exact (H t ht).choose_spec.2
  have hM := mulVec_eq_comboVec e i hrow
  have hL : Lz.mulVec (comboVec i) = evz e := by rw [← hM, ← evz_eq]
  have hc := comboOKi_of i hi
  simp only [comboOKi, hL, hM, decide_true, Bool.not_true, Bool.false_or, List.any_eq_true,
    List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨k, hk, hek⟩ := hc
  refine ⟨k, hk, funext fun j => bz_injective ?_⟩
  exact congrFun hek j

/-- **Independence of the generators modulo squares.** -/
theorem gProd_eq_sq (e : Fin 18 → Bool) (s : 𝓞 K21) (hs : gProd e = s ^ 2) :
    ∀ i, e i = false := by
  have hrow : ∀ t < 6, ∀ j < blkCnt t,
      ∑ i' : Fin 18, bz ((rBits (blkOff t + j)).getD i' false) * bz (e i') =
        bz (((sieveV.getD t []).getD 0 []).getD j false) * 0 := by
    intro t ht j hj
    haveI := fact_blkP t ht
    have F := RingFacts.of_ok (blockOK_parts t ht j hj).1
    have h := F.parity e 1 s (by rw [one_mul, hs]) false (by rw [map_one, one_pow]; rfl)
    rw [mul_zero]
    exact sum_bz_of_even false _ e h
  have hM : Mz.mulVec (evz e) = 0 := by
    funext r
    obtain ⟨h1, h2, h3⟩ := blkOf_spec r
    have e1 : blkOff (blkOf r) + ((r : ℕ) - blkOff (blkOf r)) = r := Nat.add_sub_cancel' h2
    rw [mulVec_Mz, Pi.zero_apply, ← e1, hrow _ h1 _ h3, mul_zero]
  have hz : evz e = 0 := by rw [evz_eq, hM, Matrix.mulVec_zero]
  intro i
  have := congrFun hz i
  simp only [evz, Pi.zero_apply, bz] at this
  cases h : e i
  · rfl
  · rw [h] at this; exact absurd this (by decide)

/-- **One of `Q1(a)`, `Q3(a)` is nonzero** (the chosen conic at the ring above 5). -/
theorem exists_qO_ne_zero (a r : Fin 3 → ℤ) (hr : ∑ j, r j * a j = 1)
    (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0) :
    ∃ i : Fin 3, (i = 0 ∨ i = 2) ∧ qO i a ≠ 0 := by
  haveI := fact_blkP 0 (by norm_num)
  obtain ⟨q, hq, lam, hlam, ha⟩ := exists_pt (blkP 0) (ptsOf 0) (ptsOKp_of 0 (by norm_num)) a r
    hr hF
  obtain ⟨hring, hpts⟩ := blockOK_parts 0 (by norm_num) 0 (by decide)
  have hpt := hpts q hq
  simp only [pointOKt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hpt
  obtain ⟨hci, hsqok⟩ := hpt
  have F := RingFacts.of_ok hring
  have hci3 : (choice 0 q 0).1 < 3 := by omega
  let i : Fin 3 := ⟨(choice 0 q 0).1, hci3⟩
  have hi : (i : ℕ) ∈ ([0, 2] : List ℕ) := by rcases hci with h | h <;> simp [i, h]
  have hpow := F.point_pow a (ptL 0 q) lam hlam ha i hi _ _ _ hsqok
  refine ⟨i, ?_, F.ne_zero_of_pow _ _ hpow⟩
  rcases hci with h | h
  · left; exact Fin.ext h
  · right; exact Fin.ext h

end FurioLombardo.M1
