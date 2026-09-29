import FurioLombardo.Discharge.SelmerBasis.SUnitMem

/-!
# The generators are independent modulo squares (piece (d))

Residue characters of SUnitData.lean: 29 primes `[p, t, s]` for `L42` (`chL`), 53 primes
`[p, t, s, t2]` for `N84` (`chN`), the character rows `RL`, `RN` on the generators and left
inverses `TL`, `TN`. The residue maps `ρL`, `ρN` of SUnitRes.lean are defined on the orders
`OL`, `ON`, whose images contain the generators (`ιL_mkOL`, `ιN_mkON`), and send squares of the
field lying in the order to squares. Kernel checks: the prime data (`goodL_all`, `goodN_all`),
one row per prime (`rowL_j`, `rowN_j`) and the left inverses (`leftInvL`, `leftInvN`); then
`indep_of_chars`.
-/

namespace FurioLombardo.Discharge.SelmerBasis

open NumberField FurioLombardo.M1 SU SUnitData

/-! ### The data -/

/-- Entry `i` of a character datum, as a natural number. -/
def chE (e : List ℤ) (i : ℕ) : ℕ := (e.getD i 0).toNat

def pL (j : ℕ) : ℕ := chE (chL.getD j []) 0
def tL (j : ℕ) : ℕ := chE (chL.getD j []) 1
def sL (j : ℕ) : ℕ := chE (chL.getD j []) 2
def RLf (j : ℕ) : ℕ := RL.getD j 0
def TLf (k : ℕ) : ℕ := TL.getD k 0

def pN (j : ℕ) : ℕ := chE (chN.getD j []) 0
def tN (j : ℕ) : ℕ := chE (chN.getD j []) 1
def sN (j : ℕ) : ℕ := chE (chN.getD j []) 2
def t2N (j : ℕ) : ℕ := chE (chN.getD j []) 3
def RNf (j : ℕ) : ℕ := RN.getD j 0
def TNf (k : ℕ) : ℕ := TN.getD k 0

def goodLj (j : ℕ) : Bool := goodL (pL j) (tL j) (sL j)
def goodNj (j : ℕ) : Bool := goodN (pN j) (tN j) (sN j) (t2N j)
def rowLj (j : ℕ) : Bool := rowL (pL j) (tL j) (sL j) (RLf j) 29 gL
def rowNj (j : ℕ) : Bool := rowN (pN j) (tN j) (sN j) (t2N j) (RNf j) 53 gN

/-! ### Kernel checks -/

theorem goodL_all : allLt goodLj 29 = true := by decide +kernel

theorem goodN_all : allLt goodNj 53 = true := by decide +kernel

theorem leftInvL : leftInvOK RLf 29 29 TLf = true := by decide +kernel

theorem leftInvN : leftInvOK RNf 53 53 TNf = true := by decide +kernel

theorem rowL_0 : rowLj 0 = true := by decide +kernel
theorem rowL_1 : rowLj 1 = true := by decide +kernel
theorem rowL_2 : rowLj 2 = true := by decide +kernel
theorem rowL_3 : rowLj 3 = true := by decide +kernel
theorem rowL_4 : rowLj 4 = true := by decide +kernel
theorem rowL_5 : rowLj 5 = true := by decide +kernel
theorem rowL_6 : rowLj 6 = true := by decide +kernel
theorem rowL_7 : rowLj 7 = true := by decide +kernel
theorem rowL_8 : rowLj 8 = true := by decide +kernel
theorem rowL_9 : rowLj 9 = true := by decide +kernel
theorem rowL_10 : rowLj 10 = true := by decide +kernel
theorem rowL_11 : rowLj 11 = true := by decide +kernel
theorem rowL_12 : rowLj 12 = true := by decide +kernel
theorem rowL_13 : rowLj 13 = true := by decide +kernel
theorem rowL_14 : rowLj 14 = true := by decide +kernel
theorem rowL_15 : rowLj 15 = true := by decide +kernel
theorem rowL_16 : rowLj 16 = true := by decide +kernel
theorem rowL_17 : rowLj 17 = true := by decide +kernel
theorem rowL_18 : rowLj 18 = true := by decide +kernel
theorem rowL_19 : rowLj 19 = true := by decide +kernel
theorem rowL_20 : rowLj 20 = true := by decide +kernel
theorem rowL_21 : rowLj 21 = true := by decide +kernel
theorem rowL_22 : rowLj 22 = true := by decide +kernel
theorem rowL_23 : rowLj 23 = true := by decide +kernel
theorem rowL_24 : rowLj 24 = true := by decide +kernel
theorem rowL_25 : rowLj 25 = true := by decide +kernel
theorem rowL_26 : rowLj 26 = true := by decide +kernel
theorem rowL_27 : rowLj 27 = true := by decide +kernel
theorem rowL_28 : rowLj 28 = true := by decide +kernel

theorem rowN_0 : rowNj 0 = true := by decide +kernel
theorem rowN_1 : rowNj 1 = true := by decide +kernel
theorem rowN_2 : rowNj 2 = true := by decide +kernel
theorem rowN_3 : rowNj 3 = true := by decide +kernel
theorem rowN_4 : rowNj 4 = true := by decide +kernel
theorem rowN_5 : rowNj 5 = true := by decide +kernel
theorem rowN_6 : rowNj 6 = true := by decide +kernel
theorem rowN_7 : rowNj 7 = true := by decide +kernel
theorem rowN_8 : rowNj 8 = true := by decide +kernel
theorem rowN_9 : rowNj 9 = true := by decide +kernel
theorem rowN_10 : rowNj 10 = true := by decide +kernel
theorem rowN_11 : rowNj 11 = true := by decide +kernel
theorem rowN_12 : rowNj 12 = true := by decide +kernel
theorem rowN_13 : rowNj 13 = true := by decide +kernel
theorem rowN_14 : rowNj 14 = true := by decide +kernel
theorem rowN_15 : rowNj 15 = true := by decide +kernel
theorem rowN_16 : rowNj 16 = true := by decide +kernel
theorem rowN_17 : rowNj 17 = true := by decide +kernel
theorem rowN_18 : rowNj 18 = true := by decide +kernel
theorem rowN_19 : rowNj 19 = true := by decide +kernel
theorem rowN_20 : rowNj 20 = true := by decide +kernel
theorem rowN_21 : rowNj 21 = true := by decide +kernel
theorem rowN_22 : rowNj 22 = true := by decide +kernel
theorem rowN_23 : rowNj 23 = true := by decide +kernel
theorem rowN_24 : rowNj 24 = true := by decide +kernel
theorem rowN_25 : rowNj 25 = true := by decide +kernel
theorem rowN_26 : rowNj 26 = true := by decide +kernel
theorem rowN_27 : rowNj 27 = true := by decide +kernel
theorem rowN_28 : rowNj 28 = true := by decide +kernel
theorem rowN_29 : rowNj 29 = true := by decide +kernel
theorem rowN_30 : rowNj 30 = true := by decide +kernel
theorem rowN_31 : rowNj 31 = true := by decide +kernel
theorem rowN_32 : rowNj 32 = true := by decide +kernel
theorem rowN_33 : rowNj 33 = true := by decide +kernel
theorem rowN_34 : rowNj 34 = true := by decide +kernel
theorem rowN_35 : rowNj 35 = true := by decide +kernel
theorem rowN_36 : rowNj 36 = true := by decide +kernel
theorem rowN_37 : rowNj 37 = true := by decide +kernel
theorem rowN_38 : rowNj 38 = true := by decide +kernel
theorem rowN_39 : rowNj 39 = true := by decide +kernel
theorem rowN_40 : rowNj 40 = true := by decide +kernel
theorem rowN_41 : rowNj 41 = true := by decide +kernel
theorem rowN_42 : rowNj 42 = true := by decide +kernel
theorem rowN_43 : rowNj 43 = true := by decide +kernel
theorem rowN_44 : rowNj 44 = true := by decide +kernel
theorem rowN_45 : rowNj 45 = true := by decide +kernel
theorem rowN_46 : rowNj 46 = true := by decide +kernel
theorem rowN_47 : rowNj 47 = true := by decide +kernel
theorem rowN_48 : rowNj 48 = true := by decide +kernel
theorem rowN_49 : rowNj 49 = true := by decide +kernel
theorem rowN_50 : rowNj 50 = true := by decide +kernel
theorem rowN_51 : rowNj 51 = true := by decide +kernel
theorem rowN_52 : rowNj 52 = true := by decide +kernel

theorem rowL_all (j : Fin 29) : rowLj j = true := by
  fin_cases j
  exacts [rowL_0, rowL_1, rowL_2, rowL_3, rowL_4, rowL_5, rowL_6, rowL_7, rowL_8, rowL_9, rowL_10, rowL_11, rowL_12, rowL_13, rowL_14, rowL_15, rowL_16, rowL_17, rowL_18, rowL_19, rowL_20, rowL_21, rowL_22, rowL_23, rowL_24, rowL_25, rowL_26, rowL_27, rowL_28]

theorem rowN_all (j : Fin 53) : rowNj j = true := by
  fin_cases j
  exacts [rowN_0, rowN_1, rowN_2, rowN_3, rowN_4, rowN_5, rowN_6, rowN_7, rowN_8, rowN_9, rowN_10, rowN_11, rowN_12, rowN_13, rowN_14, rowN_15, rowN_16, rowN_17, rowN_18, rowN_19, rowN_20, rowN_21, rowN_22, rowN_23, rowN_24, rowN_25, rowN_26, rowN_27, rowN_28, rowN_29, rowN_30, rowN_31, rowN_32, rowN_33, rowN_34, rowN_35, rowN_36, rowN_37, rowN_38, rowN_39, rowN_40, rowN_41, rowN_42, rowN_43, rowN_44, rowN_45, rowN_46, rowN_47, rowN_48, rowN_49, rowN_50, rowN_51, rowN_52]

theorem goodL_ok (j : Fin 29) : goodL (pL j) (tL j) (sL j) = true :=
  (allLt_iff goodLj 29).mp goodL_all j j.isLt

theorem goodN_ok (j : Fin 53) : goodN (pN j) (tN j) (sN j) (t2N j) = true :=
  (allLt_iff goodNj 53).mp goodN_all j j.isLt

/-! ### Independence -/

/-- **Piece (d), `L42`.** -/
theorem gensL_indep (e : Fin 29 → Bool) (he : IsSquare (subprod gensL e)) : ∀ s, e s = false := by
  have hp : ∀ j : Fin 29, Fact (pL j).Prime := fun j => ⟨goodK_prime (goodL_K (goodL_ok j))⟩
  refine indep_of_chars (hp := hp) ιL (fun s => mkOL (gL.getD s [])) (fun j => pL j)
    (fun j => goodK_ne_two (goodL_K (goodL_ok j))) (fun j => ρL (pL j) (tL j) (sL j) (goodL_ok j))
    (fun j X hX => isSquare_ρL (goodL_ok j) X hX) RLf
    (fun j s => rowL_spec (goodL_ok j) (rowL_all j) s) TLf leftInvL e ?_
  simp only [ιL_mkOL]; exact he

/-- **Piece (d), `N84`.** -/
theorem gensN_indep (e : Fin 53 → Bool) (he : IsSquare (subprod gensN e)) : ∀ s, e s = false := by
  have hp : ∀ j : Fin 53, Fact (pN j).Prime :=
    fun j => ⟨goodK_prime (goodL_K (goodN_L (goodN_ok j)))⟩
  refine indep_of_chars (hp := hp) ιN (fun s => mkON (gN.getD s [])) (fun j => pN j)
    (fun j => goodK_ne_two (goodL_K (goodN_L (goodN_ok j))))
    (fun j => ρN (pN j) (tN j) (sN j) (t2N j) (goodN_ok j))
    (fun j X hX => isSquare_ρN (goodN_ok j) X hX) RNf
    (fun j s => rowN_spec (goodN_ok j) (rowN_all j) s) TNf leftInvN e ?_
  simp only [ιN_mkON]; exact he

end FurioLombardo.Discharge.SelmerBasis
