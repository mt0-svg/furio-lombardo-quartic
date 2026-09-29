import FurioLombardo.M1.SieveBlocks

/-!
# The good prime sieve: the linear algebra over `F_2` and the combination check

`Mz` is the 32 x 18 character matrix of the generators (rows: rings, columns: generators) and `Lz`
the left inverse of DataSieve.lean (`hLM : Lz * Mz = 1`, kernel check). For an exponent vector `e`
with `Mz e = c`, `e = Lz c`. The vector `c` is made of one bit vector per prime, taken from the
list `sieveV` of the bit vectors of the points of `C(F_p)`; `comboOK` runs over all 128 choices
and checks that `e = Lz c` is a survivor whenever `Mz (Lz c) = c`.

Kernel checks: `hLM`, `comboOK_true`, `vecOK_true` (the bit vector of every listed point is in
`sieveV`), `ptsOK_true` (the lists of points are complete).
-/

namespace FurioLombardo.M1

/-- The character matrix. -/
def Mz : Matrix (Fin 32) (Fin 18) (ZMod 2) :=
  Matrix.of fun r i => bz ((sieveBits.getD r []).getD i false)

/-- The left inverse. -/
def Lz : Matrix (Fin 18) (Fin 32) (ZMod 2) :=
  Matrix.of fun i r => bz ((sieveL.getD i []).getD r false)

set_option maxRecDepth 100000 in
theorem hLM : Lz * Mz = 1 := by decide +kernel

/-- The block of ring `r`. -/
def blkOf (r : ℕ) : ℕ :=
  if r < 4 then 0 else if r < 7 then 1 else if r < 11 then 2 else if r < 15 then 3
  else if r < 19 then 4 else 5

theorem blkOf_spec : ∀ r : Fin 32, blkOf r < 6 ∧ blkOff (blkOf r) ≤ r ∧
    (r : ℕ) - blkOff (blkOf r) < blkCnt (blkOf r) := by decide

/-- The bit vector made of the `i t`-th vector of `sieveV` in each block `t`. -/
def comboVec (i : ℕ → ℕ) : Fin 32 → ZMod 2 := fun r =>
  bz (((sieveV.getD (blkOf r) []).getD (i (blkOf r)) []).getD (r - blkOff (blkOf r)) false)

/-- The survivors in `ZMod 2`. -/
def survZ (k : ℕ) : Fin 18 → ZMod 2 := fun i => bz (survE k i)

/-- The check for one choice. -/
def comboOKi (i : ℕ → ℕ) : Bool :=
  !(decide (Mz.mulVec (Lz.mulVec (comboVec i)) = comboVec i)) ||
    (List.range 8).any fun k => decide (Lz.mulVec (comboVec i) = survZ k)

/-- The choice given by six indices. -/
def idx6 (i0 i1 i2 i3 i4 i5 : ℕ) : ℕ → ℕ := fun t => [i0, i1, i2, i3, i4, i5].getD t 0

/-- The number of bit vectors of block `t`. -/
def nV (t : ℕ) : ℕ := (sieveV.getD t []).length

/-- All 128 choices. -/
def comboOK : Bool :=
  (List.range (nV 0)).all fun i0 => (List.range (nV 1)).all fun i1 =>
  (List.range (nV 2)).all fun i2 => (List.range (nV 3)).all fun i3 =>
  (List.range (nV 4)).all fun i4 => (List.range (nV 5)).all fun i5 =>
    comboOKi (idx6 i0 i1 i2 i3 i4 i5)

set_option maxRecDepth 100000 in
theorem comboOK_true : comboOK = true := by decide +kernel

theorem comboVec_congr (i i' : ℕ → ℕ) (h : ∀ t < 6, i t = i' t) : comboVec i = comboVec i' := by
  funext r
  simp only [comboVec, h _ (blkOf_spec r).1]

theorem comboOKi_of (i : ℕ → ℕ) (hi : ∀ t < 6, i t < nV t) : comboOKi i = true := by
  have h := comboOK_true
  simp only [comboOK, List.all_eq_true, List.mem_range] at h
  have e : comboVec i = comboVec (idx6 (i 0) (i 1) (i 2) (i 3) (i 4) (i 5)) := by
    apply comboVec_congr
    intro t ht
    interval_cases t <;> rfl
  have := h _ (hi 0 (by norm_num)) _ (hi 1 (by norm_num)) _ (hi 2 (by norm_num)) _
    (hi 3 (by norm_num)) _ (hi 4 (by norm_num)) _ (hi 5 (by norm_num))
  rw [comboOKi, e]
  exact this

/-- The bit vector of point `q` of block `t`. -/
def vecOf (t q : ℕ) : List Bool := ((sieveChoice.getD t []).getD q []).map Prod.snd

/-- The bit vector of every listed point is in `sieveV`. -/
def vecOK : Bool :=
  (List.range 6).all fun t => (List.range (ptsOf t).length).all fun q =>
    (sieveV.getD t []).contains (vecOf t q)

set_option maxRecDepth 100000 in
theorem vecOK_true : vecOK = true := by decide +kernel

/-- The lists of points are complete. -/
def ptsOK : Bool := (List.range 6).all fun t => ptsOKp (blkP t) (ptsOf t)

set_option maxRecDepth 100000 in
theorem ptsOK_true : ptsOK = true := by decide +kernel

theorem ptsOKp_of (t : ℕ) (ht : t < 6) : ptsOKp (blkP t) (ptsOf t) = true := by
  have h := ptsOK_true
  simp only [ptsOK, List.all_eq_true, List.mem_range] at h
  exact h t ht

theorem vec_mem (t q : ℕ) (ht : t < 6) (hq : q < (ptsOf t).length) :
    ∃ i < nV t, (sieveV.getD t []).getD i [] = vecOf t q := by
  have h := vecOK_true
  simp only [vecOK, List.all_eq_true, List.mem_range, List.contains_iff_mem] at h
  have hm := h t ht q hq
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hm
  refine ⟨i, hi, ?_⟩
  rw [List.getD_eq_getElem _ _ hi]
  exact e

end FurioLombardo.M1
