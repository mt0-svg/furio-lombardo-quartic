import FurioLombardo.M1.SqCond
import FurioLombardo.M1.DataSqrt

/-!
# The good prime sieve: blocks, certificates and one parity row per ring

The 32 rings of DataSieve.lean come in six blocks, one per good prime `p = 5, 11, 13, 17, 19, 23`
(`blkP t`, offset `blkOff t`, size `blkCnt t`). The kernel checks, per block, the ring certificates
(`ringOK`) and, for each normalized point `P` of `C(F_p)` in `sievePts` and each ring of the block,
the character of the chosen conic at `P` (`pointOKt`); per prime, that `sievePts` contains every
normalized point of `C(F_p)` (`ptsOKp`).

* `ring_row`: if `SqCond a e` holds and `a ≡ λ P (mod p)` with `λ ≠ 0`, the ring gives the parity
  `β + Σ_i e_i b_i ≡ 0 (mod 2)`, where `β` is the character bit of the chosen conic at `P`.
* `sum_bz_of_even`: the same relation in `ZMod 2`.
* `exists_pt`: a primitive integer point of `C` is `λ P` modulo `p` for a listed `P`.
-/

namespace FurioLombardo.M1

open NumberField

/-! ## Accessors -/

/-- The good prime of block `t`. -/
def blkP (t : ℕ) : ℕ := [5, 11, 13, 17, 19, 23].getD t 0

/-- The index of the first ring of block `t`. -/
def blkOff (t : ℕ) : ℕ := (sieveBlk.getD t (0, 0)).1

/-- The number of rings of block `t`. -/
def blkCnt (t : ℕ) : ℕ := (sieveBlk.getD t (0, 0)).2

/-- Lower coefficients of the modulus of ring `r`. -/
def rGl (r : ℕ) : List ℤ := (sieveRings.getD r (0, [], 0, 0)).2.1

/-- `DB⁻¹ mod p` for ring `r`. -/
def rUB (r : ℕ) : ℤ := (sieveRings.getD r (0, [], 0, 0)).2.2.1

/-- `Dz⁻¹ mod p` for ring `r`. -/
def rUD (r : ℕ) : ℤ := (sieveRings.getD r (0, [], 0, 0)).2.2.2

/-- Residues of the generators in ring `r`. -/
def rGen (r : ℕ) : List (List ℤ) := sieveGen.getD r []

/-- Character bits of the generators in ring `r`. -/
def rBits (r : ℕ) : List Bool := sieveBits.getD r []

/-- Residues of the conic coefficients in ring `r`. -/
def rQ (r : ℕ) : List (List (List ℤ)) := sieveQ.getD r []

/-- The non-residue of ring `r`. -/
def rNon (r : ℕ) : List ℤ := sieveNon.getD r []

/-- The certificate of ring `j` of block `t`. -/
def ringOKt (t j : ℕ) : Bool :=
  ringOK (blkP t) (rGl (blkOff t + j)) (rUB (blkOff t + j)) (rUD (blkOff t + j))
    (rGen (blkOff t + j)) (rBits (blkOff t + j)) (rQ (blkOff t + j)) (rNon (blkOff t + j))
    (sieveGY.getD (blkOff t + j) []) (sieveGZ.getD (blkOff t + j) [])

/-- The listed points of block `t`. -/
def ptsOf (t : ℕ) : List (List ℤ) := sievePts.getD t []

/-- Point `q` of block `t`. -/
def ptL (t q : ℕ) : List ℤ := (ptsOf t).getD q []

/-- The conic index and character bit of point `q` of block `t` in ring `j` of the block. -/
def choice (t q j : ℕ) : ℕ × Bool := ((sieveChoice.getD t []).getD q []).getD j (0, false)

/-- The character of the chosen conic at point `q` in ring `j` of block `t`. -/
def pointOKt (t q j : ℕ) : Bool :=
  ((choice t q j).1 == 0 || (choice t q j).1 == 2) &&
  sqOK (blkP t) (rGl (blkOff t + j)) (rNon (blkOff t + j))
    (qevL (blkP t) ((rQ (blkOff t + j)).getD (choice t q j).1 []) (ptL t q)) (choice t q j).2
    (((sievePY.getD t []).getD q []).getD j []) (((sievePZ.getD t []).getD q []).getD j [])

/-- All the certificates of block `t`. -/
def blockOK (t : ℕ) : Bool :=
  (List.range (blkCnt t)).all fun j => ringOKt t j &&
    (List.range (ptsOf t).length).all fun q => pointOKt t q j

/-- `F` at an integer triple. -/
def FZ (x y z : ℤ) : ℤ := FurioLombardo.F x y z

/-- Completeness of a list of normalized points of `C(F_p)`. -/
def ptsOKp (p : ℕ) (pts : List (List ℤ)) : Bool :=
  ((List.range p).all fun x0 => (List.range p).all fun z0 =>
    FZ x0 1 z0 % p != 0 || pts.contains [(x0 : ℤ), 1, (z0 : ℤ)]) &&
  ((List.range p).all fun z0 => FZ 1 0 z0 % p != 0 || pts.contains [1, 0, (z0 : ℤ)]) &&
  pts.contains [0, 0, 1]

/-! ## One parity row per ring -/

theorem ring_row {p : ℕ} [Fact p.Prime] {gl : List ℤ} {uB uD : ℤ} {gen : List (List ℤ)}
    {bits : List Bool} {qd : List (List (List ℤ))} {n : List ℤ} {gy gz : List (List ℤ)}
    (hok : ringOK p gl uB uD gen bits qd n gy gz = true) (a : Fin 3 → ℤ) (e : Fin 18 → Bool)
    (hsq : SqCond a e) (P : List ℤ) (lam : ZMod p) (hlam : lam ≠ 0)
    (ha : ∀ j : Fin 3, ((a j : ℤ) : ZMod p) = lam * ((P.getD j 0 : ℤ) : ZMod p))
    (ci : ℕ) (β : Bool) (hci : ci = 0 ∨ ci = 2) (y z : List ℤ)
    (hc : sqOK p gl n (qevL p (qd.getD ci []) P) β y z = true) :
    Even (β.toNat + ∑ i : Fin 18, if e i && bits.getD i false then 1 else 0) := by
  have F := RingFacts.of_ok hok
  have hci3 : ci < 3 := by omega
  let i : Fin 3 := ⟨ci, hci3⟩
  have hi : (i : ℕ) ∈ ([0, 2] : List ℕ) := by
    rcases hci with h | h <;> simp [i, h]
  have hpow := F.point_pow a P lam hlam ha i hi β y z hc
  have hne := F.ne_zero_of_pow _ β hpow
  have hi' : i = 0 ∨ i = 2 := by
    rcases hci with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  obtain ⟨s, hs⟩ := hsq i hi' hne
  exact F.parity e (qO i a) s hs β hpow

/-- A bit as an element of `ZMod 2`. -/
def bz (b : Bool) : ZMod 2 := if b then 1 else 0

theorem sum_bz_of_even (β : Bool) (b e : Fin 18 → Bool)
    (h : Even (β.toNat + ∑ i : Fin 18, if e i && b i then 1 else 0)) :
    ∑ i : Fin 18, bz (b i) * bz (e i) = bz β := by
  have h2 := (ZMod.natCast_eq_zero_iff_even (n := β.toNat + ∑ i : Fin 18,
    if e i && b i then 1 else 0)).mpr h
  push_cast at h2
  have hs : ∑ i : Fin 18, bz (b i) * bz (e i) =
      ∑ i : Fin 18, (if e i && b i then 1 else 0 : ZMod 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    cases e i <;> cases b i <;> simp [bz]
  rw [hs]
  have hb : ((β.toNat : ℕ) : ZMod 2) = bz β := by cases β <;> simp [bz]
  rw [hb] at h2
  have := eq_neg_of_add_eq_zero_right h2
  rw [this]
  cases β <;> simp [bz]

/-! ## Normalized points modulo `p` -/

theorem F_intCast_zmod {p : ℕ} (x y z : ℤ) :
    ((FurioLombardo.F x y z : ℤ) : ZMod p) =
      FurioLombardo.F (x : ZMod p) (y : ZMod p) (z : ZMod p) := by
  simp [FurioLombardo.F]

theorem F_smul {R : Type*} [CommRing R] (l x y z : R) :
    FurioLombardo.F (l * x) (l * y) (l * z) = l ^ 4 * FurioLombardo.F x y z := by
  simp only [FurioLombardo.F]; ring

theorem mod_eq_zero_of_zmod {p : ℕ} (n : ℤ) (h : ((n : ℤ) : ZMod p) = 0) : n % (p : ℤ) = 0 :=
  Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp h)

theorem contains_of_all {p : ℕ} {pts : List (List ℤ)} {l : List ℤ} {n : ℤ}
    (h : (n % (p : ℤ) != 0 || pts.contains l) = true) (hn : n % (p : ℤ) = 0) : l ∈ pts := by
  rw [hn] at h
  simpa using h

theorem exists_idx {pts : List (List ℤ)} {l : List ℤ} (h : l ∈ pts) :
    ∃ q < pts.length, pts.getD q [] = l := by
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem h
  exact ⟨q, hq, by simp [List.getD_eq_getElem?_getD, hq]⟩

/-- **A primitive point of `C` modulo `p` is a nonzero multiple of a listed point.** -/
theorem exists_pt (p : ℕ) [hp : Fact p.Prime] (pts : List (List ℤ)) (hok : ptsOKp p pts = true)
    (a r : Fin 3 → ℤ) (hr : ∑ j, r j * a j = 1)
    (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0) :
    ∃ q < pts.length, ∃ lam : ZMod p, lam ≠ 0 ∧
      ∀ j : Fin 3, ((a j : ℤ) : ZMod p) = lam * (((pts.getD q []).getD j 0 : ℤ) : ZMod p) := by
  simp only [ptsOKp, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨h1, h2⟩, h3⟩ := hok
  set A : Fin 3 → ZMod p := fun j => ((a j : ℤ) : ZMod p) with hA
  have hFA : FurioLombardo.F (A 0) (A 1) (A 2) = 0 := by
    simp only [hA]
    rw [← F_intCast_zmod, hF, Int.cast_zero]
  have hnz : ¬ (A 0 = 0 ∧ A 1 = 0 ∧ A 2 = 0) := by
    rintro ⟨e0, e1, e2⟩
    have := congrArg (fun n : ℤ => (n : ZMod p)) hr
    simp only [Fin.sum_univ_three] at this
    push_cast at this
    simp only [hA] at e0 e1 e2
    rw [e0, e1, e2] at this
    simp at this
  by_cases hA1 : A 1 = 0
  · by_cases hA0 : A 0 = 0
    · -- the point `(0 : 0 : 1)`
      have hA2 : A 2 ≠ 0 := fun h => hnz ⟨hA0, hA1, h⟩
      obtain ⟨q, hq, hget⟩ := exists_idx (by simpa using h3)
      refine ⟨q, hq, A 2, hA2, fun j => ?_⟩
      rw [hget]
      fin_cases j
      · simpa using hA0
      · simpa using hA1
      · simp [hA]
    · -- the chart `(1 : 0 : z)`
      set z0 := (A 2 * (A 0)⁻¹).val with hz0
      have hz : ((z0 : ℕ) : ZMod p) = A 2 * (A 0)⁻¹ := by rw [hz0, ZMod.natCast_zmod_val]
      have hFz : FurioLombardo.F (1 : ZMod p) 0 (A 2 * (A 0)⁻¹) = 0 := by
        have hl : FurioLombardo.F (A 0 * 1) (A 0 * 0) (A 0 * (A 2 * (A 0)⁻¹)) = 0 := by
          have hF0 : FurioLombardo.F (A 0) 0 (A 2) = 0 := hA1 ▸ hFA
          rw [mul_one, mul_zero, show A 0 * (A 2 * (A 0)⁻¹) = A 2 by field_simp]
          exact hF0
        rw [F_smul] at hl
        exact (mul_eq_zero.mp hl).resolve_left (pow_ne_zero _ hA0)
      have hmod : FZ 1 0 (z0 : ℤ) % (p : ℤ) = 0 := by
        apply mod_eq_zero_of_zmod
        rw [FZ, F_intCast_zmod]
        push_cast
        rw [hz]; exact hFz
      have hmem := contains_of_all (h2 z0 (ZMod.val_lt _)) hmod
      obtain ⟨q, hq, hget⟩ := exists_idx hmem
      refine ⟨q, hq, A 0, hA0, fun j => ?_⟩
      rw [hget]
      fin_cases j
      · simp [hA]
      · simpa using hA1
      · show A 2 = A 0 * (((z0 : ℤ) : ℤ) : ZMod p)
        push_cast
        rw [hz]; field_simp
  · -- the chart `(x : 1 : z)`
    set x0 := (A 0 * (A 1)⁻¹).val with hx0
    set z0 := (A 2 * (A 1)⁻¹).val with hz0
    have hx : ((x0 : ℕ) : ZMod p) = A 0 * (A 1)⁻¹ := by rw [hx0, ZMod.natCast_zmod_val]
    have hz : ((z0 : ℕ) : ZMod p) = A 2 * (A 1)⁻¹ := by rw [hz0, ZMod.natCast_zmod_val]
    have hFz : FurioLombardo.F (A 0 * (A 1)⁻¹) (1 : ZMod p) (A 2 * (A 1)⁻¹) = 0 := by
      have e := F_smul (A 1) (A 0 * (A 1)⁻¹) 1 (A 2 * (A 1)⁻¹)
      rw [mul_one, show A 1 * (A 0 * (A 1)⁻¹) = A 0 by field_simp,
        show A 1 * (A 2 * (A 1)⁻¹) = A 2 by field_simp, hFA] at e
      exact (mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ hA1)
    have hmod : FZ (x0 : ℤ) 1 (z0 : ℤ) % (p : ℤ) = 0 := by
      apply mod_eq_zero_of_zmod
      rw [FZ, F_intCast_zmod]
      push_cast
      rw [hx, hz]; exact hFz
    have hmem := contains_of_all (h1 x0 (ZMod.val_lt _) z0 (ZMod.val_lt _)) hmod
    obtain ⟨q, hq, hget⟩ := exists_idx hmem
    refine ⟨q, hq, A 1, hA1, fun j => ?_⟩
    rw [hget]
    fin_cases j
    · show A 0 = A 1 * (((x0 : ℤ) : ℤ) : ZMod p)
      push_cast
      rw [hx]; field_simp
    · simp [hA]
    · show A 2 = A 1 * (((z0 : ℤ) : ℤ) : ZMod p)
      push_cast
      rw [hz]; field_simp

end FurioLombardo.M1
