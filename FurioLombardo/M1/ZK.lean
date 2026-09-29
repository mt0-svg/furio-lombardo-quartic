import FurioLombardo.M1.Kron
import FurioLombardo.M1.DataField

/-!
# The lattice spanned by PARI's integral basis of K21, and the K21 Kronecker test

`zkNum` (DataField.lean) lists the power basis numerators of the 21 elements of PARI's integral
basis `zk` over the common denominator `Dz`. An element of K21 is given by its integer coordinates
`a` on this basis: `zkE a = Σ a_j w_j` with `w_j = zkNum_j(θ) / Dz`. Nothing here assumes that
`zk` is a ℤ-basis of `𝓞 K21`: integrality of the `w_j` comes from the multiplication table
(ZKInt.lean), and only the inclusion `span ℤ (w_j) ⊆ 𝓞 K21` is used.

`evK e` is the value in K21 of a Kronecker expression over these atoms; `evK_eq_of_check` turns
a kernel computation into an identity in K21.
-/

namespace FurioLombardo.M1

open Polynomial Kron

/-- `Dz⁻¹` in K21. -/
noncomputable def dInv : K21 := (Dz : K21)⁻¹

/-- The value in K21 of an expression over the integral basis. -/
noncomputable def evK (e : KE) : K21 := KE.ev zkNum θ dInv e

/-- The element of K21 with zk coordinates `a`. -/
noncomputable def zkE (a : List ℤ) : K21 := evK (.lin a)

/-- Unit vector `e_i` of length 21. -/
def unitL (i : ℕ) : List ℤ := (List.range 21).map (fun k => if k = i then 1 else 0)

/-- The `j`-th element of PARI's integral basis. -/
noncomputable def wK (j : ℕ) : K21 := zkE (unitL j)

/-- Coefficient bound for the atoms used by every K21 check. -/
def zkWb : ℕ := 10 ^ 25

/-- The Kronecker test for K21 at `N = 2 ^ k`. -/
def checkK (k : ℕ) (e : KE) : Bool := KE.check zkNum Dz fL 21 zkWb k e

theorem Dz_ne_zero : (Dz : K21) ≠ 0 := by
  have : (Dz : ℕ) ≠ 0 := by decide
  exact_mod_cast this

theorem dInv_mul : dInv * (Dz : K21) = 1 := inv_mul_cancel₀ Dz_ne_zero

theorem ofListL_fL : ofListL fL = fZ := by
  simp only [ofListL, fL, fZ]
  simp only [map_neg, map_ofNat, map_one, map_zero, eq_intCast, Int.cast_ofNat, C_neg]
  ring

/-- `θ` is a root of the coefficient list `fL`. -/
theorem evalL_θ_fL : evalL θ fL = 0 := by
  rw [← evalL_ofListL, ofListL_fL]
  have h : (fZ.map (Int.castRingHom ℚ)).eval₂ (AdjoinRoot.of fQ) θ = 0 := AdjoinRoot.eval₂_root fQ
  rw [eval₂_map] at h
  convert h using 2
  exact RingHom.ext_int _ _

theorem zkNum_length : ∀ W ∈ zkNum, W.length ≤ 21 := by decide +kernel

theorem zkNum_bound : ∀ W ∈ zkNum, ∀ x ∈ W, x.natAbs ≤ zkWb := by decide +kernel

theorem zkNum_len : zkNum.length = 21 := by decide +kernel
/-- **Identities in K21 from the kernel.** -/
theorem evK_eq_zero_of_check (k : ℕ) (e : KE) (h : checkK k e = true) : evK e = 0 :=
  KE.ev_eq_zero_of_check fL 21 zkWb k zkNum_length zkNum_bound θ dInv evalL_θ_fL dInv_mul e h

theorem evK_eq_of_check (k : ℕ) (e f : KE) (h : checkK k (.sub e f) = true) : evK e = evK f :=
  KE.ev_eq_of_check fL 21 zkWb k zkNum_length zkNum_bound θ dInv evalL_θ_fL dInv_mul e f h

@[simp] theorem evK_lin (a : List ℤ) : evK (.lin a) = zkE a := rfl
@[simp] theorem evK_int (m : ℤ) : evK (.int m) = m := rfl
@[simp] theorem evK_add (e f : KE) : evK (.add e f) = evK e + evK f := rfl
@[simp] theorem evK_sub (e f : KE) : evK (.sub e f) = evK e - evK f := rfl
@[simp] theorem evK_mul (e f : KE) : evK (.mul e f) = evK e * evK f := rfl

theorem evK_pow (e : KE) (n : ℕ) : evK (e.pow n) = evK e ^ n := KE.ev_pow θ dInv e n

theorem evK_prod (l : List KE) : evK (KE.prod l) = (l.map evK).prod := KE.ev_prod θ dInv l

theorem evK_sum (l : List KE) : evK (KE.sum l) = (l.map evK).sum := KE.ev_sum θ dInv l


theorem dot_eq_sum {R : Type*} [CommRing R] : ∀ (a : List ℤ) (vs : List R),
    dot a vs = ∑ k ∈ Finset.range (min a.length vs.length), (a.getD k 0 : R) * vs.getD k 0
  | c :: a, v :: vs => by
    rw [dot, dot_eq_sum a vs, List.length_cons, List.length_cons, Nat.succ_min_succ,
      Finset.sum_range_succ']
    simp [add_comm]
  | [], _ => by simp [dot]
  | _ :: _, [] => by simp [dot]

theorem mul_dot {R : Type*} [CommRing R] (x : R) : ∀ (a : List ℤ) (vs : List R),
    x * dot a vs = dot a (vs.map (x * ·))
  | c :: a, v :: vs => by rw [dot, List.map_cons, dot, ← mul_dot x a vs]; ring
  | [], _ => by simp [dot]
  | _ :: _, [] => by simp [dot]

/-- The basis element `w_j` as the value of its numerator. -/
noncomputable def wv (W : List ℤ) : K21 := dInv * evalL θ W

theorem zkE_eq_dot (a : List ℤ) : zkE a = dot a (zkNum.map wv) := by
  simp only [zkE, evK, KE.ev, KE.evalL_combo, mul_dot, List.map_map]
  rfl

theorem zkE_eq_sum' (a : List ℤ) :
    zkE a = ∑ i ∈ Finset.range (min a.length 21), (a.getD i 0 : K21) * wv (zkNum.getD i []) := by
  rw [zkE_eq_dot, dot_eq_sum, List.length_map, zkNum_len]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← List.getD_map (f := wv)]
  simp [wv]

theorem getD_unitL (i k : ℕ) (hk : k < 21) : (unitL i).getD k 0 = if k = i then 1 else 0 := by
  simp [unitL, List.getD_eq_getElem?_getD, hk]

theorem wK_eq (j : ℕ) (hj : j < 21) : wK j = wv (zkNum.getD j []) := by
  rw [wK, zkE_eq_sum']
  have hl : (unitL j).length = 21 := by simp [unitL]
  rw [hl, min_self]
  rw [Finset.sum_eq_single j]
  · rw [getD_unitL j j hj]; simp
  · intro b hb hbj
    rw [getD_unitL j b (Finset.mem_range.mp hb)]; simp [hbj]
  · intro h; exact absurd (Finset.mem_range.mpr hj) h

theorem zkE_eq_sum (a : List ℤ) :
    zkE a = ∑ i ∈ Finset.range (min a.length 21), (a.getD i 0 : K21) * wK i := by
  rw [zkE_eq_sum']
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [wK_eq i (by simp at hi; omega)]

theorem zkE_mem_span (a : List ℤ) :
    zkE a ∈ Submodule.span ℤ (Set.range fun i : Fin 21 => wK i) := by
  rw [zkE_eq_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hi' : i < 21 := by simp at hi; omega
  rw [← zsmul_eq_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi'⟩, rfl⟩)

end FurioLombardo.M1
