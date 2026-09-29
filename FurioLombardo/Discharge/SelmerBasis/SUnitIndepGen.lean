import FurioLombardo.Discharge.SelmerBasis.Echelon
import FurioLombardo.M1.SelmerBound

/-!
# Independence modulo squares by residue characters (piece (d), generic part)

* `quad_coords_integral`: in `K(√d) = QuadraticAlgebra K d 0` with `d ∈ 𝓞 K`, an algebraic
  integer `y = a + b ω` has `2 a` and `2 d b` in `𝓞 K` (trace of `y`, and `(y - ȳ) ω`).
* `isSquare_of_isSquare_map`: an order `O ↪ F` in which `D y` lies for every `y` with `y²` in
  `O`, and a ring map `ρ : O → R` to a field with `ρ D ≠ 0`, send squares of `F` lying in `O` to
  squares of `R`.
* `leftInv_apply`: a left inverse certificate `leftInvOK R r m T` (Echelon.lean) recovers a vector
  from its images under the rows `R`.
* `indep_of_chars`, `coord_of_chars`: residue characters `ρ_j` into `ZMod p_j` (`p_j` odd) with
  values `±1` on the generators (rows `R j` as bitmasks) and a left inverse `T` make the generators
  independent modulo squares, and read the exponent vector of any square class they span off the
  characters.
-/

namespace FurioLombardo.Discharge.SelmerBasis

open NumberField QuadraticAlgebra FurioLombardo.M1

/-- **Coordinates of an integral element of `K(√d)`.** -/
theorem quad_coords_integral {K : Type*} [Field K] [NumberField K] (d : 𝓞 K)
    (y : QuadraticAlgebra K (d : K) 0) (hy : IsIntegral ℤ y) :
    IsIntegral ℤ (2 * y.re) ∧ IsIntegral ℤ (2 * (d : K) * y.im) := by
  have hinj : Function.Injective (algebraMap K (QuadraticAlgebra K (d : K) 0)) :=
    (algebraMap K (QuadraticAlgebra K (d : K) 0)).injective
  have hs : IsIntegral ℤ (star y) := hy.map (starRingEnd (QuadraticAlgebra K (d : K) 0)).toIntAlgHom
  have hω : IsIntegral ℤ (QuadraticAlgebra.omega : QuadraticAlgebra K (d : K) 0) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have : (QuadraticAlgebra.omega : QuadraticAlgebra K (d : K) 0) ^ 2 =
        algebraMap K _ (algebraMap (𝓞 K) K d) := by
      ext <;> simp [pow_two]
    rw [this]
    exact (d.isIntegral_coe).map (IsScalarTower.toAlgHom ℤ K (QuadraticAlgebra K (d : K) 0))
  constructor
  · have h := hy.add hs
    rw [← QuadraticAlgebra.algebraMap_trace_eq_add_star, QuadraticAlgebra.trace_def,
      zero_mul, add_zero] at h
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ K (QuadraticAlgebra K (d : K) 0))
      hinj).mp h
  · have h := (hy.sub hs).mul hω
    have heq : (y - star y) * QuadraticAlgebra.omega =
        algebraMap K (QuadraticAlgebra K (d : K) 0) (2 * (d : K) * y.im) := by
      ext <;> simp <;> ring
    rw [heq] at h
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ K (QuadraticAlgebra K (d : K) 0))
      hinj).mp h

/-- **Squares through an order.** -/
theorem isSquare_of_isSquare_map {O F R : Type*} [CommRing O] [Field F] [Field R] (ι : O →+* F)
    (hι : Function.Injective ι) (ρ : O →+* R) (D : O) (hD : ρ D ≠ 0)
    (hDy : ∀ (X : O) (y : F), ι X = y ^ 2 → ∃ Y : O, ι Y = ι D * y) (X : O)
    (hX : IsSquare (ι X)) : IsSquare (ρ X) := by
  obtain ⟨y, hy⟩ := hX
  obtain ⟨Y, hY⟩ := hDy X y (by rw [hy, sq])
  have hYY : Y * Y = D * D * X := hι (by rw [map_mul, map_mul, map_mul, hY, hy]; ring)
  have h := congrArg ρ hYY
  rw [map_mul, map_mul, map_mul] at h
  refine ⟨ρ Y / ρ D, ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hD hD)]
  linear_combination (-1 : R) * h

/-- **Left inverse certificates.** If `leftInvOK R r m T` holds and the rows `R i` send `a` to
`c i`, then `a k = ∑ i, T_k,i c i`. -/
theorem leftInv_apply {R : ℕ → ℕ} {r m : ℕ} {T : ℕ → ℕ} (h : leftInvOK R r m T = true)
    (a : Fin m → ZMod 2) (c : Fin r → ZMod 2)
    (ha : ∀ i : Fin r, ∑ j, bitv m (R i) j * a j = c i) (k : Fin m) :
    a k = ∑ i, bitv r (T k) i * c i := by
  have hx : xorSel R r (T k) = 2 ^ (k : ℕ) :=
    beq_iff_eq.mp ((allLt_iff (fun k => xorSel R r (T k) == 2 ^ k) m).mp h k k.is_lt)
  calc a k = ∑ j : Fin m, bitv m (2 ^ (k : ℕ)) j * a j := (sum_bitv_two_pow_mul m a k).symm
    _ = ∑ j : Fin m, bitv m (xorSel R r (T k)) j * a j := by rw [hx]
    _ = ∑ j : Fin m, (∑ i : Fin r, bitv r (T k) i * bitv m (R i) j) * a j := by
      rw [bitv_xorSel]; simp [Finset.sum_apply]
    _ = ∑ i : Fin r, bitv r (T k) i * (∑ j : Fin m, bitv m (R i) j * a j) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, bitv r (T k) i * c i := by simp only [ha]

/-- `±1` in `ZMod p` from `ZMod 2`. -/
def sgnE (p : ℕ) (v : ZMod 2) : ZMod p := if v = 1 then -1 else 1

theorem zmod2_cases (v : ZMod 2) : v = 0 ∨ v = 1 := by
  have : ∀ v : ZMod 2, v = 0 ∨ v = 1 := by decide
  exact this v

theorem zmod2_zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

theorem sgnE_add (p : ℕ) (v w : ZMod 2) : sgnE p (v + w) = sgnE p v * sgnE p w := by
  rcases zmod2_cases v with rfl | rfl <;> rcases zmod2_cases w with rfl | rfl <;>
    simp [sgnE, zmod2_one_add_one]

theorem sgnE_sum (p : ℕ) {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sgnE p (∑ i ∈ s, f i) = ∏ i ∈ s, sgnE p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgnE]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgnE_add, ih]

theorem sgnE_pow (p : ℕ) (v : ZMod 2) (n : ℕ) : sgnE p v ^ n = sgnE p (v * n) := by
  rcases zmod2_cases v with rfl | rfl
  · simp [sgnE]
  · simp only [sgnE, ↓reduceIte, one_mul, ZMod.natCast_eq_one_iff_odd]
    rcases Nat.even_or_odd n with h | h
    · rw [h.neg_one_pow]; simp [Nat.not_odd_iff_even.mpr h]
    · rw [h.neg_one_pow]; simp [h]

theorem sgnE_bit (p : ℕ) (b : Bool) :
    (if b then (-1 : ZMod p) else 1) = sgnE p (if b then 1 else 0) := by
  cases b <;> simp [sgnE]

theorem sgnE_ne_zero {p : ℕ} [Fact p.Prime] (v : ZMod 2) : sgnE p v ≠ 0 := by
  unfold sgnE; split <;> simp

theorem eq_zero_of_sgnE {p : ℕ} (hne : (-1 : ZMod p) ≠ 1) {v : ZMod 2} (h : sgnE p v = 1) :
    v = 0 := by
  rcases zmod2_cases v with rfl | rfl
  · rfl
  · simp only [sgnE, ↓reduceIte] at h; exact absurd h hne

/-- **Coordinates from characters.** Residue characters `ρ j : O → ZMod (p j)` (`p j` an odd
prime) with `ρ j (G s) ^ ((p j - 1) / 2) = ±1` as read off bit `s` of `R j`, transferring squares,
and a left inverse `T` of the rows: if `ι X ∏ ι (G s) ^ b s` is a square and the characters of
`X` are the bits of `c`, then `b s` is odd exactly when `dotB r (T s) c`. -/
theorem coord_of_chars {O F : Type*} [CommRing O] [Field F] (ι : O →+* F) {m r : ℕ}
    (G : Fin m → O) (p : Fin r → ℕ) [hp : ∀ j, Fact (p j).Prime] (hp2 : ∀ j, p j ≠ 2)
    (ρ : ∀ j, O →+* ZMod (p j)) (hsq : ∀ j (X : O), IsSquare (ι X) → IsSquare (ρ j X))
    (R : ℕ → ℕ) (hR : ∀ j (s : Fin m),
      ρ j (G s) ^ ((p j - 1) / 2) = if (R j).testBit s then -1 else 1)
    (T : ℕ → ℕ) (hT : leftInvOK R r m T = true) (X : O) (c : ℕ)
    (hc : ∀ j : Fin r, ρ j X ^ ((p j - 1) / 2) = if c.testBit j then -1 else 1)
    (b : Fin m → ℕ) (hb : IsSquare (ι X * ∏ s, ι (G s) ^ b s)) (s : Fin m) :
    b s % 2 = if dotB r (T s) c then 1 else 0 := by
  classical
  let a : Fin m → ZMod 2 := fun s => (b s : ZMod 2)
  have key : ∀ j : Fin r, ∑ s, bitv m (R j) s * a s = bitv r c j := by
    intro j
    have hpj := (hp j).out
    have h3 : 2 < p j := lt_of_le_of_ne hpj.two_le (Ne.symm (hp2 j))
    have : Fact (2 < p j) := ⟨h3⟩
    have hne : (-1 : ZMod (p j)) ≠ 1 := ZMod.neg_one_ne_one
    obtain ⟨y, hy⟩ := hsq j (X * ∏ s, G s ^ b s) (by simpa [map_mul, map_prod, map_pow] using hb)
    rw [map_mul, map_prod] at hy
    simp only [map_pow] at hy
    have hχ : (ρ j X * ∏ s, ρ j (G s) ^ b s) ^ ((p j - 1) / 2) =
        sgnE (p j) (bitv r c j + ∑ s, bitv m (R j) s * a s) := by
      rw [mul_pow, ← Finset.prod_pow, sgnE_add, sgnE_sum, hc j, sgnE_bit]
      congr 1
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [← pow_mul, mul_comm (b s), pow_mul, hR j s, sgnE_bit, sgnE_pow]
      rfl
    have hodd : 2 * ((p j - 1) / 2) = p j - 1 := by
      rcases hpj.eq_two_or_odd' with h2 | ⟨k, hk⟩
      · exact absurd h2 (hp2 j)
      · omega
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hy
      rw [hy, zero_pow (by omega)] at hχ
      exact sgnE_ne_zero _ hχ.symm
    have h1 : sgnE (p j) (bitv r c j + ∑ s, bitv m (R j) s * a s) = 1 := by
      rw [← hχ, hy, ← sq, ← pow_mul, hodd, ZMod.pow_card_sub_one_eq_one hy0]
    have h0 := eq_zero_of_sgnE hne h1
    rw [add_comm, add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two] at h0
    exact h0
  have hs := leftInv_apply hT a (bitv r c) key s
  rw [← dotB_eq] at hs
  have hv := congrArg ZMod.val hs
  rw [ZMod.val_natCast] at hv
  rw [hv]
  split <;> rfl

/-- **Independence from characters.** -/
theorem indep_of_chars {O F : Type*} [CommRing O] [Field F] (ι : O →+* F) {m r : ℕ}
    (G : Fin m → O) (p : Fin r → ℕ) [hp : ∀ j, Fact (p j).Prime] (hp2 : ∀ j, p j ≠ 2)
    (ρ : ∀ j, O →+* ZMod (p j)) (hsq : ∀ j (X : O), IsSquare (ι X) → IsSquare (ρ j X))
    (R : ℕ → ℕ) (hR : ∀ j (s : Fin m),
      ρ j (G s) ^ ((p j - 1) / 2) = if (R j).testBit s then -1 else 1)
    (T : ℕ → ℕ) (hT : leftInvOK R r m T = true) (e : Fin m → Bool)
    (he : IsSquare (subprod (fun s => ι (G s)) e)) : ∀ s, e s = false := by
  intro s
  have hd : ∀ n x : ℕ, dotB n x 0 = false := fun n x => by
    induction n with
    | zero => rfl
    | succ n ih => simp [dotB, ih]
  have hb : IsSquare (ι 1 * ∏ s, ι (G s) ^ (if e s then 1 else 0)) := by
    rw [map_one, one_mul]
    convert he using 1
    simp only [subprod]
    exact Finset.prod_congr rfl fun s _ => by split <;> simp
  have h := coord_of_chars ι G p hp2 ρ hsq R hR T hT 1 0
    (fun j => by simp) (fun s => if e s then 1 else 0) hb s
  rw [hd] at h
  revert h
  cases e s <;> simp

end FurioLombardo.Discharge.SelmerBasis
