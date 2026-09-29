import FurioLombardo.M1.SieveRing
import FurioLombardo.M1.DataSieve

/-!
# The square condition of a class at a point

For an integer point `a` of `C` and an exponent vector `e`, `SqCond a e` says that each of
`Q1(a) G_e`, `Q3(a) G_e` whose conic value is nonzero is a square in `𝓞 K21` (`G_e = gProd e`).
Every local test of the sieve (the rings at good primes, `ℤ/27` above 3, the prime `lc` above 2)
refutes `SqCond a e` for the classes it kills.

`sqCond_of`: on `C`, `Q1 Q3 = Q2²`, so one square `Q_i(a) G_e = s²` with `Q_i(a) ≠ 0` gives the
square condition for both conics (a square root in `K21` of an algebraic integer is integral).

`survE k`: the `k`-th survivor of the good prime sieve (DataSieve.lean) as an exponent vector.
-/

namespace FurioLombardo.M1

open NumberField

/-- The survivors of the good prime sieve, as exponent vectors. -/
def survE (k : ℕ) : Fin 18 → Bool := fun i => (sieveSurv.getD k []).getD i false

/-- The square condition of the class `e` at the integer point `a`. -/
def SqCond (a : Fin 3 → ℤ) (e : Fin 18 → Bool) : Prop :=
  ∀ i : Fin 3, (i = 0 ∨ i = 2) → qO i a ≠ 0 → ∃ s : 𝓞 K21, qO i a * gProd e = s ^ 2

/-- An algebraic integer with a square root in `K21` is a square in `𝓞 K21`. -/
theorem exists_sq_of_sq {x : 𝓞 K21} {t : K21} (h : t ^ 2 = algebraMap (𝓞 K21) K21 x) :
    ∃ s : 𝓞 K21, x = s ^ 2 := by
  have hi : IsIntegral ℤ t := IsIntegral.of_pow (n := 2) (by norm_num) (h ▸ x.2)
  let s : 𝓞 K21 := ⟨t, hi⟩
  have hs : algebraMap (𝓞 K21) K21 s = t := rfl
  refine ⟨s, RingOfIntegers.coe_injective ?_⟩
  show algebraMap (𝓞 K21) K21 x = algebraMap (𝓞 K21) K21 (s ^ 2)
  rw [map_pow, hs, h]

/-- **One square gives the square condition.** -/
theorem sqCond_of (a : Fin 3 → ℤ) (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0)
    (e : Fin 18 → Bool) (i0 : Fin 3) (hi0 : i0 = 0 ∨ i0 = 2) (h0 : qO i0 a ≠ 0) (s : 𝓞 K21)
    (hs : qO i0 a * gProd e = s ^ 2) : SqCond a e := by
  intro i hi hne
  by_cases hii : i = i0
  · subst hii
    exact ⟨s, hs⟩
  have hb := bruin_point a hF
  have hprod : qO i a * qO i0 a = qO 1 a ^ 2 := by
    rcases hi with rfl | rfl <;> rcases hi0 with rfl | rfl
    · exact absurd rfl hii
    · exact hb
    · rw [mul_comm]; exact hb
    · exact absurd rfl hii
  have h0K : ((qO i0 a : 𝓞 K21) : K21) ≠ 0 := by
    rw [Ne, RingOfIntegers.coe_eq_zero_iff]; exact h0
  have hprodK : (qO i a : K21) * (qO i0 a : K21) = (qO 1 a : K21) ^ 2 := by
    rw [← map_mul, hprod, map_pow]
  have hsK : (qO i0 a : K21) * (gProd e : K21) = (s : K21) ^ 2 := by
    rw [← map_mul, hs, map_pow]
  obtain ⟨t, ht⟩ := exists_sq_of_sq (x := qO i a * gProd e)
    (t := (qO 1 a : K21) * (s : K21) / (qO i0 a : K21)) (by
      rw [div_pow, mul_pow, map_mul, ← hprodK, ← hsK]
      field_simp)
  exact ⟨t, ht⟩

end FurioLombardo.M1
