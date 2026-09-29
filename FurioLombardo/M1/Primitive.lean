import Mathlib

/-!
# Primitive integer representatives of rational points of the projective plane
-/

namespace FurioLombardo.M1

/-- A nonzero rational triple is a nonzero multiple of a primitive integer triple (one with an
integer combination equal to `1`). -/
theorem exists_primitive (x y z : ℚ) (h : (x, y, z) ≠ (0, 0, 0)) :
    ∃ (a b c : ℤ) (l : ℚ), l ≠ 0 ∧ x = l * a ∧ y = l * b ∧ z = l * c ∧
      ∃ r s t : ℤ, r * a + s * b + t * c = 1 := by
  set d : ℤ := x.den * y.den * z.den with hd
  have hd0 : (d : ℚ) ≠ 0 := by rw [hd]; push_cast; positivity
  set A : ℤ := x.num * (y.den * z.den) with hA
  set B : ℤ := y.num * (x.den * z.den) with hB
  set C : ℤ := z.num * (x.den * y.den) with hC
  have hx : x * d = A := by
    rw [hd, hA]; push_cast
    calc x * (x.den * y.den * z.den) = (x * x.den) * (y.den * z.den) := by ring
      _ = _ := by rw [Rat.mul_den_eq_num]
  have hy : y * d = B := by
    rw [hd, hB]; push_cast
    calc y * (x.den * y.den * z.den) = (y * y.den) * (x.den * z.den) := by ring
      _ = _ := by rw [Rat.mul_den_eq_num]
  have hz : z * d = C := by
    rw [hd, hC]; push_cast
    calc z * (x.den * y.den * z.den) = (z * z.den) * (x.den * y.den) := by ring
      _ = _ := by rw [Rat.mul_den_eq_num]
  set G : ℤ := (Int.gcd A B : ℤ) with hG
  set g : ℤ := (Int.gcd G C : ℤ) with hg
  have hgA : g ∣ A := (Int.gcd_dvd_left ..).trans (Int.gcd_dvd_left ..)
  have hgB : g ∣ B := (Int.gcd_dvd_left ..).trans (Int.gcd_dvd_right ..)
  have hgC : g ∣ C := Int.gcd_dvd_right ..
  obtain ⟨a, ha⟩ := hgA
  obtain ⟨b, hb⟩ := hgB
  obtain ⟨c, hc⟩ := hgC
  have hg0 : g ≠ 0 := by
    intro h0
    apply h
    have hA0 : A = 0 := by rw [ha, h0, zero_mul]
    have hB0 : B = 0 := by rw [hb, h0, zero_mul]
    have hC0 : C = 0 := by rw [hc, h0, zero_mul]
    have ex : x = 0 := by
      have := hx; rw [hA0, Int.cast_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hd0
    have ey : y = 0 := by
      have := hy; rw [hB0, Int.cast_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hd0
    have ez : z = 0 := by
      have := hz; rw [hC0, Int.cast_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hd0
    rw [ex, ey, ez]
  have hg0' : (g : ℚ) ≠ 0 := by exact_mod_cast hg0
  refine ⟨a, b, c, g / d, div_ne_zero hg0' hd0, ?_, ?_, ?_, ?_⟩
  · field_simp
    rw [hx, ha]; push_cast; ring
  · field_simp
    rw [hy, hb]; push_cast; ring
  · field_simp
    rw [hz, hc]; push_cast; ring
  · refine ⟨Int.gcdA A B * Int.gcdA G C, Int.gcdB A B * Int.gcdA G C, Int.gcdB G C, ?_⟩
    have e1 : G = A * Int.gcdA A B + B * Int.gcdB A B := Int.gcd_eq_gcd_ab A B
    have e2 : g = G * Int.gcdA G C + C * Int.gcdB G C := Int.gcd_eq_gcd_ab G C
    apply mul_left_cancel₀ hg0
    rw [mul_one]
    calc g * (Int.gcdA A B * Int.gcdA G C * a + Int.gcdB A B * Int.gcdA G C * b +
          Int.gcdB G C * c)
        = (g * a * Int.gcdA A B + g * b * Int.gcdB A B) * Int.gcdA G C + g * c * Int.gcdB G C := by
          ring
      _ = g := by rw [← ha, ← hb, ← hc, ← e1, ← e2]

end FurioLombardo.M1
