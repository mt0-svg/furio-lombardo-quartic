import FurioLombardo.M3b.Tower

/-!
# Lane M3b: `Cl[2] = 0` turns `L(S, 2)` into S-units modulo squares

For a number field `L` with `Cl(L)[2] = 0` and any set `S` of primes: an element `x ∈ Lˣ` with
even valuation at every prime outside `S` is `s y²` with `s` an `S`-unit (valuation `0` outside
`S`). This is how `Cl(L)[2] = 0` and `Cl(N)[2] = 0` enter the Selmer computation (K1):
the groups `L(S, 2)` and `N(S, 2)` are spanned by `S`-units.

Proof: `(x) = T J²` with `J = ∏_{v ∉ S} v^(v(x)/2)` and `T` supported on `S`; the class group
has odd order `2m + 1`, so `[J T^(m+1)]² = [x] [T]^(2m+1) = 1`, hence `J T^(m+1) = (y)` and
`s = x / y²` has valuation `v(x) - 2 v(J) = 0` outside `S`.
-/

namespace FurioLombardo.M3b

open NumberField IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors

variable {L : Type} [Field L] [NumberField L]

/-- `Cl(L)[2] = 0` in the model `I_L / P_L`. -/
theorem quot_sq_eq_one (hCl : ClTwoTrivial L)
    (a : (FractionalIdeal (𝓞 L)⁰ L)ˣ ⧸ (toPrincipalIdeal (𝓞 L) L).range) (ha : a ^ 2 = 1) :
    a = 1 := by
  have h := hCl ((ClassGroup.equiv L).symm a) (by rw [← map_pow, ha, map_one])
  simpa using congrArg (ClassGroup.equiv L) h

/-- The count at `v` of a product, power, inverse of unit fractional ideals, through `countHom`. -/
theorem count_units_mul (v : HeightOneSpectrum (𝓞 L)) (a b : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    count L v ((a * b : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) =
      count L v (a : FractionalIdeal (𝓞 L)⁰ L) + count L v (b : FractionalIdeal (𝓞 L)⁰ L) := by
  rw [← countHom_apply, ← countHom_apply, ← countHom_apply, map_mul, toAdd_mul]

theorem count_units_pow (v : HeightOneSpectrum (𝓞 L)) (a : (FractionalIdeal (𝓞 L)⁰ L)ˣ) (n : ℕ) :
    count L v ((a ^ n : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) =
      n * count L v (a : FractionalIdeal (𝓞 L)⁰ L) := by
  rw [← countHom_apply, ← countHom_apply, map_pow, toAdd_pow, nsmul_eq_mul]

theorem count_units_inv (v : HeightOneSpectrum (𝓞 L)) (a : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
    count L v ((a⁻¹ : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) =
      -count L v (a : FractionalIdeal (𝓞 L)⁰ L) := by
  rw [← countHom_apply, ← countHom_apply, map_inv, toAdd_inv]

theorem sq_mul_pow_succ {G : Type*} [CommGroup G] (a b : G) (m : ℕ) :
    (a * b ^ (m + 1)) ^ 2 = b * a ^ 2 * b ^ (2 * m + 1) := by
  rw [mul_pow, ← pow_mul, mul_comm b, mul_assoc, ← pow_succ']
  congr 2; ring

/-- **S-units modulo squares**: with `Cl(L)[2] = 0`, an element with even valuation outside `S`
is an `S`-unit times a square. -/
theorem exists_sUnit_mul_sq (hCl : ClTwoTrivial L) (S : Set (HeightOneSpectrum (𝓞 L))) (x : Lˣ)
    (hx : ∀ v ∉ S, Even (count L v (spanSingleton (𝓞 L)⁰ (x : L)))) :
    ∃ s y : Lˣ, x = s * y ^ 2 ∧ ∀ v ∉ S, count L v (spanSingleton (𝓞 L)⁰ (s : L)) = 0 := by
  classical
  set X := toPrincipalIdeal (𝓞 L) L x with hX
  have hXc : ∀ v, count L v (X : FractionalIdeal (𝓞 L)⁰ L) =
      count L v (spanSingleton (𝓞 L)⁰ (x : L)) := fun v => by rw [hX, coe_toPrincipalIdeal]
  -- `J = ∏_{v ∉ S} v ^ (v(x) / 2)`
  set g := toFinsupp X
  set j : HeightOneSpectrum (𝓞 L) →₀ ℤ :=
    (g.filter fun v => v ∉ S).mapRange (fun n => n / 2) (by simp) with hj
  set J := ofFinsupp L j
  have hJc : ∀ v ∉ S, 2 * count L v (J : FractionalIdeal (𝓞 L)⁰ L) =
      count L v (X : FractionalIdeal (𝓞 L)⁰ L) := by
    intro v hv
    rw [count_ofFinsupp, hj, Finsupp.mapRange_apply, Finsupp.filter_apply, if_pos hv,
      toFinsupp_apply]
    rw [hXc]
    exact Int.mul_ediv_cancel' (even_iff_two_dvd.1 (hx v hv))
  -- `T = X / J²` is supported on `S`
  set T := X * (J ^ 2)⁻¹
  have hTc : ∀ v ∉ S, count L v (T : FractionalIdeal (𝓞 L)⁰ L) = 0 := by
    intro v hv
    rw [count_units_mul, count_units_inv, count_units_pow, ← hJc v hv]
    push_cast; ring
  -- the class group has odd order `2 m + 1`
  set Q := (FractionalIdeal (𝓞 L)⁰ L)ˣ ⧸ (toPrincipalIdeal (𝓞 L) L).range
  have hodd : Odd (Nat.card Q) := odd_card_of_sq_eq_one (quot_sq_eq_one hCl)
  obtain ⟨m, hm⟩ := hodd
  have hTpow : (QuotientGroup.mk T : Q) ^ (2 * m + 1) = 1 := by
    rw [← hm]; exact pow_card_eq_one'
  have hX1 : (QuotientGroup.mk X : Q) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩
  have hsq : (QuotientGroup.mk (J * T ^ (m + 1)) : Q) ^ 2 = 1 := by
    have hXJT : X = T * J ^ 2 := by simp [T]
    calc (QuotientGroup.mk (J * T ^ (m + 1)) : Q) ^ 2
        = (QuotientGroup.mk (T * J ^ 2) : Q) * (QuotientGroup.mk T : Q) ^ (2 * m + 1) := by
          simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow]
          exact sq_mul_pow_succ (G := Q) (QuotientGroup.mk J) (QuotientGroup.mk T) m
      _ = 1 := by rw [← hXJT, hX1, hTpow, one_mul]
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).1 (quot_sq_eq_one hCl _ hsq)
  refine ⟨x * (y ^ 2)⁻¹, y, by group, fun v hv => ?_⟩
  have hs : spanSingleton (𝓞 L)⁰ ((x * (y ^ 2)⁻¹ : Lˣ) : L) =
      ((X * ((J * T ^ (m + 1)) ^ 2)⁻¹ : (FractionalIdeal (𝓞 L)⁰ L)ˣ) :
        FractionalIdeal (𝓞 L)⁰ L) := by
    rw [← hy, hX, ← map_pow, ← map_inv, ← map_mul, coe_toPrincipalIdeal]
  rw [hs, count_units_mul, count_units_inv, count_units_pow, count_units_mul, count_units_pow,
    hTc v hv, ← hJc v hv]
  push_cast; ring

end FurioLombardo.M3b
