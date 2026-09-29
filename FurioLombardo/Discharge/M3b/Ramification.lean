import Mathlib

/-!
# Ramified primes contain the discriminant of an integral quadratic generator

Generic lemmas for the M3b discharge (number fields `K ⊂ L`, no degree hypothesis):

* `mem_of_ramified`: a prime `Q` of `𝓞 L` with ramification index `> 1` over `𝓞 K` contains the
  different ideal (Mathlib `dvd_differentIdeal_iff`).
* `disc_mem_of_ramified`: if `γ ∈ 𝓞 L` generates `L` over `K`, is not in `𝓞 K` and satisfies
  `γ² + b γ + c = 0` with `b, c ∈ 𝓞 K`, then every such `Q` contains `b² - 4 c`: the minimal
  polynomial of `γ` over `𝓞 K` is `X² + b X + c`, its derivative at `γ` is `2 γ + b`, which lies
  in the different (Mathlib `aeval_derivative_mem_differentIdeal`), and `(2 γ + b)² = b² - 4 c`.
* `isIntegral_mk_half`: in `QuadraticAlgebra K a 0`, `(α + β ω) / 2` is integral when `α, β` and
  `(α² - a β²) / 4` are integers of `K` (it is a root of `X² - α X + (α² - a β²) / 4`).
-/

namespace FurioLombardo.Discharge.M3b

open NumberField Polynomial

section Different

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] FractionRing.liftAlgebra in
/-- A prime of `𝓞 L` ramified over `𝓞 K` contains the different ideal. -/
theorem differentIdeal_le_of_ramified (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : 1 < Q.ramificationIdx (𝓞 K)) : differentIdeal (𝓞 K) (𝓞 L) ≤ Q := by
  rw [← Ideal.dvd_iff_le, dvd_differentIdeal_iff]
  intro hU
  have h1 := Ideal.ramificationIdx_eq_one Q (𝓞 K)
  omega

/-- A prime of `𝓞 L` ramified over `𝓞 K` contains `b² - 4 c` for every integral generator `γ` of
`L / K` with `γ² + b γ + c = 0`. -/
theorem disc_mem_of_ramified (γ : 𝓞 L) (b c : 𝓞 K)
    (hγ : γ ^ 2 + algebraMap (𝓞 K) (𝓞 L) b * γ + algebraMap (𝓞 K) (𝓞 L) c = 0)
    (hadj : Algebra.adjoin K {algebraMap (𝓞 L) L γ} = ⊤)
    (hK : γ ∉ (algebraMap (𝓞 K) (𝓞 L)).range)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : 1 < Q.ramificationIdx (𝓞 K)) :
    algebraMap (𝓞 K) (𝓞 L) (b ^ 2 - 4 * c) ∈ Q := by
  set p : (𝓞 K)[X] := X ^ 2 + C b * X + C c with hp
  have hpdeg : p.natDegree = 2 := by rw [hp]; compute_degree!
  have hpm : p.Monic := by rw [hp]; monicity!
  have hpγ : aeval γ p = 0 := by
    rw [hp]; simp only [map_add, map_mul, aeval_X_pow, aeval_C, aeval_X]
    linear_combination hγ
  have hint : IsIntegral (𝓞 K) γ := ⟨p, hpm, by rw [← aeval_def]; exact hpγ⟩
  have hmin : minpoly (𝓞 K) γ = p := by
    have hdvd : minpoly (𝓞 K) γ ∣ p := minpoly.isIntegrallyClosed_dvd hint hpγ
    have h2 : 2 ≤ (minpoly (𝓞 K) γ).natDegree := (minpoly.two_le_natDegree_iff hint).mpr hK
    exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm hdvd
      (by rw [hpdeg]; exact h2)).symm
  have hd := aeval_derivative_mem_differentIdeal (𝓞 K) K L γ hadj
  have hder : aeval γ (derivative (minpoly (𝓞 K) γ)) = 2 * γ + algebraMap (𝓞 K) (𝓞 L) b := by
    rw [hmin, hp]
    simp only [derivative_add, derivative_X_pow, derivative_mul, derivative_C, derivative_X,
      zero_mul, zero_add, mul_one, map_add, map_mul, aeval_C, map_natCast]
    norm_num
  rw [hder] at hd
  have hQd := differentIdeal_le_of_ramified (K := K) Q hQ hd
  have hsq := Q.mul_mem_left (2 * γ + algebraMap (𝓞 K) (𝓞 L) b) hQd
  have key : algebraMap (𝓞 K) (𝓞 L) (b ^ 2 - 4 * c) =
      (2 * γ + algebraMap (𝓞 K) (𝓞 L) b) * (2 * γ + algebraMap (𝓞 K) (𝓞 L) b) -
        4 * (γ ^ 2 + algebraMap (𝓞 K) (𝓞 L) b * γ + algebraMap (𝓞 K) (𝓞 L) c) := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]; ring
  rw [key, hγ, mul_zero, sub_zero]
  exact hsq

end Different

section Half

variable {K : Type*} [Field K] [NumberField K] {a : K}

/-- `(α + β ω) / 2` is a root of `X² - α X + (α² - a β²) / 4`. -/
theorem mk_half_sq (α β n : K) (hn : α ^ 2 - a * β ^ 2 = 4 * n) :
    (⟨α / 2, β / 2⟩ : QuadraticAlgebra K a 0) ^ 2 -
      algebraMap K (QuadraticAlgebra K a 0) α * ⟨α / 2, β / 2⟩ +
        algebraMap K (QuadraticAlgebra K a 0) n = 0 := by
  ext
  · simp [sq, QuadraticAlgebra.algebraMap_eq]
    linear_combination (-1 / 4 : K) * hn
  · simp [sq, QuadraticAlgebra.algebraMap_eq]
    ring

/-- A root in a `K`-algebra field of a monic quadratic over `𝓞 K` is an algebraic integer. -/
theorem isIntegral_of_quadratic {L : Type*} [Field L] [Algebra K L] (z : L) (b c : 𝓞 K)
    (h : z ^ 2 + algebraMap (𝓞 K) L b * z + algebraMap (𝓞 K) L c = 0) : IsIntegral ℤ z := by
  have h1 : IsIntegral (𝓞 K) z := by
    refine ⟨X ^ 2 + C b * X + C c, by monicity!, ?_⟩
    rw [← aeval_def]
    simp only [map_add, map_mul, aeval_X_pow, aeval_C, aeval_X]
    exact h
  exact isIntegral_trans (R := ℤ) _ h1

end Half

end FurioLombardo.Discharge.M3b
