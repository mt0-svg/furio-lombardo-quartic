import Mathlib

/-!
# Lane M3b: the dyadic certificate for `L/K21`, kernel checked

`R = (ℤ/4)[π]/(π³ + 2)`: the ring `O_v/4 = O_v/π⁶` for the place `v` of `K21` above 2 with
`e = 3`, `f = 1` (`K21_v = ℚ₂(π)`, `π` a root of an Eisenstein polynomial `E` with
`E ≡ x³ + 2 mod 4`; code/selmer-global-bound/dyadic_nonnorm_cert.gp). Elements are written `a₀ + a₁ π + a₂ π²` with
`aᵢ ∈ ℤ/4` (`elt`, `elt_surjective`, `elt_injective`), multiplication by `tmul` (`elt_mul`).

`cert`: with `U = 3 + 3π + 3π²` and `D = 1 + 2π²` (the images of the unit `u = zk[19] - 1` and of
`d' = d / PI^18` computed by dyadic_nonnorm_cert.gp), no `a, b, c ∈ R` with one of them equal to `1`
satisfy `U c² = a² - D b²`. The three normalised cases (`certA`, `certB`, `certC`, 4096 triples
each) are checked by `decide +kernel`; `count_one` reproduces the count 128 of pairs
`(a, b)` with `1 = a² - D b²` printed by dyadic_nonnorm_kat.gp.
-/

namespace FurioLombardo.M3b.DyadicCert

open Polynomial

/-- Triples `(a₀, a₁, a₂)` over `ℤ/4`, standing for `a₀ + a₁ π + a₂ π²`. -/
abbrev T := ZMod 4 × ZMod 4 × ZMod 4

/-- Multiplication of triples, with `π³ = -2` and `π⁴ = -2 π`. -/
def tmul (a b : T) : T :=
  (a.1 * b.1 - 2 * (a.2.1 * b.2.2 + a.2.2 * b.2.1),
   a.1 * b.2.1 + a.2.1 * b.1 - 2 * (a.2.2 * b.2.2),
   a.1 * b.2.2 + a.2.1 * b.2.1 + a.2.2 * b.1)

/-- The image of `u`. -/
def U : T := (3, 3, 3)

/-- The image of `d'`. -/
def D : T := (1, 0, 2)

/-- `U c² - (a² - D b²)` on triples. -/
def res (u a b c : T) : T := tmul u (tmul c c) - (tmul a a - tmul D (tmul b b))

theorem certA : ∀ b₀ b₁ b₂ c₀ c₁ c₂ : ZMod 4, res U (1, 0, 0) (b₀, b₁, b₂) (c₀, c₁, c₂) ≠ 0 := by
  decide +kernel

theorem certB : ∀ a₀ a₁ a₂ c₀ c₁ c₂ : ZMod 4, res U (a₀, a₁, a₂) (1, 0, 0) (c₀, c₁, c₂) ≠ 0 := by
  decide +kernel

theorem certC : ∀ a₀ a₁ a₂ b₀ b₁ b₂ : ZMod 4, res U (a₀, a₁, a₂) (b₀, b₁, b₂) (1, 0, 0) ≠ 0 := by
  decide +kernel

/-- The unit `1 = (1, 0, 0)` (not the `1` of the product ring `T`). -/
def one : T := (1, 0, 0)

/-- All 64 triples. -/
def allT : List T :=
  let z : List (ZMod 4) := [0, 1, 2, 3]
  z.flatMap fun a₀ => z.flatMap fun a₁ => z.map fun a₂ => (a₀, a₁, a₂)

/-- Known answer: for `u = 1` there are 128 pairs `(a, b)` with `1 = a² - D b²`
(code/selmer-global-bound/dyadic_nonnorm_kat.gp, same arithmetic as dyadic_nonnorm_cert.gp). -/
theorem count_one :
    ((allT.flatMap fun a => allT.map fun b => (a, b)).filter
      fun t => res one t.1 t.2 one = 0).length = 128 := by
  decide +kernel

/-! ## The ring `R` -/

/-- `x³ + 2` over `ℤ/4`. -/
noncomputable def E4 : (ZMod 4)[X] := X ^ 3 + C 2

theorem E4_monic : E4.Monic := by unfold E4; monicity!

theorem E4_natDegree : E4.natDegree = 3 := by unfold E4; compute_degree!

/-- `R = (ℤ/4)[π]/(π³ + 2)`. -/
abbrev R := AdjoinRoot E4

/-- The class of `π`. -/
noncomputable def pi : R := AdjoinRoot.root E4

/-- The coefficients. -/
noncomputable abbrev of : ZMod 4 →+* R := AdjoinRoot.of E4

theorem pi_cube : pi ^ 3 = -2 := by
  have h : AdjoinRoot.mk E4 (X ^ 3 + C 2) = 0 := AdjoinRoot.mk_self
  rw [map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  have h2 : ((2 : ZMod 4) : R) = 2 := map_ofNat _ 2
  rw [h2] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The element `a₀ + a₁ π + a₂ π²`. -/
noncomputable def elt (t : T) : R := of t.1 + of t.2.1 * pi + of t.2.2 * pi ^ 2

theorem elt_mul (a b : T) : elt a * elt b = elt (tmul a b) := by
  simp only [elt, tmul, map_add, map_mul, map_sub, map_ofNat]
  linear_combination (of a.2.1 * of b.2.2 + of a.2.2 * of b.2.1 + of a.2.2 * of b.2.2 * pi) *
    pi_cube

theorem elt_sub (a b : T) : elt (a - b) = elt a - elt b := by
  simp only [elt, Prod.fst_sub, Prod.snd_sub, map_sub]
  ring

theorem elt_one : elt (1, 0, 0) = 1 := by
  simp [elt]

theorem elt_eq_mk (t : T) : elt t = AdjoinRoot.mk E4 (C t.2.2 * X ^ 2 + C t.2.1 * X + C t.1) := by
  simp only [elt, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, pi]
  ring

theorem eq_zero_of_elt_eq_zero {t : T} (h : elt t = 0) : t = 0 := by
  rw [elt_eq_mk, AdjoinRoot.mk_eq_zero] at h
  set q : (ZMod 4)[X] := C t.2.2 * X ^ 2 + C t.2.1 * X + C t.1 with hq
  have hq0 : q = 0 := by
    by_contra hne
    refine E4_monic.not_dvd_of_natDegree_lt hne ?_ h
    rw [E4_natDegree]
    exact lt_of_le_of_lt natDegree_quadratic_le (by norm_num)
  have c0 : q.coeff 0 = t.1 := by simp [hq]
  have c1 : q.coeff 1 = t.2.1 := by simp [hq]
  have c2 : q.coeff 2 = t.2.2 := by simp [hq]
  rw [hq0, coeff_zero] at c0 c1 c2
  exact Prod.ext c0.symm (Prod.ext c1.symm c2.symm)

theorem elt_injective : Function.Injective elt := by
  intro a b h
  have : elt (a - b) = 0 := by rw [elt_sub, h, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_elt_eq_zero this)

theorem elt_surjective : Function.Surjective elt := by
  intro r
  induction r using AdjoinRoot.induction_on with
  | ih p =>
    set q := p %ₘ E4
    have hq : q.natDegree < 3 := by
      rw [← E4_natDegree]
      refine natDegree_modByMonic_lt p E4_monic ?_
      intro h1
      have := congrArg natDegree h1
      rw [E4_natDegree, natDegree_one] at this
      exact absurd this (by norm_num)
    have hpq : AdjoinRoot.mk E4 p = AdjoinRoot.mk E4 q := by
      rw [AdjoinRoot.mk_eq_mk, show q = p - E4 * (p /ₘ E4) from modByMonic_eq_sub_mul_div p E4]
      exact ⟨p /ₘ E4, by ring⟩
    refine ⟨(q.coeff 0, q.coeff 1, q.coeff 2), ?_⟩
    rw [hpq, ← AdjoinRoot.aeval_eq, aeval_eq_sum_range' hq]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
      pow_one, Algebra.smul_def, AdjoinRoot.algebraMap_eq, mul_one, elt, pi]

/-- **The dyadic certificate**: no normalised solution of `U c² = a² - D b²` in `R`. -/
theorem cert : ∀ a b c : R, (a = 1 ∨ b = 1 ∨ c = 1) →
    elt U * c ^ 2 ≠ a ^ 2 - elt D * b ^ 2 := by
  intro a b c h habc
  obtain ⟨ta, rfl⟩ := elt_surjective a
  obtain ⟨tb, rfl⟩ := elt_surjective b
  obtain ⟨tc, rfl⟩ := elt_surjective c
  have hres : res U ta tb tc = 0 := by
    apply eq_zero_of_elt_eq_zero
    rw [res, elt_sub, elt_sub, ← elt_mul, ← elt_mul, ← elt_mul, ← elt_mul, ← elt_mul, ← sq,
      ← sq, ← sq, habc, sub_self]
  rw [← elt_one] at h
  obtain ⟨a₀, a₁, a₂⟩ := ta
  obtain ⟨b₀, b₁, b₂⟩ := tb
  obtain ⟨c₀, c₁, c₂⟩ := tc
  rcases h with h | h | h <;> rw [elt_injective h] at hres
  · exact certA b₀ b₁ b₂ c₀ c₁ c₂ hres
  · exact certB a₀ a₁ a₂ c₀ c₁ c₂ hres
  · exact certC a₀ a₁ a₂ b₀ b₁ b₂ hres

end FurioLombardo.M3b.DyadicCert
