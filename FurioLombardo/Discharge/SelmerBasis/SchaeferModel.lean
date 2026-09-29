import Mathlib
import FurioLombardo.Discharge.SelmerBasis.SchaeferLocal

/-!
# Schaefer's lemma through a change of model (generic, no K21)

When the sextic `f` fails the hypotheses of
the local lemma at some primes, the lemma is applied to two other models of the same curve:

* the affine model `f1 = π⁻⁶ f(a + π X)` (`affModel π a 6 f`), with `U1 = π⁻² U(a + π X)`,
  `V1 = π⁻³ V(a + π X)`, `W1 = π⁻⁴ W(a + π X)`, `θ1 = (θ - a) / π`, so `V1² - f1 = U1 W1`
  and `U(θ) = π² U1(θ1)`;
* at the primes where `lc f1` is not a unit, the inverted model `f2 = X⁶ f1(i + 1/X)`
  (`invModel i 6 f1`, the reflection of `f1(X + i)`) for a shift `i ∈ {0, 1, 2}` with
  `U1(i) ≠ 0`, with `U2 = U1(i)⁻¹ X² U1(i + 1/X)`, `V2 = X³ V1(i + 1/X) mod U2`,
  `θ2 = 1 / (θ1 - i)`, so `U1(θ1) = (θ1 - i)² U1(i) U2(θ2)`.

Valuation form (`schaefer_model_sq`): certificates in valuation form give that `v(U(θ) / c)` is a
square in the value group, `c` a content of `U1`. Number field form (`schaefer_global_of_certs`):
the certificates are identities over a number field `K` with a principal ring of integers,
integral after scaling by `D ^ N`; for every number field `F` over `K`, every root `θ` of `f` in `F`
and every height one prime `P` of `𝓞 F` with `D ∉ P`, the multiplicity of `U(θ) / c` at `P` is
even. No prime is named: the case split is `v_P(lc f1) = 1` or `< 1`.
-/

open Polynomial NumberField
open scoped nonZeroDivisors

namespace FurioLombardo.Discharge.SelmerBasis

/-- The affine model `π⁻ⁿ P(a + π X)`. -/
noncomputable def affModel {M : Type*} [Field M] (π a : M) (n : ℕ) (P : M[X]) : M[X] :=
  C (π ^ n)⁻¹ * P.comp (C a + C π * X)

/-- The inverted model `Xⁿ P(i + 1/X)`: the reflection at degree `n` of `P(X + i)`. -/
noncomputable def invModel {M : Type*} [CommRing M] (i : M) (n : ℕ) (P : M[X]) : M[X] :=
  reflect n (P.comp (X + C i))

namespace Schaefer

/-! ### Transport identities (pure algebra) -/

theorem affModel_rel {M : Type*} [Field M] {π : M} (a : M) (hπ : π ≠ 0) {f U V W : M[X]}
    (h : V ^ 2 - f = U * W) :
    affModel π a 3 V ^ 2 - affModel π a 6 f = affModel π a 2 U * affModel π a 4 W := by
  unfold affModel
  have key := congrArg (fun p : M[X] => p.comp (C a + C π * X)) h
  simp only [sub_comp, mul_comp, pow_comp] at key
  have h_sq : (C (π ^ 3)⁻¹ : M[X]) ^ 2 = C (π ^ 6)⁻¹ := by
    calc
      (C (π ^ 3)⁻¹ : M[X]) ^ 2 = (C (π ^ 3)⁻¹ * C (π ^ 3)⁻¹) := by ring
      _ = C ((π ^ 3)⁻¹ * (π ^ 3)⁻¹) := by simp
      _ = C ((π ^ 6)⁻¹) := by
        congr 1
        field_simp [hπ]
  have h_mul : (C (π ^ 2)⁻¹ : M[X]) * C (π ^ 4)⁻¹ = C (π ^ 6)⁻¹ := by
    calc
      (C (π ^ 2)⁻¹ : M[X]) * C (π ^ 4)⁻¹ = C ((π ^ 2)⁻¹ * (π ^ 4)⁻¹) := by simp
      _ = C ((π ^ 6)⁻¹) := by
        congr 1
        field_simp [hπ]
  calc
    (C (π ^ 3)⁻¹ * V.comp (C a + C π * X)) ^ 2 - C (π ^ 6)⁻¹ * f.comp (C a + C π * X)
        = ((C (π ^ 3)⁻¹ : M[X]) ^ 2) * (V.comp (C a + C π * X)) ^ 2 - C (π ^ 6)⁻¹ * f.comp (C a + C π * X) := by ring
    _ = C (π ^ 6)⁻¹ * (V.comp (C a + C π * X)) ^ 2 - C (π ^ 6)⁻¹ * f.comp (C a + C π * X) := by rw [h_sq]
    _ = C (π ^ 6)⁻¹ * ((V.comp (C a + C π * X)) ^ 2 - f.comp (C a + C π * X)) := by ring
    _ = C (π ^ 6)⁻¹ * (U.comp (C a + C π * X) * W.comp (C a + C π * X)) := by rw [key]
    _ = (C (π ^ 6)⁻¹ * U.comp (C a + C π * X)) * W.comp (C a + C π * X) := by ring
    _ = ((C (π ^ 2)⁻¹ * C (π ^ 4)⁻¹) * U.comp (C a + C π * X)) * W.comp (C a + C π * X) := by rw [h_mul]
    _ = (C (π ^ 2)⁻¹ * U.comp (C a + C π * X)) * (C (π ^ 4)⁻¹ * W.comp (C a + C π * X)) := by ring

theorem affModel_eval {M : Type*} [Field M] {π : M} (a : M) (hπ : π ≠ 0) (n : ℕ) (P : M[X])
    (θ : M) : P.eval θ = π ^ n * (affModel π a n P).eval ((θ - a) / π) := by
  calc
    P.eval θ = π ^ n * ((π ^ n)⁻¹ * P.eval θ) := by
      field_simp [pow_ne_zero n hπ]
    _ = π ^ n * ((C (π ^ n)⁻¹ * P.comp (C a + C π * X)).eval ((θ - a) / π)) := by
      have h : (C (π ^ n)⁻¹ * P.comp (C a + C π * X)).eval ((θ - a) / π) = (π ^ n)⁻¹ * P.eval θ := by
        calc
          (C (π ^ n)⁻¹ * P.comp (C a + C π * X)).eval ((θ - a) / π)
              = (C (π ^ n)⁻¹).eval ((θ - a) / π) * (P.comp (C a + C π * X)).eval ((θ - a) / π) := by
            rw [eval_mul]
          _ = (π ^ n)⁻¹ * (P.comp (C a + C π * X)).eval ((θ - a) / π) := by rw [eval_C]
          _ = (π ^ n)⁻¹ * P.eval ((C a + C π * X).eval ((θ - a) / π)) := by rw [eval_comp]
          _ = (π ^ n)⁻¹ * P.eval (a + π * ((θ - a) / π)) := by
            simp [eval_add, eval_C, eval_mul, eval_X]
          _ = (π ^ n)⁻¹ * P.eval (a + (θ - a)) := by
            field_simp [hπ]
          _ = (π ^ n)⁻¹ * P.eval θ := by
            have : a + (θ - a) = θ := by abel
            rw [this]
      rw [h]
    _ = π ^ n * (affModel π a n P).eval ((θ - a) / π) := rfl

theorem affModel_natDegree {M : Type*} [Field M] {π : M} (a : M) (hπ : π ≠ 0) (n : ℕ)
    (P : M[X]) : (affModel π a n P).natDegree = P.natDegree := by
  unfold affModel
  rw [Polynomial.natDegree_C_mul (inv_ne_zero (pow_ne_zero n hπ))]
  rw [Polynomial.natDegree_comp]
  have hdeg : (C a + C π * X).natDegree = 1 := by
    rw [add_comm, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X π hπ]
  rw [hdeg, mul_one]

theorem affModel_map {K L : Type*} [Field K] [Field L] (σ : K →+* L) (π a : K) (n : ℕ)
    (P : K[X]) : (affModel π a n P).map σ = affModel (σ π) (σ a) n (P.map σ) := by
  simp [affModel, Polynomial.map_comp]

theorem invModel_rel {M : Type*} [CommRing M] (i : M) {f U V W : M[X]} (hU : U.natDegree ≤ 2)
    (hV : V.natDegree ≤ 3) (hW : W.natDegree ≤ 4) (h : V ^ 2 - f = U * W) :
    invModel i 3 V ^ 2 - invModel i 6 f = invModel i 2 U * invModel i 4 W := by
  set g := X + C i with hg
  have hg_deg : natDegree g ≤ 1 := by
    calc
      natDegree g ≤ max (natDegree (X : M[X])) (natDegree (C i : M[X])) := natDegree_add_le _ _
      _ ≤ max 1 0 := by
        refine max_le_max ?_ ?_
        · exact natDegree_X_le
        · rw [natDegree_C]
      _ = 1 := by simp
  have hV_comp_deg : natDegree (V.comp g) ≤ 3 := by
    calc
      natDegree (V.comp g) ≤ natDegree V * natDegree g := natDegree_comp_le
      _ ≤ 3 * 1 := by nlinarith
      _ = 3 := by simp
  have hU_comp_deg : natDegree (U.comp g) ≤ 2 := by
    calc
      natDegree (U.comp g) ≤ natDegree U * natDegree g := natDegree_comp_le
      _ ≤ 2 * 1 := by nlinarith
      _ = 2 := by simp
  have hW_comp_deg : natDegree (W.comp g) ≤ 4 := by
    calc
      natDegree (W.comp g) ≤ natDegree W * natDegree g := natDegree_comp_le
      _ ≤ 4 * 1 := by nlinarith
      _ = 4 := by simp
  have h_comp : (V.comp g) ^ 2 - f.comp g = (U.comp g) * (W.comp g) := by
    calc
      (V.comp g) ^ 2 - f.comp g = (V ^ 2).comp g - f.comp g := by
        simpa using ((compRingHom g).map_pow V 2)
      _ = (V ^ 2 - f).comp g := by
        simpa using ((compRingHom g).map_sub (V ^ 2) f)
      _ = (U * W).comp g := by rw [h]
      _ = (U.comp g) * (W.comp g) := by
        simpa using ((compRingHom g).map_mul U W)
  have h_reflect := congrArg (reflect 6) h_comp
  rw [Polynomial.reflect_sub, Polynomial.reflect_mul (U.comp g) (W.comp g) hU_comp_deg hW_comp_deg] at h_reflect
  have h_sq : reflect 6 ((V.comp g) ^ 2) = reflect 3 (V.comp g) * reflect 3 (V.comp g) := by
    calc
      reflect 6 ((V.comp g) ^ 2) = reflect 6 ((V.comp g) * (V.comp g)) := by rw [sq]
      _ = reflect (3 + 3) ((V.comp g) * (V.comp g)) := by ring
      _ = reflect 3 (V.comp g) * reflect 3 (V.comp g) :=
        Polynomial.reflect_mul _ _ hV_comp_deg hV_comp_deg
  rw [h_sq] at h_reflect
  unfold invModel
  have h_sq' : (reflect 3 (V.comp (X + C i))) ^ 2 = reflect 3 (V.comp (X + C i)) * reflect 3 (V.comp (X + C i)) := by ring
  rw [h_sq']
  simpa [hg] using h_reflect

theorem invModel_eval {M : Type*} [Field M] (i : M) {n : ℕ} {P : M[X]} (hP : P.natDegree ≤ n)
    {x : M} (hx : x - i ≠ 0) : P.eval x = (x - i) ^ n * (invModel i n P).eval (x - i)⁻¹ := by
  set y := x - i with hy
  have hy_ne : y ≠ 0 := hx
  haveI : Invertible y := invertibleOfNonzero hy_ne
  have h_inv : ⅟y = y⁻¹ := invOf_eq_inv y
  set Q := P.comp (X + C i) with hQ
  have hQ_deg : Q.natDegree ≤ n := by
    calc
      Q.natDegree ≤ P.natDegree * (X + C i).natDegree := natDegree_comp_le
      _ = P.natDegree * 1 := by rw [natDegree_X_add_C]
      _ = P.natDegree := by simp
      _ ≤ n := hP
  have h_inv_model : invModel i n P = reflect n Q := rfl
  rw [h_inv_model]
  have h_eval_Q : Q.eval y = P.eval x := by
    rw [hQ, eval_comp, eval_add, eval_X, eval_C, sub_add_cancel]
  have h_eq := eval₂_reflect_mul_pow (RingHom.id M) y n Q hQ_deg
  rw [eval₂_id, eval₂_id, h_inv] at h_eq
  rw [← h_eval_Q, ← h_eq, mul_comm]

theorem invModel_coeff {M : Type*} [CommRing M] (i : M) (n : ℕ) (P : M[X]) :
    (invModel i n P).coeff n = P.eval i := by
  unfold invModel
  rw [Polynomial.coeff_reflect]
  have h : (revAt n) n = 0 := by
    rw [Polynomial.revAt_le (le_refl n), Nat.sub_self]
  rw [h]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  rw [Polynomial.eval_comp]
  simp

theorem invModel_natDegree_le {M : Type*} [CommRing M] (i : M) {n : ℕ} {P : M[X]}
    (hP : P.natDegree ≤ n) : (invModel i n P).natDegree ≤ n := by
  unfold invModel
  have h_deg : (X + C i).natDegree ≤ 1 := by
    calc
      (X + C i).natDegree ≤ max (X.natDegree) (C i).natDegree := natDegree_add_le _ _
      _ ≤ max 1 (C i).natDegree := max_le_max natDegree_X_le (le_refl _)
      _ = max 1 0 := by rw [natDegree_C]
      _ = 1 := by simp
  have h_comp : (P.comp (X + C i)).natDegree ≤ n := by
    calc
      (P.comp (X + C i)).natDegree ≤ P.natDegree * (X + C i).natDegree := natDegree_comp_le
      _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ h_deg
      _ = P.natDegree := by simp
      _ ≤ n := hP
  calc
    (reflect n (P.comp (X + C i))).natDegree ≤ max n (P.comp (X + C i)).natDegree := natDegree_reflect_le
    _ ≤ max n n := max_le_max (le_refl n) h_comp
    _ = n := by simp

theorem invModel_natDegree {M : Type*} [Field M] (i : M) {n : ℕ} {P : M[X]}
    (hP : P.natDegree ≤ n) (hi : P.eval i ≠ 0) : (invModel i n P).natDegree = n := by
  have hle : (invModel i n P).natDegree ≤ n := invModel_natDegree_le (M := M) i hP
  have hcoeff : (invModel i n P).coeff n = P.eval i := invModel_coeff i n P
  have hcoeff_ne_zero : (invModel i n P).coeff n ≠ 0 := by
    rw [hcoeff]
    exact hi
  have hge : n ≤ (invModel i n P).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hcoeff_ne_zero
  exact Nat.le_antisymm hle hge

theorem invModel_map {K L : Type*} [CommRing K] [CommRing L] (σ : K →+* L) (i : K) (n : ℕ)
    (P : K[X]) : (invModel i n P).map σ = invModel (σ i) n (P.map σ) := by
  dsimp [invModel]
  rw [← Polynomial.reflect_map]
  rw [Polynomial.map_comp]
  simp

theorem modByMonic_rel {M : Type*} [CommRing M] {f U V W : M[X]} (hU : U.Monic)
    (h : V ^ 2 - f = U * W) : ∃ W' : M[X], (V %ₘ U) ^ 2 - f = U * W' := by
  set q := V /ₘ U with hq
  set r := V %ₘ U with hr
  have hdiv : r + U * q = V := by
    rw [hr, hq]
    exact modByMonic_add_div V U
  have hr_eq : r = V - U * q := eq_sub_iff_add_eq.mpr hdiv
  refine ⟨W - 2 * V * q + U * q ^ 2, ?_⟩
  calc
    r ^ 2 - f = (V - U * q) ^ 2 - f := by rw [hr_eq]
    _ = (V ^ 2 - f) - 2 * V * U * q + U ^ 2 * q ^ 2 := by ring
    _ = U * W - 2 * V * U * q + U ^ 2 * q ^ 2 := by rw [h]
    _ = U * (W - 2 * V * q + U * q ^ 2) := by ring

theorem exists_shift {M : Type*} [Field M] (h2 : (2 : M) ≠ 0) {U : M[X]} (hU : U.natDegree = 2) :
    ∃ i : ℕ, i ≤ 2 ∧ U.eval (i : M) ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : U.eval (0 : M) = 0 := by simpa using h 0 (by omega)
  have h1 : U.eval (1 : M) = 0 := by simpa using h 1 (by omega)
  have h2' : U.eval (2 : M) = 0 := by simpa using h 2 (by omega)
  have hUzero : U = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero U (ι := Fin 3)
      (f := fun i => match i with | 0 => (0 : M) | 1 => (1 : M) | 2 => (2 : M))
      ?_ ?_ ?_
    · intro i j heq
      dsimp at heq
      match i, j with
      | 0, 0 => rfl
      | 0, 1 => simp at heq
      | 0, 2 =>
        have : (0 : M) = (2 : M) := by simpa using heq
        exact (h2 this.symm).elim
      | 1, 0 => simp at heq
      | 1, 1 => rfl
      | 1, 2 =>
        have h12 : (1 : M) = (2 : M) := by simpa using heq
        have h01 : (0 : M) = (1 : M) := by
          calc
            (0 : M) = (1 : M) - (1 : M) := by simp
            _ = (2 : M) - (1 : M) := by rw [h12]
            _ = (1 : M) := by norm_num
        exact (zero_ne_one h01).elim
      | 2, 0 =>
        have : (2 : M) = (0 : M) := by simpa using heq
        exact (h2 this).elim
      | 2, 1 =>
        have h21 : (2 : M) = (1 : M) := by simpa using heq
        have h01 : (1 : M) = (0 : M) := by
          calc
            (1 : M) = (2 : M) - (1 : M) := by norm_num
            _ = (1 : M) - (1 : M) := by rw [h21]
            _ = (0 : M) := by simp
        exact (zero_ne_one h01.symm).elim
      | 2, 2 => rfl
    · intro i
      fin_cases i <;> simp [h0, h1, h2']
    · rw [hU]
      have : Fintype.card (Fin 3) = 3 := by decide
      rw [this]
      omega
  rw [hUzero, natDegree_zero] at hU
  omega

/-! ### Integrality and content under the changes of model -/

theorem integral_comp {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) {P Q : M[X]} (hP : ∀ j, v (P.coeff j) ≤ 1)
    (hQ : ∀ j, v (Q.coeff j) ≤ 1) : ∀ j, v ((P.comp Q).coeff j) ≤ 1 := by
  have hQpow : ∀ (i j : ℕ), v ((Q ^ i).coeff j) ≤ 1 := by
    intro i
    induction' i with i ih
    · intro j
      rw [pow_zero, coeff_one]
      split <;> simp
    · intro j
      rw [pow_succ, coeff_mul]
      refine v.map_sum_le fun x hx => ?_
      have hx1 : v ((Q ^ i).coeff x.1) ≤ 1 := ih x.1
      have hx2 : v (Q.coeff x.2) ≤ 1 := hQ x.2
      rw [v.map_mul]
      exact mul_le_one' hx1 hx2
  intro j
  rw [comp_eq_sum_left, coeff_sum]
  refine v.map_sum_le fun i hi => ?_
  simp
  exact mul_le_one' (hP i) (hQpow i j)

theorem coeff_pow_le_one_of_le_one {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) (Q : M[X]) (hQ : ∀ j, v (Q.coeff j) ≤ 1) (i j : ℕ) :
    v ((Q ^ i).coeff j) ≤ 1 := by
  induction i generalizing j with
  | zero =>
    rw [pow_zero]
    rcases em (j = 0) with (rfl | hj)
    · rw [coeff_one_zero, Valuation.map_one]
    · rw [coeff_one, ite_eq_right hj, Valuation.map_zero]
      apply zero_le
  | succ i ih =>
    rw [pow_succ, coeff_mul]
    apply Valuation.map_sum_le v
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h1 : v ((Q ^ i).coeff x.1) ≤ 1 := ih x.1
    have h2 : v (Q.coeff x.2) ≤ 1 := hQ x.2
    have h1_nonneg : 0 ≤ v ((Q ^ i).coeff x.1) := by apply zero_le
    have h2_nonneg : 0 ≤ v (Q.coeff x.2) := by apply zero_le
    rw [Valuation.map_mul v]
    calc
      v ((Q ^ i).coeff x.1) * v (Q.coeff x.2) ≤ 1 * v (Q.coeff x.2) :=
        mul_le_mul_of_nonneg_right h1 h2_nonneg
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 1 := by simp

theorem lt_one_comp {M : Type*} [Field M] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation M Γ₀) {P Q : M[X]} (hP : ∀ j, v (P.coeff j) < 1)
    (hQ : ∀ j, v (Q.coeff j) ≤ 1) : ∀ j, v ((P.comp Q).coeff j) < 1 := by
  intro j
  rw [Polynomial.comp_eq_sum_left, Polynomial.coeff_sum]
  have hsum : (P.sum fun e a => (C a * Q ^ e).coeff j) =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (Q ^ i).coeff j := by
    rw [Polynomial.sum_over_range P (f := fun n a => (C a * Q ^ n).coeff j) (by
      intro n
      simp)]
    simp
  rw [hsum]
  apply Valuation.map_sum_lt v (one_ne_zero)
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Valuation.map_mul v]
  have hP_i : v (P.coeff i) < 1 := hP i
  have hQ_i : v ((Q ^ i).coeff j) ≤ 1 := coeff_pow_le_one_of_le_one v Q hQ i j
  have hP_nonneg : 0 ≤ v (P.coeff i) := by apply zero_le
  have hQ_nonneg : 0 ≤ v ((Q ^ i).coeff j) := by apply zero_le
  calc
    v (P.coeff i) * v ((Q ^ i).coeff j) ≤ v (P.coeff i) * 1 :=
      mul_le_mul_of_nonneg_left hQ_i hP_nonneg
    _ = v (P.coeff i) := by simp
    _ < 1 := hP_i


theorem integral_invModel {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {i : M} (hi : v i ≤ 1) (n : ℕ)
    {P : M[X]} (hP : ∀ j, v (P.coeff j) ≤ 1) : ∀ j, v ((invModel i n P).coeff j) ≤ 1 := by
  intro j
  unfold invModel
  rw [Polynomial.coeff_reflect]
  have hQ : ∀ j, v ((X + C i).coeff j) ≤ 1 := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0
      simp [hi, Polynomial.coeff_add, Polynomial.coeff_X]
    · by_cases hj1 : j = 1
      · subst hj1
        simp [Valuation.map_one, Polynomial.coeff_add, Polynomial.coeff_X]
      · have hcoeff : (X + C i).coeff j = 0 := by
          simp [hj0, Ne.symm hj1, Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
        simp [hcoeff, Valuation.map_zero]
  exact integral_comp v hP hQ (Polynomial.revAt n j)

theorem primitive_invModel {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {i : M} (hi : v i ≤ 1) (n : ℕ)
    {P : M[X]} (hP : ∀ j, v (P.coeff j) ≤ 1) (hP1 : ∃ j, v (P.coeff j) = 1) :
    ∃ j, v ((invModel i n P).coeff j) = 1 := by
  set Q := P.comp (X + C i) with hQdef
  have hXaddC_coeff (j : ℕ) : v ((X + C i).coeff j) ≤ 1 := by
    simp only [coeff_add, coeff_X, coeff_C]
    by_cases h0 : j = 0
    · subst h0; simp [hi]
    · by_cases h1 : j = 1
      · subst h1; simp [Valuation.map_one]
      · simp [h0, h1, eq_comm]
  have hXsubC_coeff (j : ℕ) : v ((X - C i).coeff j) ≤ 1 := by
    simp only [coeff_sub, coeff_X, coeff_C]
    by_cases h0 : j = 0
    · subst h0; simp [Valuation.map_neg, hi]
    · by_cases h1 : j = 1
      · subst h1; simp [Valuation.map_one]
      · simp [h0, h1, eq_comm]
  have hQ_int : ∀ j, v (Q.coeff j) ≤ 1 := by
    rw [hQdef]
    apply integral_comp v hP hXaddC_coeff
  have h_exists : ∃ j, v (Q.coeff j) = 1 := by
    by_contra! h_all_ne
    -- h_all_ne: ∀ j, v (Q.coeff j) ≠ 1
    have h_all_lt : ∀ j, v (Q.coeff j) < 1 := by
      intro j
      have hle := hQ_int j
      have hne : v (Q.coeff j) ≠ 1 := h_all_ne j
      exact lt_of_le_of_ne hle hne
    have hP_eq : P = Q.comp (X - C i) := by
      calc
        P = P.comp X := by simp
        _ = P.comp ((X + C i).comp (X - C i)) := by
          simp
        _ = (P.comp (X + C i)).comp (X - C i) := by rw [comp_assoc]
        _ = Q.comp (X - C i) := by rw [hQdef]
    have hP_lt : ∀ j, v (P.coeff j) < 1 := by
      rw [hP_eq]
      apply lt_one_comp v h_all_lt hXsubC_coeff
    rcases hP1 with ⟨j, hj⟩
    have := hP_lt j
    rw [hj] at this
    exact lt_irrefl _ this
  rcases h_exists with ⟨j, hj⟩
  refine ⟨revAt n j, ?_⟩
  have hcoeff : (invModel i n P).coeff (revAt n j) = Q.coeff j := by
    dsimp [invModel]
    rw [hQdef]
    rw [coeff_reflect, revAt_invol]
  rw [hcoeff, hj]

theorem derivative_eval_eq_one_of_bezout {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {f A B : M[X]} {e x : M}
    (h : A * f + B * derivative f = C e) (hf : ∀ j, v (f.coeff j) ≤ 1)
    (hB : ∀ j, v (B.coeff j) ≤ 1) (he : v e = 1) (hx : v x ≤ 1) (hfx : f.eval x = 0) :
    v (f.derivative.eval x) = 1 := by
  -- Evaluate the equation h at x
  have h_eval : (A * f + B * derivative f).eval x = (C e).eval x := by rw [h]
  -- Simplify both sides using eval properties
  simp [eval_add, eval_mul, eval_C, hfx] at h_eval
  -- Now h_eval : B.eval x * f.derivative.eval x = e
  -- Apply v to both sides
  have h_val : v (B.eval x * f.derivative.eval x) = v e := by rw [h_eval]
  rw [Valuation.map_mul, he] at h_val
  -- Now h_val : v (B.eval x) * v (f.derivative.eval x) = 1
  -- Get upper bounds from the hypotheses
  have hB_eval : v (B.eval x) ≤ 1 := eval_le_one v hB hx
  have hf'_eval : v (f.derivative.eval x) ≤ 1 :=
    eval_le_one v (derivative_le_one v hf) hx
  -- Show that v (f.derivative.eval x) cannot be < 1
  rcases lt_or_eq_of_le hf'_eval with (h_lt | h_eq)
  · -- h_lt : v (f.derivative.eval x) < 1
    have h_prod_lt_one : v (B.eval x) * v (f.derivative.eval x) < 1 := by
      calc
        v (B.eval x) * v (f.derivative.eval x) ≤ 1 * v (f.derivative.eval x) :=
          mul_le_mul' hB_eval (le_refl _)
        _ = v (f.derivative.eval x) := by simp
        _ < 1 := h_lt
    rw [h_val] at h_prod_lt_one
    exfalso
    exact lt_irrefl 1 h_prod_lt_one
  · -- h_eq : v (f.derivative.eval x) = 1
    exact h_eq

theorem invModel_C_mul {M : Type*} [CommRing M] (i a : M) (n : ℕ) (P : M[X]) :
    invModel i n (C a * P) = C a * invModel i n P := by
  unfold invModel
  rw [mul_comp, C_comp, reflect_C_mul]

theorem exists_val_eq_one {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀) {s : Finset ℕ} {g b : ℕ → M}
    (hg : ∀ j, v (g j) ≤ 1) (hb : ∀ j, v (b j) ≤ 1) (h : ∑ j ∈ s, b j * g j = 1) :
    ∃ j, v (g j) = 1 := by
  by_contra! H
  -- H: ∀ j, v (g j) ≠ 1
  have hlt : ∀ j, v (g j) < 1 := by
    intro j
    exact lt_of_le_of_ne (hg j) (H j)
  have hsum_lt : v (∑ j ∈ s, b j * g j) < 1 := by
    apply Valuation.map_sum_lt v (by norm_num : (1 : Γ₀) ≠ 0)
    intro j hj
    calc
      v (b j * g j) = v (b j) * v (g j) := Valuation.map_mul v (b j) (g j)
      _ ≤ 1 * v (g j) := mul_le_mul_left (hb j) (v (g j))
      _ = v (g j) := one_mul (v (g j))
      _ < 1 := hlt j
  rw [h, Valuation.map_one] at hsum_lt
  exact lt_irrefl 1 hsum_lt

end Schaefer

open Schaefer in
/-- **Schaefer's lemma through the two changes of model, value group form.** -/
theorem schaefer_model_sq {M : Type*} [Field M] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation M Γ₀)
    {f U V W A1 B1 : M[X]} {θ π a c e1 : M} {A2 B2 : ℕ → M[X]} {r2 : ℕ → M}
    (h2 : (2 : M) ≠ 0) (hπ : π ≠ 0)
    (hw : V ^ 2 - f = U * W) (hU : U.natDegree = 2) (hV : V.natDegree ≤ 1) (hθ : f.eval θ = 0)
    (hf1 : ∀ j, v ((affModel π a 6 f).coeff j) ≤ 1) (hf1deg : (affModel π a 6 f).natDegree = 6)
    (hbez1 : A1 * affModel π a 6 f + B1 * derivative (affModel π a 6 f) = C e1)
    (hB1 : ∀ j, v (B1.coeff j) ≤ 1)
    (he1 : v (affModel π a 6 f).leadingCoeff = 1 → v e1 = 1)
    (hbez2 : ∀ i : ℕ, i ≤ 2 → A2 i * invModel (i : M) 6 (affModel π a 6 f) +
      B2 i * derivative (invModel (i : M) 6 (affModel π a 6 f)) = C (r2 i))
    (hB2 : ∀ i : ℕ, i ≤ 2 → ∀ j, v ((B2 i).coeff j) ≤ 1)
    (hlc : v (affModel π a 6 f).leadingCoeff < 1 → ∀ i : ℕ, i ≤ 2 →
      v ((affModel π a 6 f).eval (i : M)) = 1 ∧ v (r2 i) = 1)
    (hc : ∀ j, v ((affModel π a 2 U).coeff j / c) ≤ 1)
    (hc1 : ∃ j, v ((affModel π a 2 U).coeff j / c) = 1) :
    ∃ y : M, v (U.eval θ / c) = v y ^ 2 := by
  classical
  set f1 := affModel π a 6 f with hf1def
  set U1 := affModel π a 2 U with hU1def
  set V1 := affModel π a 3 V with hV1def
  set W1 := affModel π a 4 W with hW1def
  set θ1 := (θ - a) / π with hθ1def
  have hrel1 : V1 ^ 2 - f1 = U1 * W1 := affModel_rel a hπ hw
  have hUθ : U.eval θ = π ^ 2 * U1.eval θ1 := affModel_eval a hπ 2 U θ
  have hfθ : f.eval θ = π ^ 6 * f1.eval θ1 := affModel_eval a hπ 6 f θ
  have hf1θ : f1.eval θ1 = 0 := by
    rw [hθ] at hfθ
    exact (mul_eq_zero.mp hfθ.symm).resolve_left (pow_ne_zero _ hπ)
  have hU1deg : U1.natDegree = 2 := by rw [hU1def, affModel_natDegree a hπ]; exact hU
  have hV1deg : V1.natDegree ≤ 1 := by rw [hV1def, affModel_natDegree a hπ]; exact hV
  suffices h : ∃ y : M, v (U1.eval θ1 / c) = v y ^ 2 by
    obtain ⟨y, hy⟩ := h
    refine ⟨π * y, ?_⟩
    rw [hUθ, mul_div_assoc, map_mul, hy, map_mul, map_pow, mul_pow]
  by_cases hl : v f1.leadingCoeff = 1
  · have hθ1le : v θ1 ≤ 1 := root_le_one v hf1 hl (by rw [hf1deg]; norm_num) hf1θ
    have hd : v (f1.derivative.eval θ1) = 1 :=
      derivative_eval_eq_one_of_bezout v hbez1 hf1 hB1 (he1 hl) hθ1le hf1θ
    exact schaefer_local_sq v hf1 hf1deg hl hf1θ hd hU1deg hV1deg hrel1 hc hc1
  · have hl' : v f1.leadingCoeff < 1 := lt_of_le_of_ne (hf1 f1.natDegree) hl
    obtain ⟨i, hi2, hUi⟩ := exists_shift h2 hU1deg
    obtain ⟨hfi, hri⟩ := hlc hl' i hi2
    have hvi : v (i : M) ≤ 1 := valuation_natCast_le_one v i
    set f2 := invModel (i : M) 6 f1 with hf2def
    set u2 := invModel (i : M) 2 U1 with hu2def
    have hf2 : ∀ j, v (f2.coeff j) ≤ 1 := integral_invModel v hvi 6 hf1
    have hf1i0 : f1.eval (i : M) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hfi
      exact zero_ne_one hfi
    have hf2deg : f2.natDegree = 6 := invModel_natDegree (i : M) (le_of_eq hf1deg) hf1i0
    have hl2 : v f2.leadingCoeff = 1 := by
      rw [leadingCoeff, hf2deg, hf2def, invModel_coeff]
      exact hfi
    have hθi : θ1 - i ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      rw [h0] at hf1θ
      exact hf1i0 hf1θ
    have hf2θ : f2.eval (θ1 - i)⁻¹ = 0 := by
      have h := invModel_eval (i : M) (le_of_eq hf1deg) hθi
      rw [hf1θ] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hθi)
    have hθ2le : v (θ1 - i)⁻¹ ≤ 1 := root_le_one v hf2 hl2 (by rw [hf2deg]; norm_num) hf2θ
    have hd2 : v (f2.derivative.eval (θ1 - i)⁻¹) = 1 :=
      derivative_eval_eq_one_of_bezout v (hbez2 i hi2) hf2 (hB2 i hi2) hri hθ2le hf2θ
    have hu2deg : u2.natDegree = 2 := invModel_natDegree (i : M) (le_of_eq hU1deg) hUi
    have hW1deg : W1.natDegree = 4 := natDegree_eq_four hU1deg hV1deg hf1deg hrel1
    have hrel2 : invModel (i : M) 3 V1 ^ 2 - f2 = u2 * invModel (i : M) 4 W1 :=
      invModel_rel (i : M) (le_of_eq hU1deg) (hV1deg.trans (by norm_num)) (le_of_eq hW1deg) hrel1
    set x := U1.eval (i : M) with hx
    have hlcu2 : u2.leadingCoeff = x := by
      rw [leadingCoeff, hu2deg, hu2def, invModel_coeff]
    have hCC : C x⁻¹ * C x = (1 : M[X]) := by rw [← C_mul, inv_mul_cancel₀ hUi, C_1]
    have hm2 : (C x⁻¹ * u2).Monic := by
      rw [Monic, leadingCoeff_mul, leadingCoeff_C, hlcu2, inv_mul_cancel₀ hUi]
    have hm2deg : (C x⁻¹ * u2).natDegree = 2 := by
      rw [natDegree_C_mul (inv_ne_zero hUi), hu2deg]
    have hrel2' : invModel (i : M) 3 V1 ^ 2 - f2 =
        (C x⁻¹ * u2) * (C x * invModel (i : M) 4 W1) := by
      rw [hrel2, show C x⁻¹ * u2 * (C x * invModel (i : M) 4 W1) =
        (C x⁻¹ * C x) * (u2 * invModel (i : M) 4 W1) by ring, hCC, one_mul]
    obtain ⟨W2, hW2⟩ := modByMonic_rel hm2 hrel2'
    have hV2deg : (invModel (i : M) 3 V1 %ₘ (C x⁻¹ * u2)).natDegree ≤ 1 := by
      have hne : C x⁻¹ * u2 ≠ 1 := by
        intro h1
        rw [h1, natDegree_one] at hm2deg
        exact absurd hm2deg (by norm_num)
      have := natDegree_modByMonic_lt (invModel (i : M) 3 V1) hm2 hne
      omega
    have hrel3 : (invModel (i : M) 3 V1 %ₘ (C x⁻¹ * u2)) ^ 2 - f2 = u2 * (C x⁻¹ * W2) := by
      rw [hW2]
      ring
    have hcP : ∀ j, v ((C c⁻¹ * U1).coeff j) ≤ 1 := fun j => by
      rw [coeff_C_mul, inv_mul_eq_div]; exact hc j
    have hcP1 : ∃ j, v ((C c⁻¹ * U1).coeff j) = 1 := by
      obtain ⟨j, hj⟩ := hc1
      exact ⟨j, by rw [coeff_C_mul, inv_mul_eq_div]; exact hj⟩
    have hcu : ∀ j, v (u2.coeff j / c) ≤ 1 := fun j => by
      have h := integral_invModel v hvi 2 hcP j
      rwa [invModel_C_mul, coeff_C_mul, inv_mul_eq_div] at h
    have hcu1 : ∃ j, v (u2.coeff j / c) = 1 := by
      obtain ⟨j, hj⟩ := primitive_invModel v hvi 2 hcP hcP1
      refine ⟨j, ?_⟩
      rwa [invModel_C_mul, coeff_C_mul, inv_mul_eq_div] at hj
    obtain ⟨y, hy⟩ := schaefer_local_sq v hf2 hf2deg hl2 hf2θ hd2 hu2deg hV2deg hrel3 hcu hcu1
    refine ⟨(θ1 - i) * y, ?_⟩
    have hU1θ : U1.eval θ1 = (θ1 - i) ^ 2 * u2.eval (θ1 - i)⁻¹ :=
      invModel_eval (i : M) (le_of_eq hU1deg) hθi
    rw [hU1θ, mul_div_assoc, map_mul, hy, map_mul, map_pow, mul_pow]

namespace Schaefer

/-! ### Number field facts -/

theorem val_le_one_of_isIntegral {F : Type*} [Field F] [NumberField F]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {x : F} (hx : IsIntegral ℤ x) :
    P.valuation F x ≤ 1 := by
  have hinst : IsIntegralClosure (𝓞 F) ℤ F := inferInstance
  rcases ((hinst.isIntegral_iff).mp hx) with ⟨y, hy⟩
  have h := P.valuation_le_one (R := 𝓞 F) (K := F) y
  simpa [hy] using h

theorem val_natCast_eq_one {F : Type*} [Field F] [NumberField F]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {D : ℕ} (hD : (D : 𝓞 F) ∉ P.asIdeal) :
    P.valuation F (D : F) = 1 := by
  have h1 : (D : F) = algebraMap (𝓞 F) F (D : 𝓞 F) := by
    simp
  rw [h1]
  rw [P.valuation_of_algebraMap]
  rw [P.intValuation_eq_one_iff]
  exact hD

theorem val_le_one_of_scaled {K F : Type*} [Field K] [Field F] [NumberField F] [Algebra K F]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {D : ℕ} (hD : (D : 𝓞 F) ∉ P.asIdeal)
    (N : ℕ) {x : K} (hx : IsIntegral ℤ ((D : K) ^ N * x)) :
    P.valuation F (algebraMap K F x) ≤ 1 := by
  have h_int : IsIntegral ℤ ((algebraMap K F) ((D : K) ^ N * x)) :=
    IsIntegral.algebraMap hx
  have h_val : P.valuation F (algebraMap K F ((D : K) ^ N * x)) ≤ 1 :=
    val_le_one_of_isIntegral P h_int
  have h_eq : algebraMap K F ((D : K) ^ N * x) = (D : F) ^ N * algebraMap K F x := by
    simp [map_mul, map_pow, map_natCast]
  rw [h_eq] at h_val
  have h_val_D : P.valuation F ((D : F) ^ N) = 1 := by
    calc
      P.valuation F ((D : F) ^ N) = (P.valuation F (D : F)) ^ N := by
        rw [Valuation.map_pow]
      _ = 1 ^ N := by rw [val_natCast_eq_one P hD]
      _ = 1 := by simp
  have h_mul : P.valuation F ((D : F) ^ N * algebraMap K F x) =
      P.valuation F ((D : F) ^ N) * P.valuation F (algebraMap K F x) := by
    rw [Valuation.map_mul]
  rw [h_mul, h_val_D, one_mul] at h_val
  exact h_val

theorem val_eq_one_of_mul_eq {K F : Type*} [Field K] [Field F] [NumberField F] [Algebra K F]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {D : ℕ} (hD : (D : 𝓞 F) ∉ P.asIdeal)
    (N : ℕ) {e e' : K} (he : IsIntegral ℤ e) (he' : IsIntegral ℤ e')
    (h : e * e' = (D : K) ^ N) : P.valuation F (algebraMap K F e) = 1 := by
  set σ := algebraMap K F
  have hσe_int : IsIntegral ℤ (σ e) :=
    map_isIntegral_int (σ : K →+* F).toIntAlgHom he
  have hσe'_int : IsIntegral ℤ (σ e') :=
    map_isIntegral_int (σ : K →+* F).toIntAlgHom he'
  have h_val_le_one : P.valuation F (σ e) ≤ 1 :=
    val_le_one_of_isIntegral P hσe_int
  have h_val_le_one' : P.valuation F (σ e') ≤ 1 :=
    val_le_one_of_isIntegral P hσe'_int
  have h_prod : σ e * σ e' = ((D : F) ^ N) := by
    calc
      σ e * σ e' = σ (e * e') := by rw [map_mul]
      _ = σ ((D : K) ^ N) := by rw [h]
      _ = (σ (D : K)) ^ N := by rw [map_pow]
      _ = (D : F) ^ N := by simp
  have h_val_prod : P.valuation F (σ e * σ e') = P.valuation F ((D : F) ^ N) := by rw [h_prod]
  have h_val_D_pow : P.valuation F ((D : F) ^ N) = 1 := by
    calc
      P.valuation F ((D : F) ^ N) = (P.valuation F (D : F)) ^ N := by rw [Valuation.map_pow]
      _ = 1 ^ N := by rw [val_natCast_eq_one P hD]
      _ = 1 := by simp
  have h_val_prod_eq_one : P.valuation F (σ e * σ e') = 1 := by
    rw [h_val_prod, h_val_D_pow]
  have h_val_mul : P.valuation F (σ e * σ e') = P.valuation F (σ e) * P.valuation F (σ e') := by
    rw [Valuation.map_mul]
  have h_val_mul_eq_one : P.valuation F (σ e) * P.valuation F (σ e') = 1 := by
    rw [← h_val_mul, h_val_prod_eq_one]
  have h_val_one : P.valuation F (σ e) = 1 := by
    -- In a LinearOrderedCommMonoidWithZero, if a ≤ 1, b ≤ 1, a * b = 1, then a = 1
    -- We need a lemma for this. Let's use the fact that if a < 1 then a * b ≤ a * 1 < 1
    by_contra! hlt
    have hlt' : P.valuation F (σ e) < 1 := by
      exact lt_of_le_of_ne h_val_le_one hlt
    have h_nonneg : 0 ≤ P.valuation F (σ e) := zero_le (a := P.valuation F (σ e))
    have : P.valuation F (σ e) * P.valuation F (σ e') < 1 := by
      -- Since v(σ e) < 1 and v(σ e') ≤ 1, their product is < 1
      calc
        P.valuation F (σ e) * P.valuation F (σ e') ≤ P.valuation F (σ e) * 1 :=
          mul_le_mul_of_nonneg_left h_val_le_one' h_nonneg
        _ = P.valuation F (σ e) := by simp
        _ < 1 := hlt'
    rw [h_val_mul_eq_one] at this
    exact lt_irrefl 1 this
  exact h_val_one

/-- A generator of the content ideal of a nonzero polynomial over a number field with principal
ring of integers: `P / c` is integral with coefficients generating the unit ideal. -/
theorem exists_content {K : Type*} [Field K] [NumberField K] [IsPrincipalIdealRing (𝓞 K)]
    {P : K[X]} (hP : P ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ (∀ j, IsIntegral ℤ (P.coeff j / c)) ∧ ∃ b : ℕ → K,
      (∀ j, IsIntegral ℤ (b j)) ∧ ∑ j ∈ Finset.range (P.natDegree + 1), b j * (P.coeff j / c) = 1 := by
  classical
  let s := Finset.range (P.natDegree + 1)
  -- Clear denominators: get d : nonZeroDivisors (𝓞 K) such that d * P.coeff j is integral for j ∈ s
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) s P.coeff
  set d' := (algebraMap (𝓞 K) K) (d : 𝓞 K) with hd'_def
  have hd'_ne_zero : d' ≠ 0 := by
    have hmem := d.prop
    have hne : (d : 𝓞 K) ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero.mp hmem)
    intro hzero
    apply hne
    apply NumberField.RingOfIntegers.coe_injective
    rw [← hd'_def, hzero, map_zero]
  -- For each j ∈ s, get p_j : 𝓞 K such that (p_j : K) = d' * P.coeff j
  have h_coeff_int : ∀ j, j ∈ s → ∃ p : 𝓞 K, (p : K) = d' * P.coeff j := by
    intro j hj
    rcases hd j hj with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    simpa [Algebra.smul_def, hd'_def] using hp
  -- Use choice to get a function p : ℕ → 𝓞 K
  let p : ℕ → 𝓞 K := fun j =>
    if hj : j ∈ s then (Classical.choose (h_coeff_int j hj)) else 0
  have hp : ∀ j ∈ s, (p j : K) = d' * P.coeff j := by
    intro j hj
    dsimp [p]
    rw [dif_pos hj]
    exact Classical.choose_spec (h_coeff_int j hj)
  -- Form the ideal I generated by the p_j for j ∈ s
  let I : Ideal (𝓞 K) := Ideal.span (Finset.image p s)
  have h_principal : Submodule.IsPrincipal I := by
    infer_instance
  set g := Submodule.IsPrincipal.generator I with hg_def
  have hg_spec : Submodule.span (𝓞 K) {g} = I :=
    Submodule.IsPrincipal.span_singleton_generator I
  have hgK_ne_zero : (g : K) ≠ 0 := by
    intro hgzero
    have hgzero' : g = 0 := NumberField.RingOfIntegers.coe_injective hgzero
    have h_leading_mem : p (natDegree P) ∈ I := by
      apply Ideal.subset_span
      apply Finset.mem_image.mpr
      refine ⟨natDegree P, Finset.mem_range.mpr (Nat.lt_succ_self _), rfl⟩
    rw [← hg_spec, hgzero'] at h_leading_mem
    rw [Submodule.mem_span_singleton] at h_leading_mem
    rcases h_leading_mem with ⟨a, ha⟩
    have h_leading_eq : (p (natDegree P) : K) = d' * P.coeff (natDegree P) :=
      hp (natDegree P) (Finset.mem_range.mpr (Nat.lt_succ_self _))
    have h_coeff_ne_zero : P.coeff (natDegree P) ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hP
    have hp_ne_zero : p (natDegree P) ≠ 0 := by
      intro hzero
      have hzero' : (p (natDegree P) : K) = 0 := by simpa [hzero]
      rw [h_leading_eq] at hzero'
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hzero' with (hd0 | hc0)
      · exact hd'_ne_zero hd0
      · exact h_coeff_ne_zero hc0
    apply hp_ne_zero
    simpa [hgzero'] using ha.symm
  -- Set c = g / d' in K
  let c : K := (g : K) / d'
  have hc_ne_zero : c ≠ 0 := by
    intro hczero
    apply hgK_ne_zero
    have := div_eq_zero_iff.mp hczero
    rcases this with (hg0 | hd0)
    · exact hg0
    · exact absurd hd0 hd'_ne_zero
  -- Helper lemma: for j ∈ s, P.coeff j / c = (p j : K) / (g : K)
  have h_coeff_div_c_eq : ∀ j ∈ s, P.coeff j / c = (p j : K) / (g : K) := by
    intro j hj
    calc
      P.coeff j / c = P.coeff j / ((g : K) / d') := rfl
      _ = (P.coeff j * d') / (g : K) := by
        field_simp [hc_ne_zero, hgK_ne_zero]
      _ = (d' * P.coeff j) / (g : K) := by ring
      _ = (p j : K) / (g : K) := by rw [← hp j hj]
  -- Now prove the main result
  have h_coeff_div_c_int : ∀ j, IsIntegral ℤ (P.coeff j / c) := by
    intro j
    by_cases hj : j < P.natDegree + 1
    · have hjs : j ∈ s := Finset.mem_range.mpr hj
      rw [h_coeff_div_c_eq j hjs]
      -- Now (p j : K) / (g : K) is integral because g ∣ p j
      have h_mem : p j ∈ I := by
        apply Ideal.subset_span
        apply Finset.mem_image.mpr
        exact ⟨j, hjs, rfl⟩
      -- I = Submodule.span (𝓞 K) {g} by hg_spec
      have h_mem_span : p j ∈ Submodule.span (𝓞 K) {g} :=
        hg_spec ▸ h_mem
      rw [Submodule.mem_span_singleton] at h_mem_span
      rcases h_mem_span with ⟨q, hq⟩
      -- hq : q • g = p j, i.e., q * g = p j in 𝓞 K
      have hq' : (q : K) * (g : K) = (p j : K) := by
        simpa [Algebra.smul_def] using congrArg (algebraMap (𝓞 K) K) hq
      have h_div : (p j : K) / (g : K) = (q : K) := by
        rw [← hq']
        field_simp [hgK_ne_zero]
      rw [h_div]
      -- (q : K) is integral because q ∈ 𝓞 K
      exact NumberField.RingOfIntegers.isIntegral_coe q
    · -- j ∉ s, so j ≥ natDegree + 1, hence P.coeff j = 0
      have hcoeff : P.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hcoeff]
      simp [isIntegral_zero]
  -- Now construct b : ℕ → K
  have h_sum : ∃ b : ℕ → K, (∀ j, IsIntegral ℤ (b j)) ∧
      ∑ j ∈ s, b j * (P.coeff j / c) = 1 := by
    -- g ∈ I = Submodule.span (𝓞 K) (Finset.image p s)
    -- Using mem_span_image_finset_iff_exists_fun' to write g as combination of p_j
    have hg_mem_span : g ∈ Submodule.span (𝓞 K) (p '' (s : Set ℕ)) := by
      -- I = Ideal.span (Finset.image p s) = Submodule.span (𝓞 K) (Finset.image p s)
      -- and (Finset.image p s : Set (𝓞 K)) = p '' (s : Set ℕ)
      simpa [I, Finset.coe_image] using (show g ∈ I from by
        -- g ∈ Submodule.span (𝓞 K) {g} = I
        rw [← hg_spec]
        exact Submodule.mem_span_singleton_self g)
    have hg_comb := (Submodule.mem_span_image_finset_iff_exists_fun' (R := 𝓞 K) (s := s) (v := p)).mp hg_mem_span
    rcases hg_comb with ⟨b', hb'⟩
    -- hb' : ∑ i ∈ s, b' i • p i = g  (in the submodule sense, i.e., in 𝓞 K)
    let b : ℕ → K := fun j => (b' j : K)
    have hb_int : ∀ j, IsIntegral ℤ (b j) := by
      intro j
      exact NumberField.RingOfIntegers.isIntegral_coe (b' j)
    have h_sum_eq_one : ∑ j ∈ s, b j * (P.coeff j / c) = 1 := by
      calc
        ∑ j ∈ s, b j * (P.coeff j / c) = ∑ j ∈ s, (b' j : K) * (P.coeff j / c) := rfl
        _ = ∑ j ∈ s, (b' j : K) * ((p j : K) / (g : K)) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [h_coeff_div_c_eq j hj]
        _ = ∑ j ∈ s, ((b' j : K) * (p j : K)) / (g : K) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          field_simp [hgK_ne_zero]
        _ = ((∑ j ∈ s, (b' j : K) * (p j : K)) : K) / (g : K) := by
          rw [Finset.sum_div]
        _ = ((∑ j ∈ s, b' j * p j : 𝓞 K) : K) / (g : K) := by
          simp
        _ = (g : K) / (g : K) := by
          -- From hb' : ∑ i ∈ s, b' i • p i = g
          -- In the ideal/module, a • x = a * x
          have hb'_eq : (∑ j ∈ s, b' j * p j : 𝓞 K) = g := by
            simpa [Algebra.smul_def] using hb'
          simp [hb'_eq]
        _ = 1 := by field_simp [hgK_ne_zero]
    refine ⟨b, hb_int, h_sum_eq_one⟩
  rcases h_sum with ⟨b, hb_int, hb_sum⟩
  exact ⟨c, hc_ne_zero, h_coeff_div_c_int, b, hb_int, hb_sum⟩

/-- In a linearly ordered commutative group with zero, a product of three elements at most `1`
equal to `1` has every factor `1` (the middle one here). -/
theorem mid_eq_one_of_mul {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {a b c : Γ₀}
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) (h : a * b * c = 1) : b = 1 := by
  by_contra hne
  have hb' : b < 1 := lt_of_le_of_ne hb hne
  have : a * b * c < 1 := by
    calc a * b * c ≤ a * b := mul_le_of_le_one_right' hc
      _ ≤ b := mul_le_of_le_one_left' ha
      _ < 1 := hb'
  exact absurd h (ne_of_lt this)

theorem val_sq_of_ne_zero {F : Type*} [Field F] [NumberField F]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {x y : F} (hx : x ≠ 0)
    (h : P.valuation F x = P.valuation F y ^ 2) :
    ∃ n : ℤ, P.valuation F x = WithZero.coe (Multiplicative.ofAdd (2 * n)) := by
  have hy : P.valuation F y ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at h
    exact hx ((Valuation.zero_iff _).mp h)
  obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp hy
  refine ⟨Multiplicative.toAdd m, ?_⟩
  rw [h, ← hm, ← WithZero.coe_pow]
  congr 1


end Schaefer

open Schaefer in
/-- **Schaefer's lemma through the two changes of model, number field form.** -/
theorem schaefer_global_of_certs {K : Type*} [Field K] [NumberField K]
    [IsPrincipalIdealRing (𝓞 K)] {f A1 B1 : K[X]} {π a e1 : K} {A2 B2 : ℕ → K[X]}
    {r2 y z : ℕ → K} (D N : ℕ) (hπ : π ≠ 0)
    (hf1 : ∀ j, IsIntegral ℤ ((D : K) ^ N * (affModel π a 6 f).coeff j))
    (hf1deg : (affModel π a 6 f).natDegree = 6)
    (hbez1 : A1 * affModel π a 6 f + B1 * derivative (affModel π a 6 f) =
      C (e1 * (affModel π a 6 f).leadingCoeff))
    (hB1 : ∀ j, IsIntegral ℤ ((D : K) ^ N * B1.coeff j))
    (he1 : IsIntegral ℤ e1) (he1' : ∃ e : K, IsIntegral ℤ e ∧ e1 * e = (D : K) ^ N)
    (hbez2 : ∀ i : ℕ, i ≤ 2 → A2 i * invModel (i : K) 6 (affModel π a 6 f) +
      B2 i * derivative (invModel (i : K) 6 (affModel π a 6 f)) = C (r2 i))
    (hB2 : ∀ i : ℕ, i ≤ 2 → ∀ j, IsIntegral ℤ ((D : K) ^ N * (B2 i).coeff j))
    (hr2 : ∀ i : ℕ, i ≤ 2 → IsIntegral ℤ ((D : K) ^ N * r2 i))
    (hyz : ∀ i : ℕ, i ≤ 2 → IsIntegral ℤ (y i) ∧ IsIntegral ℤ (z i) ∧
      y i * (affModel π a 6 f).leadingCoeff + z i * (affModel π a 6 f).eval (i : K) * r2 i =
        (D : K) ^ N)
    {U V W : K[X]} (hU : U.natDegree = 2) (hV : V.natDegree ≤ 1) (hw : V ^ 2 - f = U * W) :
    ∃ c : K, c ≠ 0 ∧ ∀ (F : Type*) [Field F] [NumberField F] [Algebra K F] (θ : F),
      f.eval₂ (algebraMap K F) θ = 0 → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (D : 𝓞 F) ∉ P.asIdeal →
      Even (FractionalIdeal.count F P
        (FractionalIdeal.spanSingleton (𝓞 F)⁰ (U.eval₂ (algebraMap K F) θ / algebraMap K F c))) := by
  classical
  have hU0 : U ≠ 0 := by rintro rfl; simp at hU
  have hU10 : affModel π a 2 U ≠ 0 := by
    intro h0
    have := affModel_natDegree a hπ 2 U
    rw [h0, natDegree_zero, hU] at this
    exact absurd this (by norm_num)
  obtain ⟨c, hc0, hcint, b, hbint, hbsum⟩ := exists_content hU10
  refine ⟨c, hc0, fun F _ _ _ θ hθ P hD => ?_⟩
  set σ := algebraMap K F with hσ
  set v := P.valuation F with hv
  have hσinj : Function.Injective σ := σ.injective
  -- the value of U at θ
  by_cases hx0 : U.eval₂ σ θ / σ c = 0
  · rw [hx0, FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]
    simp
  refine even_count_of_valuation P hx0 ?_
  have hint : ∀ {x : K}, IsIntegral ℤ x → v (σ x) ≤ 1 := fun {x} hx =>
    val_le_one_of_scaled P hD 0 (by rwa [pow_zero, one_mul])
  have hDN : v ((D : F) ^ N) = 1 := by rw [map_pow, val_natCast_eq_one P hD, one_pow]
  have hf1' : ∀ j, v ((affModel (σ π) (σ a) 6 (f.map σ)).coeff j) ≤ 1 := fun j => by
    rw [← affModel_map, coeff_map]; exact val_le_one_of_scaled P hD N (hf1 j)
  have hf1deg' : (affModel (σ π) (σ a) 6 (f.map σ)).natDegree = 6 := by
    rw [← affModel_map, natDegree_map_eq_of_injective hσinj, hf1deg]
  have hlcmap : (affModel (σ π) (σ a) 6 (f.map σ)).leadingCoeff =
      σ (affModel π a 6 f).leadingCoeff := by
    rw [← affModel_map, leadingCoeff_map_of_injective hσinj]
  obtain ⟨e, he, he1e⟩ := he1'
  have he1v : v (σ e1) = 1 := val_eq_one_of_mul_eq P hD N he1 he he1e
  obtain ⟨y0, hy0⟩ := schaefer_model_sq v (f := f.map σ) (U := U.map σ) (V := V.map σ)
    (W := W.map σ) (A1 := A1.map σ) (B1 := B1.map σ) (θ := θ) (π := σ π) (a := σ a) (c := σ c)
    (e1 := σ (e1 * (affModel π a 6 f).leadingCoeff)) (A2 := fun i => (A2 i).map σ)
    (B2 := fun i => (B2 i).map σ) (r2 := fun i => σ (r2 i))
    two_ne_zero ((map_ne_zero σ).mpr hπ)
    (by rw [← Polynomial.map_pow, ← Polynomial.map_sub, hw, Polynomial.map_mul])
    (by rw [natDegree_map_eq_of_injective hσinj, hU])
    (by rw [natDegree_map_eq_of_injective hσinj]; exact hV)
    (by rw [eval_map]; exact hθ)
    hf1' hf1deg'
    (by rw [← affModel_map, derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
      ← Polynomial.map_add, hbez1, map_C])
    (fun j => by rw [coeff_map]; exact val_le_one_of_scaled P hD N (hB1 j))
    (fun hl => by
      rw [hlcmap] at hl
      rw [map_mul, map_mul, he1v, hl, one_mul])
    (fun i hi => by
      have h := congrArg (Polynomial.map σ) (hbez2 i hi)
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, invModel_map,
        ← derivative_map, invModel_map, affModel_map, map_C, map_natCast] at h
      exact h)
    (fun i hi j => by rw [coeff_map]; exact val_le_one_of_scaled P hD N (hB2 i hi j))
    (fun hl i hi => by
      rw [hlcmap] at hl
      obtain ⟨hy, hz, hyz'⟩ := hyz i hi
      have hevF : v ((affModel (σ π) (σ a) 6 (f.map σ)).eval ((i : ℕ) : F)) =
          v (σ ((affModel π a 6 f).eval (i : K))) := by
        rw [← affModel_map, eval_map, ← map_natCast σ, eval₂_at_apply]
      have hev : v (σ ((affModel π a 6 f).eval (i : K))) ≤ 1 := by
        rw [← hevF]; exact eval_le_one v hf1' (by exact_mod_cast valuation_natCast_le_one v i)
      have hr : v (σ (r2 i)) ≤ 1 := val_le_one_of_scaled P hD N (hr2 i hi)
      have hsum := congrArg σ hyz'
      rw [map_add, map_mul, map_mul, map_mul, map_pow, map_natCast] at hsum
      have hylt : v (σ (y i) * σ (affModel π a 6 f).leadingCoeff) < 1 := by
        calc v (σ (y i) * σ (affModel π a 6 f).leadingCoeff)
            = v (σ (y i)) * v (σ (affModel π a 6 f).leadingCoeff) := map_mul _ _ _
          _ ≤ v (σ (affModel π a 6 f).leadingCoeff) := mul_le_of_le_one_left' (hint hy)
          _ < 1 := hl
      have hzv : v (σ (z i) * σ ((affModel π a 6 f).eval (i : K)) * σ (r2 i)) = 1 := by
        have e2 : σ (z i) * σ ((affModel π a 6 f).eval (i : K)) * σ (r2 i) =
            (D : F) ^ N - σ (y i) * σ (affModel π a 6 f).leadingCoeff := by
          rw [← hsum]; ring
        rw [e2, Valuation.map_sub_eq_of_lt_left _ (by rw [hDN]; exact hylt), hDN]
      rw [map_mul, map_mul] at hzv
      refine ⟨?_, ?_⟩
      · rw [hevF]; exact mid_eq_one_of_mul (hint hz) hev hr hzv
      · have h3 : v (σ (z i)) * v (σ (r2 i)) * v (σ ((affModel π a 6 f).eval (i : K))) = 1 := by
          rw [← hzv, mul_right_comm]
        exact mid_eq_one_of_mul (hint hz) hr hev h3)
    (fun j => by
      rw [← affModel_map, coeff_map, ← map_div₀]; exact hint (hcint j))
    (by
      have hs := congrArg σ hbsum
      rw [map_sum, map_one] at hs
      obtain ⟨j, hj⟩ := exists_val_eq_one v (s := Finset.range ((affModel π a 2 U).natDegree + 1))
        (g := fun j => σ ((affModel π a 2 U).coeff j / c)) (b := fun j => σ (b j))
        (fun j => hint (hcint j)) (fun j => hint (hbint j)) (by simpa only [map_mul] using hs)
      exact ⟨j, by rw [← affModel_map, coeff_map, ← map_div₀]; exact hj⟩)
  exact val_sq_of_ne_zero P hx0 (by rw [← hy0, eval_map])

end FurioLombardo.Discharge.SelmerBasis
