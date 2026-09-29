import Mathlib
import FurioLombardo.Vendor.Toolbox.PowerSeries.Conv

/-!
# The formal addition law of a genus 2 Jacobian at the chart `E0` (item R7)

In the translated model: `f` has degree at most 6, a
point `P0 = (0, b)` with `b ≠ 0`, a cubic `V0` with `X ^ 4 ∣ f - V0 ^ 2` (the Taylor polynomial of
`√f` at 0) and the genericity data `f - V0 ^ 2 = c0 X ^ 4 w0` with `c0 ≠ 0`, `w0` monic quadratic,
`w0(0) ≠ 0` (bundled in `Setup`).

Over `A1 = K⟦t0, t1⟧` and `A2 = K⟦s0, s1, s0', s1'⟧`:

* `v` (`exists_v`): the branch of `√f` modulo `uT t = X² + t0 X + t1` through `v0 = V0 mod X²`;
* `V`: the branch of `√f` modulo `u_s u_s'` through `V0`;
* `w`: the monic quadratic with `f - V² = c1 u_s u_s' w`;
* `W = -V + w Z`: `W ≡ -V mod w` and `W ≡ -v0 mod X²` (explicit inverse of `w` modulo `X²`);
* `u''`: the monic quadratic with `f - W² = c2 w X² u''`, and the addition series
  `G = (u''.coeff 1, u''.coeff 0)`;
* the branch identities `u_s ∣ V - v_s`, `u_s' ∣ V - v_s'`, `u'' ∣ v'' + W`.

All these polynomials have coefficients in the subring `conv` of series convergent near the origin.
-/

open Polynomial

namespace FurioLombardo.Vendor.Toolbox.G2Formal

open FurioLombardo.Vendor.Toolbox.Conv FurioLombardo.Vendor.Toolbox.SqrtMod

section Quad

variable {A : Type*} [CommRing A]

/-- The monic quadratic `X² + t₀ X + t₁`. -/
noncomputable def uT (t : Fin 2 → A) : A[X] := X ^ 2 + C (t 0) * X + C (t 1)

theorem uT_eq_add (t : Fin 2 → A) : uT t = X ^ 2 + (C (t 0) * X + C (t 1)) := by
  rw [uT, add_assoc]

theorem degree_linear_lt_two (a b : A) : (C a * X + C b).degree < 2 :=
  lt_of_le_of_lt degree_linear_le (by exact_mod_cast Nat.one_lt_two)

theorem uT_monic [Nontrivial A] (t : Fin 2 → A) : (uT t).Monic := by
  rw [uT_eq_add]
  exact monic_X_pow_add (by simpa using degree_linear_lt_two (t 0) (t 1))

theorem uT_natDegree [Nontrivial A] (t : Fin 2 → A) : (uT t).natDegree = 2 := by
  rw [uT_eq_add, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact_mod_cast degree_linear_lt_two (t 0) (t 1)

theorem map_uT {B : Type*} [CommRing B] (φ : A →+* B) (t : Fin 2 → A) :
    (uT t).map φ = uT (φ ∘ t) := by
  simp [uT, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

theorem uT_zero : uT (0 : Fin 2 → A) = X ^ 2 := by
  simp [uT]

theorem eq_uT_of_monic [Nontrivial A] {p : A[X]} (hp : p.Monic) (hd : p.natDegree = 2) :
    p = uT ![p.coeff 1, p.coeff 0] := by
  ext n
  rcases n with _ | _ | _ | n
  · simp [uT]
  · simp [uT]
  · have := hp.coeff_natDegree
    rw [hd] at this
    simp [uT, this]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp only [uT, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    simp

end Quad

variable {K : Type*} [Field K]

/-- The data of the construction: the scaling pair `(O, π)`, the translated model `f`, the cubic
`V0` and the genericity data at `P0 = (0, V0(0))`. -/
structure Setup (K : Type*) [Field K] where
  O : Subring K
  π : O
  hπ0 : (π : K) ≠ 0
  hbd : ∀ x : K, ∃ k : ℕ, (π : K) ^ k * x ∈ O
  h2 : (2 : K) ≠ 0
  f : K[X]
  hf : f.natDegree ≤ 6
  V0 : K[X]
  hV0d : V0.degree < 4
  hV00 : V0.coeff 0 ≠ 0
  c0 : K
  hc0 : c0 ≠ 0
  w0 : K[X]
  hw0m : w0.Monic
  hw0d : w0.natDegree = 2
  hfV0 : f - V0 ^ 2 = C c0 * (X ^ 4 * w0)
  hw00 : w0.coeff 0 ≠ 0

namespace Setup

variable (S : Setup K)

/-- The base branch modulo `X²`. -/
noncomputable def v0 : K[X] := S.V0 %ₘ X ^ 2

theorem V0_sub_v0 : X ^ 2 ∣ S.V0 - S.v0 := by
  refine ⟨S.V0 /ₘ X ^ 2, ?_⟩
  have := modByMonic_add_div S.V0 (X ^ 2 : K[X])
  rw [v0]
  linear_combination -this

theorem degree_v0 : S.v0.degree < 2 := by
  have := degree_modByMonic_lt S.V0 (monic_X_pow (R := K) 2)
  rwa [degree_X_pow] at this

theorem v0_coeff_zero : S.v0.coeff 0 = S.V0.coeff 0 := by
  obtain ⟨q, hq⟩ := S.V0_sub_v0
  have h := congrArg (fun p => p.coeff 0) hq
  simp only [coeff_sub] at h
  rw [pow_two, mul_assoc, coeff_X_mul_zero] at h
  linear_combination -h

theorem dvd_f_sub_v0 : X ^ 2 ∣ S.f - S.v0 ^ 2 := by
  obtain ⟨q, hq⟩ := S.V0_sub_v0
  have h4 : X ^ 2 ∣ S.f - S.V0 ^ 2 := by
    rw [S.hfV0]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (pow_dvd_pow X (by norm_num)) _) _
  have : S.f - S.v0 ^ 2 = (S.f - S.V0 ^ 2) + (S.V0 - S.v0) * (S.V0 + S.v0) := by ring
  rw [this]
  exact dvd_add h4 (Dvd.dvd.mul_right S.V0_sub_v0 _)

theorem dvd_f_sub_V0 : X ^ 4 ∣ S.f - S.V0 ^ 2 := by
  rw [S.hfV0]
  exact Dvd.dvd.mul_left (dvd_mul_right _ _) _

end Setup

section Lift

variable {O : Subring K} {π : O} {σ : Type*}

theorem C_mem_convPoly {g : MvPowerSeries σ K} (hg : g ∈ conv O π σ) :
    Polynomial.C g ∈ convPoly O π σ := by
  have := C_mem_lifts (conv O π σ).subtype ⟨g, hg⟩
  exact (lifts_iff_liftsRing _ _).mp (by simpa using this)

theorem X_mem_convPoly : (X : (MvPowerSeries σ K)[X]) ∈ convPoly O π σ :=
  (lifts_iff_liftsRing _ _).mp (X_mem_lifts _)

theorem uT_mem_convPoly {t : Fin 2 → MvPowerSeries σ K} (ht : ∀ i, t i ∈ conv O π σ) :
    uT t ∈ convPoly O π σ := by
  unfold uT
  exact Subring.add_mem _ (Subring.add_mem _ (Subring.pow_mem _ X_mem_convPoly _)
    (Subring.mul_mem _ (C_mem_convPoly (ht 0)) X_mem_convPoly)) (C_mem_convPoly (ht 1))

theorem constantCoeff_X' (i : σ) :
    MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries σ K) = 0 := by
  simp

end Lift

namespace Setup

variable (S : Setup K)

/-! ### Step 1: the chart branch `v` -/

/-- The chart polynomial `X² + t0 X + t1` over `K⟦t0, t1⟧`. -/
noncomputable abbrev u1 : (MvPowerSeries (Fin 2) K)[X] := uT (fun i => MvPowerSeries.X i)

theorem exists_v : ∃ v : (MvPowerSeries (Fin 2) K)[X], v ∈ convPoly S.O S.π (Fin 2) ∧
    v.degree < 2 ∧ v.map MvPowerSeries.constantCoeff = S.v0 ∧ u1 ∣ cst S.f - v ^ 2 := by
  set mt : (MvPowerSeries (Fin 2) K)[X] :=
    Polynomial.C (MvPowerSeries.X 0) * X + Polynomial.C (MvPowerSeries.X 1) with hmt
  have hmtc : mt ∈ convPoly S.O S.π (Fin 2) :=
    Subring.add_mem _ (Subring.mul_mem _ (C_mem_convPoly (X_mem_conv 0)) X_mem_convPoly)
      (C_mem_convPoly (X_mem_conv 1))
  have hmt0 : ∀ n, MvPowerSeries.constantCoeff (mt.coeff n) = 0 := by
    intro n
    have hmap : mt.map (MvPowerSeries.constantCoeff (σ := Fin 2) (R := K)) = 0 := by
      simp [hmt, Polynomial.map_add, Polynomial.map_mul]
    have := congrArg (fun p => p.coeff n) hmap
    simpa [Polynomial.coeff_map] using this
  have hv0c : S.v0.coeff 0 ≠ 0 := by rw [S.v0_coeff_zero]; exact S.hV00
  obtain ⟨v, hvc, hvd, hvm, hvdvd⟩ := exists_sqrtMod_conv S.hbd S.hπ0 S.h2 (d := 2) (by norm_num)
    S.f S.v0 S.dvd_f_sub_v0 hv0c (by exact_mod_cast S.degree_v0) mt hmtc hmt0
    (by exact_mod_cast degree_linear_lt_two _ _)
  refine ⟨v, hvc, by exact_mod_cast hvd, hvm, ?_⟩
  rwa [u1, uT_eq_add]

/-- The chart branch: `u1 ∣ f - v²`, `v ≡ v0` at the origin. -/
noncomputable def v : (MvPowerSeries (Fin 2) K)[X] := Classical.choose S.exists_v

theorem v_mem : S.v ∈ convPoly S.O S.π (Fin 2) := (Classical.choose_spec S.exists_v).1
theorem v_degree : S.v.degree < 2 := (Classical.choose_spec S.exists_v).2.1
theorem v_map : S.v.map MvPowerSeries.constantCoeff = S.v0 := (Classical.choose_spec S.exists_v).2.2.1
theorem u1_dvd : u1 ∣ cst S.f - S.v ^ 2 := (Classical.choose_spec S.exists_v).2.2.2

/-! ### Step 2: the branch `V` modulo `u_s u_s'` -/

/-- The chart polynomials `u_s`, `u_s'` over `K⟦s, s'⟧`. -/
noncomputable abbrev uL : (MvPowerSeries (Fin 2 ⊕ Fin 2) K)[X] :=
  uT (fun i => MvPowerSeries.X (Sum.inl i))
noncomputable abbrev uR : (MvPowerSeries (Fin 2 ⊕ Fin 2) K)[X] :=
  uT (fun i => MvPowerSeries.X (Sum.inr i))

theorem uL_map : uL.map (MvPowerSeries.constantCoeff (σ := Fin 2 ⊕ Fin 2) (R := K)) = X ^ 2 := by
  rw [map_uT]
  have : (MvPowerSeries.constantCoeff (σ := Fin 2 ⊕ Fin 2) (R := K)) ∘
      (fun i => MvPowerSeries.X (Sum.inl i)) = 0 := by
    funext i; simp
  rw [this, uT_zero]

theorem uR_map : uR.map (MvPowerSeries.constantCoeff (σ := Fin 2 ⊕ Fin 2) (R := K)) = X ^ 2 := by
  rw [map_uT]
  have : (MvPowerSeries.constantCoeff (σ := Fin 2 ⊕ Fin 2) (R := K)) ∘
      (fun i => MvPowerSeries.X (Sum.inr i)) = 0 := by
    funext i; simp
  rw [this, uT_zero]

theorem uLR_monic : (uL (K := K) * uR).Monic := (uT_monic _).mul (uT_monic _)

theorem uLR_natDegree : (uL (K := K) * uR).natDegree = 4 := by
  rw [(uT_monic _).natDegree_mul (uT_monic _), uT_natDegree, uT_natDegree]

theorem exists_V : ∃ V : (MvPowerSeries (Fin 2 ⊕ Fin 2) K)[X],
    V ∈ convPoly S.O S.π (Fin 2 ⊕ Fin 2) ∧ V.degree < 4 ∧
      V.map MvPowerSeries.constantCoeff = S.V0 ∧ uL * uR ∣ cst S.f - V ^ 2 := by
  set mt : (MvPowerSeries (Fin 2 ⊕ Fin 2) K)[X] := uL * uR - X ^ 4 with hmt
  have hmtc : mt ∈ convPoly S.O S.π (Fin 2 ⊕ Fin 2) :=
    Subring.sub_mem _ (Subring.mul_mem _ (uT_mem_convPoly fun i => X_mem_conv _)
      (uT_mem_convPoly fun i => X_mem_conv _)) (Subring.pow_mem _ X_mem_convPoly _)
  have hmt0 : ∀ n, MvPowerSeries.constantCoeff (mt.coeff n) = 0 := by
    intro n
    have hmap : mt.map (MvPowerSeries.constantCoeff (σ := Fin 2 ⊕ Fin 2) (R := K)) = 0 := by
      rw [hmt, Polynomial.map_sub, Polynomial.map_mul, uL_map, uR_map, Polynomial.map_pow,
        Polynomial.map_X]
      ring
    have := congrArg (fun p => p.coeff n) hmap
    simpa [Polynomial.coeff_map] using this
  have hmtd : mt.degree < 4 := by
    have h4 : (uL (K := K) * uR).degree = 4 := by
      rw [degree_eq_natDegree uLR_monic.ne_zero, uLR_natDegree]; rfl
    rw [hmt]
    calc (uL (K := K) * uR - X ^ 4 : (MvPowerSeries (Fin 2 ⊕ Fin 2) K)[X]).degree
          < (uL (K := K) * uR).degree := by
          apply degree_sub_lt_left
          · rw [h4, degree_X_pow]; rfl
          · exact uLR_monic.ne_zero
          · rw [uLR_monic.leadingCoeff, leadingCoeff_X_pow]
      _ = 4 := h4
  obtain ⟨V, hVc, hVd, hVm, hVdvd⟩ := exists_sqrtMod_conv S.hbd S.hπ0 S.h2 (d := 4) (by norm_num)
    S.f S.V0 S.dvd_f_sub_V0 S.hV00 (by exact_mod_cast S.hV0d) mt hmtc hmt0
    (by exact_mod_cast hmtd)
  refine ⟨V, hVc, by exact_mod_cast hVd, hVm, ?_⟩
  rwa [hmt, add_sub_cancel] at hVdvd

/-- The branch of `√f` modulo `u_s u_s'`. -/
noncomputable def V : (MvPowerSeries (Fin 2 ⊕ Fin 2) K)[X] := Classical.choose S.exists_V

theorem V_mem : S.V ∈ convPoly S.O S.π (Fin 2 ⊕ Fin 2) := (Classical.choose_spec S.exists_V).1
theorem V_degree : S.V.degree < 4 := (Classical.choose_spec S.exists_V).2.1
theorem V_map : S.V.map MvPowerSeries.constantCoeff = S.V0 := (Classical.choose_spec S.exists_V).2.2.1
theorem uLR_dvd : uL * uR ∣ cst S.f - S.V ^ 2 := (Classical.choose_spec S.exists_V).2.2.2

/-! ### Step 3: the residual quadratic `w` -/

theorem natDegree_le_of_degree_lt {A : Type*} [CommRing A] {p : A[X]} {n : ℕ}
    (h : p.degree < (n + 1 : ℕ)) : p.natDegree ≤ n := by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero]; exact Nat.zero_le _
  · have := (natDegree_lt_iff_degree_lt hp).mpr h; omega

abbrev A2 (K : Type*) [Field K] := MvPowerSeries (Fin 2 ⊕ Fin 2) K

noncomputable abbrev cc2 : A2 K →+* K := MvPowerSeries.constantCoeff

theorem map_cst {σ : Type*} (p : K[X]) :
    (cst (σ := σ) p).map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = p := by
  simp only [cst, coe_mapRingHom, Polynomial.map_map]
  have : (MvPowerSeries.constantCoeff (σ := σ) (R := K)).comp (MvPowerSeries.C (σ := σ) (R := K)) =
      RingHom.id K := by ext x : 1; simp
  rw [this, Polynomial.map_id]

theorem natDegree_cst_sub_sq {σ : Type*} {F : (MvPowerSeries σ K)[X]} (hF : F.degree < 4) :
    (cst (σ := σ) S.f - F ^ 2).natDegree ≤ 6 := by
  have hf : (cst (σ := σ) S.f).natDegree ≤ 6 := natDegree_map_le.trans S.hf
  have hV : F.natDegree ≤ 3 := natDegree_le_of_degree_lt (by exact_mod_cast hF)
  refine (natDegree_sub_le _ _).trans (max_le hf ?_)
  exact natDegree_pow_le.trans (by omega)

/-- The quotient `(f - V²) / (u_s u_s')`. -/
noncomputable def qw : (A2 K)[X] := (cst S.f - S.V ^ 2) /ₘ (uL * uR)

theorem f_sub_V_sq : cst S.f - S.V ^ 2 = uL * uR * S.qw := by
  have h := modByMonic_add_div (cst S.f - S.V ^ 2) (uL * uR)
  rw [(modByMonic_eq_zero_iff_dvd uLR_monic).mpr S.uLR_dvd, zero_add] at h
  rw [qw, h]

theorem natDegree_qw : S.qw.natDegree ≤ 2 := by
  rw [qw, natDegree_divByMonic _ uLR_monic, uLR_natDegree]
  have := S.natDegree_cst_sub_sq S.V_degree
  omega

theorem f_sub_V0_sq' : S.f - S.V0 ^ 2 = X ^ 4 * (C S.c0 * S.w0) := by
  rw [S.hfV0]; ring

theorem uLR_map : (uL * uR).map cc2 = (X ^ 4 : K[X]) := by
  rw [Polynomial.map_mul, uL_map, uR_map]; ring

theorem qw_map : S.qw.map cc2 = C S.c0 * S.w0 := by
  rw [qw, map_divByMonic _ uLR_monic, uLR_map, Polynomial.map_sub, Polynomial.map_pow, map_cst,
    S.V_map, S.f_sub_V0_sq', mul_divByMonic_cancel_left _ (monic_X_pow 4)]

theorem w0_coeff_two : S.w0.coeff 2 = 1 := by
  have := S.hw0m.coeff_natDegree; rwa [S.hw0d] at this

/-- The leading coefficient `c1 = ℓ - V₃²` of `f - V²`. -/
noncomputable def c1 : A2 K := S.qw.coeff 2

theorem c1_const : MvPowerSeries.constantCoeff S.c1 = S.c0 := by
  have := congrArg (fun p => p.coeff 2) S.qw_map
  simp only [Polynomial.coeff_map, coeff_C_mul, S.w0_coeff_two, mul_one] at this
  exact this

theorem c1_ne : MvPowerSeries.constantCoeff S.c1 ≠ 0 := by rw [S.c1_const]; exact S.hc0

theorem qw_mem : S.qw ∈ convPoly S.O S.π (Fin 2 ⊕ Fin 2) :=
  divByMonic_mem uLR_monic
    (Subring.mul_mem _ (uT_mem_convPoly fun i => X_mem_conv _) (uT_mem_convPoly fun i => X_mem_conv _))
    (Subring.sub_mem _ (cst_mem_convPoly S.hbd _) (Subring.pow_mem _ S.V_mem _))

theorem c1_mem : S.c1 ∈ conv S.O S.π (Fin 2 ⊕ Fin 2) := mem_convPoly.mp S.qw_mem 2

theorem c1_inv_mem : S.c1⁻¹ ∈ conv S.O S.π (Fin 2 ⊕ Fin 2) :=
  inv_mem_conv S.hbd S.c1_mem S.c1_ne

/-- The residual quadratic: `f - V² = c1 u_s u_s' w`. -/
noncomputable def w : (A2 K)[X] := C S.c1⁻¹ * S.qw

/-- A polynomial of degree at most 2 with coefficient 1 in degree 2 is monic of degree 2. -/
theorem monic_of_coeff_two {A : Type*} [CommRing A] [Nontrivial A] {p : A[X]}
    (hp : p.natDegree ≤ 2) (h2 : p.coeff 2 = 1) : p.Monic ∧ p.natDegree = 2 := by
  have hd : p.natDegree = 2 :=
    le_antisymm hp (le_natDegree_of_ne_zero (by rw [h2]; exact one_ne_zero))
  exact ⟨by rw [Monic, leadingCoeff, hd, h2], hd⟩

theorem w_coeff_two : S.w.coeff 2 = 1 := by
  rw [w, coeff_C_mul]
  exact MvPowerSeries.inv_mul_cancel _ S.c1_ne

theorem w_monic : S.w.Monic ∧ S.w.natDegree = 2 :=
  monic_of_coeff_two ((natDegree_C_mul_le _ _).trans S.natDegree_qw) S.w_coeff_two

theorem f_sub_V_sq_eq : cst S.f - S.V ^ 2 = C S.c1 * (uL * uR * S.w) := by
  rw [S.f_sub_V_sq, w]
  have : C S.c1 * C S.c1⁻¹ = (1 : (A2 K)[X]) := by
    rw [← C_mul, MvPowerSeries.mul_inv_cancel _ S.c1_ne, C_1]
  linear_combination (uL * uR * S.qw) * this.symm

theorem w_map : S.w.map cc2 = S.w0 := by
  rw [w, Polynomial.map_mul, Polynomial.map_C, S.qw_map, cc2, MvPowerSeries.constantCoeff_inv,
    S.c1_const, ← mul_assoc, ← C_mul, inv_mul_cancel₀ S.hc0, C_1, one_mul]

theorem w_mem : S.w ∈ convPoly S.O S.π (Fin 2 ⊕ Fin 2) :=
  Subring.mul_mem _ (C_mem_convPoly S.c1_inv_mem) S.qw_mem

/-! ### Step 4: `W`, from the inverse of `w` modulo `X²` -/

/-- The constant coefficient of `w`, a unit. -/
noncomputable def a0 : A2 K := S.w.coeff 0
noncomputable def a1 : A2 K := S.w.coeff 1

theorem a0_const : MvPowerSeries.constantCoeff S.a0 = S.w0.coeff 0 := by
  have := congrArg (fun p => p.coeff 0) S.w_map
  simp only [Polynomial.coeff_map] at this
  exact this

theorem a0_ne : MvPowerSeries.constantCoeff S.a0 ≠ 0 := by rw [S.a0_const]; exact S.hw00

theorem w_eq : S.w = X ^ 2 + C S.a1 * X + C S.a0 := by
  have := eq_uT_of_monic S.w_monic.1 S.w_monic.2
  rw [this, uT]; simp [a0, a1]

/-- The inverse of `w` modulo `X²`. -/
noncomputable def winv : (A2 K)[X] := C S.a0⁻¹ - C (S.a1 * S.a0⁻¹ * S.a0⁻¹) * X

/-- The cofactor of `X²` in `w winv - 1`. -/
noncomputable def wr : (A2 K)[X] := C (S.a0⁻¹ - S.a1 ^ 2 * S.a0⁻¹ * S.a0⁻¹) - C (S.a1 * S.a0⁻¹ * S.a0⁻¹) * X

theorem w_mul_winv : S.w * S.winv = 1 + X ^ 2 * S.wr := by
  have hι : C S.a0 * C S.a0⁻¹ = (1 : (A2 K)[X]) := by
    rw [← C_mul, MvPowerSeries.mul_inv_cancel _ S.a0_ne, C_1]
  rw [S.w_eq, winv, wr]
  simp only [map_sub, map_mul, map_pow]
  linear_combination (1 - C S.a1 * C S.a0⁻¹ * X) * hι

theorem isCoprime_w_X2 : IsCoprime S.w (X ^ 2) :=
  ⟨S.winv, -S.wr, by linear_combination S.w_mul_winv⟩

/-- The auxiliary `Z = (V - v0) winv mod X²`. -/
noncomputable def Z : (A2 K)[X] := ((S.V - cst S.v0) * S.winv) %ₘ X ^ 2

/-- `W = -V + w Z`: `W ≡ -V mod w` and `W ≡ -v0 mod X²`. -/
noncomputable def W : (A2 K)[X] := -S.V + S.w * S.Z

theorem W_add_V : S.W + S.V = S.w * S.Z := by rw [W]; ring

theorem X2_dvd_W_add_v0 : (X ^ 2 : (A2 K)[X]) ∣ S.W + cst S.v0 := by
  have h := modByMonic_add_div ((S.V - cst S.v0) * S.winv) (X ^ 2 : (A2 K)[X])
  have e : S.W + cst S.v0 = S.w * (-(X ^ 2 * (((S.V - cst S.v0) * S.winv) /ₘ X ^ 2))) +
      (S.V - cst S.v0) * (X ^ 2 * S.wr) := by
    rw [W, Z]
    linear_combination S.w * h + (S.V - cst S.v0) * S.w_mul_winv
  rw [e]
  exact dvd_add (Dvd.dvd.mul_left (Dvd.dvd.neg_right (dvd_mul_right _ _)) _)
    (Dvd.dvd.mul_left (dvd_mul_right _ _) _)

theorem Z_degree : S.Z.degree < 2 := by
  have := degree_modByMonic_lt ((S.V - cst S.v0) * S.winv) (monic_X_pow (R := A2 K) 2)
  rwa [degree_X_pow] at this

theorem W_degree : S.W.degree < 4 := by
  rw [W]
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt (by rw [degree_neg]; exact S.V_degree) ?_)
  have hZ : S.Z.natDegree ≤ 1 := natDegree_le_of_degree_lt (by exact_mod_cast S.Z_degree)
  have hwZ : (S.w * S.Z).natDegree ≤ 3 :=
    (natDegree_mul_le).trans (by rw [S.w_monic.2]; omega)
  by_cases h0 : S.w * S.Z = 0
  · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree h0]; exact_mod_cast Nat.lt_succ_of_le hwZ

theorem winv_mem : S.winv ∈ convPoly S.O S.π (Fin 2 ⊕ Fin 2) := by
  have ha0 : S.a0 ∈ conv S.O S.π (Fin 2 ⊕ Fin 2) := mem_convPoly.mp S.w_mem 0
  have ha1 : S.a1 ∈ conv S.O S.π (Fin 2 ⊕ Fin 2) := mem_convPoly.mp S.w_mem 1
  have hi : S.a0⁻¹ ∈ conv S.O S.π (Fin 2 ⊕ Fin 2) := inv_mem_conv S.hbd ha0 S.a0_ne
  exact Subring.sub_mem _ (C_mem_convPoly hi)
    (Subring.mul_mem _ (C_mem_convPoly (Subring.mul_mem _ (Subring.mul_mem _ ha1 hi) hi))
      X_mem_convPoly)

theorem W_mem : S.W ∈ convPoly S.O S.π (Fin 2 ⊕ Fin 2) := by
  refine Subring.add_mem _ (Subring.neg_mem _ S.V_mem) (Subring.mul_mem _ S.w_mem ?_)
  exact modByMonic_mem (monic_X_pow 2) (Subring.pow_mem _ X_mem_convPoly _)
    (Subring.mul_mem _ (Subring.sub_mem _ S.V_mem (cst_mem_convPoly S.hbd _)) S.winv_mem)

theorem W_map : S.W.map cc2 = -S.V0 := by
  set Wm := S.W.map cc2 with hWm
  have h1 : S.w0 ∣ Wm + S.V0 := by
    have h0 : S.w ∣ S.W + S.V := ⟨S.Z, S.W_add_V⟩
    have := Polynomial.map_dvd cc2 h0
    rwa [Polynomial.map_add, S.V_map, S.w_map] at this
  have h2 : (X ^ 2 : K[X]) ∣ Wm + S.V0 := by
    have := Polynomial.map_dvd cc2 S.X2_dvd_W_add_v0
    rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, map_cst] at this
    have e : Wm + S.V0 = (S.W.map cc2 + S.v0) + (S.V0 - S.v0) := by rw [hWm]; ring
    rw [e]
    exact dvd_add this S.V0_sub_v0
  have hcop : IsCoprime S.w0 (X ^ 2 : K[X]) := by
    have := S.isCoprime_w_X2.map (Polynomial.mapRingHom cc2)
    rwa [coe_mapRingHom, Polynomial.map_pow, Polynomial.map_X, S.w_map] at this
  have h12 : S.w0 * X ^ 2 ∣ Wm + S.V0 := hcop.mul_dvd h1 h2
  have hdeg : (Wm + S.V0).degree < (S.w0 * X ^ 2).degree := by
    rw [degree_mul, degree_eq_natDegree S.hw0m.ne_zero, S.hw0d, degree_X_pow]
    refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ S.hV0d)
    exact lt_of_le_of_lt degree_map_le S.W_degree
  have := eq_zero_of_dvd_of_degree_lt h12 hdeg
  linear_combination this

/-! ### Step 5: the sum `u''` -/

theorem X2_dvd_f_sub_W_sq : (X ^ 2 : (A2 K)[X]) ∣ cst S.f - S.W ^ 2 := by
  have h1 : (X ^ 2 : (A2 K)[X]) ∣ cst (S.f - S.v0 ^ 2) := by
    have := map_dvd (cst (σ := Fin 2 ⊕ Fin 2)) S.dvd_f_sub_v0
    rwa [map_pow, cst, coe_mapRingHom, Polynomial.map_X] at this
  have e : cst S.f - S.W ^ 2 = cst (S.f - S.v0 ^ 2) - (S.W + cst S.v0) * (S.W - cst S.v0) := by
    rw [map_sub, map_pow]; ring
  rw [e]
  exact dvd_sub h1 (Dvd.dvd.mul_right S.X2_dvd_W_add_v0 _)

theorem w_dvd_f_sub_W_sq : S.w ∣ cst S.f - S.W ^ 2 := by
  have e : cst S.f - S.W ^ 2 = S.w * (C S.c1 * (uL * uR) - S.Z * (S.W - S.V)) := by
    have h1 := S.f_sub_V_sq_eq
    have h2 := S.W_add_V
    linear_combination h1 - (S.W - S.V) * h2
  rw [e]; exact dvd_mul_right _ _

theorem wX2_monic : (S.w * X ^ 2).Monic := S.w_monic.1.mul (monic_X_pow 2)

theorem wX2_natDegree : (S.w * X ^ 2).natDegree = 4 := by
  rw [S.w_monic.1.natDegree_mul (monic_X_pow 2), S.w_monic.2, natDegree_X_pow]

theorem wX2_dvd : S.w * X ^ 2 ∣ cst S.f - S.W ^ 2 :=
  S.isCoprime_w_X2.mul_dvd S.w_dvd_f_sub_W_sq S.X2_dvd_f_sub_W_sq

/-- The quotient `(f - W²) / (w X²)`. -/
noncomputable def qu : (A2 K)[X] := (cst S.f - S.W ^ 2) /ₘ (S.w * X ^ 2)

theorem f_sub_W_sq : cst S.f - S.W ^ 2 = S.w * X ^ 2 * S.qu := by
  have h := modByMonic_add_div (cst S.f - S.W ^ 2) (S.w * X ^ 2)
  rw [(modByMonic_eq_zero_iff_dvd S.wX2_monic).mpr S.wX2_dvd, zero_add] at h
  rw [qu, h]

theorem natDegree_qu : S.qu.natDegree ≤ 2 := by
  rw [qu, natDegree_divByMonic _ S.wX2_monic, S.wX2_natDegree]
  have := S.natDegree_cst_sub_sq S.W_degree
  omega

theorem qu_map : S.qu.map cc2 = C S.c0 * X ^ 2 := by
  rw [qu, map_divByMonic _ S.wX2_monic, Polynomial.map_sub, Polynomial.map_pow, map_cst, S.W_map,
    Polynomial.map_mul, S.w_map, Polynomial.map_pow, Polynomial.map_X]
  have e : S.f - (-S.V0) ^ 2 = S.w0 * X ^ 2 * (C S.c0 * X ^ 2) := by
    rw [neg_sq, S.hfV0]; ring
  rw [e, mul_divByMonic_cancel_left _ (S.hw0m.mul (monic_X_pow 2))]

/-- The leading coefficient `c2` of `f - W²`. -/
noncomputable def c2 : A2 K := S.qu.coeff 2

theorem c2_const : MvPowerSeries.constantCoeff S.c2 = S.c0 := by
  have := congrArg (fun p => p.coeff 2) S.qu_map
  simp only [Polynomial.coeff_map, coeff_C_mul, coeff_X_pow, ↓reduceIte, mul_one] at this
  exact this

theorem c2_ne : MvPowerSeries.constantCoeff S.c2 ≠ 0 := by rw [S.c2_const]; exact S.hc0

theorem qu_mem : S.qu ∈ convPoly S.O S.π (Fin 2 ⊕ Fin 2) :=
  divByMonic_mem S.wX2_monic (Subring.mul_mem _ S.w_mem (Subring.pow_mem _ X_mem_convPoly _))
    (Subring.sub_mem _ (cst_mem_convPoly S.hbd _) (Subring.pow_mem _ S.W_mem _))

theorem c2_mem : S.c2 ∈ conv S.O S.π (Fin 2 ⊕ Fin 2) := mem_convPoly.mp S.qu_mem 2

/-- The sum: `f - W² = c2 w X² u''`. -/
noncomputable def u2 : (A2 K)[X] := C S.c2⁻¹ * S.qu

theorem u2_monic : S.u2.Monic ∧ S.u2.natDegree = 2 := by
  refine monic_of_coeff_two ((natDegree_C_mul_le _ _).trans S.natDegree_qu) ?_
  rw [u2, coeff_C_mul]
  exact MvPowerSeries.inv_mul_cancel _ S.c2_ne

theorem f_sub_W_sq_eq : cst S.f - S.W ^ 2 = C S.c2 * (S.w * X ^ 2 * S.u2) := by
  rw [S.f_sub_W_sq, u2]
  have : C S.c2 * C S.c2⁻¹ = (1 : (A2 K)[X]) := by
    rw [← C_mul, MvPowerSeries.mul_inv_cancel _ S.c2_ne, C_1]
  linear_combination (S.w * X ^ 2 * S.qu) * this.symm

theorem u2_map : S.u2.map cc2 = X ^ 2 := by
  rw [u2, Polynomial.map_mul, Polynomial.map_C, S.qu_map, cc2, MvPowerSeries.constantCoeff_inv,
    S.c2_const, ← mul_assoc, ← C_mul, inv_mul_cancel₀ S.hc0, C_1, one_mul]

theorem u2_mem : S.u2 ∈ convPoly S.O S.π (Fin 2 ⊕ Fin 2) :=
  Subring.mul_mem _ (C_mem_convPoly (inv_mem_conv S.hbd S.c2_mem S.c2_ne)) S.qu_mem

/-! ### Step 6: the addition series `G` -/

/-- The formal addition law: `u'' = X² + G₀ X + G₁`. -/
noncomputable def G : Fin 2 → A2 K := ![S.u2.coeff 1, S.u2.coeff 0]

theorem u2_eq : S.u2 = uT S.G := eq_uT_of_monic S.u2_monic.1 S.u2_monic.2

theorem G_const (i : Fin 2) : MvPowerSeries.constantCoeff (S.G i) = 0 := by
  have h1 := congrArg (fun p => p.coeff 1) S.u2_map
  have h0 := congrArg (fun p => p.coeff 0) S.u2_map
  simp only [Polynomial.coeff_map, coeff_X_pow] at h1 h0
  fin_cases i
  · simpa [G] using h1
  · simpa [G] using h0

theorem G_mem (i : Fin 2) : S.G i ∈ conv S.O S.π (Fin 2 ⊕ Fin 2) := by
  fin_cases i
  · exact mem_convPoly.mp S.u2_mem 1
  · exact mem_convPoly.mp S.u2_mem 0

end Setup

/-! ### Substitution homomorphisms -/

section SubstHom

variable {σ τ : Type*} [Finite σ]

/-- Substitution of a family with zero constant coefficients, as a `K`-algebra map. -/
noncomputable def sb (a : σ → MvPowerSeries τ K)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    MvPowerSeries σ K →ₐ[K] MvPowerSeries τ K :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)

variable {a : σ → MvPowerSeries τ K} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)

theorem sb_apply (g : MvPowerSeries σ K) : sb a ha g = MvPowerSeries.subst a g := by
  rw [sb, MvPowerSeries.coe_substAlgHom]

theorem sb_X (i : σ) : sb a ha (MvPowerSeries.X i) = a i := by
  rw [sb_apply, MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]

theorem constantCoeff_sb (g : MvPowerSeries σ K) :
    MvPowerSeries.constantCoeff (sb a ha g) = MvPowerSeries.constantCoeff g := by
  have h := MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha
    (f := g - MvPowerSeries.C (MvPowerSeries.constantCoeff g)) (by simp)
  rw [← sb_apply ha, map_sub, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes, map_sub,
    ← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.constantCoeff_C, sub_eq_zero] at h
  exact h

theorem cc_comp_sb :
    (MvPowerSeries.constantCoeff (σ := τ) (R := K)).comp (sb a ha).toRingHom =
      MvPowerSeries.constantCoeff := by
  ext g : 1
  exact constantCoeff_sb ha g

theorem map_map_sb (P : (MvPowerSeries σ K)[X]) :
    (P.map (sb a ha).toRingHom).map (MvPowerSeries.constantCoeff (σ := τ) (R := K)) =
      P.map MvPowerSeries.constantCoeff := by
  rw [Polynomial.map_map, cc_comp_sb]

theorem map_cst_sb (p : K[X]) : (cst (σ := σ) p).map (sb a ha).toRingHom = cst p := by
  simp only [cst, coe_mapRingHom, Polynomial.map_map]
  congr 1
  ext x : 1
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes, MvPowerSeries.c_eq_algebraMap]

end SubstHom

theorem map_u1_sb {τ : Type*} {a : Fin 2 → MvPowerSeries τ K}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    (uT (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) K))).map (sb a ha).toRingHom =
      uT a := by
  rw [map_uT]
  congr 1
  funext i
  exact sb_X ha i

/-! ### Step 7: the branch identities -/

/-- Uniqueness of the branch of a square root modulo `m`, when `m(0) = X^d`. -/
theorem sqrt_branch {σ : Type*} {m P Q F : (MvPowerSeries σ K)[X]} (hm : m.Monic)
    (hm0 : m.map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = X ^ m.natDegree)
    (hP : m ∣ F - P ^ 2) (hQ : m ∣ F - Q ^ 2)
    (hPQ : ((P + Q).map (MvPowerSeries.constantCoeff (σ := σ) (R := K))).coeff 0 ≠ 0) :
    m ∣ P - Q := by
  refine dvd_of_dvd_mul_of_map hm hm0 (B := P + Q) (by rwa [← Polynomial.coeff_map]) ?_
  have : (P + Q) * (P - Q) = (F - Q ^ 2) - (F - P ^ 2) := by ring
  rw [this]
  exact dvd_sub hQ hP

namespace Setup

variable (S : Setup K)

/-- The chart family of the left point. -/
noncomputable abbrev ρL : MvPowerSeries (Fin 2) K →ₐ[K] A2 K :=
  sb (fun i => MvPowerSeries.X (Sum.inl i)) (fun i => by simp)
noncomputable abbrev ρR : MvPowerSeries (Fin 2) K →ₐ[K] A2 K :=
  sb (fun i => MvPowerSeries.X (Sum.inr i)) (fun i => by simp)
noncomputable abbrev ρG : MvPowerSeries (Fin 2) K →ₐ[K] A2 K := sb S.G S.G_const

/-- The ordinates of the chart at `s`, at `s'` and at `G(s, s')`. -/
noncomputable def vL : (A2 K)[X] := S.v.map ρL.toRingHom
noncomputable def vR : (A2 K)[X] := S.v.map ρR.toRingHom
noncomputable def vG : (A2 K)[X] := S.v.map S.ρG.toRingHom

theorem two_V00 : (2 : K) * S.V0.coeff 0 ≠ 0 := mul_ne_zero S.h2 S.hV00

theorem uT_map_X2 {σ : Type*} (t : Fin 2 → MvPowerSeries σ K)
    (ht : ∀ i, MvPowerSeries.constantCoeff (t i) = 0) :
    (uT t).map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = X ^ (uT t).natDegree := by
  rw [uT_natDegree, map_uT]
  have : (MvPowerSeries.constantCoeff (σ := σ) (R := K)) ∘ t = 0 := funext ht
  rw [this, uT_zero]

theorem dvd_f_sub_sq_of_sb {a : Fin 2 → A2 K} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    uT a ∣ cst S.f - (S.v.map (sb a ha).toRingHom) ^ 2 := by
  have := Polynomial.map_dvd (sb a ha).toRingHom S.u1_dvd
  rwa [map_u1_sb, Polynomial.map_sub, Polynomial.map_pow, map_cst_sb] at this

theorem map_v_sb {a : Fin 2 → A2 K} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    (S.v.map (sb a ha).toRingHom).map cc2 = S.v0 := by
  rw [cc2, map_map_sb, S.v_map]

theorem uL_dvd_V_sub : uL ∣ S.V - S.vL := by
  refine sqrt_branch (uT_monic _) (uT_map_X2 _ (fun i => by simp))
    (dvd_trans (dvd_mul_right _ _) S.uLR_dvd) (S.dvd_f_sub_sq_of_sb (fun i => by simp)) ?_
  rw [Polynomial.map_add, S.V_map, vL, S.map_v_sb, coeff_add, S.v0_coeff_zero, ← two_mul]
  exact S.two_V00

theorem uR_dvd_V_sub : uR ∣ S.V - S.vR := by
  refine sqrt_branch (uT_monic _) (uT_map_X2 _ (fun i => by simp))
    (dvd_trans (dvd_mul_left _ _) S.uLR_dvd) (S.dvd_f_sub_sq_of_sb (fun i => by simp)) ?_
  rw [Polynomial.map_add, S.V_map, vR, S.map_v_sb, coeff_add, S.v0_coeff_zero, ← two_mul]
  exact S.two_V00

theorem u2_dvd_vG_add_W : S.u2 ∣ S.vG + S.W := by
  have hm0 : S.u2.map cc2 = X ^ S.u2.natDegree := by rw [S.u2_map, S.u2_monic.2]
  have hW : S.u2 ∣ cst S.f - (-S.W) ^ 2 := by
    have e : (-S.W) ^ 2 = S.W ^ 2 := by ring
    rw [e, S.f_sub_W_sq_eq]
    exact Dvd.dvd.mul_left (dvd_mul_left _ _) _
  have hG : S.u2 ∣ cst S.f - S.vG ^ 2 := by
    rw [S.u2_eq, vG]; exact S.dvd_f_sub_sq_of_sb S.G_const
  have := sqrt_branch S.u2_monic.1 hm0 hG hW ?_
  · rwa [sub_neg_eq_add] at this
  rw [Polynomial.map_add, vG, S.map_v_sb, Polynomial.map_neg, S.W_map, neg_neg, coeff_add,
    S.v0_coeff_zero, ← two_mul]
  exact S.two_V00

end Setup

end FurioLombardo.Vendor.Toolbox.G2Formal
