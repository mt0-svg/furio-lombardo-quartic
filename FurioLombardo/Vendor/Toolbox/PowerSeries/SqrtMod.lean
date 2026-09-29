import Mathlib
import FurioLombardo.Vendor.Toolbox.PowerSeries.FormalFix

/-!
# Square roots modulo a monic polynomial close to `X^d`, over power series

Let `K` be a field of characteristic not `2`, `O` a subring of `K`, `π ∈ O` nonzero, and
`A = K⟦t⟧` the power series in the variables `σ`. For a monic `m ∈ A[X]` of degree `d` of the form
`m = X^d + π^(j+k) m̃`, with `m̃` of degree `< d`, coefficients in `O⟦t⟧` and no constant term,
and a polynomial `V₀ ∈ K[X]` with `X^d ∣ f - V₀²` and `V₀(0) ≠ 0`, there is `Ṽ ∈ A[X]` with
coefficients in `O⟦t⟧` and no constant term such that `m ∣ f - (V₀ + π^j Ṽ)²`, provided `j` and `k`
are large enough for three explicit integrality conditions (`exists_sqrtMod`).

Tools, of independent use:

* `FurioLombardo.Vendor.Toolbox.SqrtMod.isCoprime_of_map_constantCoeff`: over `A = K⟦t⟧`, a monic `m` reducing to
  `X^d` at `t = 0` is coprime to every `B` whose constant coefficient does not vanish at `t = 0`
  (the resultant reduces to `B(0)^d`, a unit of `A`). This is the branch lemma: `m ∣ B Z` gives
  `m ∣ Z`.
* `FurioLombardo.Vendor.Toolbox.SqrtMod.ordIdeal n`: the ideal of power series of order at least `n`; polynomials with
  all coefficients in it are the ideal `(ordIdeal n).map C`, stable under `%ₘ m` for monic `m`
  (`modByMonic_mem_map_C`).

Origin: written for this formalization (the formal group of the Jacobian at the place above 2,
`FurioLombardo.Discharge.R7`).
-/

namespace FurioLombardo.Vendor.Toolbox.SqrtMod

open Polynomial

section OrdIdeal

variable {σ R : Type*} [CommRing R]

/-- The ideal of power series of order at least `n`. -/
def ordIdeal (n : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {F | (n : ℕ∞) ≤ F.order}
  add_mem' {a b} ha hb := le_trans (le_min ha hb) MvPowerSeries.min_order_le_add
  zero_mem' := by simp
  smul_mem' c {F} hF := by
    change (n : ℕ∞) ≤ (c * F).order
    exact le_trans (le_trans hF le_add_self) MvPowerSeries.le_order_mul

theorem mem_ordIdeal {n : ℕ} {F : MvPowerSeries σ R} : F ∈ ordIdeal n ↔ (n : ℕ∞) ≤ F.order :=
  Iff.rfl

theorem ordIdeal_mul_le (a b : ℕ) :
    ordIdeal (σ := σ) (R := R) a * ordIdeal b ≤ ordIdeal (a + b) := by
  rw [Ideal.mul_le]
  intro x hx y hy
  rw [mem_ordIdeal] at hx hy ⊢
  calc ((a + b : ℕ) : ℕ∞) = (a : ℕ∞) + b := by push_cast; rfl
    _ ≤ x.order + y.order := add_le_add hx hy
    _ ≤ (x * y).order := MvPowerSeries.le_order_mul

theorem ordIdeal_one_iff {F : MvPowerSeries σ R} :
    F ∈ ordIdeal 1 ↔ MvPowerSeries.constantCoeff F = 0 := by
  rw [mem_ordIdeal, Nat.cast_one, MvPowerSeries.one_le_order_iff_constCoeff_eq_zero]

/-- Reduction modulo a monic polynomial keeps the coefficients in an ideal. -/
theorem modByMonic_mem_map_C {S : Type*} [CommRing S] {I : Ideal S} {m p : S[X]} (hm : m.Monic)
    (hp : p ∈ I.map (C : S →+* S[X])) : p %ₘ m ∈ I.map (C : S →+* S[X]) := by
  rw [Ideal.mem_map_C_iff] at hp ⊢
  have h0 : p.map (Ideal.Quotient.mk I) = 0 := by
    ext n; simp [coeff_map, Ideal.Quotient.eq_zero_iff_mem.mpr (hp n)]
  have h1 := map_modByMonic (p := p) (Ideal.Quotient.mk I) hm
  rw [h0, zero_modByMonic] at h1
  intro n
  have h2 := congrArg (fun q => q.coeff n) h1
  simpa [coeff_map, Ideal.Quotient.eq_zero_iff_mem] using h2

theorem mem_map_C_iff' {S : Type*} [CommRing S] {I : Ideal S} {p : S[X]} :
    p ∈ I.map (C : S →+* S[X]) ↔ ∀ n, p.coeff n ∈ I :=
  Ideal.mem_map_C_iff

end OrdIdeal

section Coprime

variable {σ K : Type*} [Field K]

/-- **Branch lemma.** Over `K⟦t⟧`, a monic `m` with `m(0) = X^d` is coprime to every `B` whose
constant coefficient is nonzero at `t = 0`. -/
theorem isCoprime_of_map_constantCoeff {m B : (MvPowerSeries σ K)[X]} (hm : m.Monic)
    (hm0 : m.map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = X ^ m.natDegree)
    (hB : MvPowerSeries.constantCoeff (B.coeff 0) ≠ 0) : IsCoprime m B := by
  rw [← isUnit_resultant_iff_isCoprime hm, MvPowerSeries.isUnit_iff_constantCoeff]
  have h1 := resultant_map_map m B m.natDegree B.natDegree
    (MvPowerSeries.constantCoeff (σ := σ) (R := K))
  rw [hm0, resultant_X_pow_left _ _ _ natDegree_map_le, coeff_map] at h1
  change IsUnit (MvPowerSeries.constantCoeff (resultant m B m.natDegree B.natDegree))
  rw [← h1]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hB)

/-- The branch lemma in the form used: `m ∣ B Z` gives `m ∣ Z`. -/
theorem dvd_of_dvd_mul_of_map {m B Z : (MvPowerSeries σ K)[X]} (hm : m.Monic)
    (hm0 : m.map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = X ^ m.natDegree)
    (hB : MvPowerSeries.constantCoeff (B.coeff 0) ≠ 0) (h : m ∣ B * Z) : m ∣ Z :=
  (isCoprime_of_map_constantCoeff hm hm0 hB).dvd_of_dvd_mul_left h

end Coprime

section Lifts

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-- Reduction modulo a monic polynomial that lifts keeps lifting. -/
theorem modByMonic_mem_liftsRing {m p : S[X]} (hm : m.Monic) (hml : m ∈ liftsRing f)
    (hp : p ∈ liftsRing f) : p %ₘ m ∈ liftsRing f := by
  rw [← lifts_iff_liftsRing] at hml hp ⊢
  obtain ⟨m', hm'map, -, hm'⟩ := lifts_and_natDegree_eq_and_monic hml hm
  obtain ⟨p', rfl⟩ := (mem_lifts p).mp hp
  rw [mem_lifts]
  exact ⟨p' %ₘ m', by rw [map_modByMonic f hm', hm'map]⟩

theorem coeff_mem_range_of_mem_liftsRing {p : S[X]} (hp : p ∈ liftsRing f) (n : ℕ) :
    p.coeff n ∈ Set.range f := by
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts] at hp
  exact hp n

theorem mem_liftsRing_of_coeff {p : S[X]} (hp : ∀ n, p.coeff n ∈ Set.range f) : p ∈ liftsRing f := by
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts]
  exact hp

end Lifts

section Main

variable {K : Type*} [Field K] {σ : Type*} (O : Subring K)

/-- The inclusion `O⟦t⟧ → K⟦t⟧`. -/
noncomputable abbrev incl : MvPowerSeries σ O →+* MvPowerSeries σ K :=
  MvPowerSeries.map O.subtype

omit [Field K] in
theorem mem_range_incl {K : Type*} [CommRing K] {O : Subring K} {F : MvPowerSeries σ K} :
    F ∈ Set.range (MvPowerSeries.map (σ := σ) O.subtype) ↔ ∀ d, MvPowerSeries.coeff d F ∈ O := by
  constructor
  · rintro ⟨G, rfl⟩ d
    simp [MvPowerSeries.coeff_map]
  · intro h
    exact ⟨F.toSubring O h, MvPowerSeries.map_toSubring _ _ _⟩

/-- Constants: polynomials of `K[X]` as polynomials over `K⟦t⟧`. -/
noncomputable abbrev cst : K[X] →+* (MvPowerSeries σ K)[X] :=
  Polynomial.mapRingHom (MvPowerSeries.C (σ := σ) (R := K))

theorem cst_mem_liftsRing {p : K[X]} (hp : ∀ n, p.coeff n ∈ O) :
    cst (σ := σ) p ∈ liftsRing (incl (σ := σ) O) := by
  classical
  refine mem_liftsRing_of_coeff _ fun n => ?_
  rw [mem_range_incl]
  intro d
  simp only [cst, coe_mapRingHom, coeff_map]
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact hp n
  · exact O.zero_mem

theorem cst_mem_ordIdeal_zero {p : K[X]} :
    MvPowerSeries.constantCoeff (σ := σ) ((cst (σ := σ) p).coeff 0) = p.coeff 0 := by
  simp [cst, coeff_map]

/-- Vectors of power series as polynomials of degree `< d`. -/
noncomputable def toPoly {A : Type*} [CommRing A] {d : ℕ} (y : Fin d → A) : A[X] :=
  ∑ i : Fin d, C (y i) * X ^ (i : ℕ)

theorem coeff_toPoly {A : Type*} [CommRing A] {d : ℕ} (y : Fin d → A) (n : ℕ) :
    (toPoly y).coeff n = if h : n < d then y ⟨n, h⟩ else 0 := by
  classical
  simp only [toPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      · simp
      · intro hn; exact hb (Fin.ext hn.symm)
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    · simp
    · intro hn; exact h (hn ▸ i.2)

theorem toPoly_fromPoly {A : Type*} [CommRing A] {d : ℕ} {p : A[X]} (hp : p.natDegree < d) :
    toPoly (fun i : Fin d => p.coeff i) = p := by
  ext n
  rw [coeff_toPoly]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]

theorem natDegree_toPoly_lt {A : Type*} [CommRing A] {d : ℕ} (hd : 0 < d) (y : Fin d → A) :
    (toPoly y).natDegree < d := by
  have h : (toPoly y).natDegree ≤ d - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_toPoly, dif_neg (by omega)]
  omega

/-- A scalar of `K` as a constant polynomial over `K⟦t⟧`. -/
noncomputable abbrev CC (x : K) : (MvPowerSeries σ K)[X] := Polynomial.C (MvPowerSeries.C x)

theorem degree_CC_mul_le (x : K) (p : (MvPowerSeries σ K)[X]) : (CC x * p).degree ≤ p.degree := by
  rw [CC, ← smul_eq_C_mul]; exact degree_smul_le _ _

theorem cst_C (x : K) : cst (σ := σ) (Polynomial.C x) = CC x := by
  simp [cst]

/-- The coefficientwise condition of the fixed point: coefficients in `O`, no constant term. -/
def IntNoConst (O : Subring K) : (σ →₀ ℕ) → K → Prop := fun e x => x ∈ O ∧ (e = 0 → x = 0)

theorem toPoly_mem_of_coeffSet {d : ℕ} {y : Fin d → MvPowerSeries σ K}
    (hy : y ∈ FormalFix.CoeffSet (IntNoConst O)) :
    toPoly y ∈ liftsRing (incl (σ := σ) O) ∧
      toPoly y ∈ (ordIdeal (σ := σ) (R := K) 1).map (C : _ →+* (MvPowerSeries σ K)[X]) := by
  constructor
  · refine mem_liftsRing_of_coeff _ fun n => ?_
    rw [coeff_toPoly]
    split_ifs with h
    · rw [mem_range_incl]
      exact fun e => (hy ⟨n, h⟩ e).1
    · exact ⟨0, map_zero _⟩
  · rw [Ideal.mem_map_C_iff]
    intro n
    rw [coeff_toPoly]
    split_ifs with h
    · rw [ordIdeal_one_iff, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hy ⟨n, h⟩ 0).2 rfl
    · exact Ideal.zero_mem _

theorem coeffSet_of_mem {d : ℕ} {p : (MvPowerSeries σ K)[X]} (hl : p ∈ liftsRing (incl (σ := σ) O))
    (h1 : p ∈ (ordIdeal (σ := σ) (R := K) 1).map (C : _ →+* (MvPowerSeries σ K)[X])) :
    (fun i : Fin d => p.coeff i) ∈ FormalFix.CoeffSet (IntNoConst O) := by
  intro i e
  refine ⟨(mem_range_incl.mp (coeff_mem_range_of_mem_liftsRing _ hl i)) e, ?_⟩
  rintro rfl
  have := (Ideal.mem_map_C_iff.mp h1) i
  rw [ordIdeal_one_iff] at this
  simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using this

theorem toPoly_sub_mem {d : ℕ} {y z : Fin d → MvPowerSeries σ K} {n : ℕ}
    (h : ∀ i, (n : ℕ∞) ≤ (y i - z i).order) :
    toPoly y - toPoly z ∈ (ordIdeal (σ := σ) (R := K) n).map (C : _ →+* (MvPowerSeries σ K)[X]) := by
  rw [Ideal.mem_map_C_iff]
  intro l
  rw [coeff_sub, coeff_toPoly, coeff_toPoly]
  split_ifs with hl
  · exact h ⟨l, hl⟩
  · simpa using Ideal.zero_mem _

/-- **Square roots modulo `m = X^d + π^(j+k) m̃`.** -/
theorem exists_sqrtMod (h2 : (2 : K) ≠ 0) {d : ℕ} (hd : 0 < d) {π : K} (hπ : π ∈ O)
    (f V0 U0 q h : K[X]) (hq : f - V0 ^ 2 = X ^ d * q) (hU : V0 * U0 = 1 + X ^ d * h)
    (hU0 : U0.coeff 0 ≠ 0) (j k : ℕ)
    (ha : ∀ n, (Polynomial.C (π ^ k * 2⁻¹) * U0 * q).coeff n ∈ O)
    (hb : ∀ n, (Polynomial.C (π ^ j * 2⁻¹) * U0).coeff n ∈ O)
    (hc : ∀ n, (Polynomial.C (π ^ (j + k)) * h).coeff n ∈ O)
    (mt : (MvPowerSeries σ K)[X]) (hmt : mt ∈ liftsRing (incl (σ := σ) O))
    (hmt1 : mt ∈ (ordIdeal (σ := σ) (R := K) 1).map (C : _ →+* (MvPowerSeries σ K)[X]))
    (hmtd : mt.degree < d) :
    ∃ Vt : (MvPowerSeries σ K)[X], Vt ∈ liftsRing (incl (σ := σ) O) ∧
      Vt ∈ (ordIdeal (σ := σ) (R := K) 1).map (C : _ →+* (MvPowerSeries σ K)[X]) ∧
      Vt.natDegree < d ∧
      (X ^ d + CC (π ^ (j + k)) * mt) ∣ cst f - (cst V0 + CC (π ^ j) * Vt) ^ 2 := by
  classical
  set I1 := (ordIdeal (σ := σ) (R := K) 1).map (C : _ →+* (MvPowerSeries σ K)[X]) with hI1
  set L := liftsRing (incl (σ := σ) O) with hL
  set m := X ^ d + CC (π ^ (j + k)) * mt with hmdef
  have hmmonic : m.Monic := by
    exact monic_X_pow_add (lt_of_le_of_lt (degree_CC_mul_le _ _) hmtd)
  have hmdeg : m.natDegree = d := by
    rw [hmdef, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]
    exact lt_of_le_of_lt (degree_CC_mul_le _ _) hmtd
  have hCCL : ∀ x ∈ O, CC (σ := σ) x ∈ L := fun x hx => by
    rw [← cst_C]; exact cst_mem_liftsRing O (fun n => by
      rw [Polynomial.coeff_C]; split_ifs
      · exact hx
      · exact O.zero_mem)
  have hmL : m ∈ L := L.add_mem (L.pow_mem (mem_liftsRing_of_coeff _ fun n => by
      rw [coeff_X]; split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩) _) (L.mul_mem (hCCL _ (O.pow_mem hπ _)) hmt)
  set a' := cst (σ := σ) (Polynomial.C (π ^ k * 2⁻¹) * U0 * q) with ha'
  set b' := cst (σ := σ) (Polynomial.C (π ^ j * 2⁻¹) * U0) with hb'
  set c' := cst (σ := σ) (Polynomial.C (π ^ (j + k)) * h) with hc'
  have ha'L : a' ∈ L := cst_mem_liftsRing O ha
  have hb'L : b' ∈ L := cst_mem_liftsRing O hb
  have hc'L : c' ∈ L := cst_mem_liftsRing O hc
  let G : (MvPowerSeries σ K)[X] → (MvPowerSeries σ K)[X] :=
    fun V => -(a' * mt) - b' * V ^ 2 + c' * mt * V
  let T : (Fin d → MvPowerSeries σ K) → (Fin d → MvPowerSeries σ K) :=
    fun y i => (G (toPoly y) %ₘ m).coeff i
  have hGL : ∀ V ∈ L, G V ∈ L := fun V hV =>
    L.add_mem (L.sub_mem (L.neg_mem (L.mul_mem ha'L hmt)) (L.mul_mem hb'L (L.pow_mem hV 2)))
      (L.mul_mem (L.mul_mem hc'L hmt) hV)
  have hGI : ∀ V ∈ I1, G V ∈ I1 := fun V hV =>
    I1.add_mem (I1.sub_mem (I1.neg_mem (I1.mul_mem_left _ hmt1))
      (I1.mul_mem_left _ (by rw [pow_two]; exact I1.mul_mem_left _ hV)))
      (I1.mul_mem_right _ (I1.mul_mem_left _ hmt1))
  have hS : ∀ y ∈ FormalFix.CoeffSet (IntNoConst O), T y ∈ FormalFix.CoeffSet (IntNoConst O) := by
    intro y hy
    obtain ⟨hyL, hyI⟩ := toPoly_mem_of_coeffSet O hy
    exact coeffSet_of_mem O (modByMonic_mem_liftsRing _ hmmonic hmL (hGL _ hyL))
      (modByMonic_mem_map_C hmmonic (hGI _ hyI))
  have h0 : (0 : Fin d → MvPowerSeries σ K) ∈ FormalFix.CoeffSet (IntNoConst O) := by
    intro i e
    exact ⟨by simpa using O.zero_mem, fun _ => by simp⟩
  have hT : FormalFix.Contracting (FormalFix.CoeffSet (IntNoConst O)) T := by
    intro y hy z hz n hn i
    obtain ⟨-, hyI⟩ := toPoly_mem_of_coeffSet O hy
    obtain ⟨-, hzI⟩ := toPoly_mem_of_coeffSet O hz
    have hsub := toPoly_sub_mem hn
    have hsum : toPoly y + toPoly z ∈ I1 := I1.add_mem hyI hzI
    have hprod : ∀ P ∈ (ordIdeal (σ := σ) (R := K) n).map (C : _ →+* (MvPowerSeries σ K)[X]),
        ∀ Q ∈ I1, P * Q ∈ (ordIdeal (σ := σ) (R := K) (n + 1)).map
          (C : _ →+* (MvPowerSeries σ K)[X]) := by
      intro P hP Q hQ
      have := Ideal.mul_mem_mul hP hQ
      rw [← Ideal.map_mul] at this
      exact Ideal.map_mono (ordIdeal_mul_le n 1) this
    have hdiff : G (toPoly y) - G (toPoly z) ∈ (ordIdeal (σ := σ) (R := K) (n + 1)).map
        (C : _ →+* (MvPowerSeries σ K)[X]) := by
      have e : G (toPoly y) - G (toPoly z) =
          -(b' * ((toPoly y - toPoly z) * (toPoly y + toPoly z))) +
            c' * ((toPoly y - toPoly z) * mt) := by
        simp only [G]; ring
      rw [e]
      exact Ideal.add_mem _ (neg_mem (Ideal.mul_mem_left _ _ (hprod _ hsub _ hsum)))
        (Ideal.mul_mem_left _ _ (hprod _ hsub _ hmt1))
    have := Ideal.mem_map_C_iff.mp (modByMonic_mem_map_C hmmonic hdiff) i
    rw [sub_modByMonic, coeff_sub] at this
    exact this
  -- the fixed point
  set y := FormalFix.fix T with hydef
  have hyS : y ∈ FormalFix.CoeffSet (IntNoConst O) := FormalFix.fix_mem_coeffSet h0 hS
  have hTy : T y = y := FormalFix.T_fix h0 hS hT
  obtain ⟨hyL, hyI⟩ := toPoly_mem_of_coeffSet O hyS
  set Vt := toPoly y with hVt
  refine ⟨Vt, hyL, hyI, natDegree_toPoly_lt hd y, ?_⟩
  have hm1 : m ≠ 1 := by
    intro h1; have := congrArg natDegree h1; rw [hmdeg, natDegree_one] at this; omega
  have hmod : G Vt %ₘ m = Vt := by
    have e1 : toPoly (T y) = G Vt %ₘ m := by
      apply toPoly_fromPoly
      exact lt_of_lt_of_eq (natDegree_modByMonic_lt _ hmmonic hm1) hmdeg
    rw [← e1, hTy]
  have hdvd1 : m ∣ G Vt - Vt := by
    have := modByMonic_add_div (G Vt) m
    rw [hmod] at this
    exact ⟨G Vt /ₘ m, by linear_combination (-1 : (MvPowerSeries σ K)[X]) * this⟩
  -- the identity
  have hq' : cst (σ := σ) f - cst V0 ^ 2 = X ^ d * cst q := by
    have := congrArg (cst (σ := σ)) hq
    simpa [map_sub, map_pow, map_mul] using this
  have hU' : cst (σ := σ) V0 * cst U0 = 1 + X ^ d * cst h := by
    have := congrArg (cst (σ := σ)) hU
    simpa [map_add, map_mul, map_pow] using this
  have hi2 : (2 : (MvPowerSeries σ K)[X]) * CC (2 : K)⁻¹ = 1 := by
    rw [show (2 : (MvPowerSeries σ K)[X]) = CC (2 : K) by rw [CC, map_ofNat, map_ofNat], CC, CC, ← map_mul, ← map_mul,
      mul_inv_cancel₀ h2, map_one, map_one]
  have ha'e : a' = CC (π) ^ k * CC 2⁻¹ * cst U0 * cst q := by
    simp [ha', map_mul, map_pow, cst_C]
  have hb'e : b' = CC (π) ^ j * CC 2⁻¹ * cst U0 := by
    simp [hb', map_mul, map_pow, cst_C]
  have hc'e : c' = CC (π) ^ (j + k) * cst h := by
    simp [hc', map_mul, map_pow, cst_C]
  have hmE : m = X ^ d + CC π ^ (j + k) * mt := by
    rw [hmdef, CC, CC, map_pow, map_pow]
  have hG : G Vt = -(a' * mt) - b' * Vt ^ 2 + c' * mt * Vt := rfl
  have hCC2 : CC (σ := σ) (π ^ j) = CC π ^ j := by rw [CC, CC, map_pow, map_pow]
  have key : cst U0 * (cst f - (cst V0 + CC (π ^ j) * Vt) ^ 2) =
      2 * CC π ^ j * (G Vt - Vt) + m * (cst U0 * cst q - 2 * CC π ^ j * cst h * Vt) := by
    rw [hG, ha'e, hb'e, hc'e, hmE, hCC2]
    linear_combination cst U0 * hq' - 2 * CC π ^ j * Vt * hU' +
      (CC π ^ (j + k) * cst U0 * cst q * mt + CC π ^ (2 * j) * cst U0 * Vt ^ 2) * hi2
  have hdvd2 : m ∣ cst U0 * (cst f - (cst V0 + CC (π ^ j) * Vt) ^ 2) := by
    rw [key]
    exact dvd_add (dvd_mul_of_dvd_right hdvd1 _) (dvd_mul_right _ _)
  have hm0 : m.map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = X ^ m.natDegree := by
    rw [hmdeg, hmdef, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X,
      map_C]
    have : mt.map (MvPowerSeries.constantCoeff (σ := σ) (R := K)) = 0 := by
      ext n
      rw [coeff_map, coeff_zero, ← ordIdeal_one_iff]
      exact Ideal.mem_map_C_iff.mp hmt1 n
    rw [this, mul_zero, add_zero]
  refine dvd_of_dvd_mul_of_map hmmonic hm0 ?_ hdvd2
  simpa [cst, coeff_map] using hU0

end Main

end FurioLombardo.Vendor.Toolbox.SqrtMod
