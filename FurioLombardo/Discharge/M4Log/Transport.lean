import Mathlib
import FurioLombardo.Vendor.Toolbox.PowerSeries.SqrtMod
import FurioLombardo.Vendor.Toolbox.PowerSeries.BoundedRes

/-!
# The weighted transport `X ↦ p X`, `t ↦ w · t` on `K⟦τ⟧[X]` (lane lean-m4log, explicit `Adm`)

For weights `w : τ → K` and `p : K`, `tw w p` is the ring endomorphism of `K⟦τ⟧[X]` that rescales the
series coefficients by `w` (`MvPowerSeries.rescale w`) and substitutes `p X` for `X`. The chart
polynomial `u1 = X² + t0 X + t1` goes to `p² u1` when `w = (p, p²)` (`tw_u1`), so the chain of
R7/Formal.lean in the coordinates `X = p X̃`, `t = (p t̃0, p² t̃1)` is the transported chain.

`TInt O w p c P`: after transport, `P` is `c` times a polynomial with coefficients in `O⟦τ⟧`;
`TIntS O w c s`: after rescaling, the series `s` is `c` times a series with coefficients in `O`.
They give the bounded denominators of `Setup.Adm` (`mem_bddR_of_tIntS`, `mem_LR_of_tInt`) and the
integrality of `GoodM` (`pow_mul_coeff_mem_of_tIntS`).

Other tools: `sqrtMod_unique` (two square roots modulo a monic `m` reducing to `X^d`, of degree
`< d` and equal at the origin, are equal), `divByMonic_mem_liftsRing`, `inv_mem_intSeries`
(inverse of an integral series with unit constant term).
-/

open Polynomial

namespace FurioLombardo.Discharge.M4Log.Model

open FurioLombardo.Vendor.Toolbox.SqrtMod FurioLombardo.Vendor.Toolbox.Bounded

variable {K : Type*} [Field K] {τ : Type*}

/-! ## The transport -/

/-- `X ↦ p X` and `t ↦ w · t`. -/
noncomputable def tw (w : τ → K) (p : K) : (MvPowerSeries τ K)[X] →+* (MvPowerSeries τ K)[X] :=
  (Polynomial.compRingHom (C (MvPowerSeries.C p) * X)).comp
    (Polynomial.mapRingHom (MvPowerSeries.rescale w))

theorem tw_apply (w : τ → K) (p : K) (P : (MvPowerSeries τ K)[X]) :
    tw w p P = (P.map (MvPowerSeries.rescale w)).comp (C (MvPowerSeries.C p) * X) := rfl

theorem coeff_tw (w : τ → K) (p : K) (P : (MvPowerSeries τ K)[X]) (n : ℕ) :
    (tw w p P).coeff n = MvPowerSeries.C (p ^ n) * MvPowerSeries.rescale w (P.coeff n) := by
  rw [tw_apply, Polynomial.comp_C_mul_X_coeff, coeff_map, map_pow, mul_comm]

theorem tw_C (w : τ → K) (p : K) (a : MvPowerSeries τ K) :
    tw w p (C a) = C (MvPowerSeries.rescale w a) := by
  rw [tw_apply, Polynomial.map_C, Polynomial.C_comp]

/-- Rescaling fixes constants. -/
theorem rescale_C_tw (w : τ → K) (a : K) :
    MvPowerSeries.rescale w (MvPowerSeries.C a : MvPowerSeries τ K) = MvPowerSeries.C a := by
  classical
  ext n
  rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C]
  split_ifs with h
  · subst h; simp
  · rw [mul_zero]

/-- Rescaling a variable. -/
theorem rescale_X_tw (w : τ → K) (i : τ) :
    MvPowerSeries.rescale w (MvPowerSeries.X i : MvPowerSeries τ K) =
      MvPowerSeries.C (w i) * MvPowerSeries.X i := by
  classical
  ext n
  rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  split_ifs with h
  · subst h; simp
  · rw [mul_zero, mul_zero]

/-- Rescaling by nonzero weights is injective. -/
theorem rescale_injective_tw {w : τ → K} (hw : ∀ i, w i ≠ 0) :
    Function.Injective (MvPowerSeries.rescale w : MvPowerSeries τ K →+* MvPowerSeries τ K) := by
  intro a b h
  have e := congrArg (MvPowerSeries.rescale w⁻¹) h
  simp only [MvPowerSeries.rescale_rescale] at e
  have h1 : w * w⁻¹ = 1 := funext fun i => mul_inv_cancel₀ (hw i)
  rwa [h1, MvPowerSeries.rescale_one, RingHom.id_apply, RingHom.id_apply] at e

theorem coeff_tw_eq_zero_iff (w : τ → K) {p : K} (hp : p ≠ 0) (hw : ∀ i, w i ≠ 0)
    (P : (MvPowerSeries τ K)[X]) (n : ℕ) : (tw w p P).coeff n = 0 ↔ P.coeff n = 0 := by
  rw [coeff_tw]
  have hu : IsUnit (MvPowerSeries.C (p ^ n) : MvPowerSeries τ K) :=
    (isUnit_iff_ne_zero.mpr (pow_ne_zero n hp)).map MvPowerSeries.C
  rw [hu.mul_right_eq_zero, map_eq_zero_iff _ (rescale_injective_tw hw)]

theorem support_tw (w : τ → K) {p : K} (hp : p ≠ 0) (hw : ∀ i, w i ≠ 0)
    (P : (MvPowerSeries τ K)[X]) : (tw w p P).support = P.support := by
  ext n
  rw [mem_support_iff, mem_support_iff, Ne, Ne, coeff_tw_eq_zero_iff w hp hw]

theorem tw_X (w : τ → K) (p : K) : tw w p X = C (MvPowerSeries.C p) * X := by
  rw [tw_apply, Polynomial.map_X, Polynomial.X_comp]

theorem tw_cst (w : τ → K) (p : K) (f : K[X]) :
    tw w p (cst (σ := τ) f) = cst (σ := τ) (f.comp (C p * X)) := by
  rw [tw_apply]
  simp only [cst, Polynomial.coe_mapRingHom]
  rw [Polynomial.map_map, Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    show (MvPowerSeries.rescale w).comp MvPowerSeries.C = (MvPowerSeries.C : K →+* MvPowerSeries τ K) from
      RingHom.ext fun a => rescale_C_tw w a]

theorem natDegree_tw (w : τ → K) {p : K} (hp : p ≠ 0) (hw : ∀ i, w i ≠ 0)
    (P : (MvPowerSeries τ K)[X]) : (tw w p P).natDegree = P.natDegree := by
  rw [Polynomial.natDegree, Polynomial.natDegree, Polynomial.degree, Polynomial.degree, support_tw w hp hw]

theorem degree_tw (w : τ → K) {p : K} (hp : p ≠ 0) (hw : ∀ i, w i ≠ 0)
    (P : (MvPowerSeries τ K)[X]) : (tw w p P).degree = P.degree := by
  rw [Polynomial.degree, Polynomial.degree, support_tw w hp hw]

theorem map_tw (w : τ → K) (p : K) (P : (MvPowerSeries τ K)[X]) :
    (tw w p P).map MvPowerSeries.constantCoeff =
      (P.map MvPowerSeries.constantCoeff).comp (C p * X) := by
  ext n
  rw [Polynomial.coeff_map, coeff_tw, map_mul, MvPowerSeries.constantCoeff_C,
    Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map, mul_comm]
  congr 1
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_rescale]
  simp

theorem tw_injective (w : τ → K) {p : K} (hp : p ≠ 0) (hw : ∀ i, w i ≠ 0) :
    Function.Injective (tw w p) := by
  intro P Q h
  refine Polynomial.ext fun n => ?_
  have e := congrArg (fun R => R.coeff n) h
  simp only [coeff_tw] at e
  have hu : IsUnit (MvPowerSeries.C (p ^ n) : MvPowerSeries τ K) :=
    (isUnit_iff_ne_zero.mpr (pow_ne_zero n hp)).map MvPowerSeries.C
  exact rescale_injective_tw hw (hu.mul_left_cancel e)

/-! ## The chart weights -/

/-- The weights `(p, p²)` of `(t0, t1)`. -/
noncomputable def wt1 (p : K) : Fin 2 → K := ![p, p ^ 2]

/-- The weights `(p, p², p, p²)` of `(s0, s1, s0', s1')`. -/
noncomputable def wt2 (p : K) : Fin 2 ⊕ Fin 2 → K := Sum.elim (wt1 p) (wt1 p)

theorem wt1_ne_zero {p : K} (hp : p ≠ 0) (i : Fin 2) : wt1 p i ≠ 0 := by
  fin_cases i <;> simp [wt1, hp]

theorem wt2_ne_zero {p : K} (hp : p ≠ 0) (i : Fin 2 ⊕ Fin 2) : wt2 p i ≠ 0 := by
  rcases i with i | i <;> exact wt1_ne_zero hp i

/-- The chart polynomial `X² + t0 X + t1` over `K⟦t⟧`. -/
noncomputable abbrev uP {σ : Type*} (t : Fin 2 → σ) : (MvPowerSeries σ K)[X] :=
  X ^ 2 + C (MvPowerSeries.X (t 0)) * X + C (MvPowerSeries.X (t 1))

theorem tw_uP_one (p : K) :
    tw (wt1 p) p (uP (K := K) (id : Fin 2 → Fin 2)) =
      C (MvPowerSeries.C (p ^ 2)) * uP (K := K) (id : Fin 2 → Fin 2) := by
  simp only [uP, map_add, map_mul, map_pow, tw_X, tw_C, rescale_X_tw, wt2, wt1, Sum.elim_inl,
    Sum.elim_inr, id, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

theorem tw_uP_inl (p : K) :
    tw (wt2 p) p (uP (K := K) (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2)) =
      C (MvPowerSeries.C (p ^ 2)) * uP (K := K) (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) := by
  simp only [uP, map_add, map_mul, map_pow, tw_X, tw_C, rescale_X_tw, wt2, wt1, Sum.elim_inl,
    Sum.elim_inr, id, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

theorem tw_uP_inr (p : K) :
    tw (wt2 p) p (uP (K := K) (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2)) =
      C (MvPowerSeries.C (p ^ 2)) * uP (K := K) (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) := by
  simp only [uP, map_add, map_mul, map_pow, tw_X, tw_C, rescale_X_tw, wt2, wt1, Sum.elim_inl,
    Sum.elim_inr, id, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-! ## Integrality after transport -/

/-- After transport, `P` is `c` times a polynomial with coefficients in `O⟦τ⟧`. -/
def TInt (O : Subring K) (w : τ → K) (p c : K) (P : (MvPowerSeries τ K)[X]) : Prop :=
  ∃ Q ∈ liftsRing (incl (σ := τ) O), tw w p P = C (MvPowerSeries.C c) * Q

/-- After rescaling, `s` is `c` times a series with coefficients in `O`. -/
def TIntS (O : Subring K) (w : τ → K) (c : K) (s : MvPowerSeries τ K) : Prop :=
  ∃ q ∈ intSeries O τ, MvPowerSeries.rescale w s = MvPowerSeries.C c * q

theorem coeff_mem_intSeries_of_liftsRing {O : Subring K} {P : (MvPowerSeries τ K)[X]}
    (hP : P ∈ liftsRing (incl (σ := τ) O)) (n : ℕ) : P.coeff n ∈ intSeries O τ := by
  rw [mem_intSeries]
  exact mem_range_incl.mp (coeff_mem_range_of_mem_liftsRing _ hP n)

theorem liftsRing_of_coeff_mem_intSeries {O : Subring K} {P : (MvPowerSeries τ K)[X]}
    (hP : ∀ n, P.coeff n ∈ intSeries O τ) : P ∈ liftsRing (incl (σ := τ) O) := by
  apply mem_liftsRing_of_coeff
  intro n
  have h := hP n
  rw [mem_intSeries] at h
  apply (mem_range_incl (σ := τ) (F := P.coeff n)).mpr
  exact h

/-- Coefficients of a transported integral polynomial. -/
theorem tIntS_coeff {O : Subring K} {w : τ → K} {p c : K} (hp : p ≠ 0)
    {P : (MvPowerSeries τ K)[X]} (h : TInt O w p c P) (n : ℕ) :
    TIntS O w (c / p ^ n) (P.coeff n) := by
  obtain ⟨Q, hQ, hPQ⟩ := h
  refine ⟨Q.coeff n, coeff_mem_intSeries_of_liftsRing hQ n, ?_⟩
  have e := congrArg (fun R => R.coeff n) hPQ
  simp only [coeff_tw, Polynomial.coeff_C_mul] at e
  have hu : MvPowerSeries.C (p ^ n)⁻¹ * MvPowerSeries.C (p ^ n) = (1 : MvPowerSeries τ K) := by
    rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero n hp), map_one]
  calc MvPowerSeries.rescale w (P.coeff n)
      = MvPowerSeries.C (p ^ n)⁻¹ * (MvPowerSeries.C (p ^ n) * MvPowerSeries.rescale w (P.coeff n)) := by
        rw [← mul_assoc, hu, one_mul]
    _ = MvPowerSeries.C (p ^ n)⁻¹ * (MvPowerSeries.C c * Q.coeff n) := by rw [e]
    _ = MvPowerSeries.C (c / p ^ n) * Q.coeff n := by
        rw [← mul_assoc, ← map_mul, div_eq_mul_inv, mul_comm c]

/-- Rescaling by a constant `l = r i * w i` through the rescaling by `w`. -/
theorem coeff_rescale_const_eq {w r : τ → K} {l : K} (hr : ∀ i, l = r i * w i)
    (s : MvPowerSeries τ K) (d : τ →₀ ℕ) :
    MvPowerSeries.coeff d (MvPowerSeries.rescale (fun _ => l) s) =
      (d.prod fun i m => r i ^ m) * MvPowerSeries.coeff d (MvPowerSeries.rescale w s) := by
  rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_rescale, ← mul_assoc, ← Finsupp.prod_mul]
  congr 1
  exact Finsupp.prod_congr fun i _ => by rw [hr i, mul_pow]

theorem prod_pow_mem {O : Subring K} {r : τ → K} (hr : ∀ i, r i ∈ O) (d : τ →₀ ℕ) :
    (d.prod fun i m => r i ^ m) ∈ O := by
  unfold Finsupp.prod
  exact O.prod_mem fun i _ => pow_mem (hr i) _

/-- A series integral after rescaling by `w` has bounded denominators after rescaling by `l`,
when `l / w i ∈ O` for every `i`. -/
theorem mem_bddR_of_tIntS {O : Subring K} {π : O} (hπ : (π : K) ≠ 0)
    (hbd : ∀ x : K, ∃ k : ℕ, (π : K) ^ k * x ∈ O) {w : τ → K} {l : K}
    (hl : ∀ i, ∃ r ∈ O, l = r * w i) {c : K} {s : MvPowerSeries τ K} (h : TIntS O w c s) :
    s ∈ bddR τ π l := by
  choose r hrO hr using hl
  obtain ⟨q, hq, hsq⟩ := h
  obtain ⟨N, hN⟩ := hbd c
  rw [mem_bddR]
  refine ⟨N, fun d => ?_⟩
  rw [coeff_rescale_const_eq hr, hsq, MvPowerSeries.coeff_C_mul]
  have e : (π : K) ^ N * ((d.prod fun i m => r i ^ m) * (c * MvPowerSeries.coeff d q)) =
      (d.prod fun i m => r i ^ m) * ((π : K) ^ N * c) * MvPowerSeries.coeff d q := by ring
  rw [e]
  exact O.mul_mem (O.mul_mem (prod_pow_mem hrO d) hN) (hq d)

/-- The polynomial version of `mem_bddR_of_tIntS`. -/
theorem coeff_mem_bddR_of_tInt {O : Subring K} {π : O} (hπ : (π : K) ≠ 0)
    (hbd : ∀ x : K, ∃ k : ℕ, (π : K) ^ k * x ∈ O) {w : τ → K} {p l : K} (hp : p ≠ 0)
    (hl : ∀ i, ∃ r ∈ O, l = r * w i) {c : K} {P : (MvPowerSeries τ K)[X]} (h : TInt O w p c P)
    (n : ℕ) : P.coeff n ∈ bddR τ π l := by
  have hTIntS : TIntS O w (c / p ^ n) (P.coeff n) := tIntS_coeff hp h n
  exact mem_bddR_of_tIntS hπ hbd hl hTIntS

/-- The integrality of `GoodM`: `l ^ |d| coeff_d s ∈ O` when `c ∈ O` and `l / w i ∈ O`. -/
theorem pow_mul_coeff_mem_of_tIntS {O : Subring K} {w : τ → K} {l : K}
    (hl : ∀ i, ∃ r ∈ O, l = r * w i) {c : K} (hc : c ∈ O) {s : MvPowerSeries τ K}
    (h : TIntS O w c s) (d : τ →₀ ℕ) : l ^ d.degree * MvPowerSeries.coeff d s ∈ O := by
  choose r hrO hr using hl
  obtain ⟨q, hq, hsq⟩ := h
  have hdeg : (d.prod fun _ m => l ^ m) = l ^ d.degree := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum]; rfl
  have e := coeff_rescale_const_eq hr s d
  rw [MvPowerSeries.coeff_rescale, hdeg, hsq, MvPowerSeries.coeff_C_mul] at e
  rw [e]
  exact O.mul_mem (prod_pow_mem hrO d) (O.mul_mem hc (hq d))

/-- Inverses: an integral series with a unit constant term has an integral inverse. -/
theorem inv_mem_intSeries {O : Subring K} {s : MvPowerSeries τ K} (hs : s ∈ intSeries O τ)
    (h0 : (MvPowerSeries.constantCoeff s)⁻¹ ∈ O) (h00 : MvPowerSeries.constantCoeff s ≠ 0) :
    s⁻¹ ∈ intSeries O τ := by
  obtain ⟨s', rfl⟩ := mem_range_incl.mpr hs
  have hc' : IsUnit (MvPowerSeries.constantCoeff s') := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, h0⟩, ?_⟩
    apply Subtype.ext
    have e : ((MvPowerSeries.constantCoeff s' : O) : K) =
        MvPowerSeries.constantCoeff (incl (σ := τ) O s') := by
      rw [incl, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map]
      rfl
    simp only [Subring.coe_mul, Subring.coe_one, e]
    exact mul_inv_cancel₀ h00
  obtain ⟨u, hu⟩ := (MvPowerSeries.isUnit_iff_constantCoeff.mpr hc')
  have hinv : incl (σ := τ) O (u⁻¹ : (MvPowerSeries τ O)ˣ) = (incl (σ := τ) O s')⁻¹ := by
    rw [MvPowerSeries.eq_inv_iff_mul_eq_one h00, ← map_mul, ← hu, Units.inv_mul, map_one]
  rw [← hinv, mem_intSeries]
  exact mem_range_incl.mp ⟨_, rfl⟩

theorem tIntS_inv {O : Subring K} {w : τ → K} {c : K} {s : MvPowerSeries τ K}
    (hc : c ≠ 0) {q : MvPowerSeries τ K} (hq : q ∈ intSeries O τ)
    (hq0 : (MvPowerSeries.constantCoeff q)⁻¹ ∈ O) (hq00 : MvPowerSeries.constantCoeff q ≠ 0)
    (hs : MvPowerSeries.rescale w s = MvPowerSeries.C c * q) : TIntS O w c⁻¹ s⁻¹ := by
  have hcs : MvPowerSeries.constantCoeff (MvPowerSeries.rescale w s) ≠ 0 := by
    rw [hs, map_mul, MvPowerSeries.constantCoeff_C]
    exact mul_ne_zero hc hq00
  have hs0 : MvPowerSeries.constantCoeff s ≠ 0 := by
    rwa [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_rescale,
      Finsupp.prod_zero_index, one_mul, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hcs
  refine ⟨q⁻¹, inv_mem_intSeries hq hq0 hq00, ?_⟩
  have e1 : MvPowerSeries.rescale w s⁻¹ = (MvPowerSeries.rescale w s)⁻¹ := by
    rw [MvPowerSeries.eq_inv_iff_mul_eq_one hcs, ← map_mul, MvPowerSeries.inv_mul_cancel _ hs0, map_one]
  rw [e1, hs, MvPowerSeries.mul_inv_rev, MvPowerSeries.C_inv, mul_comm]

/-! ## Polynomial tools -/

theorem divByMonic_mem_liftsRing {O : Subring K} {m P : (MvPowerSeries τ K)[X]} (hm : m.Monic)
    (hml : m ∈ liftsRing (incl (σ := τ) O)) (hP : P ∈ liftsRing (incl (σ := τ) O)) :
    P /ₘ m ∈ liftsRing (incl (σ := τ) O) := by
  rw [← lifts_iff_liftsRing] at hml hP ⊢
  obtain ⟨m', hm'map, -, hm'⟩ := lifts_and_natDegree_eq_and_monic hml hm
  obtain ⟨P', rfl⟩ := (mem_lifts P).mp hP
  rw [mem_lifts]
  exact ⟨P' /ₘ m', by rw [map_divByMonic _ hm', hm'map]⟩

/-- A monic `m` dividing a polynomial of smaller degree: the polynomial is zero. -/
theorem eq_zero_of_monic_dvd {R : Type*} [CommRing R] {m P : R[X]} (hm : m.Monic) (h : m ∣ P)
    (hd : P.degree < m.degree) : P = 0 := by
  nontriviality R
  have hmod0 : P %ₘ m = 0 := ((Polynomial.modByMonic_eq_zero_iff_dvd hm).mpr h)
  have hmodP : P %ₘ m = P := ((Polynomial.modByMonic_eq_self_iff hm).mpr hd)
  rw [hmodP] at hmod0
  exact hmod0

/-- **Uniqueness of square roots modulo `m`** reducing to `X^d` at the origin: two roots of
degree `< deg m`, equal at the origin and with a nonzero constant term there, are equal. -/
theorem sqrtMod_unique (h2 : (2 : K) ≠ 0) {m F A B : (MvPowerSeries τ K)[X]} (hm : m.Monic)
    (hm0 : m.map (MvPowerSeries.constantCoeff (σ := τ) (R := K)) = X ^ m.natDegree)
    (hA : A.degree < m.degree) (hB : B.degree < m.degree)
    (hAB : A.map (MvPowerSeries.constantCoeff (σ := τ) (R := K)) =
      B.map (MvPowerSeries.constantCoeff (σ := τ) (R := K)))
    (hA0 : MvPowerSeries.constantCoeff (A.coeff 0) ≠ 0)
    (hFA : m ∣ F - A ^ 2) (hFB : m ∣ F - B ^ 2) : A = B := by
  have hdvd : m ∣ (A + B) * (A - B) := by
    have e : (A + B) * (A - B) = (F - B ^ 2) - (F - A ^ 2) := by ring
    rw [e]
    exact dvd_sub hFB hFA
  have hB0 : MvPowerSeries.constantCoeff (B.coeff 0) = MvPowerSeries.constantCoeff (A.coeff 0) := by
    have e := congrArg (fun P => P.coeff 0) hAB
    simp only [Polynomial.coeff_map] at e
    exact e.symm
  have hAB0 : MvPowerSeries.constantCoeff ((A + B).coeff 0) ≠ 0 := by
    rw [Polynomial.coeff_add, map_add, hB0, ← two_mul]
    exact mul_ne_zero h2 hA0
  have hm' := dvd_of_dvd_mul_of_map hm hm0 hAB0 hdvd
  have hdeg : (A - B).degree < m.degree := lt_of_le_of_lt (degree_sub_le _ _) (max_lt hA hB)
  exact sub_eq_zero.mp (eq_zero_of_monic_dvd hm hm' hdeg)

/-- The inverse modulo `X²` of a polynomial whose constant coefficient is a unit series. -/
theorem exists_inv_mod_X2 {O : Subring K} {E : (MvPowerSeries τ K)[X]}
    (hE : E ∈ liftsRing (incl (σ := τ) O))
    (h0 : (MvPowerSeries.constantCoeff (E.coeff 0))⁻¹ ∈ O)
    (h00 : MvPowerSeries.constantCoeff (E.coeff 0) ≠ 0) :
    ∃ Ei ∈ liftsRing (incl (σ := τ) O), (X ^ 2 : (MvPowerSeries τ K)[X]) ∣ E * Ei - 1 := by
  classical
  have hi : E.coeff 0 * (E.coeff 0)⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ h00
  have hi0 : (E.coeff 0)⁻¹ ∈ intSeries O τ :=
    inv_mem_intSeries (coeff_mem_intSeries_of_liftsRing hE 0) h0 h00
  have h1 := coeff_mem_intSeries_of_liftsRing hE 1
  refine ⟨C (E.coeff 0)⁻¹ - C (E.coeff 1 * (E.coeff 0)⁻¹ * (E.coeff 0)⁻¹) * X, ?_, ?_⟩
  · apply liftsRing_of_coeff_mem_intSeries
    intro n
    rcases n with _ | _ | n
    · simpa [Polynomial.coeff_C, Polynomial.coeff_X] using hi0
    · simpa [Polynomial.coeff_C, Polynomial.coeff_X] using
        (intSeries O τ).neg_mem ((intSeries O τ).mul_mem ((intSeries O τ).mul_mem h1 hi0) hi0)
    · simp
  · rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simp [Polynomial.coeff_mul, hi]
    · simp [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, Polynomial.coeff_C, Polynomial.coeff_X,
        Polynomial.coeff_one]
      linear_combination (-(E.coeff 1)) * (E.coeff 0)⁻¹ * hi

end FurioLombardo.Discharge.M4Log.Model
