import Mathlib
import FurioLombardo.Discharge.R7.Psi
import FurioLombardo.Vendor.Toolbox.Polynomial.CoeffLim

/-!
# The set `Z` of reduced pairs of degree 2 (R7)

`MPair L` is a pair `(t, v)` with `t : Fin 2 → L` (the quadratic `uT t = X² + t₀ X + t₁`) and
`v : L[X]`; `InZ f D` says `deg v < 2` and `uT t ∣ f - v²`. On the model `F = f(X - a)`,
`cls F a D` is the translated class `clsA F a t v`. Facts: classes of pairs lie in `Jac F`, every
point of `Jac F` is `1` or a class (`jac_eq_one_or_cls`), classes determine pairs
(`eq_of_cls_eq`), negation, and closedness of `Z` under coefficientwise limits.
-/

open Polynomial Filter Topology
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3a
open FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.PolyLim

namespace FurioLombardo.Discharge.R7.FinIdx

/-- A pair `(t, v)`: the quadratic `uT t` and the polynomial `v`. -/
structure MPair (L : Type*) [Field L] where
  t : Fin 2 → L
  v : L[X]

variable {L : Type*} [Field L]

/-- Membership in `Z`: `deg v < 2` and `uT t ∣ f - v²`. -/
def InZ (f : L[X]) (D : MPair L) : Prop := D.v.degree < 2 ∧ uT D.t ∣ f - D.v ^ 2

/-- The pair `(t, -v)`. -/
noncomputable def MPair.neg (D : MPair L) : MPair L := ⟨D.t, -D.v⟩

theorem InZ.neg {f : L[X]} {D : MPair L} (h : InZ f D) : InZ f D.neg := by
  refine ⟨?_, ?_⟩
  · change (-D.v).degree < 2
    rw [degree_neg]; exact h.1
  · change uT D.t ∣ f - (-D.v) ^ 2
    rw [neg_sq]; exact h.2

/-- A polynomial of degree `< 2` has `natDegree ≤ 1`. -/
theorem natDegree_le_one_of_degree_lt_two {v : L[X]} (hv : v.degree < 2) : v.natDegree ≤ 1 := by
  by_cases hv0 : v = 0
  · simp [hv0]
  · have := (natDegree_lt_iff_degree_lt (n := 2) hv0).mpr (by exact_mod_cast hv); omega

/-- The divisibility of a pair, translated by `a`. -/
theorem dvd_comp_sub {f F : L[X]} {a : L} (hf : f.comp (X - C a) = F) {t : Fin 2 → L}
    {v : L[X]} (hd : uT t ∣ f - v ^ 2) :
    (uT t).comp (X - C a) ∣ (v.comp (X - C a)) ^ 2 - F := by
  have := map_dvd (compRingHom (X - C a)) hd
  simp only [coe_compRingHom_apply, sub_comp, pow_comp, hf] at this
  have h2 := (dvd_neg).mpr this
  rwa [neg_sub] at h2

theorem comp_add_comp_sub (a : L) (p : L[X]) : (p.comp (X + C a)).comp (X - C a) = p := by
  rw [comp_assoc, add_comp, X_comp, C_comp, sub_add_cancel, comp_X]

/-- The class of a Mumford ideal only depends on the value of `u`. -/
theorem mk0_mumford0_eq_of_eq {F : L[X]} [GoodSextic F] {u u' : L[X]} (hu : u ≠ 0)
    (hu' : u' ≠ 0) (e : u = u') (v : L[X]) :
    ClassGroup.mk0 (mumford0 F hu v) = ClassGroup.mk0 (mumford0 F hu' v) := by
  subst e; rfl

/-- The class of a pair on the model `F` translated by `a`. -/
noncomputable def cls (F : L[X]) [GoodSextic F] (a : L) (D : MPair L) : Pic F :=
  clsA F a D.t D.v

variable {f F : L[X]} [GoodSextic F] {a : L}

theorem cls_mem_Jac (hf : f.comp (X - C a) = F) {D : MPair L} (hD : InZ f D) :
    cls F a D ∈ Jac F := by
  obtain ⟨w, hw⟩ := dvd_comp_sub hf hD.2
  have hp := parity_mumford F (monic_uT_comp a D.t) hw
    (exists_coprime_of_squarefree GoodSextic.squarefree hw)
  rw [natDegree_uT_comp] at hp
  change parity F (cls F a D) = 1
  exact hp

theorem cls_neg (hf : f.comp (X - C a) = F) {D : MPair L} (hD : InZ f D) :
    cls F a D.neg = (cls F a D)⁻¹ := by
  have h := mk0_mumford_neg_of_dvd F (monic_uT_comp a D.t).ne_zero (dvd_comp_sub hf hD.2)
  change ClassGroup.mk0 (mumford0 F _ ((-D.v).comp (X - C a))) = _
  rw [neg_comp]
  exact h

theorem eq_of_cls_eq (hf : f.comp (X - C a) = F) {D D' : MPair L} (hD : InZ f D)
    (hD' : InZ f D') (h : cls F a D = cls F a D') : D = D' := by
  have ht := eq_of_clsA_eq F hf hD.2 hD'.2 h
  obtain ⟨t, v⟩ := D
  obtain ⟨t', v'⟩ := D'
  simp only at ht
  subst ht
  have hv := (eq_of_mk0_mumford_eq F (monic_uT_comp a t) (monic_uT_comp a t)
    (natDegree_uT_comp a t) (natDegree_uT_comp a t) (dvd_comp_sub hf hD.2)
    (dvd_comp_sub hf hD'.2) h).2
  have hv' := map_dvd (compRingHom (X + C a)) hv
  simp only [coe_compRingHom_apply, sub_comp, comp_sub_comp_add] at hv'
  have hdeg : (v - v').degree < (uT t).degree := by
    rw [degree_eq_natDegree (uT_monic t).ne_zero, uT_natDegree]
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt hD.1 hD'.1)
  have := eq_zero_of_dvd_of_degree_lt hv' hdeg
  rw [sub_eq_zero] at this
  subst this
  rfl

theorem jac_eq_one_or_cls (hf : f.comp (X - C a) = F) (x : Jac F) :
    x = 1 ∨ ∃ D : MPair L, InZ f D ∧ (x : Pic F) = cls F a D := by
  rcases jac_eq_one_or_reduced F x with h | ⟨u, v, w, hu, hud, hvd, hw, hx⟩
  · exact Or.inl h
  right
  have hum : (u.comp (X + C a)).Monic :=
    hu.comp (monic_X_add_C a) (by rw [natDegree_X_add_C]; exact one_ne_zero)
  have hud' : (u.comp (X + C a)).natDegree = 2 := by
    rw [natDegree_comp, hud, natDegree_X_add_C]
  set t : Fin 2 → L := ![(u.comp (X + C a)).coeff 1, (u.comp (X + C a)).coeff 0]
  have ht : uT t = u.comp (X + C a) := (eq_uT_of_monic hum hud').symm
  have hfF : F.comp (X + C a) = f := by rw [← hf, comp_sub_comp_add]
  refine ⟨⟨t, v.comp (X + C a)⟩, ⟨?_, ?_⟩, ?_⟩
  · change (v.comp (X + C a)).degree < 2
    refine lt_of_le_of_lt (degree_le_of_natDegree_le (n := 1) ?_) (by norm_num)
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
    exact natDegree_le_one_of_degree_lt_two hvd
  · change uT t ∣ f - (v.comp (X + C a)) ^ 2
    rw [ht]
    refine ⟨-(w.comp (X + C a)), ?_⟩
    have := congrArg (fun p => p.comp (X + C a)) hw
    simp only [sub_comp, pow_comp, mul_comp, hfF] at this
    linear_combination -this
  · rw [hx]
    change _ = ClassGroup.mk0 (mumford0 F _ ((v.comp (X + C a)).comp (X - C a)))
    rw [comp_add_comp_sub]
    exact mk0_mumford0_eq_of_eq _ _ (by rw [ht, comp_add_comp_sub]) v

/-! ### Limits of pairs -/

section Lim

variable {K : Type*} [NormedField K] {ι : Type*} {l : Filter ι}

/-- Convergence of pairs: `t` in `K²` and `v` coefficientwise. -/
def DTendsto (l : Filter ι) (D : ι → MPair K) (D0 : MPair K) : Prop :=
  Tendsto (fun n => (D n).t) l (𝓝 D0.t) ∧ PTendsto l (fun n => (D n).v) D0.v

/-- The size of a pair. -/
noncomputable def dsize (D : MPair K) : ℝ := ‖D.t 0‖ + ‖D.t 1‖ + psize 1 D.v

theorem ptendsto_uT {t : ι → Fin 2 → K} {t0 : Fin 2 → K} (h : Tendsto t l (𝓝 t0)) :
    PTendsto l (fun n => uT (t n)) (uT t0) := by
  intro i
  have h0 : Tendsto (fun n => t n 0) l (𝓝 (t0 0)) := tendsto_pi_nhds.mp h 0
  have h1 : Tendsto (fun n => t n 1) l (𝓝 (t0 1)) := tendsto_pi_nhds.mp h 1
  simp only [uT, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  refine (tendsto_const_nhds.add (h0.mul tendsto_const_nhds)).add ?_
  split_ifs
  · exact h1
  · exact tendsto_const_nhds

theorem natDegree_sub_sq_le {f v : K[X]} (hv : v.degree < 2) :
    (f - v ^ 2).natDegree ≤ max f.natDegree 2 := by
  have h1 := natDegree_le_one_of_degree_lt_two hv
  refine (natDegree_sub_le _ _).trans (max_le_max le_rfl ?_)
  exact natDegree_pow_le.trans (by omega)

/-- **`Z` is closed.** -/
theorem InZ.of_tendsto [l.NeBot] {f : K[X]} {D : ι → MPair K} {D0 : MPair K}
    (hD : ∀ᶠ n in l, InZ f (D n)) (h : DTendsto l D D0) : InZ f D0 := by
  refine ⟨h.2.degree_lt (hD.mono fun n hn => hn.1), ?_⟩
  exact ((ptendsto_const f).sub (h.2.pow 2)).dvd (N := max f.natDegree 2) (d := 2)
    (hD.mono fun n hn => natDegree_sub_sq_le hn.1) (ptendsto_uT h.1)
    (Eventually.of_forall fun n => ⟨uT_monic _, uT_natDegree _⟩) (uT_monic _) (uT_natDegree _)
    (hD.mono fun n hn => hn.2)

theorem DTendsto.comp_tendsto {κ : Type*} {l' : Filter κ} {φ : κ → ι} (hφ : Tendsto φ l' l)
    {D : ι → MPair K} {D0 : MPair K} (h : DTendsto l D D0) : DTendsto l' (D ∘ φ) D0 :=
  ⟨h.1.comp hφ, h.2.comp_tendsto hφ⟩

/-- Extraction for pairs of bounded size. -/
theorem exists_subseq_dtendsto [ProperSpace K] {D : ℕ → MPair K}
    (hv : ∀ n, (D n).v.degree < 2) {B : ℝ} (hB : ∀ n, dsize (D n) ≤ B) :
    ∃ D0 : MPair K, ∃ φ : ℕ → ℕ, StrictMono φ ∧ DTendsto atTop (D ∘ φ) D0 := by
  set x : ℕ → Fin 4 → K := fun n => ![(D n).t 0, (D n).t 1, (D n).v.coeff 0, (D n).v.coeff 1]
  have hx : ∀ n, x n ∈ Metric.closedBall (0 : Fin 4 → K) B := by
    intro n
    have hd := hB n
    simp only [dsize, psize, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hd
    have n0 := norm_nonneg ((D n).t 0)
    have n1 := norm_nonneg ((D n).t 1)
    have n2 := norm_nonneg ((D n).v.coeff 0)
    have n3 := norm_nonneg ((D n).v.coeff 1)
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)]
    intro i
    fin_cases i <;> simp [x] <;> linarith
  obtain ⟨y, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hx
  have hc : ∀ j : Fin 4, Tendsto (fun n => x (φ n) j) atTop (𝓝 (y j)) :=
    fun j => tendsto_pi_nhds.mp hlim j
  refine ⟨⟨![y 0, y 1], C (y 3) * X + C (y 2)⟩, φ, hφ, ?_, ?_⟩
  · refine tendsto_pi_nhds.mpr fun i => ?_
    fin_cases i
    · exact hc 0
    · exact hc 1
  · intro i
    rcases i with _ | _ | i
    · have := hc 2; simp only [x] at this; simpa using this
    · have := hc 3; simp only [x] at this; simpa using this
    · have h0 : ∀ n, (D (φ n)).v.coeff (i + 2) = 0 := fun n =>
        coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le (hv _) (by exact_mod_cast (by omega : 2 ≤ i + 2)))
      simp only [Function.comp, h0]
      simp

end Lim

end FurioLombardo.Discharge.R7.FinIdx
