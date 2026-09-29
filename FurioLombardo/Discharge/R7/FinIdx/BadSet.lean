import Mathlib
import FurioLombardo.Discharge.R7.FinIdx.Comp

/-!
# Good translation targets (R7, algebraic part)

For `D* ∈ Z` and `s1` with `u*(s1) ≠ 0`, the set of `s2` for which some pair `T` over
`(X - s1)(X - s2)` makes `res2 u* (comp T (-D*))` vanish is finite (`finite_bad`): such a
composition cubic `V` lies in a finite set `𝒲` of cubics (determined by a monic divisor `p` of
`u*` and the value `V(s1)`), and `s2` is a root of the nonzero polynomial `f - V²`.
-/

open Polynomial Filter Topology
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3a
open FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.PolyLim

namespace FurioLombardo.Discharge.R7.FinIdx

section Alg

variable {K : Type*} [Field K]

/-- A divisor `p` of `u` with `p u ∣ f - W²` is coprime to `W` when `f` is squarefree. -/
theorem isCoprime_of_squarefree_dvd {f p u W : K[X]} (hf : Squarefree f)
    (hpu : p ∣ u) (hp0 : p ≠ 0) (hdvd : p * u ∣ f - W ^ 2) : IsCoprime p W := by
  refine isCoprime_of_irreducible_dvd (fun h => hp0 h.1) ?_
  intro q hq hqp hqW
  have h1 : q * q ∣ p * u := mul_dvd_mul hqp (dvd_trans hqp hpu)
  have h2 : q * q ∣ W ^ 2 := by rw [sq]; exact mul_dvd_mul hqW hqW
  have h3 : q * q ∣ f := by
    have e : f = (f - W ^ 2) + W ^ 2 := by ring
    rw [e]; exact dvd_add (dvd_trans h1 hdvd) h2
  exact hq.not_isUnit (hf q h3)

/-- **Uniqueness of the lift**: two cubics with the same residue modulo `u`, the same
value at `s1` and `p u ∣ f - W²` for a common nonconstant divisor `p` of `u` coincide. -/
theorem eq_of_lift (h2 : (2 : K) ≠ 0) {f p u W W' : K[X]} {s1 : K}
    (hu0 : u ≠ 0) (hud : u.natDegree = 2) (hpu : p ∣ u) (hpd : 1 ≤ p.natDegree)
    (hs1 : u.eval s1 ≠ 0) (hW : W.natDegree ≤ 3) (hW' : W'.natDegree ≤ 3)
    (hWW : u ∣ W - W') (hd : p * u ∣ f - W ^ 2) (hd' : p * u ∣ f - W' ^ 2)
    (hcop : IsCoprime p W) (heval : W.eval s1 = W'.eval s1) : W = W' := by
  obtain ⟨m, hm⟩ := hWW
  have hmd : m.natDegree ≤ 1 := by
    by_cases hm0 : m = 0
    · simp [hm0]
    · have h3 : (W - W').natDegree ≤ 3 := (natDegree_sub_le _ _).trans (max_le hW hW')
      rw [hm, natDegree_mul hu0 hm0, hud] at h3
      omega
  have hpm1 : p ∣ m * (W + W') := by
    have h1 : p * u ∣ u * (m * (W + W')) := by
      have e : u * (m * (W + W')) = (f - W' ^ 2) - (f - W ^ 2) := by
        linear_combination (W + W') * hm.symm
      rw [e]; exact dvd_sub hd' hd
    rw [mul_comm p u] at h1
    exact (mul_dvd_mul_iff_left hu0).mp h1
  obtain ⟨k, hk⟩ := dvd_trans hpu (dvd_mul_right u m)
  have hcop2 : IsCoprime p (W + W') := by
    have hc2 : IsCoprime p (C 2 * W) :=
      IsCoprime.mul_right ⟨0, C 2⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ h2, C_1]⟩
        hcop
    have e : W + W' = C 2 * W + p * (-k) := by
      rw [show (C 2 : K[X]) = 2 from map_ofNat C 2]
      linear_combination -hm - hk
    rw [e]
    exact hc2.add_mul_left_right _
  have hpm : p ∣ m := hcop2.dvd_of_dvd_mul_right hpm1
  have hms : m.IsRoot s1 := by
    have e := congrArg (eval s1) hm
    simp only [eval_sub, eval_mul, heval, sub_self] at e
    exact (mul_eq_zero.mp e.symm).resolve_left hs1
  have hXm : X - C s1 ∣ m := dvd_iff_isRoot.mpr hms
  have hcopX : IsCoprime p (X - C s1) := by
    refine ((irreducible_X_sub_C s1).coprime_iff_not_dvd.mpr ?_).symm
    intro hX
    exact hs1 (dvd_iff_isRoot.mp (dvd_trans hX hpu))
  have hpX : p * (X - C s1) ∣ m := hcopX.mul_dvd hpm hXm
  have hm0 : m = 0 := by
    by_contra hm0
    have := natDegree_le_of_dvd hpX hm0
    have hp0 : p ≠ 0 := by rintro rfl; simp at hpd
    rw [natDegree_mul hp0 (X_sub_C_ne_zero s1), natDegree_X_sub_C] at this
    omega
  rw [hm0, mul_zero, sub_eq_zero] at hm
  exact hm

theorem finite_eval_eq_sq {f W : K[X]} (hf : ¬ IsSquare f) :
    Set.Finite {s : K | f.eval s = (W.eval s) ^ 2} := by
  have h0 : f - W ^ 2 ≠ 0 := by
    intro h
    exact hf ⟨W, by rw [sub_eq_zero.mp h, sq]⟩
  refine (Polynomial.finite_setOfPred_isRoot h0).subset fun s hs => ?_
  simp only [Set.mem_ofPred_eq] at hs ⊢
  simp [IsRoot, hs]

theorem finite_sq_eq (c : K) : Set.Finite {y : K | y ^ 2 = c} := by
  have h0 : (X ^ 2 - C c : K[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) c
  refine (Polynomial.finite_setOfPred_isRoot h0).subset fun y hy => ?_
  simp only [Set.mem_ofPred_eq] at hy ⊢
  simp [IsRoot, hy]

theorem uT_pair (s1 s2 : K) : uT ![-(s1 + s2), s1 * s2] = (X - C s1) * (X - C s2) := by
  simp only [uT, Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_add, map_mul]
  ring

end Alg

variable {L : Type*} [Field L] {f : L[X]} [GoodSextic f]

/-- **The bad set is finite.** -/
theorem finite_bad {Ds : MPair L} (hDs : InZ f Ds) {s1 : L} (hs1 : (uT Ds.t).eval s1 ≠ 0) :
    Set.Finite {s2 : L | ∃ vT : L[X], InZ f ⟨![-(s1 + s2), s1 * s2], vT⟩ ∧ s2 ≠ s1 ∧
      (uT Ds.t).eval s2 ≠ 0 ∧
      res2 Ds.t (comp f ⟨![-(s1 + s2), s1 * s2], vT⟩ Ds.neg).t = 0} := by
  classical
  set u := uT Ds.t with hu_def
  have hu0 : u ≠ 0 := (uT_monic Ds.t).ne_zero
  set P : Set L[X] := insert u ((fun β => X - C β) '' {β | u.IsRoot β}) with hP_def
  have hPfin : P.Finite :=
    ((Polynomial.finite_setOfPred_isRoot hu0).image _).insert u
  have hPdiv : ∀ p ∈ P, p ∣ u ∧ 1 ≤ p.natDegree := by
    intro p hp
    rcases hp with rfl | ⟨β, hβ, rfl⟩
    · exact ⟨dvd_rfl, by rw [hu_def, uT_natDegree]; omega⟩
    · exact ⟨dvd_iff_isRoot.mpr hβ, by rw [natDegree_X_sub_C]⟩
  set 𝒲 : Set L[X] := {W | W.natDegree ≤ 3 ∧ u ∣ W + Ds.v ∧ (W.eval s1) ^ 2 = f.eval s1 ∧
    ∃ p ∈ P, p * u ∣ f - W ^ 2} with h𝒲_def
  set pW : L[X] → L[X] := fun W => if h : ∃ p ∈ P, p * u ∣ f - W ^ 2 then h.choose else 0
  have hpW : ∀ W ∈ 𝒲, pW W ∈ P ∧ pW W * u ∣ f - W ^ 2 := by
    intro W hW
    have h := hW.2.2.2
    simp only [pW, h, ↓reduceDIte]
    exact h.choose_spec
  have h𝒲fin : 𝒲.Finite := by
    refine Set.Finite.of_finite_image (f := fun W => (pW W, W.eval s1)) ?_ ?_
    · refine (hPfin.prod (finite_sq_eq (f.eval s1))).subset ?_
      rintro _ ⟨W, hW, rfl⟩
      exact ⟨(hpW W hW).1, hW.2.2.1⟩
    · intro W hW W' hW' hWW'
      simp only [Prod.mk.injEq] at hWW'
      obtain ⟨hp, hs⟩ := hWW'
      obtain ⟨hpP, hpd⟩ := hpW W hW
      obtain ⟨-, hpd'⟩ := hpW W' hW'
      rw [← hp] at hpd'
      obtain ⟨hpu, hp1⟩ := hPdiv _ hpP
      have hp0 : pW W ≠ 0 := by intro h0; rw [h0] at hp1; simp at hp1
      refine eq_of_lift (GoodSextic.two_ne_zero (f := f)) hu0 (uT_natDegree _) hpu hp1 hs1
        hW.1 hW'.1 ?_ hpd hpd' (isCoprime_of_squarefree_dvd GoodSextic.squarefree hpu hp0 hpd) hs
      have e : W - W' = (W + Ds.v) - (W' + Ds.v) := by ring
      rw [e]; exact dvd_sub hW.2.1 hW'.2.1
  refine (h𝒲fin.biUnion fun W _ =>
    finite_eval_eq_sq (W := W) (GoodSextic.not_isSquare (f := f))).subset ?_
  rintro s2 ⟨vT, hT, -, hs2, hres⟩
  set T : MPair L := ⟨![-(s1 + s2), s1 * s2], vT⟩
  have hDn := hDs.neg
  have hr : res2 T.t Ds.neg.t ≠ 0 := by
    change res2 T.t Ds.t ≠ 0
    rw [res2_comm, res2_eq_eval_mul]
    exact mul_ne_zero hs1 hs2
  set V := crtV T Ds.neg
  have huT : uT T.t = (X - C s1) * (X - C s2) := uT_pair s1 s2
  have hval : ∀ s, (X - C s) ∣ uT T.t → V.eval s = vT.eval s ∧ f.eval s = (vT.eval s) ^ 2 := by
    intro s hs
    have h1 := dvd_iff_isRoot.mp (dvd_trans hs (dvd_crtV_sub T Ds.neg))
    have h2 := dvd_iff_isRoot.mp (dvd_trans hs hT.2)
    simp only [IsRoot, eval_sub, eval_pow, sub_eq_zero] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨hV1, hf1⟩ := hval s1 (by rw [huT]; exact dvd_mul_right _ _)
  obtain ⟨hV2, hf2⟩ := hval s2 (by rw [huT]; exact dvd_mul_left _ _)
  have hfV := f_sub_crtV_sq' hT hDn hr
  have hwc := uT_comp hT hDn hr
  refine Set.mem_biUnion (x := V) ⟨natDegree_crtV hT.1, ?_, by rw [hV1, hf1], ?_⟩ ?_
  · have := dvd_crtV_sub' hr
    change u ∣ V - -Ds.v at this
    rwa [sub_neg_eq_add] at this
  · rcases res2_eq_zero hres with ht | ⟨β, hβ1, hβ2⟩
    · refine ⟨u, Set.mem_insert _ _, ?_⟩
      have hw : compW f T Ds.neg = u := by rw [← hwc, ← ht]
      rw [hfV, hw]
      have e : uT T.t * uT Ds.neg.t * u = u * u * uT T.t := by change uT T.t * u * u = _; ring
      rw [e]
      exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    · refine ⟨X - C β, Set.mem_insert_of_mem _ ⟨β, hβ1, rfl⟩, ?_⟩
      rw [hwc] at hβ2
      obtain ⟨c, hc⟩ := dvd_iff_isRoot.mpr hβ2
      rw [hfV, hc]
      have e : uT T.t * uT Ds.neg.t * ((X - C β) * c) = (X - C β) * u * (uT T.t * c) := by
        change uT T.t * u * ((X - C β) * c) = _; ring
      rw [e]
      exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  · change f.eval s2 = (V.eval s2) ^ 2
    rw [hV2, hf2]

end FurioLombardo.Discharge.R7.FinIdx
