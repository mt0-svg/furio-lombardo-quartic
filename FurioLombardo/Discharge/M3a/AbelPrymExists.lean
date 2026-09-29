import FurioLombardo.Discharge.M3a.AbelPrymRuling

/-!
# A certificate exists at every point (WP4 of the M3a discharge, the degenerate locus)

`AbelPrym.bruinPhi` takes the value `1` at a point of `D_δ` with no certificate. Over any field
with `2 ≠ 0`, `cert_exists` shows that no such point exists as soon as

* `f = -δ det(M1 + 2t M2 + t² M3)` has no root in the field,
* `-δ det M3` (the leading coefficient of `f`) is not a square, and
* the point has `(r, s) ≠ (0, 0)` (for `D_δ` this says that `p` is not a common zero of the three
  conics).

The proof follows the definition of a certificate: the rank condition (`rank_of`) from
`(s² M1 - 2rs M2 + r² M3) p ≠ 0`, which holds because `f` has no root
(`N_ne_zero_of_noRoot`); a tangent vector `T` independent of `P` from the dimension count
(`exists_indep_in_ker`); a nonzero minor of `(p, T_p)` (`exists_minor_ne`); `a₃ ≠ 0`
(`a3_ne_of`); `V` (`exists_V`); and `Cert.ofEntry`.
-/

open Polynomial Matrix
open FurioLombardo.M3a FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.M3a.AbelPrym

variable {L : Type*} [Field L]

/-! ## Linear algebra -/

theorem det_zero_of_kernel (A : Matrix (Fin 3) (Fin 3) L) (p : Fin 3 → L) (hp : p ≠ 0)
    (h : A *ᵥ p = 0) : A.det = 0 :=
  (Matrix.exists_mulVec_eq_zero_iff (M := A)).mp ⟨p, hp, h⟩

/-- If the three minors of `(p, q)` vanish and `p ≠ 0`, then `q` is a multiple of `p`. -/
theorem minors_zero_parallel (p q : Fin 3 → L) (hp : p ≠ 0)
    (h1 : p 1 * q 2 - p 2 * q 1 = 0) (h2 : p 2 * q 0 - p 0 * q 2 = 0)
    (h3 : p 0 * q 1 - p 1 * q 0 = 0) : ∃ c : L, q = c • p := by
  have key : ∀ j : Fin 3, p j ≠ 0 → ∃ c : L, q = c • p := by
    intro j hj
    refine ⟨q j / p j, funext fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hj]
    fin_cases j <;> fin_cases i <;> simp <;>
      first
      | linear_combination h1 | linear_combination -h1
      | linear_combination h2 | linear_combination -h2
      | linear_combination h3 | linear_combination -h3
  by_contra h
  apply hp
  funext j
  by_contra hj
  exact h (key j hj)

/-- A surjective `Φ : L⁵ → L³` has a kernel vector independent of a given nonzero one. -/
theorem exists_indep_in_ker (Φ : V5 L →ₗ[L] (Fin 3 → L)) (hs : Function.Surjective Φ)
    {P : V5 L} (hP : Φ P = 0) (hP0 : P ≠ 0) :
    ∃ T : V5 L, Φ T = 0 ∧ LinearIndependent L ![T, P] := by
  have hrange : Module.finrank L (LinearMap.range Φ) = 3 := by
    rw [LinearMap.range_eq_top.mpr hs, finrank_top]; simp
  have hker : Module.finrank L (LinearMap.ker Φ) = 2 := by
    have := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hrange, finrank_V5] at this; omega
  have hle : L ∙ P ≤ LinearMap.ker Φ := (Submodule.span_singleton_le_iff_mem _ _).mpr hP
  have hne : L ∙ P ≠ LinearMap.ker Φ := by
    intro h
    have := finrank_span_singleton (K := L) hP0
    rw [h, hker] at this; omega
  obtain ⟨T, hT, hTn⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  refine ⟨T, hT, ?_⟩
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_cases ha : a = 0
  · subst ha
    simp only [zero_smul, zero_add] at hab
    exact ⟨rfl, (smul_eq_zero.mp hab).resolve_right hP0⟩
  · exfalso
    apply hTn
    have : T = (-(b / a)) • P := by
      have h' : a • T = -(b • P) := eq_neg_of_add_eq_zero_left hab
      calc T = a⁻¹ • (a • T) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        _ = (-(b / a)) • P := by rw [h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self P)

/-! ## The tangent line -/

variable (M : Fin 3 → Matrix (Fin 3) (Fin 3) L) (δ : L)

theorem polarD_sub_smul (i : Fin 3) (P T : V5 L) (c : L) :
    polarD M δ i P (T - c • P) = polarD M δ i P T - c * polarD M δ i P P := by
  rw [sub_eq_add_neg, ← neg_smul, polarD_add, polarD_smul]; ring

/-- A tangent vector `(0, u, v)` at a point with `(r, s) ≠ 0` is zero. -/
theorem tangent_rs_zero (hδ : δ ≠ 0) (h2 : (2 : L) ≠ 0) (P : V5 L)
    (hrs : P.2.1 ≠ 0 ∨ P.2.2 ≠ 0) (u v : L) (h : ∀ i, polarD M δ i P (0, u, v) = 0) :
    u = 0 ∧ v = 0 := by
  have e0 := h 0
  have e1 := h 1
  have e2 := h 2
  simp only [polarD, dotProduct_zero, mulVec_zero, zero_dotProduct, add_zero, zero_sub,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at e0 e1 e2
  have hδ2 : δ * 2 ≠ 0 := mul_ne_zero hδ h2
  have c0 : P.2.1 * u = 0 := by
    have : δ * 2 * (P.2.1 * u) = 0 := by linear_combination -e0
    exact (mul_eq_zero.mp this).resolve_left hδ2
  have c1 : P.2.1 * v + P.2.2 * u = 0 := by
    have : δ * (P.2.1 * v + P.2.2 * u) = 0 := by linear_combination -e1
    exact (mul_eq_zero.mp this).resolve_left hδ
  have c2 : P.2.2 * v = 0 := by
    have : δ * 2 * (P.2.2 * v) = 0 := by linear_combination -e2
    exact (mul_eq_zero.mp this).resolve_left hδ2
  rcases hrs with hr | hs
  · have hu : u = 0 := (mul_eq_zero.mp c0).resolve_left hr
    subst hu
    refine ⟨rfl, ?_⟩
    have : P.2.1 * v = 0 := by linear_combination c1
    exact (mul_eq_zero.mp this).resolve_left hr
  · have hv : v = 0 := (mul_eq_zero.mp c2).resolve_left hs
    subst hv
    refine ⟨?_, rfl⟩
    have : P.2.2 * u = 0 := by linear_combination c1
    exact (mul_eq_zero.mp this).resolve_left hs

/-- At a point with `(r, s) ≠ 0`, a tangent vector independent of `P` has a nonzero minor. -/
theorem exists_minor_ne (hδ : δ ≠ 0) (h2 : (2 : L) ≠ 0) (P T : V5 L) (hp : P.1 ≠ 0)
    (hrs : P.2.1 ≠ 0 ∨ P.2.2 ≠ 0) (hT : ∀ i, polarD M δ i P T = 0)
    (hP : ∀ i, polarD M δ i P P = 0) (hind : LinearIndependent L ![T, P]) :
    P.1 1 * T.1 2 - P.1 2 * T.1 1 ≠ 0 ∨ P.1 2 * T.1 0 - P.1 0 * T.1 2 ≠ 0 ∨
      P.1 0 * T.1 1 - P.1 1 * T.1 0 ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2', h3⟩ := hc
  obtain ⟨c, hcT⟩ := minors_zero_parallel P.1 T.1 hp h1 h2' h3
  have hW : T - c • P = (0, T.2.1 - c * P.2.1, T.2.2 - c * P.2.2) := by
    ext i
    · simp [hcT]
    · simp
    · simp
  have hWt : ∀ i, polarD M δ i P (0, T.2.1 - c * P.2.1, T.2.2 - c * P.2.2) = 0 := fun i => by
    rw [← hW, polarD_sub_smul, hT i, hP i]; ring
  obtain ⟨hu, hv⟩ := tangent_rs_zero M δ hδ h2 P hrs _ _ hWt
  have hTP : T = c • P := by
    have : T - c • P = 0 := by rw [hW, hu, hv]; rfl
    exact sub_eq_zero.mp this
  have := LinearIndependent.pair_iff.mp hind 1 (-c) (by rw [hTP]; simp)
  exact one_ne_zero this.1

/-- The entries `(l, 3)`, `l < 3`, of `⋆A` are the constant minors of `(p, T_p)`. -/
theorem hodge_entry_of_minor (P T : V5 L)
    (h : P.1 1 * T.1 2 - P.1 2 * T.1 1 ≠ 0 ∨ P.1 2 * T.1 0 - P.1 0 * T.1 2 ≠ 0 ∨
      P.1 0 * T.1 1 - P.1 1 * T.1 0 ≠ 0) :
    ∃ l : Fin 4, l ≠ 3 ∧ ∃ c : L, c ≠ 0 ∧ hodge (plucker (plk P) (plk T)) l 3 = C c := by
  rcases h with h0 | h1 | h2
  · exact ⟨0, by decide, _, h0, hodge_plk_03 P T⟩
  · exact ⟨1, by decide, _, h1, hodge_plk_13 P T⟩
  · exact ⟨2, by decide, _, h2, hodge_plk_23 P T⟩

/-! ## The rank condition from the absence of roots -/

omit [Field L] in
theorem eval_det_pencil {L : Type*} [Field L] (M1 M2 M3 : Matrix (Fin 3) (Fin 3) L) (u : L) :
    (pencil M1 M2 M3).det.eval u = (M1 + (2 * u) • M2 + u ^ 2 • M3).det := by
  calc
    (pencil M1 M2 M3).det.eval u = (Polynomial.evalRingHom u) ((pencil M1 M2 M3).det) := rfl
    _ = ((Polynomial.evalRingHom u).mapMatrix (pencil M1 M2 M3)).det := by
      rw [RingHom.map_det]
    _ = (M1 + (2 * u) • M2 + u ^ 2 • M3).det := by
      congr
      ext a b
      simp [pencil]
      ring

/-- If `f = -δ det(M1 + 2t M2 + t² M3)` has no root and `-δ det M3 ≠ 0`, then
`(s² M1 - 2rs M2 + r² M3) p ≠ 0` for `p ≠ 0` and `(r, s) ≠ 0`: otherwise `p` spans the kernel of
the pencil at `t = -r/s` (or of `M3` when `s = 0`). -/
theorem N_ne_zero_of_noRoot (M1 M2 M3 : Matrix (Fin 3) (Fin 3) L) (δ : L) (f : L[X])
    (hf : f = -C δ * (pencil M1 M2 M3).det) (hroot : ∀ u : L, f.eval u ≠ 0)
    (hlc : -δ * M3.det ≠ 0) (p : Fin 3 → L) (hp : p ≠ 0) (r s : L) (hrs : r ≠ 0 ∨ s ≠ 0) :
    (s ^ 2 • M1 - (2 * r * s) • M2 + r ^ 2 • M3) *ᵥ p ≠ 0 := by
  intro hN
  by_cases hs : s = 0
  · subst hs
    have hr : r ≠ 0 := hrs.resolve_right (fun h => h rfl)
    have h3 : M3 *ᵥ p = 0 := by
      have : (r ^ 2) • (M3 *ᵥ p) = 0 := by
        rw [← smul_mulVec]; simpa using hN
      exact (smul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hr)
    exact hlc (by rw [det_zero_of_kernel M3 p hp h3, mul_zero])
  · set t := -r / s
    have hMt : s ^ 2 • (M1 + (2 * t) • M2 + t ^ 2 • M3) = s ^ 2 • M1 - (2 * r * s) • M2 + r ^ 2 • M3 := by
      ext a b
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, t]
      field_simp
      ring
    have hk : (M1 + (2 * t) • M2 + t ^ 2 • M3) *ᵥ p = 0 := by
      have : s ^ 2 • ((M1 + (2 * t) • M2 + t ^ 2 • M3) *ᵥ p) = 0 := by
        rw [← smul_mulVec, hMt]; exact hN
      exact (smul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hs)
    apply hroot t
    rw [hf, eval_mul, eval_neg, eval_C, eval_det_pencil, det_zero_of_kernel _ p hp hk, mul_zero]

/-! ## Existence of a certificate -/

variable {M1 M2 M3 : Matrix (Fin 3) (Fin 3) L} {δ : L}

theorem swapPt_r (x : DPoint L M1 M2 M3 δ) : (swapPt x).r = x.s := rfl

theorem swapPt_s (x : DPoint L M1 M2 M3 δ) : (swapPt x).s = x.r := rfl

theorem polarD_pt_pt (x : DPoint L M1 M2 M3 δ) (i : Fin 3) :
    polarD ![M1, M2, M3] δ i (pt x) (pt x) = 0 := by
  rw [polarD_self, quadD_pt, mul_zero]

/-- **A certificate at every point.** Over a field with `2 ≠ 0`, if
`f = -δ det(M1 + 2t M2 + t² M3)` has no root and `-δ det M3` is not a square, every point of
`D_δ` with `(r, s) ≠ 0` has a certificate, so `bruinPhi` there is the class of Bruin's divisor and
never the fallback value `1`. -/
theorem cert_exists (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (h2ne : (2 : L) ≠ 0)
    (hδ : δ ≠ 0) {f : L[X]} (hf : f = -C δ * (pencil M1 M2 M3).det)
    (hlc : ¬ IsSquare (-δ * M3.det)) (hroot : ∀ u : L, f.eval u ≠ 0)
    (x : DPoint L M1 M2 M3 δ) (hrs : x.r ≠ 0 ∨ x.s ≠ 0) : Nonempty (Cert M1 M2 M3 δ f x) := by
  have hlc0 : -δ * M3.det ≠ 0 := fun h => hlc ⟨0, by rw [h]; ring⟩
  have hN := N_ne_zero_of_noRoot M1 M2 M3 δ f hf hroot hlc0 x.p x.ne_zero x.r x.s hrs
  have hN' : ((pt x).2.2 ^ 2 • ![M1, M2, M3] 0 - (2 * (pt x).2.1 * (pt x).2.2) • ![M1, M2, M3] 1 +
      (pt x).2.1 ^ 2 • ![M1, M2, M3] 2) *ᵥ (pt x).1 ≠ 0 := hN
  have hrank := rank_of (symm_fun h1 h2 h3) hδ h2ne (pt x) hrs hN'
  have hPP : ∀ i, polarD ![M1, M2, M3] δ i (pt x) (pt x) = 0 := polarD_pt_pt x
  obtain ⟨T, hT, hind⟩ := exists_indep_in_ker _ hrank (P := pt x) (funext hPP)
    (fun h => x.ne_zero (congrArg Prod.fst h))
  have hT' : ∀ i, polarD ![M1, M2, M3] δ i (pt x) T = 0 := fun i => congrFun hT i
  have hmin := exists_minor_ne ![M1, M2, M3] δ hδ h2ne (pt x) T x.ne_zero hrs hT' hPP hind
  have ha3 := a3_ne_of h1 h2 h3 h2ne hlc x hT' hmin
  obtain ⟨l, hl3, c, hc, hl⟩ := hodge_entry_of_minor (pt x) T hmin
  obtain ⟨V, hV, hent⟩ := exists_V h1 h2 h3 h2ne hf x hT' ha3 l hl3 hc hl
  exact ⟨Cert.ofEntry h1 h2 h3 h2ne hf x T hT' hrank hind ha3 l hl3 hc hl V hV hent⟩

/-- Under the hypotheses of `cert_exists`, `bruinPhi` is the class of a certificate. -/
theorem bruinPhi_eq_cls_of (h1 : M1ᵀ = M1) (h2 : M2ᵀ = M2) (h3 : M3ᵀ = M3) (h2ne : (2 : L) ≠ 0)
    (hδ : δ ≠ 0) {f : L[X]} [GoodSextic f] (hf : f = -C δ * (pencil M1 M2 M3).det)
    (hlc : ¬ IsSquare (-δ * M3.det)) (hroot : ∀ u : L, f.eval u ≠ 0)
    (x : DPoint L M1 M2 M3 δ) (hrs : x.r ≠ 0 ∨ x.s ≠ 0) :
    ∃ c : Cert M1 M2 M3 δ f x, bruinPhi M1 M2 M3 δ f x = c.cls := by
  obtain ⟨c⟩ := cert_exists h1 h2 h3 h2ne hδ hf hlc hroot x hrs
  exact ⟨c, bruinPhi_eq_of_cert c⟩

end FurioLombardo.Discharge.M3a.AbelPrym
