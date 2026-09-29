import Mathlib
import FurioLombardo.Discharge.R7.FinIdx.ZSet

/-!
# The composition of two pairs (R7)

For pairs `D = (t, v)`, `D' = (t', v')` with nonzero resultant `res2 t t'` of `uT t, uT t'`:
the CRT cubic `crtV D D'` (`≡ v mod uT t`, `≡ v' mod uT t'`), the quotient
`compQ f D D' = (f - V²) /ₘ (uT t · uT t')`, its monic normalization `compW`, and the reduced pair
`comp f D D' = (compW, (-V) %ₘ compW)`. It lies in `Z` (`InZ.comp`), represents the sum of the
classes (`cls_comp`), and is continuous where the resultant is nonzero (`DTendsto.comp`).
-/

open Polynomial Filter Topology
open FurioLombardo.M3a FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M3a
open FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.PolyLim

namespace FurioLombardo.Discharge.R7.FinIdx

variable {L : Type*} [Field L]

/-- The resultant of the monic quadratics `uT t` and `uT t'`. -/
noncomputable def res2 (t t' : Fin 2 → L) : L := resQ t' (uT t - uT t')

/-- The difference of two monic quadratics. -/
theorem uT_sub_uT (t t' : Fin 2 → L) :
    uT t - uT t' = C (t 0 - t' 0) * X + C (t 1 - t' 1) := by
  simp only [uT, map_sub]; ring

/-- The resultant as a polynomial in the coefficients. -/
theorem res2_eq (t t' : Fin 2 → L) :
    res2 t t' = (t 1 - t' 1) ^ 2 - t' 0 * (t 1 - t' 1) * (t 0 - t' 0) +
      t' 1 * (t 0 - t' 0) ^ 2 := by
  rw [res2, resQ, uT_sub_uT]
  simp only [coeff_add, coeff_C_mul, coeff_X_zero, coeff_X_one, coeff_C_zero, coeff_C_succ]
  ring

theorem res2_comm (t t' : Fin 2 → L) : res2 t t' = res2 t' t := by
  rw [res2_eq, res2_eq]; ring

theorem res2_eq_eval_mul (t : Fin 2 → L) (s1 s2 : L) :
    res2 t ![-(s1 + s2), s1 * s2] = (uT t).eval s1 * (uT t).eval s2 := by
  rw [res2_eq]
  simp only [uT, eval_add, eval_mul, eval_pow, eval_X, eval_C, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

theorem isCoprime_of_res2_ne {t t' : Fin 2 → L} (h : res2 t t' ≠ 0) :
    IsCoprime (uT t) (uT t') := by
  have hd : (uT t - uT t').degree < 2 := by
    rw [uT_sub_uT]; exact degree_linear_lt_two _ _
  have hc := isCoprime_uT t' hd h
  have : IsCoprime (uT t') (uT t) := by
    have := hc.add_mul_left_right 1
    simpa using this
  exact this.symm

/-- A vanishing resultant gives equal quadratics or a common root. -/
theorem res2_eq_zero {t t' : Fin 2 → L} (h : res2 t t' = 0) :
    t = t' ∨ ∃ β : L, (uT t).eval β = 0 ∧ (uT t').eval β = 0 := by
  rw [res2_eq] at h
  by_cases h1 : t 0 - t' 0 = 0
  · left
    rw [h1] at h
    have h0 : t 1 - t' 1 = 0 := by
      have : (t 1 - t' 1) ^ 2 = 0 := by linear_combination h
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    funext i
    fin_cases i
    · exact sub_eq_zero.mp h1
    · exact sub_eq_zero.mp h0
  · right
    refine ⟨-(t 1 - t' 1) / (t 0 - t' 0), ?_, ?_⟩
    · simp only [uT, eval_add, eval_mul, eval_pow, eval_X, eval_C]
      field_simp
      linear_combination h
    · simp only [uT, eval_add, eval_mul, eval_pow, eval_X, eval_C]
      field_simp
      linear_combination h

/-- The adjugate of `uT t - uT t'` modulo `uT t'`. -/
noncomputable def adjD (t t' : Fin 2 → L) : L[X] :=
  -C (t 0 - t' 0) * X + C ((t 1 - t' 1) - (t 0 - t' 0) * t' 0)

theorem mul_adjD (t t' : Fin 2 → L) :
    (uT t - uT t') * adjD t t' = C (res2 t t') - C ((t 0 - t' 0) ^ 2) * uT t' := by
  rw [uT_sub_uT, adjD, res2_eq, uT]
  simp only [map_sub, map_mul, map_pow, map_add]
  ring

/-- The CRT cubic of two pairs. -/
noncomputable def crtV (D D' : MPair L) : L[X] :=
  D.v + uT D.t * (C (res2 D.t D'.t)⁻¹ * (((D'.v - D.v) * adjD D.t D'.t) %ₘ uT D'.t))

theorem natDegree_crtV {D D' : MPair L} (hv : D.v.degree < 2) : (crtV D D').natDegree ≤ 3 := by
  have h1 := natDegree_le_one_of_degree_lt_two hv
  have hm : (((D'.v - D.v) * adjD D.t D'.t) %ₘ uT D'.t).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt ((D'.v - D.v) * adjD D.t D'.t) (uT_monic D'.t)
      (by intro h; have := congrArg natDegree h; rw [uT_natDegree] at this; simp at this)
    rw [uT_natDegree] at this; omega
  refine (natDegree_add_le _ _).trans (max_le (by omega) ?_)
  refine natDegree_mul_le.trans ?_
  rw [uT_natDegree]
  have := (natDegree_C_mul_le (res2 D.t D'.t)⁻¹ (((D'.v - D.v) * adjD D.t D'.t) %ₘ uT D'.t))
  omega

theorem dvd_crtV_sub (D D' : MPair L) : uT D.t ∣ crtV D D' - D.v :=
  ⟨_, by rw [crtV, add_sub_cancel_left]⟩

theorem dvd_crtV_sub' {D D' : MPair L} (h : res2 D.t D'.t ≠ 0) : uT D'.t ∣ crtV D D' - D'.v := by
  set R := res2 D.t D'.t
  set P := (D'.v - D.v) * adjD D.t D'.t
  set d1 := D.t 0 - D'.t 0
  have hm := modByMonic_add_div P (uT D'.t)
  have hadj := mul_adjD D.t D'.t
  have hR : C R⁻¹ * C R = 1 := by rw [← C_mul, inv_mul_cancel₀ h, C_1]
  refine ⟨C R⁻¹ * (P %ₘ uT D'.t) - C R⁻¹ * (D'.v - D.v) * C (d1 ^ 2) -
    C R⁻¹ * (uT D.t - uT D'.t) * (P /ₘ uT D'.t), ?_⟩
  rw [crtV]
  linear_combination (C R⁻¹ * (uT D.t - uT D'.t)) * hm + (C R⁻¹ * (D'.v - D.v)) * hadj +
    (D'.v - D.v) * hR

theorem dvd_f_sub_crtV_sq {f : L[X]} {D D' : MPair L} (hD : InZ f D) (hD' : InZ f D')
    (h : res2 D.t D'.t ≠ 0) : uT D.t * uT D'.t ∣ f - crtV D D' ^ 2 := by
  have key : ∀ (u v : L[X]), u ∣ f - v ^ 2 → u ∣ crtV D D' - v → u ∣ f - crtV D D' ^ 2 := by
    intro u v h1 h2
    have e : f - crtV D D' ^ 2 = (f - v ^ 2) - (crtV D D' - v) * (crtV D D' + v) := by ring
    rw [e]; exact dvd_sub h1 (dvd_mul_of_dvd_left h2 _)
  exact (isCoprime_of_res2_ne h).mul_dvd (key _ _ hD.2 (dvd_crtV_sub D D'))
    (key _ _ hD'.2 (dvd_crtV_sub' h))

/-- The quotient `(f - V²) /ₘ (uT t · uT t')`. -/
noncomputable def compQ (f : L[X]) (D D' : MPair L) : L[X] :=
  (f - crtV D D' ^ 2) /ₘ (uT D.t * uT D'.t)

/-- Its monic normalization. -/
noncomputable def compW (f : L[X]) (D D' : MPair L) : L[X] :=
  C ((compQ f D D').coeff 2)⁻¹ * compQ f D D'

/-- **The composition of two pairs.** -/
noncomputable def comp (f : L[X]) (D D' : MPair L) : MPair L :=
  ⟨![(compW f D D').coeff 1, (compW f D D').coeff 0], (-crtV D D') %ₘ compW f D D'⟩

variable {f : L[X]} [GoodSextic f]

theorem uT_mul_monic (t t' : Fin 2 → L) : (uT t * uT t').Monic := (uT_monic t).mul (uT_monic t')

theorem uT_mul_natDegree (t t' : Fin 2 → L) : (uT t * uT t').natDegree = 4 := by
  rw [natDegree_mul (uT_monic t).ne_zero (uT_monic t').ne_zero, uT_natDegree, uT_natDegree]

set_option linter.unusedSectionVars false in
theorem f_sub_crtV_sq {D D' : MPair L} (hD : InZ f D) (hD' : InZ f D') (h : res2 D.t D'.t ≠ 0) :
    f - crtV D D' ^ 2 = uT D.t * uT D'.t * compQ f D D' := by
  have h0 := (modByMonic_eq_zero_iff_dvd (uT_mul_monic D.t D'.t)).mpr (dvd_f_sub_crtV_sq hD hD' h)
  have := modByMonic_add_div (f - crtV D D' ^ 2) (uT D.t * uT D'.t)
  rw [h0, zero_add] at this
  exact this.symm

theorem natDegree_f_sub_crtV_sq {D D' : MPair L} (hv : D.v.degree < 2) :
    (f - crtV D D' ^ 2).natDegree ≤ 6 := by
  have h3 := natDegree_crtV (D' := D') hv
  refine (natDegree_sub_le _ _).trans (max_le (GoodSextic.natDegree_eq (f := f)).le ?_)
  exact natDegree_pow_le.trans (by omega)

set_option linter.unusedVariables false in
theorem natDegree_compQ {D D' : MPair L} (hD : InZ f D) (hD' : InZ f D')
    (h : res2 D.t D'.t ≠ 0) : (compQ f D D').natDegree ≤ 2 := by
  rw [compQ, natDegree_divByMonic _ (uT_mul_monic D.t D'.t), uT_mul_natDegree]
  have := natDegree_f_sub_crtV_sq (f := f) (D' := D') hD.1
  omega

theorem compQ_coeff_two_ne {D D' : MPair L} (hD : InZ f D) (hD' : InZ f D')
    (h : res2 D.t D'.t ≠ 0) : (compQ f D D').coeff 2 ≠ 0 := by
  have e := congrArg (fun p => p.coeff 6) (f_sub_crtV_sq hD hD' h)
  rw [show (6 : ℕ) = 4 + 2 from rfl, coeff_mul_add_eq_of_natDegree_le
    (uT_mul_natDegree D.t D'.t).le (natDegree_compQ hD hD' h)] at e
  have h4 : (uT D.t * uT D'.t).coeff 4 = 1 := by
    have := (uT_mul_monic D.t D'.t).coeff_natDegree
    rwa [uT_mul_natDegree] at this
  rw [h4, one_mul, coeff_sub, sq, show (4 + 2 : ℕ) = 3 + 3 from rfl,
    coeff_mul_add_eq_of_natDegree_le (natDegree_crtV hD.1) (natDegree_crtV hD.1)] at e
  rw [← e]
  intro h0
  have hl : f.coeff 6 = f.leadingCoeff := by
    rw [leadingCoeff, GoodSextic.natDegree_eq (f := f)]
  apply GoodSextic.not_isSquare_leadingCoeff (f := f)
  refine ⟨(crtV D D').coeff 3, ?_⟩
  rw [← hl]
  linear_combination h0

theorem compW_monic {D D' : MPair L} (hD : InZ f D) (hD' : InZ f D') (h : res2 D.t D'.t ≠ 0) :
    (compW f D D').Monic ∧ (compW f D D').natDegree = 2 := by
  have hq := compQ_coeff_two_ne hD hD' h
  have hd2 : (compQ f D D').natDegree = 2 :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_compQ hD hD' h) hq
  have hd : (compW f D D').natDegree = 2 := by
    rw [compW, natDegree_C_mul (inv_ne_zero hq), hd2]
  refine ⟨?_, hd⟩
  rw [Monic, leadingCoeff, hd, compW, coeff_C_mul, inv_mul_cancel₀ hq]

theorem uT_comp {D D' : MPair L} (hD : InZ f D) (hD' : InZ f D') (h : res2 D.t D'.t ≠ 0) :
    uT (comp f D D').t = compW f D D' :=
  (eq_uT_of_monic (compW_monic hD hD' h).1 (compW_monic hD hD' h).2).symm

/-- `compQ = Q₂ · compW`. -/
theorem compQ_eq {D D' : MPair L} (hD : InZ f D) (hD' : InZ f D') (h : res2 D.t D'.t ≠ 0) :
    compQ f D D' = C ((compQ f D D').coeff 2) * compW f D D' := by
  rw [compW, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (compQ_coeff_two_ne hD hD' h), C_1, one_mul]

/-- `f - V² = Q₂ · u u' w`. -/
theorem f_sub_crtV_sq' {D D' : MPair L} (hD : InZ f D) (hD' : InZ f D')
    (h : res2 D.t D'.t ≠ 0) :
    f - crtV D D' ^ 2 = C ((compQ f D D').coeff 2) * (uT D.t * uT D'.t * compW f D D') := by
  rw [f_sub_crtV_sq hD hD' h]
  nth_rewrite 1 [compQ_eq hD hD' h]
  ring

theorem InZ.comp {D D' : MPair L} (hD : InZ f D) (hD' : InZ f D') (h : res2 D.t D'.t ≠ 0) :
    InZ f (comp f D D') := by
  obtain ⟨hm, hd⟩ := compW_monic hD hD' h
  refine ⟨?_, ?_⟩
  · change ((-crtV D D') %ₘ compW f D D').degree < 2
    have := degree_modByMonic_lt (-crtV D D') hm
    rwa [degree_eq_natDegree hm.ne_zero, hd] at this
  · rw [uT_comp hD hD' h]
    change compW f D D' ∣ f - ((-crtV D D') %ₘ compW f D D') ^ 2
    have h1 := modByMonic_add_div (-crtV D D') (compW f D D')
    set r := (-crtV D D') %ₘ compW f D D'
    have e : f - r ^ 2 = (f - crtV D D' ^ 2) -
        (crtV D D' - r) * (compW f D D' * (-crtV D D' /ₘ compW f D D')) := by
      linear_combination (crtV D D' - r) * h1
    rw [e, f_sub_crtV_sq' hD hD' h]
    exact dvd_sub (dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
      (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)

/-- **The class of the composition is the product of the classes.** -/
theorem cls_comp {F : L[X]} [GoodSextic F] {a : L} (hf : f.comp (X - C a) = F) {D D' : MPair L}
    (hD : InZ f D) (hD' : InZ f D') (h : res2 D.t D'.t ≠ 0) :
    cls F a (comp f D D') = cls F a D * cls F a D' := by
  set T := compRingHom (X - C a)
  have hT : ∀ p : L[X], T p = p.comp (X - C a) := fun p => coe_compRingHom_apply _ _
  set V := crtV D D'
  set w := compW f D D'
  set r := (-V) %ₘ w
  set q := (compQ f D D').coeff 2
  have hq : q ≠ 0 := compQ_coeff_two_ne hD hD' h
  have hu : (uT D.t).comp (X - C a) ≠ 0 := (monic_uT_comp a D.t).ne_zero
  have hu' : (uT D'.t).comp (X - C a) ≠ 0 := (monic_uT_comp a D'.t).ne_zero
  have hwm : w.Monic := (compW_monic hD hD' h).1
  have hwd : w.natDegree = 2 := (compW_monic hD hD' h).2
  have hw : w.comp (X - C a) ≠ 0 :=
    (hwm.comp (monic_X_sub_C a) (by rw [natDegree_X_sub_C]; exact one_ne_zero)).ne_zero
  have hdv : ∀ {p g : L[X]}, p ∣ g → p.comp (X - C a) ∣ g.comp (X - C a) := fun {p g} hpg => by
    have := map_dvd T hpg
    rwa [hT, hT] at this
  have e1 : ClassGroup.mk0 (mumford0 F hu (V.comp (X - C a))) =
      ClassGroup.mk0 (mumford0 F hu (D.v.comp (X - C a))) :=
    mk0_mumford_congr F hu (by rw [← sub_comp]; exact hdv (dvd_crtV_sub D D'))
  have e2 : ClassGroup.mk0 (mumford0 F hu' (V.comp (X - C a))) =
      ClassGroup.mk0 (mumford0 F hu' (D'.v.comp (X - C a))) :=
    mk0_mumford_congr F hu' (by rw [← sub_comp]; exact hdv (dvd_crtV_sub' h))
  have hV : (V.comp (X - C a)) ^ 2 - F =
      C (-q) * ((uT D.t).comp (X - C a) * (uT D'.t).comp (X - C a) * w.comp (X - C a)) := by
    have := congrArg (fun p => p.comp (X - C a)) (f_sub_crtV_sq' hD hD' h)
    simp only [sub_comp, pow_comp, mul_comp, C_comp, hf] at this
    rw [C_neg]
    linear_combination -this
  have e3 := mk0_mumford_mul F hu hu' (V := V.comp (X - C a)) (r := C (-q) * w.comp (X - C a))
    (by rw [hV]; ring)
  have e4 := mk0_mumford_eq_of_sq_sub F (neg_ne_zero.mpr hq) (mul_ne_zero hu hu') hw hV
  have e5 : ClassGroup.mk0 (mumford0 F hw (-V.comp (X - C a))) =
      ClassGroup.mk0 (mumford0 F hw (r.comp (X - C a))) := by
    refine mk0_mumford_congr F hw ?_
    have h1 := modByMonic_add_div (-V) w
    rw [← neg_comp, ← sub_comp]
    exact hdv ⟨-V /ₘ w, by linear_combination -h1⟩
  have e0 : ClassGroup.mk0 (mumford0 F (monic_uT_comp a (comp f D D').t).ne_zero
      (r.comp (X - C a))) = ClassGroup.mk0 (mumford0 F hw (r.comp (X - C a))) :=
    mk0_mumford0_eq_of_eq _ _ (by rw [uT_comp hD hD' h]) _
  change ClassGroup.mk0 (mumford0 F (monic_uT_comp a (comp f D D').t).ne_zero
      (r.comp (X - C a))) = ClassGroup.mk0 (mumford0 F hu (D.v.comp (X - C a))) *
      ClassGroup.mk0 (mumford0 F hu' (D'.v.comp (X - C a)))
  rw [e0, ← e5, ← e4, ← e3, e1, e2]

section Lim

variable {K : Type*} [NormedField K] {ι : Type*} {l : Filter ι} {g : K[X]} [GoodSextic g]

theorem tendsto_res2 {t t' : ι → Fin 2 → K} {t0 t0' : Fin 2 → K} (h : Tendsto t l (𝓝 t0))
    (h' : Tendsto t' l (𝓝 t0')) : Tendsto (fun n => res2 (t n) (t' n)) l (𝓝 (res2 t0 t0')) := by
  have h0 := tendsto_pi_nhds.mp h 0
  have h1 := tendsto_pi_nhds.mp h 1
  have h0' := tendsto_pi_nhds.mp h' 0
  have h1' := tendsto_pi_nhds.mp h' 1
  simp only [res2_eq]
  exact (((h1.sub h1').pow 2).sub ((h0'.mul (h1.sub h1')).mul (h0.sub h0'))).add
    (h1'.mul ((h0.sub h0').pow 2))

theorem ptendsto_adjD {t t' : ι → Fin 2 → K} {t0 t0' : Fin 2 → K} (h : Tendsto t l (𝓝 t0))
    (h' : Tendsto t' l (𝓝 t0')) :
    PTendsto l (fun n => adjD (t n) (t' n)) (adjD t0 t0') := by
  have h0 := tendsto_pi_nhds.mp h 0
  have h1 := tendsto_pi_nhds.mp h 1
  have h0' := tendsto_pi_nhds.mp h' 0
  have h1' := tendsto_pi_nhds.mp h' 1
  exact ((ptendsto_C (h0.sub h0')).neg.mul (ptendsto_const X)).add
    (ptendsto_C ((h1.sub h1').sub ((h0.sub h0').mul h0')))

theorem natDegree_adjD (t t' : Fin 2 → K) : (adjD t t').natDegree ≤ 1 := by
  rw [adjD, ← C_neg]
  exact natDegree_linear_le

/-- **Continuity of the composition** where the resultant is nonzero. -/
theorem DTendsto.comp {D D' : ι → MPair K} {D0 D0' : MPair K} (h : DTendsto l D D0)
    (h' : DTendsto l D' D0') (hZ : ∀ᶠ n in l, InZ g (D n) ∧ InZ g (D' n)) (hZ0 : InZ g D0)
    (hZ0' : InZ g D0') (hr : res2 D0.t D0'.t ≠ 0) :
    DTendsto l (fun n => comp g (D n) (D' n)) (comp g D0 D0') := by
  have hR := tendsto_res2 h.1 h'.1
  have hRev : ∀ᶠ n in l, res2 (D n).t (D' n).t ≠ 0 := hR.eventually_ne hr
  have hRi := hR.inv₀ hr
  have hP := (h'.2.sub h.2).mul (ptendsto_adjD h.1 h'.1)
  have hPd : ∀ᶠ n in l, (((D' n).v - (D n).v) * adjD (D n).t (D' n).t).natDegree ≤ 2 := by
    refine hZ.mono fun n hn => natDegree_mul_le.trans ?_
    have h1 := natDegree_le_one_of_degree_lt_two hn.1.1
    have h2 := natDegree_le_one_of_degree_lt_two hn.2.1
    have h3 := natDegree_adjD (D n).t (D' n).t
    have h4 := natDegree_sub_le (D' n).v (D n).v
    omega
  have hm := hP.modByMonic (N := 2) (d := 2) hPd (ptendsto_uT h'.1)
    (Eventually.of_forall fun n => ⟨uT_monic _, uT_natDegree _⟩) (uT_monic _) (uT_natDegree _)
  have hV : PTendsto l (fun n => crtV (D n) (D' n)) (crtV D0 D0') :=
    h.2.add ((ptendsto_uT h.1).mul (hm.C_mul hRi))
  have hg := (ptendsto_const g).sub (hV.pow 2)
  have hQ : PTendsto l (fun n => compQ g (D n) (D' n)) (compQ g D0 D0') :=
    hg.divByMonic (N := 6) (d := 4) (hZ.mono fun n hn => natDegree_f_sub_crtV_sq hn.1.1)
      ((ptendsto_uT h.1).mul (ptendsto_uT h'.1))
      (Eventually.of_forall fun n => ⟨uT_mul_monic _ _, uT_mul_natDegree _ _⟩)
      (uT_mul_monic _ _) (uT_mul_natDegree _ _)
  have hQ2i := (hQ 2).inv₀ (compQ_coeff_two_ne hZ0 hZ0' hr)
  have hW : PTendsto l (fun n => compW g (D n) (D' n)) (compW g D0 D0') := hQ.C_mul hQ2i
  refine ⟨tendsto_pi_nhds.mpr fun i => ?_, ?_⟩
  · fin_cases i
    · exact hW 1
    · exact hW 0
  · exact hV.neg.modByMonic (N := 3) (d := 2)
      (hZ.mono fun n hn => by rw [natDegree_neg]; exact natDegree_crtV hn.1.1) hW
      ((hZ.and hRev).mono fun n hn => compW_monic hn.1.1 hn.1.2 hn.2)
      (compW_monic hZ0 hZ0' hr).1 (compW_monic hZ0 hZ0' hr).2

end Lim

end FurioLombardo.Discharge.R7.FinIdx
