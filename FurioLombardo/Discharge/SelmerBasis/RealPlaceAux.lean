import Mathlib

/-!
# Helper lemmas for the real places (lane selmer-basis, local side)

Polynomial and sign lemmas used by `imageIn_real` (RealPlace.lean).
The quotient `G` of `f` by its four real root factors is negative on `ℝ` (`rp_G_props`, `rp_quad_pos`),
which gives the sign of `f` (`rp_oval`) and of `f'` at the roots (`rp_deriv_signs`); `rp_sign_core`
turns the local facts `hU1`, `hU2` on a representative `p` of `μ(Q)` into the two sign conditions.
-/

open Polynomial

namespace FurioLombardo.Discharge.SelmerBasis.RealAux

theorem rp_lc_neg (c : ℝ) (h : ¬ IsSquare c) : c < 0 := by
  by_contra hc
  push Not at hc
  exact h ⟨Real.sqrt c, (Real.mul_self_sqrt hc).symm⟩

theorem rp_quad_pos (g : ℝ[X]) (hdeg : g.natDegree = 2) (hno : ∀ x : ℝ, g.eval x ≠ 0)
    (x : ℝ) : 0 < g.leadingCoeff * g.eval x := by
  set A := g.coeff 2 with hAdef
  set B := g.coeff 1 with hBdef
  set D := g.coeff 0 with hDdef
  have hg : g = C A * X ^ 2 + C B * X + C D := by
    conv_lhs => rw [as_sum_range_C_mul_X_pow g, hdeg]
    simp [Finset.sum_range_succ, hAdef, hBdef, hDdef]
    ring
  have hA : g.leadingCoeff = A := by rw [leadingCoeff, hdeg]
  have heval : ∀ y, g.eval y = A * y ^ 2 + B * y + D := by
    intro y
    conv_lhs => rw [hg]
    simp
  have hA0 : A ≠ 0 := by
    rw [← hA]
    exact leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (n := 0) (by omega))
  have hdisc : B ^ 2 - 4 * A * D < 0 := by
    by_contra h
    push Not at h
    obtain ⟨x0, hx0⟩ := exists_quadratic_eq_zero hA0
      ⟨Real.sqrt (discrim A B D), by rw [Real.mul_self_sqrt (by rw [discrim]; linarith)]⟩
    apply hno x0
    rw [heval]
    linear_combination hx0
  rw [hA, heval]
  nlinarith [sq_nonneg (2 * A * x + B)]

theorem rp_factor4 (f : ℝ[X]) (a b c d : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : f.eval a = 0) (hb : f.eval b = 0) (hc : f.eval c = 0) (hd : f.eval d = 0) :
    ∃ G : ℝ[X], f = G * ((X - C a) * (X - C b) * (X - C c) * (X - C d)) := by
  obtain ⟨f1, rfl⟩ : ∃ f1, f = (X - C a) * f1 := ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr ha).symm⟩
  have hb1 : f1.eval b = 0 := by
    rw [eval_mul, eval_sub, eval_X, eval_C] at hb
    exact (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr hab.ne')
  obtain ⟨f2, rfl⟩ : ∃ f2, f1 = (X - C b) * f2 := ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr hb1).symm⟩
  have hc2 : f2.eval c = 0 := by
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hc
    have h1 : c - a ≠ 0 := sub_ne_zero.mpr (hab.trans hbc).ne'
    have h2 : c - b ≠ 0 := sub_ne_zero.mpr hbc.ne'
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left h1)).resolve_left h2
  obtain ⟨f3, rfl⟩ : ∃ f3, f2 = (X - C c) * f3 := ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr hc2).symm⟩
  have hd3 : f3.eval d = 0 := by
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hd
    have h1 : d - a ≠ 0 := sub_ne_zero.mpr (hab.trans (hbc.trans hcd)).ne'
    have h2 : d - b ≠ 0 := sub_ne_zero.mpr (hbc.trans hcd).ne'
    have h3 : d - c ≠ 0 := sub_ne_zero.mpr hcd.ne'
    exact (mul_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left h1)).resolve_left
      h2)).resolve_left h3
  obtain ⟨f4, rfl⟩ : ∃ f4, f3 = (X - C d) * f4 := ⟨_, (mul_divByMonic_eq_iff_isRoot.mpr hd3).symm⟩
  exact ⟨f4, by ring⟩

theorem rp_G_props (f G : ℝ[X]) (a b c d : ℝ) (hf : Squarefree f) (hdeg : f.natDegree = 6)
    (hfac : f = G * ((X - C a) * (X - C b) * (X - C c) * (X - C d)))
    (hall : ∀ x : ℝ, f.eval x = 0 → x = a ∨ x = b ∨ x = c ∨ x = d) :
    G.natDegree = 2 ∧ G.leadingCoeff = f.leadingCoeff ∧ ∀ x : ℝ, G.eval x ≠ 0 := by
  set P := (X - C a) * (X - C b) * (X - C c) * (X - C d) with hPdef
  have hPm : P.Monic :=
    (((monic_X_sub_C a).mul (monic_X_sub_C b)).mul (monic_X_sub_C c)).mul (monic_X_sub_C d)
  have hPdeg : P.natDegree = 4 := by
    rw [hPdef, (((monic_X_sub_C a).mul (monic_X_sub_C b)).mul (monic_X_sub_C c)).natDegree_mul
      (monic_X_sub_C d), ((monic_X_sub_C a).mul (monic_X_sub_C b)).natDegree_mul (monic_X_sub_C c),
      (monic_X_sub_C a).natDegree_mul (monic_X_sub_C b)]
    simp
  have hf0 : f ≠ 0 := hf.ne_zero
  have hG0 : G ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hfac
    exact hf0 hfac
  refine ⟨?_, ?_, ?_⟩
  · have h := natDegree_mul hG0 hPm.ne_zero
    rw [← hfac, hdeg, hPdeg] at h
    omega
  · rw [hfac, leadingCoeff_mul, hPm.leadingCoeff, mul_one]
  · intro x hx
    have hfx : f.eval x = 0 := by rw [hfac, eval_mul, hx, zero_mul]
    have hPx : P.IsRoot x := by
      rcases hall x hfx with rfl | rfl | rfl | rfl <;> simp [hPdef]
    have h2 : (X - C x) * (X - C x) ∣ f := by
      rw [hfac]
      exact mul_dvd_mul (dvd_iff_isRoot.mpr hx) (dvd_iff_isRoot.mpr hPx)
    exact not_isUnit_X_sub_C x (hf _ h2)

theorem rp_oval (a b c d x : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h : (x - a) * (x - b) * (x - c) * (x - d) < 0) :
    (a - x) * (d - x) < 0 ∧ 0 < (b - x) * (c - x) := by
  have e1 : (a - x) * (d - x) = (x - a) * (x - d) := by ring
  have e2 : (b - x) * (c - x) = (x - b) * (x - c) := by ring
  have e3 : (x - a) * (x - b) * (x - c) * (x - d) = ((x - a) * (x - d)) * ((x - b) * (x - c)) := by
    ring
  rw [e1, e2]
  rw [e3] at h
  rcases lt_or_ge x b with hxb | hxb
  · have hq : 0 < (x - b) * (x - c) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hxb) (sub_neg.mpr (hxb.trans hbc))
    exact ⟨by nlinarith, hq⟩
  rcases lt_or_ge x c with hxc | hxc
  · exfalso
    have hq : (x - b) * (x - c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hp : (x - a) * (x - d) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    nlinarith
  · have hq0 : 0 ≤ (x - b) * (x - c) := mul_nonneg (by linarith) (by linarith)
    have hp : (x - a) * (x - d) < 0 := by
      by_contra hp
      push Not at hp
      nlinarith
    exact ⟨hp, by nlinarith⟩

theorem rp_deriv_signs (G : ℝ[X]) (a b c d : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hG : ∀ x : ℝ, G.eval x < 0) :
    0 < (G * ((X - C a) * (X - C b) * (X - C c) * (X - C d))).derivative.eval a ∧
    (G * ((X - C a) * (X - C b) * (X - C c) * (X - C d))).derivative.eval b < 0 ∧
    0 < (G * ((X - C a) * (X - C b) * (X - C c) * (X - C d))).derivative.eval c ∧
    (G * ((X - C a) * (X - C b) * (X - C c) * (X - C d))).derivative.eval d < 0 := by
  have hba := sub_pos.mpr hab
  have hcb := sub_pos.mpr hbc
  have hdc := sub_pos.mpr hcd
  have hca := sub_pos.mpr (hab.trans hbc)
  have hdb := sub_pos.mpr (hbc.trans hcd)
  have hda := sub_pos.mpr (hab.trans (hbc.trans hcd))
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, eval_add,
    eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, zero_mul, add_zero, zero_add,
    mul_one, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_pos (mul_pos (mul_pos (neg_pos.mpr (hG a)) hba) hca) hda]
  · nlinarith [mul_pos (mul_pos (mul_pos (neg_pos.mpr (hG b)) hba) hcb) hdb]
  · nlinarith [mul_pos (mul_pos (mul_pos (neg_pos.mpr (hG c)) hca) hcb) hdc]
  · nlinarith [mul_pos (mul_pos (mul_pos (neg_pos.mpr (hG d)) hda) hdb) hdc]

theorem rp_monic_quad (u : ℝ[X]) (hu : u.Monic) (hdeg : u.natDegree = 2) :
    (∀ x : ℝ, 0 < u.eval x) ∨ ∃ α β : ℝ, u = (X - C α) * (X - C β) := by
  by_cases h : ∃ α, u.IsRoot α
  · right
    obtain ⟨α, hα⟩ := h
    have h1 := mul_divByMonic_eq_iff_isRoot.mpr hα
    set q := u /ₘ (X - C α) with hqdef
    have hq : q.Monic := by
      have h2 := congrArg leadingCoeff h1
      rwa [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, hu.leadingCoeff] at h2
    have hqdeg : q.natDegree = 1 := by
      rw [hqdef, natDegree_divByMonic _ (monic_X_sub_C α), hdeg, natDegree_X_sub_C]
    refine ⟨α, -(q.coeff 0), ?_⟩
    calc u = (X - C α) * q := h1.symm
      _ = (X - C α) * (X + C (q.coeff 0)) := congrArg _ (hq.eq_X_add_C hqdeg)
      _ = _ := by rw [C_neg, sub_neg_eq_add]
  · left
    push Not at h
    intro x
    have := rp_quad_pos u hdeg (fun y hy => h y hy) x
    rwa [hu.leadingCoeff, one_mul] at this

theorem rp_isCoprime_w {K : Type*} [Field K] (f u v w : K[X]) (hf : Squarefree f)
    (hu : u.Monic) (hv : v.degree < 2) (hw : v ^ 2 - f = u * w) (hcop : ¬ IsCoprime u f)
    (hdvd : ¬ u ∣ f) : IsCoprime w f := by
  have hf0 : f ≠ 0 := hf.ne_zero
  have hu0 : u ≠ 0 := hu.ne_zero
  have hv2 : v ^ 2 = u * w + f := by linear_combination hw
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hdvd ⟨-w, by linear_combination -hw⟩
  have hvdeg : v.natDegree < 2 := (natDegree_lt_iff_degree_lt hv0).mpr hv
  obtain ⟨π', hπ'irr, hπ'u, hπ'f⟩ : ∃ π', Irreducible π' ∧ π' ∣ u ∧ π' ∣ f := by
    by_contra hcon
    push Not at hcon
    exact hcop (isCoprime_of_irreducible_dvd (fun h => hu0 h.1) hcon)
  have hassocv : ∀ π : K[X], Irreducible π → π ∣ v → Associated π v := by
    intro π hπ hπv
    obtain ⟨c, hc⟩ := hπv
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact hv0 hc
    have hπdeg : 0 < π.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hπ)
    have hcdeg : c.natDegree = 0 := by
      have h := natDegree_mul hπ.ne_zero hc0
      rw [← hc] at h
      omega
    have hcu : IsUnit c := by
      rw [isUnit_iff_degree_eq_zero, degree_eq_natDegree hc0, hcdeg]
      rfl
    exact ⟨hcu.unit, by rw [IsUnit.unit_spec, hc]⟩
  have hπ'v : π' ∣ v := hπ'irr.prime.dvd_of_dvd_pow (n := 2)
    (by rw [hv2]; exact dvd_add (dvd_mul_of_dvd_left hπ'u w) hπ'f)
  have hπ'assoc := hassocv π' hπ'irr hπ'v
  apply isCoprime_of_irreducible_dvd (fun h => hf0 h.2)
  intro π hπ hπw hπf
  have hπv : π ∣ v := hπ.prime.dvd_of_dvd_pow (n := 2)
    (by rw [hv2]; exact dvd_add (dvd_mul_of_dvd_right hπw u) hπf)
  have hπu : π ∣ u := ((hassocv π hπ hπv).trans hπ'assoc.symm).dvd.trans hπ'u
  have h2 : π * π ∣ f := by
    have e : f = v ^ 2 - u * w := by linear_combination -hw
    rw [e, sq]
    exact dvd_sub (mul_dvd_mul hπv hπv) (mul_dvd_mul hπu hπw)
  exact hπ.not_isUnit (hf π h2)

theorem rp_v_eq_zero {K : Type*} [Field K] (f u v w : K[X]) (hf : Squarefree f)
    (hu : u.Monic) (hdeg : u.natDegree = 2) (hv : v.degree < 2) (hw : v ^ 2 - f = u * w)
    (hdvd : u ∣ f) : v = 0 := by
  have huv : u ∣ v ^ 2 := by
    have e : v ^ 2 = u * w + f := by linear_combination hw
    rw [e]
    exact dvd_add (dvd_mul_right _ _) hdvd
  have huv' : u ∣ v :=
    ((hf.squarefree_of_dvd hdvd).dvd_pow_iff_dvd
      two_ne_zero).mp huv
  exact eq_zero_of_dvd_of_degree_lt huv' (by rw [degree_eq_natDegree hu.ne_zero, hdeg]; exact hv)

theorem rp_not_double {K : Type*} [Field K] (f u v w : K[X]) (hf : Squarefree f)
    (hw : v ^ 2 - f = u * w) (α : K) (hu : u = (X - C α) ^ 2) (hfa : f.eval α = 0) : False := by
  have hv : v.eval α = 0 := by
    have h := congrArg (eval α) hw
    simp only [eval_sub, eval_pow, eval_mul, hu, eval_X, eval_C, sub_self, hfa] at h
    simpa using h
  have h1 : (X - C α) ∣ v := dvd_iff_isRoot.mpr hv
  have h2 : (X - C α) * (X - C α) ∣ f := by
    have e : f = v ^ 2 - u * w := by linear_combination -hw
    rw [e, hu, sq, sq, mul_assoc]
    exact dvd_sub (mul_dvd_mul h1 h1) (mul_dvd_mul_left _ (dvd_mul_of_dvd_left dvd_rfl w))
  exact not_isUnit_X_sub_C α (hf _ h2)

theorem rp_U2_tpt {K : Type*} [Field K] (f u q : K[X]) (s : K) (hfuq : f = u * q)
    (hus : u.eval s = 0) :
    u.derivative.eval s * (u - q).eval s = -(f.derivative.eval s) := by
  rw [hfuq, derivative_mul, eval_add, eval_mul, eval_mul, eval_sub, hus]
  ring

theorem rp_U2_w {K : Type*} [Field K] (f u v w : K[X]) (s : K) (hw : v ^ 2 - f = u * w)
    (hus : u.eval s = 0) (hfs : f.eval s = 0) :
    u.derivative.eval s * w.eval s = -(f.derivative.eval s) := by
  have hv : v.eval s = 0 := by
    have h := congrArg (eval s) hw
    simp only [eval_sub, eval_pow, eval_mul, hus, hfs, zero_mul, sub_zero] at h
    exact pow_eq_zero_iff two_ne_zero |>.mp h
  have h := congrArg (fun p => p.derivative.eval s) hw
  simp only [derivative_sub, derivative_sq, derivative_mul, eval_sub, eval_add, eval_mul, hv,
    hus, mul_zero, zero_mul, add_zero, zero_sub] at h
  linear_combination -h

theorem rp_natDegree_w {K : Type*} [Field K] (f u v w : K[X]) (hf : f.natDegree = 6)
    (hu : u.Monic) (hdeg : u.natDegree = 2) (hv : v.degree < 2) (hw : v ^ 2 - f = u * w) :
    w.natDegree = 4 := by
  have hv1 : v.natDegree < 2 := by
    by_cases hv0 : v = 0
    · rw [hv0, natDegree_zero]; norm_num
    · exact (natDegree_lt_iff_degree_lt hv0).mpr hv
  have hv2 : (v ^ 2).natDegree < f.natDegree := by
    rw [natDegree_pow, hf]
    omega
  have h6 : (v ^ 2 - f).natDegree = 6 := by rw [natDegree_sub_eq_right_of_natDegree_lt hv2, hf]
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hw
    rw [hw, natDegree_zero] at h6
    norm_num at h6
  rw [hw, natDegree_mul hu.ne_zero hw0, hdeg] at h6
  omega

theorem rp_sign_core (f u p : ℝ[X]) (r0 r1 r2 r3 : ℝ) (h01 : r0 < r1) (h12 : r1 < r2)
    (h23 : r2 < r3)
    (hroots : f.eval r0 = 0 ∧ f.eval r1 = 0 ∧ f.eval r2 = 0 ∧ f.eval r3 = 0)
    (hall : ∀ x : ℝ, f.eval x = 0 → x = r0 ∨ x = r1 ∨ x = r2 ∨ x = r3)
    (hoval : ∀ x : ℝ, 0 < f.eval x → (r0 - x) * (r3 - x) < 0 ∧ 0 < (r1 - x) * (r2 - x))
    (hd0 : 0 < f.derivative.eval r0) (hd1 : f.derivative.eval r1 < 0)
    (hd2 : 0 < f.derivative.eval r2) (hd3 : f.derivative.eval r3 < 0)
    (hu : u.Monic) (hdeg : u.natDegree = 2)
    (hnn : ∀ x : ℝ, u.eval x = 0 → 0 ≤ f.eval x)
    (hnd : ∀ x : ℝ, f.eval x = 0 → u ≠ (X - C x) ^ 2)
    (hU1 : ∀ s : ℝ, (s = r0 ∨ s = r1 ∨ s = r2 ∨ s = r3) → u.eval s ≠ 0 → 0 < u.eval s * p.eval s)
    (hU2 : ∀ s : ℝ, (s = r0 ∨ s = r1 ∨ s = r2 ∨ s = r3) → u.eval s = 0 →
      u.derivative.eval s * p.eval s = -(f.derivative.eval s)) :
    0 < p.eval r0 * p.eval r3 ∧ 0 < p.eval r1 * p.eval r2 := by
  have n01 : r0 ≠ r1 := h01.ne
  have n12 : r1 ≠ r2 := h12.ne
  have n23 : r2 ≠ r3 := h23.ne
  have n02 : r0 ≠ r2 := (h01.trans h12).ne
  have n13 : r1 ≠ r3 := (h12.trans h23).ne
  have n03 : r0 ≠ r3 := (h01.trans (h12.trans h23)).ne
  have hne : ∀ s, (s = r0 ∨ s = r1 ∨ s = r2 ∨ s = r3) → f.derivative.eval s ≠ 0 := by
    rintro s (rfl | rfl | rfl | rfl)
    exacts [hd0.ne', hd1.ne, hd2.ne', hd3.ne]
  have hrs : ∀ s, (s = r0 ∨ s = r1 ∨ s = r2 ∨ s = r3) → f.eval s = 0 := by
    rintro s (rfl | rfl | rfl | rfl)
    exacts [hroots.1, hroots.2.1, hroots.2.2.1, hroots.2.2.2]
  let o : ℝ → ℝ → ℝ := fun x s => if x = s then -(f.derivative.eval s) else s - x
  have hovec : ∀ x, 0 ≤ f.eval x → o x r0 * o x r3 < 0 ∧ 0 < o x r1 * o x r2 := by
    intro x hx
    rcases hx.lt_or_eq with hpos | hzero
    · have hx : ∀ s, (s = r0 ∨ s = r1 ∨ s = r2 ∨ s = r3) → x ≠ s := by
        intro s hs h
        rw [h, hrs s hs] at hpos
        exact lt_irrefl _ hpos
      simp only [o, ite_eq_right (hx r0 (by simp)), ite_eq_right (hx r1 (by simp)), ite_eq_right (hx r2 (by simp)),
        ite_eq_right (hx r3 (by simp))]
      exact hoval x hpos
    · rcases hall x hzero.symm with rfl | rfl | rfl | rfl
      · simp only [o, ite_eq_left rfl, ite_eq_right n01, ite_eq_right n02, ite_eq_right n03]
        constructor <;> nlinarith
      · simp only [o, ite_eq_left rfl, ite_eq_right n01.symm, ite_eq_right n12, ite_eq_right n13]
        constructor <;> nlinarith
      · simp only [o, ite_eq_left rfl, ite_eq_right n02.symm, ite_eq_right n12.symm, ite_eq_right n23]
        constructor <;> nlinarith
      · simp only [o, ite_eq_left rfl, ite_eq_right n03.symm, ite_eq_right n13.symm, ite_eq_right n23.symm]
        constructor <;> nlinarith
  have hstep : ∀ α β, u = (X - C α) * (X - C β) → ∀ s, (s = r0 ∨ s = r1 ∨ s = r2 ∨ s = r3) →
      0 < p.eval s * (o α s * o β s) := by
    intro α β hαβ s hs
    have hsq : 0 < (f.derivative.eval s) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (hne s hs)).symm
    by_cases ha : α = s <;> by_cases hb : β = s
    · exfalso
      apply hnd s (hrs s hs)
      rw [hαβ, ha, hb, sq]
    · have hus : u.eval s = 0 := by rw [hαβ, ha]; simp
      have hder : u.derivative.eval s = s - β := by
        rw [hαβ, ha]; simp [derivative_mul]
      have h2 := hU2 s hs hus
      rw [hder] at h2
      simp only [o, ite_eq_left ha, ite_eq_right hb]
      have e : p.eval s * (-(f.derivative.eval s) * (s - β)) =
          -(f.derivative.eval s) * ((s - β) * p.eval s) := by ring
      rw [e, h2]
      nlinarith
    · have hus : u.eval s = 0 := by rw [hαβ, hb]; simp
      have hder : u.derivative.eval s = s - α := by
        rw [hαβ, hb]; simp [derivative_mul]
      have h2 := hU2 s hs hus
      rw [hder] at h2
      simp only [o, ite_eq_left hb, ite_eq_right ha]
      have e : p.eval s * ((s - α) * -(f.derivative.eval s)) =
          -(f.derivative.eval s) * ((s - α) * p.eval s) := by ring
      rw [e, h2]
      nlinarith
    · have hus : u.eval s = (s - α) * (s - β) := by rw [hαβ]; simp
      have hus0 : u.eval s ≠ 0 := by
        rw [hus]
        exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm ha)) (sub_ne_zero.mpr (Ne.symm hb))
      have h1 := hU1 s hs hus0
      simp only [o, ite_eq_right ha, ite_eq_right hb]
      rw [hus] at h1
      linarith
  rcases rp_monic_quad u hu hdeg with hpos | ⟨α, β, hαβ⟩
  · have hp : ∀ s, (s = r0 ∨ s = r1 ∨ s = r2 ∨ s = r3) → 0 < p.eval s := fun s hs =>
      pos_of_mul_pos_right (hU1 s hs (hpos s).ne') (hpos s).le
    exact ⟨mul_pos (hp _ (by simp)) (hp _ (by simp)), mul_pos (hp _ (by simp)) (hp _ (by simp))⟩
  · obtain ⟨a03, a12⟩ := hovec α (hnn α (by rw [hαβ]; simp))
    obtain ⟨b03, b12⟩ := hovec β (hnn β (by rw [hαβ]; simp))
    have s0 := hstep α β hαβ r0 (by simp)
    have s1 := hstep α β hαβ r1 (by simp)
    have s2 := hstep α β hαβ r2 (by simp)
    have s3 := hstep α β hαβ r3 (by simp)
    constructor
    · have he : 0 < (o α r0 * o β r0) * (o α r3 * o β r3) := by
        nlinarith [mul_pos_of_neg_of_neg a03 b03]
      have h' : 0 < (p.eval r0 * p.eval r3) * ((o α r0 * o β r0) * (o α r3 * o β r3)) := by
        nlinarith [mul_pos s0 s3]
      exact pos_of_mul_pos_left h' he.le
    · have he : 0 < (o α r1 * o β r1) * (o α r2 * o β r2) := by
        nlinarith [mul_pos a12 b12]
      have h' : 0 < (p.eval r1 * p.eval r2) * ((o α r1 * o β r1) * (o α r2 * o β r2)) := by
        nlinarith [mul_pos s1 s2]
      exact pos_of_mul_pos_left h' he.le

end FurioLombardo.Discharge.SelmerBasis.RealAux
