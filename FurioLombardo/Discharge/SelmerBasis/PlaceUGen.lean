import FurioLombardo.Discharge.SelmerBasis.PlaceWRows

/-!
# Unramified quadratic components: square certificates and the standard basis

At a place with residue field `𝔽₂` (`hres`), an unramified quadratic component is `F = QF K A B` with
`‖A + 1‖ < 1` and `‖B - 1‖ < 1` (residue field `𝔽₄`, `Y = QF.mk 0 1` a unit with
`Y² + Y + 1 ≡ 0`). This is the shape of the three components at w2 and of the quartic component over
the Eisenstein component at v.

* `isSquare_of_unram_cert`: the square certificate `x = (π^mh (u0 + s1 Y))² + π^n0 r0 + π^n1 r1 Y + t`
  with a unit `u0 + s1 Y` and `n0, n1 > 2 mh + 2e`;
* `bU π e i`: the standard basis of `Fˣ / Fˣ²`: `π`, the units `1 + π^(2j+1) w_l` (`j < e`,
  `w = ![1, Y]`) and `1 + 4 Y`, with its unit data (`dfact_bU`), echelon (`echelonOK_stdU`) and
  independence (`bU_indep`).
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis

/-! ## The echelon of the standard basis (shape `⟨e, 2, 2, 0⟩`) -/

/-- The depth index of `bU i`, `1 ≤ i ≤ 2e`. -/
def jU (i : ℕ) : ℕ := (i - 1) / 2

/-- The digit of `bU i`, `1 ≤ i ≤ 2e`. -/
def lU (i : ℕ) : ℕ := (i - 1) % 2

/-- The unit datum of `bU i`. -/
def uStdU (e i : ℕ) : UDatum :=
  if i = 0 then .none else if i = 2 * e + 1 then .four 2 else .odd (2 * jU i + 1) (2 ^ lU i)

/-- The pivot of `bU i`. -/
def pivStdU (e i : ℕ) : CPos :=
  if i = 0 then .val else if i = 2 * e + 1 then .four else .odd (2 * jU i + 1) (lU i)

theorem echelonOK_stdU (e : ℕ) (he : 0 < e) :
    echelonOK (fun i p => admB ⟨e, 2, 2, 0⟩ (uStdU e i) p)
      (fun i p => digB ⟨e, 2, 2, 0⟩ (kStd i) (uStdU e i) p) (pivStdU e) (2 * e + 2) = true := by
  have h_dotB : dotB 2 2 2 = true := by
    decide
  unfold echelonOK
  rw [allLt_iff]
  intro i hi
  by_cases hi0 : i = 0
  · subst hi0
    have h_adm : admB ⟨e, 2, 2, 0⟩ (uStdU e 0) (pivStdU e 0) = true := by
      simp [admB, pivStdU]
    have h_dig : digB ⟨e, 2, 2, 0⟩ (kStd 0) (uStdU e 0) (pivStdU e 0) = true := by
      simp [digB, kStd, pivStdU]
    simp
    rw [h_adm, h_dig]
    simp
    rw [allLt_iff]
    intro i' hi'
    by_cases hi'0 : i' = 0
    · subst hi'0; simp
    · have h_not_le : ¬ i' ≤ 0 := by omega
      simp [kStd, hi'0, admB, digB, pivStdU]
  · have hi_pos : 1 ≤ i := by omega
    by_cases hi_last : i = 2 * e + 1
    · subst hi_last
      have h_adm : admB ⟨e, 2, 2, 0⟩ (uStdU e (2*e+1)) (pivStdU e (2*e+1)) = true := by
        simp [admB, uStdU, pivStdU, he]
      have h_dig : digB ⟨e, 2, 2, 0⟩ (kStd (2*e+1)) (uStdU e (2*e+1)) (pivStdU e (2*e+1)) = true := by
        simp [digB, uStdU, pivStdU, h_dotB]
      simp
      rw [h_adm, h_dig]
      simp
      rw [allLt_iff]
      intro i' hi'
      have hi'_le : i' ≤ 2*e+1 := by omega
      simp [hi'_le]
    · have hi_le : i ≤ 2 * e := by omega
      have h_adm : admB ⟨e, 2, 2, 0⟩ (uStdU e i) (pivStdU e i) = true := by
        dsimp [admB, uStdU, pivStdU]
        simp [hi0, hi_last]
        have h_mod : (2 * jU i + 1) % 2 = 1 := by omega
        have h_lt : 2 * jU i + 1 < 2 * e := by
          have hj : jU i < e := by
            rw [jU]
            have : i - 1 < 2 * e := by omega
            omega
          omega
        have h_l_lt_2 : lU i < 2 := by
          rw [lU]
          exact Nat.mod_lt (i - 1) (by norm_num : 0 < 2)
        exact And.intro h_lt (by omega)
      have h_dig : digB ⟨e, 2, 2, 0⟩ (kStd i) (uStdU e i) (pivStdU e i) = true := by
        dsimp [digB, kStd, uStdU, pivStdU]
        simp [hi0, hi_last, Nat.testBit_two_pow_self]
      simp
      rw [h_adm, h_dig]
      simp
      rw [allLt_iff]
      intro i' hi'
      by_cases hi'0 : i' = 0
      · subst hi'0
        simp [admB, pivStdU]
      · by_cases hi'last : i' = 2 * e + 1
        · subst hi'last
          have h_adm' : admB ⟨e, 2, 2, 0⟩ (uStdU e (2*e+1)) (pivStdU e i) = true := by
            dsimp [admB, uStdU, pivStdU]
            simp [hi0, hi_last]
            have h_lt : 2 * jU i + 1 < 2 * e := by
              have hj : jU i < e := by
                rw [jU]
                have : i - 1 < 2 * e := by omega
                omega
              omega
            have h_l_lt_2 : lU i < 2 := by
              rw [lU]
              exact Nat.mod_lt (i - 1) (by norm_num : 0 < 2)
            have h_l_le_1 : lU i ≤ 1 := by omega
            exact And.intro h_lt h_l_le_1
          have h_dig' : digB ⟨e, 2, 2, 0⟩ (kStd (2*e+1)) (uStdU e (2*e+1)) (pivStdU e i) = false := by
            dsimp [digB, kStd, uStdU, pivStdU]
            simp [hi0, hi_last]
          have h_not_le : ¬ 2*e+1 ≤ i := by omega
          simp [h_adm', h_dig', h_not_le]
        · have hi'_le : i' ≤ 2 * e := by omega
          by_cases hi'_le_i : i' ≤ i
          · simp [hi'_le_i]
          · have hi_lt_i' : i < i' := by omega
            have h_adm' : admB ⟨e, 2, 2, 0⟩ (uStdU e i') (pivStdU e i) = true := by
              dsimp [admB, uStdU, pivStdU]
              have h_mod : (2 * jU i + 1) % 2 = 1 := by omega
              have h_lt : 2 * jU i + 1 < 2 * e := by
                have hj : jU i < e := by
                  rw [jU]
                  have : i - 1 < 2 * e := by omega
                  omega
                omega
              have h_l_lt_2 : lU i < 2 := by
                rw [lU]
                exact Nat.mod_lt (i - 1) (by norm_num : 0 < 2)
              have hj_le : jU i ≤ jU i' := by
                rw [jU, jU]
                exact Nat.div_le_div_right (by omega)
              simp [hi'0, hi'last, hi0, hi_last, h_mod, h_lt, h_l_lt_2, hj_le]
            have h_dig' : digB ⟨e, 2, 2, 0⟩ (kStd i') (uStdU e i') (pivStdU e i) = false := by
              dsimp [digB, kStd, uStdU, pivStdU]
              simp [hi'0, hi'last, hi0, hi_last]
              rw [Nat.testBit_two_pow]
              by_cases hj_eq : jU i = jU i'
              · have hl_ne : lU i ≠ lU i' := by
                  intro h_eq
                  have h_eq_i : i = i' := by
                    have hi_eq : i = 2 * jU i + lU i + 1 := by
                      rw [jU, lU]; omega
                    have hi'_eq : i' = 2 * jU i' + lU i' + 1 := by
                      rw [jU, lU]; omega
                    omega
                  exact hi_lt_i'.ne h_eq_i
                simp [hj_eq, hl_ne.symm]
              · simp [hj_eq]
            have h_not_le : ¬ i' ≤ i := by omega
            simp [h_adm', h_dig', h_not_le]

/-! ## The model `Y² - Y + 1` of the unramified quadratic extension -/

/-- `X² - X + 1` has no root over a field with residue field `𝔽₂`: `QF K (-1) 1` is a field. -/
theorem noRoot_model {K : Type*} [NormedField K] [IsUltrametricDist K]
    (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) : ∀ r : K, r ^ 2 ≠ -1 + 1 * r := by
  intro r
  intro h_eq
  have h_mul : r * (r - 1) = -1 := by
    calc
      r * (r - 1) = r ^ 2 - r := by ring
      _ = (-1 + 1 * r) - r := by rw [h_eq]
      _ = -1 := by ring
  have h_norm : ‖r * (r - 1)‖ = ‖(-1 : K)‖ := by rw [h_mul]
  rw [norm_mul, norm_neg, norm_one] at h_norm
  -- h_norm : ‖r‖ * ‖r - 1‖ = 1
  by_cases h_le : ‖r‖ ≤ 1
  · -- case ‖r‖ ≤ 1
    rcases hres r h_le with (h_lt | h_lt)
    · -- ‖r‖ < 1
      have h_sub_le_one : ‖r - 1‖ ≤ 1 := by
        calc
          ‖r - 1‖ = ‖r + (-1)‖ := by rw [sub_eq_add_neg]
          _ ≤ max ‖r‖ ‖(-1 : K)‖ := IsUltrametricDist.norm_add_le_max r (-1)
          _ = max ‖r‖ 1 := by simp
          _ ≤ 1 := max_le h_le (by norm_num)
      have h_nonneg_r : 0 ≤ ‖r‖ := norm_nonneg _
      have h_prod_lt_one : ‖r‖ * ‖r - 1‖ < 1 := by
        calc
          ‖r‖ * ‖r - 1‖ ≤ ‖r‖ * 1 := mul_le_mul_of_nonneg_left h_sub_le_one h_nonneg_r
          _ = ‖r‖ := by simp
          _ < 1 := h_lt
      linarith
    · -- ‖r - 1‖ < 1
      have h_nonneg_sub : 0 ≤ ‖r - 1‖ := norm_nonneg _
      have h_prod_lt_one : ‖r‖ * ‖r - 1‖ < 1 := by
        calc
          ‖r‖ * ‖r - 1‖ ≤ 1 * ‖r - 1‖ := mul_le_mul_of_nonneg_right h_le h_nonneg_sub
          _ = ‖r - 1‖ := by simp
          _ < 1 := h_lt
      linarith
  · -- case 1 < ‖r‖
    have h_one_lt : 1 < ‖r‖ := lt_of_not_ge h_le
    have h_norm_neg_one : ‖(-1 : K)‖ = 1 := by simp
    have h_ne : ‖r‖ ≠ ‖(-1 : K)‖ := by
      rw [h_norm_neg_one]
      linarith
    have h_sub_eq : ‖r - 1‖ = ‖r‖ := by
      calc
        ‖r - 1‖ = ‖r + (-1)‖ := by rw [sub_eq_add_neg]
        _ = max ‖r‖ ‖(-1 : K)‖ := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne
        _ = max ‖r‖ 1 := by simp
        _ = ‖r‖ := max_eq_left (by linarith)
    rw [h_sub_eq] at h_norm
    have h_nonneg : 0 ≤ ‖r‖ := norm_nonneg _
    nlinarith

section Unram

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)]

/-! ## Square certificates -/

/-- **The square certificate at an unramified component.** With `Y = QF.mk K A B 0 1` and a unit
`S'' = u0 + s1 Y`, the element `x = (π^mh S'')² + π^n0 r0 + π^n1 r1 Y + t` is a square as soon as
`u0, s1, r0, r1` are integral, `‖t‖ ≤ ‖π‖^n0` and `n0, n1 > 2 mh + 2e`. -/
theorem isSquare_of_unram_cert [ProperSpace K] {π : K} (hπ : NormUnif π)
    (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (hA : ‖A + 1‖ < 1) (hB : ‖B - 1‖ < 1)
    {e : ℕ} (h2 : ‖(2 : K)‖ = ‖π‖ ^ e)
    {mh n0 n1 : ℕ} {u0 s1 r0 r1 : K} (hu0 : ‖u0‖ ≤ 1) (hs1 : ‖s1‖ ≤ 1) (hunit : ‖u0‖ = 1 ∨ ‖s1‖ = 1)
    (hr0 : ‖r0‖ ≤ 1) (hr1 : ‖r1‖ ≤ 1) (hn0 : 2 * mh + 2 * e < n0) (hn1 : 2 * mh + 2 * e < n1)
    {x t : QF K A B} (ht : ‖t‖ ≤ ‖π‖ ^ n0)
    (hx : x = (algebraMap K (QF K A B) π ^ mh * QF.mk K A B u0 s1) ^ 2 +
        algebraMap K (QF K A B) (π ^ n0 * r0) + algebraMap K (QF K A B) (π ^ n1 * r1) * QF.mk K A B 0 1 +
        t) :
    IsSquare x := by
  set Y := QF.mk K A B 0 1 with hY
  set S'' := QF.mk K A B u0 s1 with hS''
  set S := algebraMap K (QF K A B) π ^ mh * S'' with hS
  have hYnorm : ‖Y‖ = 1 := by
    rw [hY, qfU_norm hres hA hB 0 1]
    simp
  have hS''norm : ‖S''‖ = 1 := by
    rw [hS'', qfU_norm hres hA hB u0 s1]
    rcases hunit with (hu | hs)
    · have hle : ‖s1‖ ≤ ‖u0‖ := by rw [hu]; exact hs1
      rw [max_eq_left hle, hu]
    · have hle : ‖u0‖ ≤ ‖s1‖ := by rw [hs]; exact hu0
      rw [max_eq_right hle, hs]
  have hπpos : 0 < ‖π‖ := norm_pos_iff.mpr hπ.ne_zero
  have hπlt1 : ‖π‖ < 1 := hπ.norm_lt_one
  have hS0 : S ≠ 0 := by
    rw [hS]
    have hnorm : ‖algebraMap K (QF K A B) π ^ mh * S''‖ > 0 := by
      rw [norm_mul, norm_pow, QF.norm_algebraMap (K := K) (a := A) (b := B), hS''norm, mul_one]
      exact pow_pos hπpos _
    intro hzero
    rw [hzero, norm_zero] at hnorm
    linarith
  have hSnorm : ‖S‖ = ‖π‖ ^ mh := by
    rw [hS, norm_mul, norm_pow, QF.norm_algebraMap (K := K) (a := A) (b := B), hS''norm, mul_one]
  have h4norm : ‖(4 : QF K A B)‖ = ‖π‖ ^ (2 * e) := by
    calc
      ‖(4 : QF K A B)‖ = ‖algebraMap K (QF K A B) (4 : K)‖ := rfl
      _ = ‖(4 : K)‖ := QF.norm_algebraMap (K := K) (a := A) (b := B) (4 : K)
      _ = ‖(2 : K) * (2 : K)‖ := by norm_num
      _ = ‖(2 : K)‖ * ‖(2 : K)‖ := norm_mul _ _
      _ = (‖π‖ ^ e) * (‖π‖ ^ e) := by rw [h2]
      _ = ‖π‖ ^ (e + e) := by rw [pow_add]
      _ = ‖π‖ ^ (2 * e) := by ring
  have hsq : (‖π‖ ^ mh) ^ 2 = ‖π‖ ^ (2 * mh) := by
    rw [sq, ← pow_add, two_mul]
  have h4Snorm : ‖(4 : QF K A B)‖ * ‖S‖ ^ 2 = ‖π‖ ^ (2 * mh + 2 * e) := by
    rw [h4norm, hSnorm, hsq]
    rw [pow_add]
    ring
  have hx_sub_S2 : x - S ^ 2 = algebraMap K (QF K A B) (π ^ n0 * r0) +
      algebraMap K (QF K A B) (π ^ n1 * r1) * Y + t := by
    rw [hx, hS, hS'']
    ring
  have hnormA : ‖algebraMap K (QF K A B) (π ^ n0 * r0)‖ ≤ ‖π‖ ^ n0 := by
    rw [QF.norm_algebraMap (K := K) (a := A) (b := B), norm_mul, norm_pow]
    have hpos : 0 ≤ ‖π‖ ^ n0 := pow_nonneg (norm_nonneg _) _
    have h := mul_le_mul_of_nonneg_left hr0 hpos
    simpa [mul_one] using h
  have hnormB : ‖algebraMap K (QF K A B) (π ^ n1 * r1) * Y‖ ≤ ‖π‖ ^ n1 := by
    rw [norm_mul, QF.norm_algebraMap (K := K) (a := A) (b := B), hYnorm, mul_one, norm_mul, norm_pow]
    have hpos : 0 ≤ ‖π‖ ^ n1 := pow_nonneg (norm_nonneg _) _
    have h := mul_le_mul_of_nonneg_left hr1 hpos
    simpa [mul_one] using h
  have hnormt : ‖t‖ ≤ ‖π‖ ^ n0 := ht
  have hp_lt_n0 : ‖π‖ ^ n0 < ‖π‖ ^ (2 * mh + 2 * e) :=
    pow_lt_pow_right_of_lt_one₀ hπpos hπlt1 hn0
  have hp_lt_n1 : ‖π‖ ^ n1 < ‖π‖ ^ (2 * mh + 2 * e) :=
    pow_lt_pow_right_of_lt_one₀ hπpos hπlt1 hn1
  have hA_lt : ‖algebraMap K (QF K A B) (π ^ n0 * r0)‖ < ‖π‖ ^ (2 * mh + 2 * e) :=
    lt_of_le_of_lt hnormA hp_lt_n0
  have hB_lt : ‖algebraMap K (QF K A B) (π ^ n1 * r1) * Y‖ < ‖π‖ ^ (2 * mh + 2 * e) :=
    lt_of_le_of_lt hnormB hp_lt_n1
  have hC_lt : ‖t‖ < ‖π‖ ^ (2 * mh + 2 * e) :=
    lt_of_le_of_lt hnormt hp_lt_n0
  have hmax_lt : max (‖algebraMap K (QF K A B) (π ^ n0 * r0)‖)
      (max (‖algebraMap K (QF K A B) (π ^ n1 * r1) * Y‖) ‖t‖) < ‖π‖ ^ (2 * mh + 2 * e) :=
    max_lt hA_lt (max_lt hB_lt hC_lt)
  have hx_sub_S2_norm_lt : ‖x - S ^ 2‖ < ‖(4 : QF K A B)‖ * ‖S‖ ^ 2 := by
    rw [hx_sub_S2]
    have hsum : ‖algebraMap K (QF K A B) (π ^ n0 * r0) + algebraMap K (QF K A B) (π ^ n1 * r1) * Y + t‖
        ≤ max (‖algebraMap K (QF K A B) (π ^ n0 * r0)‖)
            (max (‖algebraMap K (QF K A B) (π ^ n1 * r1) * Y‖) ‖t‖) := by
      calc
        ‖algebraMap K (QF K A B) (π ^ n0 * r0) + algebraMap K (QF K A B) (π ^ n1 * r1) * Y + t‖
            = ‖(algebraMap K (QF K A B) (π ^ n0 * r0) + algebraMap K (QF K A B) (π ^ n1 * r1) * Y) + t‖ := by ring
        _ ≤ max ‖algebraMap K (QF K A B) (π ^ n0 * r0) + algebraMap K (QF K A B) (π ^ n1 * r1) * Y‖ ‖t‖ :=
          IsUltrametricDist.norm_add_le_max _ _
        _ ≤ max (max ‖algebraMap K (QF K A B) (π ^ n0 * r0)‖ ‖algebraMap K (QF K A B) (π ^ n1 * r1) * Y‖) ‖t‖ :=
          max_le_max (IsUltrametricDist.norm_add_le_max _ _) (le_refl _)
        _ = max ‖algebraMap K (QF K A B) (π ^ n0 * r0)‖ (max ‖algebraMap K (QF K A B) (π ^ n1 * r1) * Y‖ ‖t‖) := by
          simp [max_assoc]
    calc
      ‖algebraMap K (QF K A B) (π ^ n0 * r0) + algebraMap K (QF K A B) (π ^ n1 * r1) * Y + t‖
          ≤ max (‖algebraMap K (QF K A B) (π ^ n0 * r0)‖)
              (max (‖algebraMap K (QF K A B) (π ^ n1 * r1) * Y‖) ‖t‖) := hsum
      _ < ‖π‖ ^ (2 * mh + 2 * e) := hmax_lt
      _ = ‖(4 : QF K A B)‖ * ‖S‖ ^ 2 := by rw [h4Snorm]
  have h2F : (2 : QF K A B) ≠ 0 := by
    have hnorm2 : ‖(2 : QF K A B)‖ > 0 := by
      rw [qfU_two h2, QF.norm_algebraMap (K := K) (a := A) (b := B)]
      exact pow_pos hπpos _
    intro hzero
    rw [hzero, norm_zero] at hnorm2
    linarith
  have hunif : NormUnif (algebraMap K (QF K A B) π) := qfU_normUnif hπ hres hA hB
  exact isSquare_of_sub_sq_lt hunif h2F hS0 hx_sub_S2_norm_lt

/-! ## The standard basis -/

/-- The standard basis of `Fˣ / Fˣ²`: `π` (`i = 0`), `1 + π^(2 jU i + 1) w_(lU i)`
(`1 ≤ i ≤ 2e`, `w = ![1, Y]`), `1 + 4 Y` (`i = 2e + 1`). -/
noncomputable def bU (π : K) (e i : ℕ) : QF K A B :=
  if i = 0 then algebraMap K (QF K A B) π
  else if i = 2 * e + 1 then 1 + 4 * QF.mk K A B 0 1
  else 1 + algebraMap K (QF K A B) π ^ (2 * jU i + 1) * (if lU i = 0 then 1 else QF.mk K A B 0 1)

theorem dfact_bU {π : K} (hπ : NormUnif π) (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1)
    (hA : ‖A + 1‖ < 1) (hB : ‖B - 1‖ < 1) {e : ℕ} (he : 0 < e) (h2 : ‖(2 : K)‖ = ‖π‖ ^ e)
    (i : ℕ) (hi : i < 2 * e + 2) :
    DFact ⟨e, 2, 2, 0⟩ (algebraMap K (QF K A B) π) ![1, QF.mk K A B 0 1] (bU π e i) 1 (kStd i)
      (uStdU e i) := by
  set πF := algebraMap K (QF K A B) π
  set w : Fin 2 → QF K A B := ![1, QF.mk K A B 0 1]
  have hπF : NormUnif πF := qfU_normUnif (A := A) (B := B) hπ hres hA hB
  have hπ0 : πF ≠ 0 := hπF.ne_zero
  have hπ1 : ‖πF‖ < 1 := hπF.norm_lt_one
  have h2_lt_one : ‖(2 : K)‖ < 1 := by
    rw [h2]
    exact pow_lt_one₀ (norm_nonneg _) (hπ.norm_lt_one) he.ne'
  have hπnorm_pos : 0 < ‖π‖ := norm_pos_iff.mpr hπ.ne_zero
  have h2_ne_zero : (2 : K) ≠ 0 := by
    intro hzero
    have hnorm0 : ‖(2 : K)‖ = 0 := by simpa [hzero] using norm_zero (E := K)
    rw [h2] at hnorm0
    have hpos : 0 < ‖π‖ ^ e := pow_pos hπnorm_pos e
    linarith
  have h4_ne_zero_K : (4 : K) ≠ 0 := by
    have : (4 : K) = (2 : K) * (2 : K) := by norm_num
    rw [this]
    exact mul_ne_zero h2_ne_zero h2_ne_zero
  have h4_ne_zero : (4 : QF K A B) ≠ 0 := by
    have h := (map_ne_zero (algebraMap K (QF K A B))).mpr h4_ne_zero_K
    have h_eq : algebraMap K (QF K A B) (4 : K) = (4 : QF K A B) := map_natCast (algebraMap K (QF K A B)) 4
    rw [h_eq] at h
    exact h
  have h2_lt_one_F : ‖(2 : QF K A B)‖ < 1 := by
    have := qfU_two (A := A) (B := B) (π := π) h2
    rw [this]
    exact pow_lt_one₀ (norm_nonneg _) hπ1 he.ne'
  have h4_lt_one : ‖(4 : QF K A B)‖ < 1 := by
    have h4_eq : (4 : QF K A B) = (2 : QF K A B) * (2 : QF K A B) := by norm_num
    rw [h4_eq, norm_mul]
    have hpos : 0 ≤ ‖(2 : QF K A B)‖ := norm_nonneg _
    nlinarith
  have hY_le_one : ‖QF.mk K A B 0 1‖ ≤ 1 := (qfU_omega (A := A) (B := B) hres hA hB h2_lt_one).1
  have hw : ∀ l : Fin 2, ‖w l‖ ≤ 1 := by
    intro l
    fin_cases l
    · simp [w]
    · simp [w, hY_le_one]
  have hlift_two : liftW w 2 = QF.mk K A B 0 1 := by
    dsimp [liftW, w]
    have h0 : bitv 2 2 0 = (0 : ZMod 2) := by decide
    have h1 : bitv 2 2 1 = (1 : ZMod 2) := by decide
    calc
      ∑ l : Fin 2, ((bitv 2 2 l).val : QF K A B) * (![1, QF.mk K A B 0 1]) l
          = ((bitv 2 2 0).val : QF K A B) * (![1, QF.mk K A B 0 1]) 0
          + ((bitv 2 2 1).val : QF K A B) * (![1, QF.mk K A B 0 1]) 1 := by
        simp [Fin.sum_univ_two]
      _ = ((0 : ZMod 2).val : QF K A B) * 1 + ((1 : ZMod 2).val : QF K A B) * QF.mk K A B 0 1 := by
        simp [h0, h1]
      _ = (0 : QF K A B) * 1 + (1 : QF K A B) * QF.mk K A B 0 1 := by
        simp [ZMod.val_zero, ZMod.val_one]
      _ = QF.mk K A B 0 1 := by simp
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · -- i = 0
    have hb : bU π e 0 = πF := by simp [bU, πF]
    have hu : uStdU e 0 = .none := by simp [uStdU]
    have hk : kStd 0 = 1 := rfl
    rw [hb, hu, hk]
    exact dfact_pi _ _ _
  by_cases h_last : i = 2 * e + 1
  · -- i = 2e + 1
    subst h_last
    have hb : bU π e (2 * e + 1) = 1 + 4 * QF.mk K A B 0 1 := by
      simp [bU]
    have hu : uStdU e (2 * e + 1) = .four 2 := by simp [uStdU]
    have hk : kStd (2 * e + 1) = 0 := by
      simp [kStd]
    rw [hb, hu, hk]
    have htarget : (1 : QF K A B) + 4 * QF.mk K A B 0 1 = 1 + 4 * liftW w 2 := by
      rw [hlift_two]
    rw [htarget]
    exact dfact_four_std (F := QF K A B) ⟨e, 2, 2, 0⟩ πF w hw h4_ne_zero h4_lt_one 2
  · -- 1 ≤ i ≤ 2e
    have hlU_lt_2 : lU i < 2 := by
      dsimp [lU]
      exact Nat.mod_lt (i - 1) (by omega : 0 < 2)
    let l : Fin 2 := ⟨lU i, hlU_lt_2⟩
    have h_wl : w l = (if lU i = 0 then (1 : QF K A B) else QF.mk K A B 0 1) := by
      dsimp [w, l]
      by_cases hl0 : lU i = 0
      · simp [hl0]
      · have hl1 : lU i = 1 := by omega
        simp [hl1]
    have hb : bU π e i = 1 + πF ^ (2 * jU i + 1) * w l := by
      dsimp [bU, πF]
      simp [hi0.ne', h_last, h_wl]
    have hu : uStdU e i = .odd (2 * jU i + 1) (2 ^ lU i) := by
      simp [uStdU, hi0.ne', h_last]
    have hk : kStd i = 0 := by
      simp [kStd, hi0.ne']
    have ht_pos : 0 < 2 * jU i + 1 := by omega
    rw [hb, hu, hk]
    simpa [l] using dfact_odd_std (π := πF) ⟨e, 2, 2, 0⟩ hπ0 hπ1 w hw (2 * jU i + 1) ht_pos l

theorem bU_ne_zero {π : K} (hπ : NormUnif π) (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1)
    (hA : ‖A + 1‖ < 1) (hB : ‖B - 1‖ < 1) {e : ℕ} (he : 0 < e) (h2 : ‖(2 : K)‖ = ‖π‖ ^ e) (i : ℕ) :
    bU (A := A) (B := B) π e i ≠ 0 := by
  unfold bU
  split
  · -- i = 0
    simpa using (algebraMap K (QF K A B)).injective.ne hπ.ne_zero
  · -- i ≠ 0
    rename_i hi0
    split
    · -- i = 2 * e + 1
      intro hzero
      have hneg : (4 : QF K A B) * QF.mk K A B 0 1 = -1 := by
        calc
          (4 : QF K A B) * QF.mk K A B 0 1 = (1 + (4 : QF K A B) * QF.mk K A B 0 1) - 1 := by ring
          _ = 0 - 1 := by rw [hzero]
          _ = -1 := by simp
      have hnorm_mk : ‖QF.mk K A B 0 1‖ = 1 := by
        rw [qfU_norm hres hA hB 0 1]
        simp
      have hnorm_4 : ‖(4 : QF K A B)‖ = ‖(2 : K)‖ ^ 2 := by
        calc
          ‖(4 : QF K A B)‖ = ‖algebraMap K (QF K A B) (4 : K)‖ := rfl
          _ = ‖(4 : K)‖ := QF.norm_algebraMap K A B (4 : K)
          _ = ‖(2 : K) ^ 2‖ := by norm_num
          _ = ‖(2 : K)‖ ^ 2 := by rw [norm_pow]
      have hnorm_prod : ‖(4 : QF K A B) * QF.mk K A B 0 1‖ = ‖(4 : QF K A B)‖ * ‖QF.mk K A B 0 1‖ := by
        rw [norm_mul]
      have hnorm_val : ‖(4 : QF K A B) * QF.mk K A B 0 1‖ = ‖(2 : K)‖ ^ 2 := by
        rw [hnorm_prod, hnorm_4, hnorm_mk, mul_one]
      have hnorm_val2 : ‖(4 : QF K A B) * QF.mk K A B 0 1‖ = ‖π‖ ^ (2 * e) := by
        rw [hnorm_val, h2]
        rw [pow_two, ← pow_add, two_mul]
      have hnorm_neg_one : ‖(-1 : QF K A B)‖ = 1 := by simp
      have hnorm_eq : ‖(4 : QF K A B) * QF.mk K A B 0 1‖ = ‖(-1 : QF K A B)‖ := by rw [hneg]
      rw [hnorm_neg_one] at hnorm_eq
      rw [hnorm_val2] at hnorm_eq
      have h_pow_lt_one : ‖π‖ ^ (2 * e) < 1 := by
        apply pow_lt_one₀ (norm_nonneg _) hπ.norm_lt_one
        omega
      rw [← hnorm_eq] at h_pow_lt_one
      linarith
    · -- i ≠ 2 * e + 1
      rename_i hi2e1
      intro hzero
      have hprod_eq_neg_one : algebraMap K (QF K A B) π ^ (2 * jU i + 1) * (if lU i = 0 then 1 else QF.mk K A B 0 1) = -1 := by
        calc
          algebraMap K (QF K A B) π ^ (2 * jU i + 1) * (if lU i = 0 then 1 else QF.mk K A B 0 1) =
            (1 + algebraMap K (QF K A B) π ^ (2 * jU i + 1) * (if lU i = 0 then 1 else QF.mk K A B 0 1)) - 1 := by ring
          _ = 0 - 1 := by rw [hzero]
          _ = -1 := by simp
      have hnorm_neg_one : ‖(-1 : QF K A B)‖ = 1 := by simp
      have hnorm_prod : ‖algebraMap K (QF K A B) π ^ (2 * jU i + 1) * (if lU i = 0 then 1 else QF.mk K A B 0 1)‖ = ‖(-1 : QF K A B)‖ := by
        rw [hprod_eq_neg_one]
      rw [hnorm_neg_one] at hnorm_prod
      rw [norm_mul] at hnorm_prod
      have hnorm_pow : ‖algebraMap K (QF K A B) π ^ (2 * jU i + 1)‖ = ‖π‖ ^ (2 * jU i + 1) := by
        rw [norm_pow, QF.norm_algebraMap K A B π]
      rw [hnorm_pow] at hnorm_prod
      have hnorm_w_le_one : ‖(if lU i = 0 then 1 else QF.mk K A B 0 1 : QF K A B)‖ ≤ 1 := by
        by_cases hli : lU i = 0
        · rw [ite_eq_left hli]
          simp
        · rw [ite_eq_right hli]
          rw [qfU_norm hres hA hB 0 1]
          simp
      have h_pow_lt_one : ‖π‖ ^ (2 * jU i + 1) < 1 := by
        apply pow_lt_one₀ (norm_nonneg _) hπ.norm_lt_one
        omega
      have hprod_lt_one : ‖π‖ ^ (2 * jU i + 1) * ‖(if lU i = 0 then 1 else QF.mk K A B 0 1 : QF K A B)‖ < 1 := by
        calc
          ‖π‖ ^ (2 * jU i + 1) * ‖(if lU i = 0 then 1 else QF.mk K A B 0 1 : QF K A B)‖ ≤
            ‖π‖ ^ (2 * jU i + 1) * 1 :=
            mul_le_mul_of_nonneg_left hnorm_w_le_one (pow_nonneg (norm_nonneg _) _)
          _ = ‖π‖ ^ (2 * jU i + 1) := by simp
          _ < 1 := h_pow_lt_one
      rw [← hnorm_prod] at hprod_lt_one
      linarith

/-- **The standard basis of an unramified component is independent modulo squares.** -/
theorem bU_indep {π : K} (hπ : NormUnif π) (hres : ∀ y : K, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1)
    (hA : ‖A + 1‖ < 1) (hB : ‖B - 1‖ < 1) {e : ℕ} (he : 0 < e) (h2 : ‖(2 : K)‖ = ‖π‖ ^ e) :
    ∀ ε : Fin (2 * e + 2) → ZMod 2,
      IsSquare (∏ i : Fin (2 * e + 2), bU (A := A) (B := B) π e i ^ (ε i).val) → ε = 0 := by
  intro ε hε
  have h21 : ‖(2 : K)‖ < 1 := by
    rw [h2]; exact pow_lt_one₀ (norm_nonneg _) hπ.norm_lt_one he.ne'
  set b : Fin (2 * e + 2) → (QF K A B)ˣ := fun i =>
    Units.mk0 (bU (A := A) (B := B) π e i) (bU_ne_zero hπ hres hA hB he h2 i) with hb
  have hsq : IsSquare (∏ i, b i ^ (ε i).val) :=
    isSquare_units_of_isSquare _ (by simpa [hb, Units.coe_prod] using hε)
  have hQ : CompOK ⟨e, 2, 2, 0⟩ (algebraMap K (QF K A B) π) ![1, QF.mk K A B 0 1] :=
    compOK_F4 (qfU_normUnif hπ hres hA hB) he (qfU_two h2) (qfU_omega hres hA hB h21).1
      (qfU_omega hres hA hB h21).2 (qfU_res hπ hres hA hB) 0
  exact sb_indep_of_echelonOK b (fun i p => admB ⟨e, 2, 2, 0⟩ (uStdU e i) p)
    (fun i p => digB ⟨e, 2, 2, 0⟩ (kStd i) (uStdU e i) p) (pivStdU e)
    (fun p ε' hadm hsq' => comp_test b (MonoidHom.id _) _ hQ (fun _ => 1) (fun i => kStd i)
      (fun i => uStdU e i) (fun i => dfact_bU hπ hres hA hB he h2 i i.isLt) p ε' hadm hsq')
    (echelonOK_stdU e he) ε hsq

end Unram

end FurioLombardo.Discharge.SelmerBasis
