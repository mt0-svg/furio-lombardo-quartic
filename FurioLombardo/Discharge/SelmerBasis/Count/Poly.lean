import Mathlib

/-!
# Count lane: monic quadratic divisors of a sextic

Bounds on the number of monic quadratic divisors of a sextic `f` over a field, the input of the bound
`#A(K)[2] ≤ 1 + #{monic quadratic u ∣ f}`: at most `3` when `f` has no root (`cnt_quadDiv_noRoot`), at
most `7` when `f` has a monic irreducible quadratic factor (`cnt_quadDiv_irrFactor`, from the bound
`C(n, k)` of `cnt_monicDiv_choose`). For `f = c q (A² - d B²)` with `d = disc q` (M3a's normal form):
no root when `d` is not a square and `f` is squarefree (`cnt_noRoot_normForm`); a monic irreducible
quadratic factor when `N(D) = D0² - d D1²` is not a square (`cnt_irrFactor_of_ND`).

The bound `C(n, k)` counts the size `k` submultisets of the roots of `f` in its splitting field.
-/

set_option autoImplicit false

open Polynomial

namespace FurioLombardo.Discharge.SelmerBasis.Count

theorem cnt_monicDiv_choose {K : Type*} [Field K] (f : K[X]) (hf0 : f ≠ 0) (k : ℕ) :
    ∃ D : Finset K[X], D.card ≤ f.natDegree.choose k ∧
      ∀ u : K[X], u.Monic → u.natDegree = k → u ∣ f → u ∈ D := by
  classical
  set L := SplittingField f
  let φ : K[X] → L[X] := fun u => u.map (algebraMap K L)
  have hφ : Function.Injective φ := map_injective _ (algebraMap K L).injective
  have hs : Splits (f.map (algebraMap K L)) := SplittingField.splits f
  have hfL : f.map (algebraMap K L) ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hf0
  set s := (f.map (algebraMap K L)).roots
  have hcard : s.card = f.natDegree := by
    rw [← hs.natDegree_eq_card_roots, natDegree_map]
  let T : Finset L[X] :=
    (Multiset.powersetCard k s).toFinset.image (fun t => (t.map (fun r => X - C r)).prod)
  refine ⟨T.preimage φ hφ.injOn, ?_, ?_⟩
  · calc (T.preimage φ hφ.injOn).card ≤ T.card := by rw [Finset.card_preimage]; exact Finset.card_filter_le _ _
      _ ≤ (Multiset.powersetCard k s).toFinset.card := Finset.card_image_le
      _ ≤ (Multiset.powersetCard k s).card := Multiset.toFinset_card_le _
      _ = f.natDegree.choose k := by rw [Multiset.card_powersetCard, hcard]
  · intro u hu hud huf
    rw [Finset.mem_preimage]
    have hdvd : φ u ∣ f.map (algebraMap K L) := Polynomial.map_dvd _ huf
    have hus : Splits (φ u) := hs.of_dvd hfL hdvd
    have hum : (φ u).Monic := hu.map _
    refine Finset.mem_image.mpr ⟨(φ u).roots, ?_, (hus.eq_prod_roots_of_monic hum).symm⟩
    rw [Multiset.mem_toFinset, Multiset.mem_powersetCard]
    refine ⟨(Polynomial.roots.le_of_dvd hfL hdvd), ?_⟩
    rw [← hus.natDegree_eq_card_roots]
    simp only [φ, natDegree_map, hud]

theorem cnt_quadDiv_irrFactor {K : Type*} [Field K] (f g : K[X]) (hf0 : f ≠ 0)
    (hdeg : f.natDegree = 6) (hg : Irreducible g) (hgm : g.Monic) (hgd : g.natDegree = 2)
    (hgf : g ∣ f) :
    ∃ D : Finset K[X], D.card ≤ 7 ∧
      ∀ u : K[X], u.Monic → u.natDegree = 2 → u ∣ f → u ∈ D := by
  classical
  obtain ⟨h, rfl⟩ := hgf
  have hh0 : h ≠ 0 := right_ne_zero_of_mul hf0
  have hhd : h.natDegree = 4 := by
    rw [natDegree_mul hgm.ne_zero hh0, hgd] at hdeg; omega
  obtain ⟨D, hDc, hD⟩ := cnt_monicDiv_choose h hh0 2
  refine ⟨insert g D, ?_, ?_⟩
  · calc (insert g D).card ≤ D.card + 1 := Finset.card_insert_le _ _
      _ ≤ 6 + 1 := by
        have : h.natDegree.choose 2 = 6 := by rw [hhd]; rfl
        omega
      _ = 7 := rfl
  · intro u hu hud huf
    by_cases hgu : g ∣ u
    · rw [Finset.mem_insert]; left
      exact eq_of_monic_of_dvd_of_natDegree_le hgm hu hgu (by rw [hud, hgd])
    · rw [Finset.mem_insert]; right
      have hc : IsCoprime u g := ((hg.coprime_iff_not_dvd).mpr hgu).symm
      exact hD u hu hud (hc.dvd_of_dvd_mul_left huf)

theorem cnt_quadDiv_noRoot {K : Type*} [Field K] (f : K[X]) (hf0 : f ≠ 0) (hdeg : f.natDegree ≤ 6)
    (hroot : ∀ x : K, f.eval x ≠ 0) :
    ∃ D : Finset K[X], D.card ≤ 3 ∧
      ∀ u : K[X], u.Monic → u.natDegree = 2 → u ∣ f → u ∈ D := by
  classical
  obtain ⟨D0, -, hD0⟩ := cnt_monicDiv_choose f hf0 2
  let D := D0.filter (fun u => u.Monic ∧ u.natDegree = 2 ∧ u ∣ f)
  have hirr : ∀ u ∈ D, Irreducible u := by
    intro u hu
    obtain ⟨-, hum, hud, huf⟩ := Finset.mem_filter.mp hu
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [hud, Finset.mem_Icc]; omega
    · intro r hr
      obtain ⟨w, hw⟩ := huf
      apply hroot r
      rw [hw, eval_mul, hr.eq_zero, zero_mul]
  refine ⟨D, ?_, fun u hu hud huf => Finset.mem_filter.mpr ⟨hD0 u hu hud huf, hu, hud, huf⟩⟩
  have hpw : (D : Set K[X]).Pairwise (Function.onFun IsCoprime id) := by
    intro u hu v hv huv
    simp only [Function.onFun, id]
    obtain ⟨-, hum, hud, -⟩ := Finset.mem_filter.mp hu
    obtain ⟨-, hvm, hvd, -⟩ := Finset.mem_filter.mp hv
    rw [(hirr u hu).coprime_iff_not_dvd]
    intro huv'
    exact huv (eq_of_monic_of_dvd_of_natDegree_le hum hvm huv' (by rw [hud, hvd])).symm
  have hprod : ∏ u ∈ D, id u ∣ f :=
    Finset.prod_dvd_of_coprime hpw (fun u hu => (Finset.mem_filter.mp hu).2.2.2)
  have hmon : ∀ u ∈ D, (id u).Monic := fun u hu => (Finset.mem_filter.mp hu).2.1
  have hdp : (∏ u ∈ D, id u).natDegree = 2 * D.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ hmon, Finset.sum_congr rfl
      (fun u hu => (Finset.mem_filter.mp hu).2.2.1), Finset.sum_const, smul_eq_mul, mul_comm]
  have := natDegree_le_of_dvd hprod hf0
  omega

theorem cnt_noRoot_normForm {K : Type*} [Field K] (_h2 : (2 : K) ≠ 0) (c q1 q0 a1 a0 b1 b0 : K)
    (f : K[X]) (hf : f = C c * (X ^ 2 + C q1 * X + C q0) *
      ((X ^ 2 + C a1 * X + C a0) ^ 2 - C (q1 ^ 2 - 4 * q0) * (C b1 * X + C b0) ^ 2))
    (hsf : Squarefree f) (hd : ¬ IsSquare (q1 ^ 2 - 4 * q0)) (x : K) : f.eval x ≠ 0 := by
  intro hx
  have hc : c ≠ 0 := by
    rintro rfl
    rw [hf, C_0, zero_mul, zero_mul] at hsf
    exact not_squarefree_zero hsf
  rw [hf] at hx
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_X] at hx
  rcases mul_eq_zero.mp hx with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hc h
    · exact hd ⟨2 * x + q1, by linear_combination (-4) * h⟩
  · by_cases hB : b1 * x + b0 = 0
    · have hA : x ^ 2 + a1 * x + a0 = 0 := by
        have : (x ^ 2 + a1 * x + a0) ^ 2 = 0 := by rw [hB] at h; linear_combination h
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      have hAd : (X - C x) ∣ (X ^ 2 + C a1 * X + C a0 : K[X]) := by
        rw [dvd_iff_isRoot]; simpa using hA
      have hBd : (X - C x) ∣ (C b1 * X + C b0 : K[X]) := by
        rw [dvd_iff_isRoot]; simpa using hB
      obtain ⟨A', hA'⟩ := hAd
      obtain ⟨B', hB'⟩ := hBd
      have hdvd : (X - C x) * (X - C x) ∣ f := by
        rw [hf, hA', hB']
        exact Dvd.intro (C c * (X ^ 2 + C q1 * X + C q0) * (A' ^ 2 - C (q1 ^ 2 - 4 * q0) * B' ^ 2))
          (by ring)
      exact not_isUnit_X_sub_C x (hsf _ hdvd)
    · refine hd ⟨(x ^ 2 + a1 * x + a0) / (b1 * x + b0), ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hB hB)]
      linear_combination -h

/-- A monic quadratic whose discriminant is not a square is irreducible. -/
theorem cnt_quad_irreducible {K : Type*} [Field K] (s t : K)
    (hd : ¬ IsSquare (s ^ 2 - 4 * t)) :
    (X ^ 2 + C s * X + C t : K[X]).Monic ∧ (X ^ 2 + C s * X + C t : K[X]).natDegree = 2 ∧
      Irreducible (X ^ 2 + C s * X + C t : K[X]) := by
  have hm : (X ^ 2 + C s * X + C t : K[X]).Monic := by monicity!
  have hdeg : (X ^ 2 + C s * X + C t : K[X]).natDegree = 2 := by compute_degree!
  refine ⟨hm, hdeg, ?_⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [hdeg, Finset.mem_Icc]; omega
  · intro r hr
    apply hd
    refine ⟨2 * r + s, ?_⟩
    have : r ^ 2 + s * r + t = 0 := by simpa [IsRoot] using hr
    linear_combination (-4) * this

theorem cnt_irrFactor_of_ND {K : Type*} [Field K] (_h2 : (2 : K) ≠ 0) (c q1 q0 a1 a0 b1 b0 : K)
    (f : K[X]) (hf : f = C c * (X ^ 2 + C q1 * X + C q0) *
      ((X ^ 2 + C a1 * X + C a0) ^ 2 - C (q1 ^ 2 - 4 * q0) * (C b1 * X + C b0) ^ 2))
    (hND : ¬ IsSquare ((a1 ^ 2 + (q1 ^ 2 - 4 * q0) * b1 ^ 2 - 4 * a0) ^ 2 -
      (q1 ^ 2 - 4 * q0) * (2 * a1 * b1 - 4 * b0) ^ 2)) :
    ∃ g : K[X], g.Monic ∧ g.natDegree = 2 ∧ Irreducible g ∧ g ∣ f := by
  set d := q1 ^ 2 - 4 * q0 with hd_def
  by_cases hsq : IsSquare d
  · obtain ⟨w, hw⟩ := hsq
    set D0 := a1 ^ 2 + d * b1 ^ 2 - 4 * a0
    set D1 := 2 * a1 * b1 - 4 * b0
    have hfac : (X ^ 2 + C a1 * X + C a0) ^ 2 - C d * (C b1 * X + C b0) ^ 2 =
        (X ^ 2 + C (a1 + w * b1) * X + C (a0 + w * b0)) *
          (X ^ 2 + C (a1 - w * b1) * X + C (a0 - w * b0)) := by
      rw [hw]; simp only [map_add, map_sub, map_mul]; ring
    have hdp : (a1 + w * b1) ^ 2 - 4 * (a0 + w * b0) = D0 + w * D1 := by
      simp only [D0, D1]; rw [hw]; ring
    have hdm : (a1 - w * b1) ^ 2 - 4 * (a0 - w * b0) = D0 - w * D1 := by
      simp only [D0, D1]; rw [hw]; ring
    have hprod : (D0 + w * D1) * (D0 - w * D1) = D0 ^ 2 - d * D1 ^ 2 := by rw [hw]; ring
    by_cases hp : IsSquare (D0 + w * D1)
    · have hm : ¬ IsSquare (D0 - w * D1) := by
        intro hm
        apply hND
        have := hp.mul hm
        rwa [hprod] at this
      obtain ⟨hmon, hdeg, hirr⟩ := cnt_quad_irreducible (a1 - w * b1) (a0 - w * b0) (hdm ▸ hm)
      refine ⟨_, hmon, hdeg, hirr, ?_⟩
      rw [hf, hfac]
      exact Dvd.intro_left (C c * (X ^ 2 + C q1 * X + C q0) * (X ^ 2 + C (a1 + w * b1) * X + C (a0 + w * b0)))
        (by ring)
    · obtain ⟨hmon, hdeg, hirr⟩ := cnt_quad_irreducible (a1 + w * b1) (a0 + w * b0) (hdp ▸ hp)
      refine ⟨_, hmon, hdeg, hirr, ?_⟩
      rw [hf, hfac]
      exact Dvd.intro (C c * (X ^ 2 + C q1 * X + C q0) * (X ^ 2 + C (a1 - w * b1) * X + C (a0 - w * b0)))
        (by ring)
  · obtain ⟨hmon, hdeg, hirr⟩ := cnt_quad_irreducible q1 q0 hsq
    refine ⟨_, hmon, hdeg, hirr, ?_⟩
    rw [hf]
    exact Dvd.intro (C c * ((X ^ 2 + C a1 * X + C a0) ^ 2 - C d * (C b1 * X + C b0) ^ 2)) (by ring)

end FurioLombardo.Discharge.SelmerBasis.Count
