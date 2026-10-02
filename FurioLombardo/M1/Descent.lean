import FurioLombardo.M1.BruinCheck
import FurioLombardo.M1.SSet
import FurioLombardo.M1.SelmerBound

/-!
# The descent class lies in `K21(S, 2)`

For a primitive integer point `a` of `C` (`r · a = 1` for some integer vector `r`) and a prime
`v ∉ S`, the three values `Q1(a), Q2(a), Q3(a)` are not all in `v` (`not_all_mem`): otherwise the
reduced net has a common zero, so the three partial derivatives of its Jacobian cubic vanish there
too (`Vendor.NetOfConics.dJ_eq_zero_of_common_zero`), the six matrix kills the Veronese vector,
and `N M = cS I` with `cS ∉ v` forces the point to vanish modulo `v`. With `Q1 Q3 = Q2²` on `C`,
the class of `Q1(a)` (or of `Q3(a)`) then satisfies the criterion `mk_mem_selmerGroup_two`.
-/

namespace FurioLombardo.M1

open Vendor.NetOfConics NumberField IsDedekindDomain

/-- The value of `Q_(i+1)` at an integer point. -/
noncomputable def qO (i : Fin 3) (a : Fin 3 → ℤ) : 𝓞 K21 := qev (qC i) (fun j => (a j : 𝓞 K21))

theorem F_intCast {R : Type*} [CommRing R] (x y z : ℤ) :
    FurioLombardo.F (x : R) (y : R) (z : R) = ((FurioLombardo.F x y z : ℤ) : R) := by
  simp [FurioLombardo.F]

theorem bruin_point (a : Fin 3 → ℤ) (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0) :
    qO 0 a * qO 2 a = qO 1 a ^ 2 := by
  have h := bruin_O (fun j => (a j : 𝓞 K21))
  rw [F_intCast, hF, Int.cast_zero, mul_zero, sub_eq_zero] at h
  exact h

theorem cS_not_mem (v : HeightOneSpectrum (𝓞 K21)) (hv : v ∉ S) : zkO cSL ∉ v.asIdeal := by
  rw [cSO_eq]
  have hP := v.isPrime
  have h2 : (2 : 𝓞 K21) ∉ v.asIdeal := fun h => hv (Or.inl h)
  have h7 : (7 : 𝓞 K21) ∉ v.asIdeal := fun h => hv (Or.inr (Or.inl h))
  have h16 := gO_not_mem v hv 16 (by norm_num)
  have h17 := gO_not_mem v hv 17 (by norm_num)
  intro h
  rcases hP.mem_or_mem h with h | h
  · rcases hP.mem_or_mem h with h | h
    · rcases hP.mem_or_mem h with h | h
      · exact h2 (hP.mem_of_pow_mem _ h)
      · exact h7 (hP.mem_of_pow_mem _ h)
    · exact h16 (hP.mem_of_pow_mem _ h)
  · exact h17 (hP.mem_of_pow_mem _ h)

/-- At a prime outside `S`, the three conics do not all vanish at a primitive integer point.
Lemma 2.3 of the paper. -/
theorem not_all_mem (v : HeightOneSpectrum (𝓞 K21)) (hv : v ∉ S) (a r : Fin 3 → ℤ)
    (hr : ∑ j, r j * a j = 1) (h : ∀ i, qO i a ∈ v.asIdeal) : False := by
  letI := Ideal.Quotient.field v.asIdeal
  let φ : 𝓞 K21 →+* 𝓞 K21 ⧸ v.asIdeal := Ideal.Quotient.mk v.asIdeal
  let R : Fin 3 → 𝓞 K21 ⧸ v.asIdeal := fun j => φ (a j : 𝓞 K21)
  have hR : R ≠ 0 := by
    intro h0
    have hmem : ∀ j, ((a j : ℤ) : 𝓞 K21) ∈ v.asIdeal := fun j =>
      Ideal.Quotient.eq_zero_iff_mem.mp (congrFun h0 j)
    have h1 : ((∑ j, r j * a j : ℤ) : 𝓞 K21) ∈ v.asIdeal := by
      push_cast
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmem j)
    rw [hr, Int.cast_one] at h1
    exact v.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hz : ∀ i, qev (fun m => φ (qC i m)) R = 0 := by
    intro i
    rw [← map_qev]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i)
  have hrow : ∀ k : Fin 6, ∑ m : Fin 6, φ (zkO (sixA k m)) * veronese R m = 0 := by
    intro k
    by_cases hk : (k : ℕ) < 3
    · have hs : ∀ m : Fin 6, sixA k m = qcA k m := fun m => by simp [sixA, hk]
      have hq := hz ⟨k, hk⟩
      rw [qev_eq_sum_veronese] at hq
      simpa [hs, qC] using hq
    · let l : Fin 3 := ⟨k - 3, by omega⟩
      have hs : ∀ m : Fin 6, sixA k m = dJA l m := fun m => by simp [sixA, hk, l]
      have hd := dJ_eq_zero_of_common_zero (fun i m => φ (qC i m)) R hR hz l
      rw [← qev_coeffs_dJ, coeffs_dJ_map φ qC l, qev_eq_sum_veronese] at hd
      simpa [hs, coeffs_dJ_qC] using hd
  have hcS : φ (zkO cSL) ≠ 0 := fun h0 =>
    cS_not_mem v hv (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hV : veronese R = 0 := by
    funext j
    have e1 : ∀ m : Fin 6, ∑ k : Fin 6, φ (zkO (nA j k)) * φ (zkO (sixA k m)) =
        if j = m then φ (zkO cSL) else 0 := by
      intro m
      have := congrArg φ (sum_N_six j m)
      rw [map_sum] at this
      simp only [map_mul] at this
      rw [this]
      split_ifs <;> simp
    have key : φ (zkO cSL) * veronese R j = 0 := by
      calc φ (zkO cSL) * veronese R j
          = ∑ m : Fin 6, (∑ k : Fin 6, φ (zkO (nA j k)) * φ (zkO (sixA k m))) * veronese R m := by
            simp only [e1, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        _ = ∑ k : Fin 6, φ (zkO (nA j k)) * ∑ m : Fin 6, φ (zkO (sixA k m)) * veronese R m := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            simp only [mul_assoc]
        _ = 0 := by simp [hrow]
    simpa using (mul_eq_zero.mp key).resolve_left hcS
  exact veronese_ne_zero R hR hV

/-- **The descent class is in `K21(S, 2)`**: for a primitive integer point of `C` and `i = 0` or
`i = 2`, the class of `Q_(i+1)(a)` (a unit `u`) is in the Selmer group. -/
theorem mem_selmer_of_qO (a r : Fin 3 → ℤ) (hr : ∑ j, r j * a j = 1)
    (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0) (i : Fin 3) (hi : i = 0 ∨ i = 2) (u : K21ˣ)
    (hu : (u : K21) = (qO i a : K21)) :
    (QuotientGroup.mk u : SqClass K21) ∈ selmerGroup (K := K21) (S := S) (n := 2) := by
  apply mk_mem_selmerGroup_two S u
  intro v hv
  have hb := bruin_point a hF
  have hnot : ¬ (qO 0 a ∈ v.asIdeal ∧ qO 2 a ∈ v.asIdeal) := by
    rintro ⟨h0, h2⟩
    have h1 : qO 1 a ∈ v.asIdeal := by
      have : qO 1 a ^ 2 ∈ v.asIdeal := hb ▸ v.asIdeal.mul_mem_right _ h0
      exact v.isPrime.mem_of_pow_mem 2 this
    refine not_all_mem v hv a r hr fun k => ?_
    fin_cases k
    exacts [h0, h1, h2]
  have hb' : (qO 0 a : K21) * (qO 2 a : K21) = (qO 1 a : K21) ^ 2 := by
    rw [← map_mul, hb, map_pow]
  rw [hu]
  rcases hi with rfl | rfl
  · by_cases h0 : qO 0 a ∈ v.asIdeal
    · have h2 : qO 2 a ∉ v.asIdeal := fun h2 => hnot ⟨h0, h2⟩
      exact ⟨qO 2 a, qO 1 a, h2, hb'⟩
    · exact ⟨qO 0 a, qO 0 a, h0, by ring⟩
  · by_cases h2 : qO 2 a ∈ v.asIdeal
    · have h0 : qO 0 a ∉ v.asIdeal := fun h0 => hnot ⟨h0, h2⟩
      exact ⟨qO 0 a, qO 1 a, h0, by rw [mul_comm]; exact hb'⟩
    · exact ⟨qO 2 a, qO 2 a, h2, by ring⟩

/-! ## The generators -/

theorem gO_ne_zero (i : ℕ) (hi : i < 18) : gO i ≠ 0 := by
  intro h0
  by_cases h12 : i < 12
  · have := gO_mul_gIO i h12
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  · have key : ∀ j (hj : j < 6), gO (primeIdx.getD j 0) ≠ 0 := by
      intro j hj hz
      have := gO_mul_cO j hj
      rw [hz, zero_mul] at this
      interval_cases j <;> simp [primeOf] at this
    interval_cases i
    exacts [key 0 (by norm_num) h0, key 1 (by norm_num) h0, key 2 (by norm_num) h0,
      key 3 (by norm_num) h0, key 4 (by norm_num) h0, key 5 (by norm_num) h0]

/-- The eighteen generators as units of `K21`. -/
noncomputable def gU (i : Fin 18) : K21ˣ :=
  Units.mk0 (gO i : K21) (by
    rw [Ne, RingOfIntegers.coe_eq_zero_iff]
    exact gO_ne_zero i i.isLt)

theorem gU_mem (i : Fin 18) :
    (QuotientGroup.mk (gU i) : SqClass K21) ∈ selmerGroup (K := K21) (S := S) (n := 2) := by
  apply mk_mem_selmerGroup_two S (gU i)
  intro v hv
  exact ⟨gO i, gO i, gO_not_mem v hv i i.isLt, by simp [gU, sq]⟩

end FurioLombardo.M1
