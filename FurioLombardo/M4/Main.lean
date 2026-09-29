import Mathlib
import FurioLombardo.M4.QCert

/-!
# The assembly of the local inputs at v: centres, constant boxes and tails
-/


open FurioLombardo.M4

variable {V : Type*} [AddCommGroup V] [Module ℤ_[2] V]

theorem FurioLombardo.M4.projO_apply (UG : Matrix (Fin 6) (Fin 6) ℤ) (x : Fin 6 → ℤ_[2]) (i : Fin 4) :
    projO UG x i = imv UG x ⟨i.val + 2, by omega⟩ := by
  rfl

theorem FurioLombardo.M4.dvdV_icast {n B : ℕ} {c : Fin n → ℤ} (h : ∀ i, (2 : ℤ) ^ B ∣ c i) : DvdV B (icast c) := by
  intro i
  have hi := h i
  have hdvd := map_dvd (Int.castRingHom ℤ_[2]) hi
  simpa [DvdV, icast, map_pow] using hdvd

theorem FurioLombardo.M4.dvdV_imv {m n B : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) {x : Fin n → ℤ_[2]} (h : DvdV B x) : DvdV B (imv A x) := by
  intro i
  simp only [imv, Matrix.mulVec_apply, dotProduct]
  apply Finset.dvd_sum
  intro j hj
  have hx := h j
  exact Dvd.dvd.mul_left hx (A i j : ℤ_[2])

theorem FurioLombardo.M4.dvdV_cancel {d B k : ℕ} {x : Fin d → ℤ_[2]} (h : DvdV (B + k) ((2 : ℤ_[2]) ^ k • x)) : DvdV B x := by
  intro i
  have hi := h i
  rw [Pi.smul_apply, smul_eq_mul] at hi
  rw [pow_add] at hi
  rw [mul_comm ((2 : ℤ_[2]) ^ B)] at hi
  have hpow_ne_zero : (2 : ℤ_[2]) ^ k ≠ 0 := pow_ne_zero k two_ne_zero
  rwa [mul_dvd_mul_iff_left hpow_ne_zero] at hi

theorem FurioLombardo.M4.condIII_neg {Λ S : Submodule ℤ_[2] V} {W : Set V} {y : V} (hy : CondIII Λ S W y) : CondIII Λ S W (-y) := by
  intro n z w hz hw hnegS hInSL
  rcases hInSL with ⟨s, hs, l, hl, he⟩
  -- he: z - w = s + (2 : ℤ_[2]) ^ 1 • l
  have he' : z - w = s + (2 : ℤ_[2]) • l := by simpa [pow_one] using he
  have hyz : y - (2 : ℤ_[2]) ^ n • (-z) ∈ S := by
    have h1 : (-y) - (2 : ℤ_[2]) ^ n • z = -(y + (2 : ℤ_[2]) ^ n • z) := by
      abel
    have h2 : y - (2 : ℤ_[2]) ^ n • (-z) = y + (2 : ℤ_[2]) ^ n • z := by
      simp [smul_neg]
    rw [h2]
    have hneg : -(y + (2 : ℤ_[2]) ^ n • z) ∈ S := by
      rw [← h1]
      exact hnegS
    simpa [neg_neg] using S.neg_mem hneg
  have hInSLneg : InSL Λ S 1 (-z - w) := by
    -- -z - w = (z - w) - 2•z = s + 2•l - 2•z = s + 2•(l - z)
    have hcalc : -z - w = s + (2 : ℤ_[2]) • (l - z) := by
      calc
        -z - w = (z - w) - (2 : ℤ_[2]) • z := by
          simp [two_smul, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
        _ = (s + (2 : ℤ_[2]) • l) - (2 : ℤ_[2]) • z := by rw [he']
        _ = s + ((2 : ℤ_[2]) • l - (2 : ℤ_[2]) • z) := by abel
        _ = s + (2 : ℤ_[2]) • (l - z) := by rw [smul_sub]
    refine ⟨s, hs, l - z, Submodule.sub_mem Λ hl hz, ?_⟩
    simpa using hcalc
  have hnegz : InSL Λ S 1 (-z) := hy n (-z) w (Submodule.neg_mem Λ hz) hw hyz hInSLneg
  rcases hnegz with ⟨s', hs', l', hl', he'⟩
  -- he': -z = s' + (2 : ℤ_[2]) ^ 1 • l'
  have he'' : -z = s' + (2 : ℤ_[2]) • l' := by simpa [pow_one] using he'
  have hcalc2 : z = (-s') + (2 : ℤ_[2]) • (-l') := by
    calc
      z = -(-z) := by simp
      _ = -(s' + (2 : ℤ_[2]) • l') := by rw [he'']
      _ = (-s') + (2 : ℤ_[2]) • (-l') := by
        simp [smul_neg, add_comm]
  exact ⟨-s', S.neg_mem hs', -l', Submodule.neg_mem Λ hl', hcalc2⟩

theorem FurioLombardo.M4.leading_neg {Λ S : Submodule ℤ_[2] V} {W : Set V} {ν : ℕ} {y : V} (hy : Leading Λ S W ν y) :
    Leading Λ S W ν (-y) := by
  rcases hy with ⟨s0, hs0, z0, hz0, l, hl, hy_eq, hz0_not, hz0_w⟩
  have hneg : -y = (-s0) + (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • (-(l + z0)) := by
    rw [hy_eq]
    simp [add_comm, add_assoc, smul_neg, smul_add, mul_smul, two_smul, pow_succ]
  refine ⟨-s0, Submodule.neg_mem _ hs0, z0, hz0, -(l + z0), Submodule.neg_mem _ (Submodule.add_mem _ hl hz0), hneg, hz0_not, hz0_w⟩

theorem FurioLombardo.M4.mem_boxesOf {ex : List (ℕ × ℕ × ℕ)} {cb : List CBox} {tb : List TBox} {d : ℕ} {p : ℕ × ℕ}
    (h : p ∈ boxesOf ex cb tb d) :
    (∃ e ∈ ex, e.1 = d ∧ p = (e.2.1, e.2.2)) ∨ (∃ b ∈ cb, b.disc = d ∧ p = (b.c, b.s)) ∨
      (∃ b ∈ tb, b.disc = d ∧ p = (b.c, b.s)) := by
  rw [boxesOf] at h
  simp only [List.mem_append] at h
  rcases h with (h | h)
  · rcases h with (h | h)
    · -- h : p ∈ map (fun e => (e.2.1, e.2.2)) (filter (fun e => e.1 == d) ex)
      rw [List.mem_map] at h
      simp only [List.mem_filter, beq_iff_eq] at h
      rcases h with ⟨e, ⟨he, hd⟩, hp⟩
      exact Or.inl ⟨e, he, hd, hp.symm⟩
    · -- h : p ∈ map (fun b => (b.c, b.s)) (filter (fun b => b.disc == d) cb)
      rw [List.mem_map] at h
      simp only [List.mem_filter, beq_iff_eq] at h
      rcases h with ⟨b, ⟨hb, hd⟩, hp⟩
      exact Or.inr (Or.inl ⟨b, hb, hd, hp.symm⟩)
  · -- h : p ∈ map (fun b => (b.c, b.s)) (filter (fun b => b.disc == d) tb)
    rw [List.mem_map] at h
    simp only [List.mem_filter, beq_iff_eq] at h
    rcases h with ⟨b, ⟨hb, hd⟩, hp⟩
    exact Or.inr (Or.inr ⟨b, hb, hd, hp.symm⟩)

theorem FurioLombardo.M4.condIII_of_mem {Λ S : Submodule ℤ_[2] V} {W : Set V} {y : V} (hS : Saturated Λ S) (hy : y ∈ S) : CondIII Λ S W y := by
  intro n z w hz hw h hInSL
  have h2zS : (2 : ℤ_[2]) ^ n • z ∈ S := by
    have := Submodule.sub_mem S hy h
    simpa [sub_sub_cancel] using this
  have hzS : z ∈ S := sat_two_pow hS n hz h2zS
  refine ⟨z, hzS, 0, Submodule.zero_mem Λ, ?_⟩
  simp

theorem FurioLombardo.M4.det_approx {a b : Fin 6 → ℤ_[2]} {la lb : Fin 6 → ℤ} {qa qb : ℕ} (UG : Matrix (Fin 6) (Fin 6) ℤ)
    (ha : DvdV qa (a - icast la)) (hb : DvdV qb (b - icast lb)) {Del : ℤ}
    (hDel : UG.mulVec la 0 * UG.mulVec lb 1 - UG.mulVec la 1 * UG.mulVec lb 0 = Del) :
    (2 : ℤ_[2]) ^ min qa qb ∣ (imv UG a 0 * imv UG b 1 - imv UG a 1 * imv UG b 0) - (Del : ℤ_[2]) := by
  set q := min qa qb
  have hq_qa : q ≤ qa := min_le_left _ _
  have hq_qb : q ≤ qb := min_le_right _ _
  have hq_pow_qa : (2 : ℤ_[2]) ^ q ∣ (2 : ℤ_[2]) ^ qa :=
    pow_dvd_pow (2 : ℤ_[2]) hq_qa
  have hq_pow_qb : (2 : ℤ_[2]) ^ q ∣ (2 : ℤ_[2]) ^ qb :=
    pow_dvd_pow (2 : ℤ_[2]) hq_qb
  set A := imv UG a
  set A' := icast (UG.mulVec la)
  set B := imv UG b
  set B' := icast (UG.mulVec lb)
  have hA_sub_A' : A - A' = imv UG (a - icast la) := by
    calc
      A - A' = imv UG a - icast (UG.mulVec la) := rfl
      _ = imv UG a - imv UG (icast la) := by rw [imv_icast]
      _ = imv UG (a - icast la) := by rw [imv_sub]
  have hB_sub_B' : B - B' = imv UG (b - icast lb) := by
    calc
      B - B' = imv UG b - icast (UG.mulVec lb) := rfl
      _ = imv UG b - imv UG (icast lb) := by rw [imv_icast]
      _ = imv UG (b - icast lb) := by rw [imv_sub]
  have hA_sub_A'_dvd : DvdV qa (A - A') := by
    rw [hA_sub_A']
    intro i
    unfold imv
    simp [Matrix.mulVec_apply, dotProduct]
    apply Finset.dvd_sum
    intro j _
    have haj := ha j
    exact dvd_mul_of_dvd_right haj _
  have hB_sub_B'_dvd : DvdV qb (B - B') := by
    rw [hB_sub_B']
    intro i
    unfold imv
    simp [Matrix.mulVec_apply, dotProduct]
    apply Finset.dvd_sum
    intro j _
    have haj := hb j
    exact dvd_mul_of_dvd_right haj _
  have hA_sub_A'_dvd_q : DvdV q (A - A') := by
    intro i
    have hi := hA_sub_A'_dvd i
    exact dvd_trans hq_pow_qa hi
  have hB_sub_B'_dvd_q : DvdV q (B - B') := by
    intro i
    have hi := hB_sub_B'_dvd i
    exact dvd_trans hq_pow_qb hi
  have hDel_cast : (Del : ℤ_[2]) = A' 0 * B' 1 - A' 1 * B' 0 := by
    calc
      (Del : ℤ_[2]) = ((UG.mulVec la 0 * UG.mulVec lb 1 - UG.mulVec la 1 * UG.mulVec lb 0 : ℤ) : ℤ_[2]) := by
        rw [hDel]
      _ = (UG.mulVec la 0 : ℤ_[2]) * (UG.mulVec lb 1 : ℤ_[2]) - (UG.mulVec la 1 : ℤ_[2]) * (UG.mulVec lb 0 : ℤ_[2]) := by
        simp
      _ = A' 0 * B' 1 - A' 1 * B' 0 := by
        simp [A', B', icast]
  rw [hDel_cast]
  have hgoal : (A 0 * B 1 - A 1 * B 0) - (A' 0 * B' 1 - A' 1 * B' 0) =
      ((A 0 - A' 0) * B 1 + A' 0 * (B 1 - B' 1)) - ((A 1 - A' 1) * B 0 + A' 1 * (B 0 - B' 0)) := by
    ring
  rw [hgoal]
  apply dvd_sub
  · apply dvd_add
    · have hdvd : (2 : ℤ_[2]) ^ q ∣ A 0 - A' 0 := hA_sub_A'_dvd_q 0
      exact dvd_mul_of_dvd_left hdvd _
    · have hdvd : (2 : ℤ_[2]) ^ q ∣ B 1 - B' 1 := hB_sub_B'_dvd_q 1
      exact dvd_mul_of_dvd_right hdvd _
  · apply dvd_add
    · have hdvd : (2 : ℤ_[2]) ^ q ∣ A 1 - A' 1 := hA_sub_A'_dvd_q 1
      exact dvd_mul_of_dvd_left hdvd _
    · have hdvd : (2 : ℤ_[2]) ^ q ∣ B 0 - B' 0 := hB_sub_B'_dvd_q 0
      exact dvd_mul_of_dvd_right hdvd _

theorem FurioLombardo.M4.dvdV_imv_six {N : ℕ} {v : Fin 6 → ℤ_[2]} (h : DvdV N v) (G : Matrix (Fin 6) (Fin 6) ℤ) (j : Fin 6) :
    (2 : ℤ_[2]) ^ N ∣ imv G v j := by
  unfold imv
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.dvd_sum
  intro k _
  have hk := h k
  exact dvd_mul_of_dvd_right hk _

theorem FurioLombardo.M4.four_dvd_imv_of_mem {Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} (ℓ : Fin 7 → Fin 6 → ℤ_[2])
    (hΛ : Λ = Submodule.span ℤ_[2] (Set.range ℓ)) (l : Fin 7 → Fin 6 → ℤ)
    (hl : ∀ i, DvdV 2 (ℓ i - icast (l i))) (G : Matrix (Fin 6) (Fin 6) ℤ)
    (hGl : ∀ (i : Fin 7) (j : Fin 6), (4 : ℤ) ∣ G.mulVec (l i) j) {x : Fin 6 → ℤ_[2]} (hx : x ∈ Λ)
    (j : Fin 6) : (4 : ℤ_[2]) ∣ imv G x j := by
  have hsq : (2 : ℤ_[2]) ^ 2 = (4 : ℤ_[2]) := by norm_num
  have h_span := dvd_imv_of_mem_span ℓ hΛ G 2 ?_ hx j
  · simpa [hsq] using h_span
  · intro i k
    have h_decomp : ℓ i = icast (l i) + (ℓ i - icast (l i)) := by
      simp
    rw [h_decomp, imv_add]
    have h_first : (4 : ℤ_[2]) ∣ imv G (icast (l i)) k := by
      rw [imv_icast]
      dsimp [icast]
      exact map_dvd (Int.castRingHom ℤ_[2]) (hGl i k)
    have h_second : (4 : ℤ_[2]) ∣ imv G (ℓ i - icast (l i)) k := by
      have h_dvdV : DvdV 2 (ℓ i - icast (l i)) := hl i
      have h := dvdV_imv_six h_dvdV G k
      simpa [hsq] using h
    have h_sum : (4 : ℤ_[2]) ∣ imv G (icast (l i)) k + imv G (ℓ i - icast (l i)) k :=
      dvd_add h_first h_second
    simpa [hsq] using h_sum

theorem FurioLombardo.M4.dvdV_of_succ_smul {d B n : ℕ} {a : Fin d → ℤ_[2]} (h : DvdV (B + n) (((n : ℤ_[2]) + 1) • a)) : DvdV B a := by
  have h' : DvdV (B + n) ((2 : ℤ_[2]) ^ n • a) := dvdV_two_pow_smul h
  intro i
  have hi := h' i
  simp [Pi.smul_apply] at hi
  rw [pow_add] at hi
  have h2n : (2 : ℤ_[2]) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℤ_[2]) ≠ 0)
  rw [mul_comm ((2 : ℤ_[2]) ^ B) ((2 : ℤ_[2]) ^ n)] at hi
  rwa [mul_dvd_mul_iff_left h2n] at hi

theorem FurioLombardo.M4.lip_sharp {d B : ℕ} {α : ℕ → Fin d → ℤ_[2]} {D : Fin d → ℤ_[2]} (Y : ℤ_[2])
    (ha : ∀ n : ℕ, DvdV (B + n) (((n : ℤ_[2]) + 1) • α n))
    (hD : HasSum (fun n => Y ^ (n + 1) • α n) D) : DvdV B D := by
  refine dvdV_of_hasSum ?hf hD
  intro n
  apply dvdV_smul (Y ^ (n + 1))
  have hsucc := succ_dvd_two_pow n
  rcases hsucc with ⟨k, hk⟩
  -- hk : (2 : ℤ_[2]) ^ n = ((n : ℤ_[2]) + 1) * k
  have hdvd : DvdV B (α n) := by
    intro i
    have hi := (ha n) i
    rcases hi with ⟨t, ht⟩
    -- ht : ((n : ℤ_[2]) + 1) * α n i = 2 ^ (B + n) * t
    have h_eq : ((n : ℤ_[2]) + 1) * α n i = ((n : ℤ_[2]) + 1) * ((2 : ℤ_[2]) ^ B * (k * t)) := by
      calc
        ((n : ℤ_[2]) + 1) * α n i = (2 : ℤ_[2]) ^ (B + n) * t := ht
        _ = ((2 : ℤ_[2]) ^ B * ((2 : ℤ_[2]) ^ n)) * t := by rw [pow_add]
        _ = ((2 : ℤ_[2]) ^ B * (((n : ℤ_[2]) + 1) * k)) * t := by rw [hk]
        _ = ((n : ℤ_[2]) + 1) * ((2 : ℤ_[2]) ^ B * (k * t)) := by ring
    have hnz : ((n : ℤ_[2]) + 1) ≠ 0 := by
      simpa using Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have h_cancel := mul_left_cancel₀ hnz h_eq
    -- h_cancel : α n i = (2 : ℤ_[2]) ^ B * (k * t)
    exact ⟨k * t, h_cancel⟩
  exact hdvd

theorem FurioLombardo.M4.centre_leading {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {UG : Matrix (Fin 6) (Fin 6) ℤ} {W : Fin 16 → Fin 6 → ℤ}
    {r ν q : ℕ} (hQ : QChar Λ S (projO UG) r) (hν : ν + 1 ≤ r) (hq : ν + 3 ≤ q) {y : Fin 6 → ℤ}
    (hok : ClassOK UG W ν y) {lc : Fin 6 → ℤ_[2]} (hlc : lc ∈ Λ) (hball : DvdV q (lc - icast y)) :
    Leading Λ S (Wset W) ν lc := by
  rcases exists_eq_two_pow_smul hball with ⟨t, ht⟩
  have hc : lc = icast y + (2 : ℤ_[2]) ^ q • t := by
    calc
      lc = icast y + (lc - icast y) := by rw [add_comm, sub_add_cancel]
      _ = icast y + (2 : ℤ_[2]) ^ q • t := by rw [ht]
  rcases hok with ⟨h1', h2', h3'⟩
  have hQval_y (i : Fin 4) : projO UG (icast y) i = (UG.mulVec y ⟨i.val + 2, by omega⟩ : ℤ_[2]) := by
    calc
      projO UG (icast y) i = imv UG (icast y) ⟨i.val + 2, by omega⟩ := rfl
      _ = icast (UG.mulVec y) ⟨i.val + 2, by omega⟩ := by rw [imv_icast]
      _ = (UG.mulVec y ⟨i.val + 2, by omega⟩ : ℤ_[2]) := rfl
  have h1 : ∀ i, (2 : ℤ_[2]) ^ (ν + 2) ∣ projO UG (icast y) i := by
    intro i
    have hi : 2 ≤ i.val + 2 := by omega
    have h := h1' ⟨i.val + 2, by omega⟩ (by simpa using hi)
    rw [hQval_y i]
    exact (intCast_two_pow_dvd_iff (ν + 2) (UG.mulVec y ⟨i.val + 2, by omega⟩)).mpr h
  have h2 : ∃ i, ¬ (2 : ℤ_[2]) ^ (ν + 3) ∣ projO UG (icast y) i := by
    rcases h2' with ⟨o, ho, hnot⟩
    set i : Fin 4 := ⟨o.val - 2, by omega⟩ with hi_def
    refine ⟨i, ?_⟩
    have hQval : projO UG (icast y) i = (UG.mulVec y o : ℤ_[2]) := by
      rw [hQval_y i]
      have h_eq : (⟨i.val + 2, by omega⟩ : Fin 6) = o := by
        apply Fin.ext
        dsimp [i]
        omega
      rw [h_eq]
    rw [hQval]
    rw [intCast_two_pow_dvd_iff]
    exact hnot
  have h3 : ∀ w ∈ Wset W, ∃ i, ¬ (2 : ℤ_[2]) ^ (ν + 3) ∣ projO UG (icast y) i - (2 : ℤ_[2]) ^ ν * projO UG w i := by
    intro w hw
    rcases hw with ⟨m, rfl⟩
    rcases h3' m with ⟨o, ho, hnot⟩
    set i : Fin 4 := ⟨o.val - 2, by omega⟩ with hi_def
    refine ⟨i, ?_⟩
    have hQval_y : projO UG (icast y) i = (UG.mulVec y o : ℤ_[2]) := by
      rw [hQval_y i]
      have h_eq : (⟨i.val + 2, by omega⟩ : Fin 6) = o := by
        apply Fin.ext
        dsimp [i]
        omega
      rw [h_eq]
    have hQval_w : projO UG (icast (W m)) i = (UG.mulVec (W m) o : ℤ_[2]) := by
      calc
        projO UG (icast (W m)) i = imv UG (icast (W m)) ⟨i.val + 2, by omega⟩ := rfl
        _ = icast (UG.mulVec (W m)) ⟨i.val + 2, by omega⟩ := by rw [imv_icast]
        _ = icast (UG.mulVec (W m)) o := by
          have h_eq : (⟨i.val + 2, by omega⟩ : Fin 6) = o := by
            apply Fin.ext
            dsimp [i]
            omega
          rw [h_eq]
        _ = (UG.mulVec (W m) o : ℤ_[2]) := rfl
    rw [hQval_y, hQval_w]
    have hcast : (UG.mulVec y o : ℤ_[2]) - (2 : ℤ_[2]) ^ ν * (UG.mulVec (W m) o : ℤ_[2]) =
                ((UG.mulVec y o - (2 : ℤ) ^ ν * UG.mulVec (W m) o : ℤ) : ℤ_[2]) := by
      simp
    rw [hcast]
    rw [intCast_two_pow_dvd_iff]
    exact hnot
  exact leading_of_Q_approx hQ hν hq hlc hc h1 h2 h3

theorem FurioLombardo.M4.const_box_leading {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {W : Set (Fin 6 → ℤ_[2])}
    (h4 : ∀ x, DvdV 2 x → x ∈ Λ) {ν B : ℕ} {lc : Fin 6 → ℤ_[2]} (hlead : Leading Λ S W ν lc)
    (hB : B = ν + 3) {α : ℕ → Fin 6 → ℤ_[2]} (ha : ∀ n : ℕ, DvdV (B + n) (((n : ℤ_[2]) + 1) • α n))
    {Y : ℤ_[2]} {lX : Fin 6 → ℤ_[2]} (hs : HasSum (fun n => Y ^ (n + 1) • α n) (lX - lc)) :
    Leading Λ S W ν lX := by
  -- First, deduce DvdV B (α n) for all n using ha and succ_dvd_two_pow
  have h_alpha : ∀ n, DvdV B (α n) := by
    intro n
    intro i
    have h := ha n i
    have h_succ : ((n : ℤ_[2]) + 1) ∣ (2 : ℤ_[2]) ^ n := succ_dvd_two_pow n
    rcases h_succ with ⟨k, hk⟩
    have h_pow_add : (2 : ℤ_[2]) ^ (B + n) = (2 : ℤ_[2]) ^ B * (2 : ℤ_[2]) ^ n := by
      rw [pow_add]
    rw [h_pow_add, hk] at h
    have h' : ((n : ℤ_[2]) + 1) * ((2 : ℤ_[2]) ^ B * k) ∣ ((n : ℤ_[2]) + 1) * (α n i) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using h
    have h_nonzero : ((n : ℤ_[2]) + 1) ≠ 0 := by
      have : ((n : ℤ_[2]) + 1) = ((n + 1 : ℕ) : ℤ_[2]) := by simp
      rw [this]
      exact Nat.cast_ne_zero.mpr (by omega)
    have h_cancel : (2 : ℤ_[2]) ^ B * k ∣ α n i :=
      (mul_dvd_mul_iff_left h_nonzero).mp h'
    exact (dvd_mul_right ((2 : ℤ_[2]) ^ B) k).trans h_cancel
  -- Each term Y^(n+1) • α n is DvdV B
  have h_terms : ∀ n, DvdV B (Y ^ (n + 1) • α n) := by
    intro n
    apply dvdV_smul (Y ^ (n + 1)) (h_alpha n)
  -- Hence the sum is DvdV B
  have hlip : DvdV B (lX - lc) := dvdV_of_hasSum h_terms hs
  -- B = ν + 3 = 2 + (ν + 1)
  have hB_eq : B = 2 + (ν + 1) := by
    omega
  -- So DvdV (2 + (ν + 1)) (lX - lc)
  have hlip' : DvdV (2 + (ν + 1)) (lX - lc) := by
    rw [← hB_eq]
    exact hlip
  -- Apply mem_of_dvdV to get l ∈ Λ with lX - lc = 2^(ν+1) • l
  rcases mem_of_dvdV h4 hlip' with ⟨l, hl, heq⟩
  -- Conclude with leading_perturb
  exact leading_perturb hlead hl heq

theorem FurioLombardo.M4.tail_sharp {d B t : ℕ} {α : ℕ → Fin d → ℤ_[2]} {D : Fin d → ℤ_[2]} (Z : ℤ_[2])
    (ha : ∀ n : ℕ, 1 ≤ n → DvdV (B + n) (((n : ℤ_[2]) + 1) • α n))
    (hD : HasSum (fun n => ((2 : ℤ_[2]) ^ t * Z) ^ (n + 1) • α n) D) :
    DvdV (B + 2 * t) (D - ((2 : ℤ_[2]) ^ t * Z) • α 0) := by
  set f := fun n : ℕ => ((2 : ℤ_[2]) ^ t * Z) ^ (n + 1) • α n with hf
  have hf0 : f 0 = ((2 : ℤ_[2]) ^ t * Z) • α 0 := by
    simp [f, pow_one]
  have hsum : HasSum (fun n => if n = 0 then 0 else f n) (D - f 0) := by
    have h0 : HasSum (fun n => if n = 0 then f 0 else 0) (f 0) := hasSum_ite_eq 0 (f 0)
    have hsub := hD.sub h0
    have heq : (fun n => f n - (if n = 0 then f 0 else 0)) = (fun n => if n = 0 then 0 else f n) := by
      ext n
      by_cases h : n = 0
      · subst h; simp
      · simp [h]
    simpa [heq] using hsub
  have hterms : ∀ n, DvdV (B + 2 * t) (if n = 0 then 0 else f n) := by
    intro n
    split_ifs with hn
    · -- n = 0
      intro i; simp
    · -- n ≥ 1
      have hn1 : 1 ≤ n := by omega
      have hdvd_pow : DvdV (B + n) ((2 : ℤ_[2]) ^ n • α n) :=
        dvdV_two_pow_smul (ha n hn1)
      -- hdvd_pow i : 2^(B+n) ∣ 2^n * α n i
      -- 2^(B+n) = 2^B * 2^n, so 2^B * 2^n ∣ 2^n * α n i
      -- cancel 2^n to get 2^B ∣ α n i
      have halpha : DvdV B (α n) := by
        intro i
        have hdvd := hdvd_pow i
        rw [pow_add] at hdvd
        -- hdvd : (2^B * 2^n) ∣ 2^n * α n i
        rw [mul_comm ((2 : ℤ_[2]) ^ B) ((2 : ℤ_[2]) ^ n)] at hdvd
        -- hdvd : (2^n * 2^B) ∣ 2^n * α n i
        have h2n : (2 : ℤ_[2]) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℤ_[2]) ≠ 0)
        exact (mul_dvd_mul_iff_left h2n).mp hdvd
      have hineq : 2 * t ≤ t * (n + 1) := by
        have hn' : 2 ≤ n + 1 := by omega
        nlinarith
      have h4 : DvdV (B + (t * (n + 1))) ((2 : ℤ_[2]) ^ (t * (n + 1)) • α n) :=
        dvdV_two_pow_smul_add halpha
      have h5 : DvdV (B + (t * (n + 1))) (((2 : ℤ_[2]) ^ t * Z) ^ (n + 1) • α n) := by
        have := dvdV_smul (Z ^ (n + 1)) h4
        simpa [mul_pow, pow_mul, smul_smul, mul_comm] using this
      have hineq' : B + 2 * t ≤ B + (t * (n + 1)) := Nat.add_le_add_left hineq B
      exact dvdV_mono hineq' h5
  have hresult : DvdV (B + 2 * t) (D - f 0) := dvdV_of_hasSum hterms hsum
  simpa [hf0] using hresult

theorem FurioLombardo.M4.tail_leading {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {W : Set (Fin 6 → ℤ_[2])} (hS : Saturated Λ S)
    (h4 : ∀ x, DvdV 2 x → x ∈ Λ) {ν B s0 t : ℕ} (hs0 : 1 ≤ s0) (ht : ν + 2 + s0 ≤ B + t)
    {g yi : Fin 6 → ℤ_[2]} (hg : Leading Λ S W ν g) (hyi : yi ∈ S) {α : ℕ → Fin 6 → ℤ_[2]}
    (ha : ∀ n : ℕ, DvdV (B + n) (((n : ℤ_[2]) + 1) • α n)) (ha0 : α 0 = (2 : ℤ_[2]) ^ (s0 - 1) • g)
    {u : ℤ_[2]} (hu : IsUnit u) {lX : Fin 6 → ℤ_[2]}
    (hs : HasSum (fun n => ((2 : ℤ_[2]) ^ t * u) ^ (n + 1) • α n) (lX - yi)) :
    Leading Λ S W (ν + (t + s0 - 1)) lX := by
  set j := t + s0 - 1 with hj
  have h1 : DvdV (B + 2 * t) (lX - yi - ((2 : ℤ_[2]) ^ t * u) • α 0) :=
    tail_sharp u (fun n _ => ha n) hs
  have h2 : DvdV (2 + (ν + j + 1)) (lX - yi - ((2 : ℤ_[2]) ^ t * u) • α 0) :=
    dvdV_mono (by omega) h1
  obtain ⟨l, hl, hle⟩ := mem_of_dvdV h4 h2
  have hpow : ((2 : ℤ_[2]) ^ t * u) • α 0 = (2 : ℤ_[2]) ^ j • (u • g) := by
    rw [ha0, smul_smul, smul_smul, hj, show t + s0 - 1 = t + (s0 - 1) by omega, pow_add]
    congr 1
    ring
  obtain ⟨w, hw⟩ := unit_eq_one_add_two hu
  have hlX : lX = yi + (2 : ℤ_[2]) ^ j • (u • g) + (2 : ℤ_[2]) ^ (ν + j + 1) • l := by
    rw [← hpow, ← hle]; abel
  rw [hlX]
  exact leading_tail hS hg hyi u w hw hl
