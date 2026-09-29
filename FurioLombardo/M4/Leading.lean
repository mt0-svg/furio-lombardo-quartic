import Mathlib
import FurioLombardo.M4.Boxes

/-!
# Leading level and class modulo a saturated submodule (condition (iii))
-/


open FurioLombardo.M4

variable {V : Type*} [AddCommGroup V] [Module ℤ_[2] V]

theorem FurioLombardo.M4.sat_two_pow {Λ S : Submodule ℤ_[2] V} (hS : Saturated Λ S) (n : ℕ) {x : V} (hx : x ∈ Λ)
    (h : (2 : ℤ_[2]) ^ n • x ∈ S) : x ∈ S := by
  induction' n with n ih generalizing x
  · -- n = 0: (2^0) • x = 1 • x = x
    simpa using h
  · -- n+1: (2^(n+1)) • x = 2^n • (2 • x)
    have hpow : (2 : ℤ_[2]) ^ (n + 1) • x = (2 : ℤ_[2]) ^ n • ((2 : ℤ_[2]) • x) := by
      calc
        (2 : ℤ_[2]) ^ (n + 1) • x = ((2 : ℤ_[2]) ^ n * (2 : ℤ_[2])) • x := by rw [pow_succ]
        _ = (2 : ℤ_[2]) ^ n • ((2 : ℤ_[2]) • x) := by rw [mul_smul]
    rw [hpow] at h
    have h2x : (2 : ℤ_[2]) • x ∈ Λ := Λ.smul_mem (2 : ℤ_[2]) hx
    have h2xS : (2 : ℤ_[2]) • x ∈ S := ih h2x h
    exact hS.2 x hx h2xS

theorem FurioLombardo.M4.leading_add {Λ S : Submodule ℤ_[2] V} {W : Set V} {ν : ℕ} {y t : V} (hy : Leading Λ S W ν y)
    (ht : t ∈ Λ) : Leading Λ S W ν (y + (2 : ℤ_[2]) ^ (ν + 1) • t) := by
  rcases hy with ⟨s0, hs0, z0, hz0, l, hl, hy_eq, hz0_not, hw_not⟩
  refine ⟨s0, hs0, z0, hz0, l + t, Submodule.add_mem Λ hl ht, ?_, hz0_not, hw_not⟩
  rw [hy_eq]
  calc
    (s0 + (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • l) + (2 : ℤ_[2]) ^ (ν + 1) • t
        = s0 + (2 : ℤ_[2]) ^ ν • z0 + ((2 : ℤ_[2]) ^ (ν + 1) • l + (2 : ℤ_[2]) ^ (ν + 1) • t) := by abel
    _ = s0 + (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • (l + t) := by rw [smul_add]

theorem FurioLombardo.M4.leading_add_mem {Λ S : Submodule ℤ_[2] V} {W : Set V} {ν : ℕ} {y s : V} (hy : Leading Λ S W ν y)
    (hs : s ∈ S) : Leading Λ S W ν (y + s) := by
  rcases hy with ⟨s0, hs0, z0, hz0, l, hl, hy_eq, h_not_inSL, h_not_W⟩
  refine ⟨s0 + s, Submodule.add_mem _ hs0 hs, z0, hz0, l, hl, ?_, h_not_inSL, h_not_W⟩
  calc
    y + s = (s0 + (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • l) + s := by rw [hy_eq]
    _ = (s0 + s) + (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • l := by abel

theorem FurioLombardo.M4.leading_perturb {Λ S : Submodule ℤ_[2] V} {W : Set V} {ν : ℕ} {y y0 t : V} (hy0 : Leading Λ S W ν y0)
    (ht : t ∈ Λ) (h : y - y0 = (2 : ℤ_[2]) ^ (ν + 1) • t) : Leading Λ S W ν y := by
  rcases hy0 with ⟨s0, hs0, z0, hz0, l, hl, hy0_eq, h_not_inSL, h_not_inSL_w⟩
  have hy_eq : y = y0 + (2 : ℤ_[2]) ^ (ν + 1) • t := by
    calc
      y = (y - y0) + y0 := by abel
      _ = ((2 : ℤ_[2]) ^ (ν + 1) • t) + y0 := by rw [h]
      _ = y0 + (2 : ℤ_[2]) ^ (ν + 1) • t := by abel
  rw [hy0_eq] at hy_eq
  refine ⟨s0, hs0, z0, hz0, l + t, Submodule.add_mem Λ hl ht, ?_, h_not_inSL, h_not_inSL_w⟩
  calc
    y = (s0 + (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • l) + (2 : ℤ_[2]) ^ (ν + 1) • t := hy_eq
    _ = s0 + (2 : ℤ_[2]) ^ ν • z0 + ((2 : ℤ_[2]) ^ (ν + 1) • l + (2 : ℤ_[2]) ^ (ν + 1) • t) := by abel
    _ = s0 + (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • (l + t) := by rw [smul_add]

theorem FurioLombardo.M4.leading_smul_unit {Λ S : Submodule ℤ_[2] V} {W : Set V} {ν : ℕ} {y : V} (hS : Saturated Λ S)
    (hy : Leading Λ S W ν y) (u w : ℤ_[2]) (hu : u = 1 + 2 * w) : Leading Λ S W ν (u • y) := by
  rcases hy with ⟨s0, hs0, z0, hz0, l, hl, hy_eq, hz_not, hz_forall⟩
  refine ⟨u • s0, Submodule.smul_mem S u hs0, z0, hz0, w • z0 + u • l, ?_, ?_, hz_not, hz_forall⟩
  · have hwz : w • z0 ∈ Λ := Submodule.smul_mem Λ w hz0
    have hul : u • l ∈ Λ := Submodule.smul_mem Λ u hl
    exact Submodule.add_mem Λ hwz hul
  · rw [hy_eq]
    calc
      u • (s0 + (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • l) =
          u • s0 + u • ((2 : ℤ_[2]) ^ ν • z0) + u • ((2 : ℤ_[2]) ^ (ν + 1) • l) := by
        simp [smul_add]
      _ = u • s0 + (2 : ℤ_[2]) ^ ν • (u • z0) + (2 : ℤ_[2]) ^ (ν + 1) • (u • l) := by
        simp [smul_smul, mul_comm]
      _ = u • s0 + (2 : ℤ_[2]) ^ ν • ((1 + 2 * w) • z0) + (2 : ℤ_[2]) ^ (ν + 1) • (u • l) := by rw [hu]
      _ = u • s0 + (2 : ℤ_[2]) ^ ν • (z0 + (2 : ℤ_[2]) • (w • z0)) + (2 : ℤ_[2]) ^ (ν + 1) • (u • l) := by
        simp [add_smul, one_smul, mul_smul]
      _ = u • s0 + ((2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ ν • ((2 : ℤ_[2]) • (w • z0))) + (2 : ℤ_[2]) ^ (ν + 1) • (u • l) := by
        simp [smul_add]
      _ = u • s0 + ((2 : ℤ_[2]) ^ ν • z0 + ((2 : ℤ_[2]) ^ ν * (2 : ℤ_[2])) • (w • z0)) + (2 : ℤ_[2]) ^ (ν + 1) • (u • l) := by
        simp [smul_smul, mul_assoc]
      _ = u • s0 + ((2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • (w • z0)) + (2 : ℤ_[2]) ^ (ν + 1) • (u • l) := by
        simp [pow_succ]
      _ = u • s0 + (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • (w • z0 + u • l) := by
        simp [smul_add, add_assoc]

theorem FurioLombardo.M4.leading_two_pow_smul {Λ S : Submodule ℤ_[2] V} {W : Set V} {ν : ℕ} {y : V} (hy : Leading Λ S W ν y) (j : ℕ) :
    Leading Λ S W (ν + j) ((2 : ℤ_[2]) ^ j • y) := by
  rcases hy with ⟨s0, hs0, z0, hz0, l, hl, hy_eq, hz0_not, hz0w_not⟩
  have hs0' : (2 : ℤ_[2]) ^ j • s0 ∈ S := Submodule.smul_mem S (r := (2 : ℤ_[2]) ^ j) hs0
  refine ⟨(2 : ℤ_[2]) ^ j • s0, hs0', z0, hz0, l, hl, ?_, hz0_not, hz0w_not⟩
  calc
    (2 : ℤ_[2]) ^ j • y = (2 : ℤ_[2]) ^ j • (s0 + (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • l) := by rw [hy_eq]
    _ = (2 : ℤ_[2]) ^ j • s0 + (2 : ℤ_[2]) ^ j • ((2 : ℤ_[2]) ^ ν • z0) + (2 : ℤ_[2]) ^ j • ((2 : ℤ_[2]) ^ (ν + 1) • l) := by
      simp [smul_add]
    _ = (2 : ℤ_[2]) ^ j • s0 + ((2 : ℤ_[2]) ^ j * (2 : ℤ_[2]) ^ ν) • z0 + ((2 : ℤ_[2]) ^ j * (2 : ℤ_[2]) ^ (ν + 1)) • l := by
      simp [← mul_smul]
    _ = (2 : ℤ_[2]) ^ j • s0 + ((2 : ℤ_[2]) ^ (j + ν)) • z0 + ((2 : ℤ_[2]) ^ (j + (ν + 1))) • l := by
      simp [pow_add]
    _ = (2 : ℤ_[2]) ^ j • s0 + ((2 : ℤ_[2]) ^ (ν + j)) • z0 + ((2 : ℤ_[2]) ^ ((ν + j) + 1)) • l := by
      rw [add_comm j ν, ← add_assoc, add_comm j ν]

theorem FurioLombardo.M4.leading_tail {Λ S : Submodule ℤ_[2] V} {W : Set V} {ν j : ℕ} {g yi t : V} (hS : Saturated Λ S)
    (hg : Leading Λ S W ν g) (hyi : yi ∈ S) (u w : ℤ_[2]) (hu : u = 1 + 2 * w) (ht : t ∈ Λ) :
    Leading Λ S W (ν + j) (yi + (2 : ℤ_[2]) ^ j • (u • g) + (2 : ℤ_[2]) ^ (ν + j + 1) • t) := by
  have h1 : Leading Λ S W ν (u • g) := leading_smul_unit hS hg u w hu
  have h2 : Leading Λ S W (ν + j) ((2 : ℤ_[2]) ^ j • (u • g)) := leading_two_pow_smul h1 j
  have h3 : Leading Λ S W (ν + j) (((2 : ℤ_[2]) ^ j • (u • g)) + yi) := leading_add_mem h2 hyi
  have h4 : Leading Λ S W (ν + j) ((((2 : ℤ_[2]) ^ j • (u • g)) + yi) + (2 : ℤ_[2]) ^ (ν + j + 1) • t) :=
    leading_add h3 ht
  simpa [add_comm, add_left_comm, add_assoc] using h4

theorem FurioLombardo.M4.not_mem_of_leading {Λ S : Submodule ℤ_[2] V} {W : Set V} {ν : ℕ} {y : V} (hS : Saturated Λ S)
    (hy : Leading Λ S W ν y) : y ∉ S := by
  intro hyS
  rcases hy with ⟨s0, hs0, z0, hz0, l, hl, hy_eq, h_not, h_all⟩
  have hz0plus2l_in_Λ : z0 + (2 : ℤ_[2]) • l ∈ Λ :=
    Submodule.add_mem Λ hz0 (Submodule.smul_mem Λ (2 : ℤ_[2]) hl)
  have hy_minus_s0_in_S : y - s0 ∈ S :=
    Submodule.sub_mem S hyS hs0
  have h_factor : y - s0 = (2 : ℤ_[2]) ^ ν • (z0 + (2 : ℤ_[2]) • l) := by
    calc
      y - s0 = ((2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ (ν + 1) • l) := by
        rw [hy_eq]
        abel
      _ = (2 : ℤ_[2]) ^ ν • z0 + ((2 : ℤ_[2]) ^ ν * (2 : ℤ_[2])) • l := by
        rw [pow_succ]
      _ = (2 : ℤ_[2]) ^ ν • z0 + (2 : ℤ_[2]) ^ ν • ((2 : ℤ_[2]) • l) := by
        rw [mul_smul]
      _ = (2 : ℤ_[2]) ^ ν • (z0 + (2 : ℤ_[2]) • l) := by
        rw [smul_add]
  rw [h_factor] at hy_minus_s0_in_S
  have hz0plus2l_in_S : z0 + (2 : ℤ_[2]) • l ∈ S :=
    sat_two_pow hS ν hz0plus2l_in_Λ hy_minus_s0_in_S
  have hz0_in_SL : InSL Λ S 1 z0 := by
    refine ⟨z0 + (2 : ℤ_[2]) • l, hz0plus2l_in_S, -l, Submodule.neg_mem Λ hl, ?_⟩
    simp [smul_neg, add_assoc]
  exact h_not hz0_in_SL

theorem FurioLombardo.M4.condIII_of_leading {Λ S : Submodule ℤ_[2] V} {W : Set V} {ν : ℕ} {y : V} (hS : Saturated Λ S)
    (hy : Leading Λ S W ν y) : CondIII Λ S W y := by
  obtain ⟨s0, hs0, z0, hz0, l, hl, rfl, hz0n, hz0w⟩ := hy
  intro n z w hz hw hsub hzw
  have hmΛ : z0 + (2 : ℤ_[2]) • l ∈ Λ := Λ.add_mem hz0 (Λ.smul_mem _ hl)
  have hd : (2 : ℤ_[2]) ^ ν • (z0 + (2 : ℤ_[2]) • l) - (2 : ℤ_[2]) ^ n • z ∈ S := by
    have := S.sub_mem hsub hs0
    convert this using 1
    rw [smul_add, smul_smul, ← pow_succ]
    abel
  rcases lt_trichotomy n ν with h | h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    have h1 : (2 : ℤ_[2]) ^ n • ((2 : ℤ_[2]) ^ (k + 1) • (z0 + (2 : ℤ_[2]) • l) - z) ∈ S := by
      convert hd using 1
      rw [smul_sub, smul_smul, ← pow_add, add_assoc]
    have h2 := sat_two_pow hS n (Λ.sub_mem (Λ.smul_mem _ hmΛ) hz) h1
    refine ⟨-((2 : ℤ_[2]) ^ (k + 1) • (z0 + (2 : ℤ_[2]) • l) - z), S.neg_mem h2,
      (2 : ℤ_[2]) ^ k • (z0 + (2 : ℤ_[2]) • l), Λ.smul_mem _ hmΛ, ?_⟩
    rw [pow_one, smul_smul, ← pow_succ']
    abel
  · subst h
    have h1 : (2 : ℤ_[2]) ^ n • ((z0 + (2 : ℤ_[2]) • l) - z) ∈ S := by
      convert hd using 1
      rw [smul_sub]
    have h2 := sat_two_pow hS n (Λ.sub_mem hmΛ hz) h1
    exfalso
    apply hz0w w hw
    obtain ⟨s1, hs1, l1, hl1, he⟩ := hzw
    refine ⟨s1 + ((z0 + (2 : ℤ_[2]) • l) - z), S.add_mem hs1 h2, l1 - l, Λ.sub_mem hl1 hl, ?_⟩
    rw [pow_one] at he ⊢
    rw [smul_sub]
    have : z0 - w = (z - w) + ((z0 + (2 : ℤ_[2]) • l) - z) - (2 : ℤ_[2]) • l := by abel
    rw [this, he]
    abel
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    have h1 : (2 : ℤ_[2]) ^ ν • ((2 : ℤ_[2]) ^ (k + 1) • z - (z0 + (2 : ℤ_[2]) • l)) ∈ S := by
      have := S.neg_mem hd
      convert this using 1
      rw [smul_sub, smul_smul, ← pow_add, add_assoc]
      abel
    have h2 := sat_two_pow hS ν (Λ.sub_mem (Λ.smul_mem _ hz) hmΛ) h1
    exfalso
    apply hz0n
    refine ⟨-((2 : ℤ_[2]) ^ (k + 1) • z - (z0 + (2 : ℤ_[2]) • l)), S.neg_mem h2,
      (2 : ℤ_[2]) ^ k • z - l, Λ.sub_mem (Λ.smul_mem _ hz) hl, ?_⟩
    rw [pow_one, smul_sub, smul_smul, ← pow_succ']
    abel
