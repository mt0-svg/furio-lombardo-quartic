import Mathlib
import FurioLombardo.M4.Stoll

/-!
# The local argument at `v` in submodule form (lane M3a)

Lane M4 states the local chain at `v` with two `ℤ_[2]`-submodules of `V`: `Λ = log A(k_v)` and its
saturated submodule `S = Ḡ_sat`, and condition (iii) as `CondIII Λ S W y`. This file bridges that form
to `FurioLombardo.M4.stoll_log` (with `M = Λ ⧸ S`), and runs the halving step (L3) twice to build
the group `Γ'`.

* `InSL`, `Saturated`, `CondIII`: the definitions of lane M4 (same bodies, so the two versions agree
  by `Iff.rfl`).
* `stoll_sat`: Stoll's theorem at one place in submodule form: under `hloc`, `hker`, `hW`, `hsat`,
  condition (iii) at `x` gives `lam (ι x) ∈ S`. Krull's intersection theorem for the finitely
  generated `ℤ_[2]`-module `Λ ⧸ S` replaces the hypothesis `hkrull` of `stoll_log`.
* `exists_quarter`: two halvings: if `4 r = n a + m b` with `a = lam (ι γa)`, `b = lam (ι γb)`,
  `r ∈ Λ = range lam`, then `r = lam (ι R)` for a global `R`.
* `twist_sat`: the local argument for one twist, with `Γ'` the preimage of `S`.
-/

namespace FurioLombardo.M3a

variable {V : Type*} [AddCommGroup V] [Module ℤ_[2] V]

/-- `z ∈ S + 2^n Λ` (as in lane M4). -/
def InSL (Λ S : Submodule ℤ_[2] V) (n : ℕ) (z : V) : Prop :=
  ∃ s ∈ S, ∃ l ∈ Λ, z = s + (2 : ℤ_[2]) ^ n • l

/-- `S` is a saturated submodule of `Λ` at 2 (as in lane M4). -/
def Saturated (Λ S : Submodule ℤ_[2] V) : Prop :=
  S ≤ Λ ∧ ∀ x ∈ Λ, (2 : ℤ_[2]) • x ∈ S → x ∈ S

/-- Condition (iii) at `y` (as in lane M4): if `y ≡ 2^n z mod S` with `z ∈ Λ`,
and `z` is congruent modulo `S + 2Λ` to an element of `W`, then `z ∈ S + 2Λ`. -/
def CondIII (Λ S : Submodule ℤ_[2] V) (W : Set V) (y : V) : Prop :=
  ∀ (n : ℕ) (z w : V), z ∈ Λ → w ∈ W → y - (2 : ℤ_[2]) ^ n • z ∈ S → InSL Λ S 1 (z - w) →
    InSL Λ S 1 z

theorem nsmul_eq_two_pow_smul (n : ℕ) (v : V) : (2 ^ n : ℕ) • v = (2 : ℤ_[2]) ^ n • v := by
  rw [← Nat.cast_smul_eq_nsmul ℤ_[2]]; push_cast; rfl

theorem two_nsmul_eq_smul (v : V) : (2 : ℕ) • v = (2 : ℤ_[2]) • v := by
  simpa using nsmul_eq_two_pow_smul (V := V) 1 v

/-- Krull's intersection theorem in the form used here: in a finitely generated `ℤ_[2]`-module an
element divisible by every power of 2 is zero. -/
theorem eq_zero_of_forall_two_pow_dvd {M : Type*} [AddCommGroup M] [Module ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (m : M) (h : ∀ n : ℕ, ∃ z : M, m = (2 ^ n : ℕ) • z) : m = 0 := by
  have hI : (Ideal.span {(2 : ℤ_[2])}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact_mod_cast PadicInt.p_nonunit (p := 2)
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) _ hI
  have hm : m ∈ (⨅ i : ℕ, (Ideal.span {(2 : ℤ_[2])}) ^ i • ⊤ : Submodule ℤ_[2] M) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨z, hz⟩ := h i
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, hz,
      nsmul_eq_two_pow_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  rw [hK] at hm
  exact (Submodule.mem_bot _).mp hm

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- **Stoll's theorem at one place, submodule form**.
`Λ` is the range of `lam` (hypothesis `hrange`), `S` is saturated in `Λ`, `Γ` contains `T` and has
logarithms in `S`. Then condition (iii) at `x` forces `lam (ι x) ∈ S`. -/
theorem stoll_sat [IsNoetherian ℤ_[2] V] (ι : A →+ B) (lam : B →+ V) (Λ S : Submodule ℤ_[2] V)
    (T : A) (Γ : AddSubgroup A) (W : Set V) (x : A)
    (hrange : ∀ l : V, l ∈ Λ ↔ ∃ b : B, lam b = l) (hS : Saturated Λ S)
    (hloc : ∀ Q : A, (∃ b : B, ι Q = (2 : ℕ) • b) → ∃ Q' : A, Q = (2 : ℕ) • Q')
    (hker : ∀ b : B, lam b = 0 → ∃ c : B, b = (2 : ℕ) • c ∨ b = ι T + (2 : ℕ) • c)
    (hT : T ∈ Γ) (hΓ : ∀ γ ∈ Γ, lam (ι γ) ∈ S)
    (hW : ∀ Q : A, ∃ w ∈ W, ∃ b : B, lam (ι Q) = w + (2 : ℕ) • lam b)
    (hsat : ∀ Q : A, InSL Λ S 1 (lam (ι Q)) →
      ∃ γ ∈ Γ, ∃ b : B, lam (ι Q) = lam (ι γ) + (2 : ℕ) • lam b)
    (hiii : CondIII Λ S W (lam (ι x))) :
    lam (ι x) ∈ S := by
  have hlamΛ : ∀ b : B, lam b ∈ Λ := fun b => (hrange _).mpr ⟨b, rfl⟩
  -- the logarithm with values in `Λ`, and the quotient `M = Λ ⧸ S`
  set S' : Submodule ℤ_[2] Λ := S.comap Λ.subtype with hS'
  let lamΛ : B →+ Λ :=
    { toFun := fun b => ⟨lam b, hlamΛ b⟩
      map_zero' := by ext; simp
      map_add' := fun b c => by ext; simp }
  have hlamΛ_apply : ∀ b, (lamΛ b : V) = lam b := fun b => rfl
  let pr : Λ →+ Λ ⧸ S' := (S'.mkQ).toAddMonoidHom
  have hpr0 : ∀ z : Λ, pr z = 0 ↔ (z : V) ∈ S := fun z => by
    change S'.mkQ z = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hS', Submodule.mem_comap,
      Submodule.subtype_apply]
  have hfin : Module.Finite ℤ_[2] (Λ ⧸ S') := inferInstance
  -- `W` pulled back to `Λ`
  let W' : Set Λ := {w | (w : V) ∈ W}
  have key := FurioLombardo.M4.stoll_log ι lamΛ pr T Γ W' x hloc
    (fun b hb => hker b (by rw [← hlamΛ_apply, hb]; rfl)) hT
    (fun γ hγ => (hpr0 _).mpr (hΓ γ hγ))
    (fun Q => by
      obtain ⟨w, hw, b, hb⟩ := hW Q
      have hwΛ : w ∈ Λ := by
        have : w = lam (ι Q) - (2 : ℕ) • lam b := by rw [hb]; abel
        rw [this]; exact Λ.sub_mem (hlamΛ _) (Λ.smul_of_tower_mem _ (hlamΛ _))
      refine ⟨⟨w, hwΛ⟩, hw, b, ?_⟩
      ext; simp [hlamΛ_apply, hb])
    (fun Q ⟨m, hm⟩ => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective S' m
      have h1 : pr (lamΛ (ι Q) - (2 : ℕ) • z) = 0 := by
        rw [map_sub, map_nsmul, hm]; exact sub_self _
      rw [hpr0] at h1
      obtain ⟨γ, hγ, b, hb⟩ := hsat Q ⟨_, h1, z, z.2, by
        simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, hlamΛ_apply, pow_one,
          ← two_nsmul_eq_smul]
        abel⟩
      exact ⟨γ, hγ, b, by ext; simp [hlamΛ_apply, hb]⟩)
    (fun m hm => by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective S' m
      have : ((2 : ℕ) • z : Λ) ∈ S' := by
        rw [← Submodule.Quotient.mk_eq_zero]; simpa using hm
      have h2 : (2 : ℤ_[2]) • (z : V) ∈ S := by
        rw [hS', Submodule.mem_comap] at this; simpa [two_nsmul_eq_smul] using this
      exact (Submodule.Quotient.mk_eq_zero _).mpr (by
        rw [hS', Submodule.mem_comap]; exact hS.2 _ z.2 h2))
    (fun m hm => eq_zero_of_forall_two_pow_dvd m hm)
    (fun n z w hz hw ⟨m, hm⟩ => by
      obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective S' z
      obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective S' m
      have hy : lam (ι x) - (2 : ℤ_[2]) ^ n • (z0 : V) ∈ S := by
        have h1 : pr (lamΛ (ι x) - (2 ^ n : ℕ) • z0) = 0 := by
          rw [map_sub, map_nsmul]; change pr _ - (2 ^ n : ℕ) • S'.mkQ z0 = 0
          rw [Submodule.mkQ_apply, hz]; simp
        rw [hpr0] at h1
        simpa [hlamΛ_apply, nsmul_eq_two_pow_smul] using h1
      have hzw : InSL Λ S 1 ((z0 : V) - (w : V)) := by
        have h1 : pr (z0 - w - (2 : ℕ) • l) = 0 := by
          rw [map_sub, map_sub, map_nsmul]
          change S'.mkQ z0 - S'.mkQ w - (2 : ℕ) • S'.mkQ l = 0
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mkQ_apply]
          change Submodule.Quotient.mk z0 - pr w - _ = 0
          rw [hm]; simp
        rw [hpr0] at h1
        refine ⟨_, h1, l, l.2, ?_⟩
        simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, pow_one, ← two_nsmul_eq_smul]
        abel
      obtain ⟨s, hs, l', hl', he⟩ := hiii n z0 w z0.2 hw hy hzw
      refine ⟨Submodule.Quotient.mk ⟨l', hl'⟩, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      rw [hS', Submodule.mem_comap]
      simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul_of_tower, he,
        pow_one, two_nsmul_eq_smul]
      simpa using hs)
  exact (hpr0 _).mp key

/-- Two halvings: if `4 r = n a + m b` with `a = lam (ι γa)`, `b = lam (ι γb)`
and `r ∈ Λ = range lam`, then `r = lam (ι R)` for a global point `R`. -/
theorem exists_quarter (ι : A →+ B) (lam : B →+ V) (Λ : Submodule ℤ_[2] V) (T : A)
    (htfV : ∀ v : V, (2 : ℤ_[2]) • v = 0 → v = 0)
    (hrange : ∀ l : V, l ∈ Λ ↔ ∃ b : B, lam b = l)
    (hloc : ∀ Q : A, (∃ b : B, ι Q = (2 : ℕ) • b) → ∃ Q' : A, Q = (2 : ℕ) • Q')
    (hker : ∀ b : B, lam b = 0 → ∃ c : B, b = (2 : ℕ) • c ∨ b = ι T + (2 : ℕ) • c)
    (hTlam : lam (ι T) = 0) (γa γb : A) (n m : ℤ) (r : V) (hr : r ∈ Λ)
    (h4 : (4 : ℤ_[2]) • r = n • lam (ι γa) + m • lam (ι γb)) :
    ∃ R : A, lam (ι R) = r := by
  have htf : ∀ u w : V, (2 : ℤ_[2]) • u = (2 : ℤ_[2]) • w → u = w := fun u w h =>
    sub_eq_zero.mp (htfV _ (by rw [smul_sub, h, sub_self]))
  have h2r : (2 : ℤ_[2]) • r ∈ Λ := Λ.smul_mem _ hr
  obtain ⟨b1, hb1⟩ := (hrange _).mp h2r
  obtain ⟨b2, hb2⟩ := (hrange _).mp hr
  have hγ : lam (ι (n • γa + m • γb)) = (2 : ℕ) • lam b1 := by
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul, ← h4, hb1,
      two_nsmul_eq_smul, smul_smul]
    norm_num
  obtain ⟨R1, hR1⟩ := FurioLombardo.M4.halve ι lam T hloc hker hTlam _ ⟨b1, hγ⟩
  have hR1' : lam (ι R1) = (2 : ℕ) • lam b2 := by
    apply htf
    rw [← two_nsmul_eq_smul, ← hR1, hγ, hb1, hb2]
    simp only [two_nsmul_eq_smul]
  obtain ⟨R2, hR2⟩ := FurioLombardo.M4.halve ι lam T hloc hker hTlam _ ⟨b2, hR1'⟩
  refine ⟨R2, htf _ _ ?_⟩
  rw [← two_nsmul_eq_smul, ← hR2, hR1', hb2, two_nsmul_eq_smul]

/-- Every element of `ℤ_[2]` is `n + 2 c` with `n ∈ {0, 1}`. -/
theorem padic_two_decomp (c : ℤ_[2]) : ∃ n : ℕ, ∃ c' : ℤ_[2], c = n + 2 * c' := by
  obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range c
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hn
  obtain ⟨c', hc'⟩ := hn
  exact ⟨n, c', by push_cast at hc'; linear_combination hc'⟩

/-- **The local argument for one twist**, submodule form. `φ : D_δ(k) → A(k)` is the
Abel-Prym map on the lifts of rational points, `ga = φ(x_a)`, `gb = φ(x_b)` the images of the
known lifts, `Γ'` the preimage of `S`. Hypotheses: `hloc`, `hker`,
`hrange` (`Λ = log A(k_v)`), `hS` (`S` saturated), `ha`, `hb` (the logarithms of
the known points lie in `S`), `hT2` (`T` is 2-torsion), `hW` (every global logarithm is congruent to
an element of `W` modulo `2Λ`), `hq` (the lattice fact: `r` with `4 r = n a + m b` and
`S ≤ span {a, b, r}`), `hiii` (condition (iii) at every lift) and `hzero` (a lift with
`λ ∈ S` is good). Conclusion: every lift is good. Corollary 4.3 of the paper. -/
theorem twist_sat [IsNoetherian ℤ_[2] V] (htfV : ∀ v : V, (2 : ℤ_[2]) • v = 0 → v = 0)
    (ι : A →+ B) (lam : B →+ V) (Λ S : Submodule ℤ_[2] V) (W : Set V) (T : A)
    {Dk : Type*} (φ : Dk → A) (ga gb : A) (Good : Dk → Prop)
    (hrange : ∀ l : V, l ∈ Λ ↔ ∃ b : B, lam b = l) (hS : Saturated Λ S)
    (ha : lam (ι ga) ∈ S) (hb : lam (ι gb) ∈ S) (hT2 : (2 : ℕ) • T = 0)
    (hloc : ∀ Q : A, (∃ b : B, ι Q = (2 : ℕ) • b) → ∃ Q' : A, Q = (2 : ℕ) • Q')
    (hker : ∀ b : B, lam b = 0 → ∃ c : B, b = (2 : ℕ) • c ∨ b = ι T + (2 : ℕ) • c)
    (hW : ∀ Q : A, ∃ w ∈ W, ∃ b : B, lam (ι Q) = w + (2 : ℕ) • lam b)
    (hq : ∃ n m : ℤ, ∃ r ∈ Λ, (4 : ℤ_[2]) • r = n • lam (ι ga) + m • lam (ι gb) ∧
      S ≤ Submodule.span ℤ_[2] {lam (ι ga), lam (ι gb), r})
    (hiii : ∀ x : Dk, CondIII Λ S W (lam (ι (φ x - ga))))
    (hzero : ∀ x : Dk, lam (ι (φ x - ga)) ∈ S → Good x) :
    ∀ x : Dk, Good x := by
  have hlamΛ : ∀ b : B, lam b ∈ Λ := fun b => (hrange _).mpr ⟨b, rfl⟩
  have hTlam : lam (ι T) = 0 := htfV _ (by rw [← two_nsmul_eq_smul, ← map_nsmul, ← map_nsmul,
    hT2, map_zero, map_zero])
  set Γ : AddSubgroup A := (S.toAddSubgroup).comap (lam.comp ι) with hΓdef
  have hmemΓ : ∀ γ, γ ∈ Γ ↔ lam (ι γ) ∈ S := fun γ => Iff.rfl
  obtain ⟨n, m, r, hrΛ, h4, hspan⟩ := hq
  obtain ⟨R, hR⟩ := exists_quarter ι lam Λ T htfV hrange hloc hker hTlam _ _ n m r hrΛ h4
  have hrS : r ∈ S := by
    apply hS.2 r hrΛ
    apply hS.2 _ (Λ.smul_mem _ hrΛ)
    rw [smul_smul, show (2 : ℤ_[2]) * 2 = 4 by norm_num, h4]
    exact S.add_mem (S.smul_of_tower_mem _ ha) (S.smul_of_tower_mem _ hb)
  -- every element of `S` is a global logarithm in `S` modulo `2Λ`
  have hreach : ∀ s ∈ S, ∃ γ ∈ Γ, ∃ l ∈ Λ, s = lam (ι γ) + (2 : ℤ_[2]) • l := by
    intro s hs
    have hs' := hspan hs
    rw [Submodule.mem_span_insert] at hs'
    obtain ⟨α, s1, hs1, rfl⟩ := hs'
    rw [Submodule.mem_span_insert] at hs1
    obtain ⟨β, s2, hs2, rfl⟩ := hs1
    rw [Submodule.mem_span_singleton] at hs2
    obtain ⟨ρ, rfl⟩ := hs2
    obtain ⟨na, α', rfl⟩ := padic_two_decomp α
    obtain ⟨nb, β', rfl⟩ := padic_two_decomp β
    obtain ⟨nr, ρ', rfl⟩ := padic_two_decomp ρ
    refine ⟨na • ga + nb • gb + nr • R, ?_, α' • lam (ι ga) + β' • lam (ι gb) + ρ' • r,
      ?_, ?_⟩
    · rw [hmemΓ]; simp only [map_add, map_nsmul, hR]
      exact S.add_mem (S.add_mem (S.smul_of_tower_mem _ ha) (S.smul_of_tower_mem _ hb))
        (S.smul_of_tower_mem _ hrS)
    · exact Λ.add_mem (Λ.add_mem (Λ.smul_mem _ (hlamΛ _)) (Λ.smul_mem _ (hlamΛ _)))
        (Λ.smul_mem _ hrΛ)
    · simp only [map_add, map_nsmul, hR]
      simp only [add_smul, mul_smul, smul_add, ← Nat.cast_smul_eq_nsmul ℤ_[2]]
      abel
  intro x
  apply hzero x
  refine stoll_sat ι lam Λ S T Γ W (φ x - ga) hrange hS hloc hker ?_ (fun γ hγ => hγ) hW ?_ (hiii x)
  · rw [hmemΓ, hTlam]; exact S.zero_mem
  · rintro Q ⟨s, hs, l, hl, hQ⟩
    obtain ⟨γ, hγ, l', hl', hs'⟩ := hreach s hs
    obtain ⟨b, hb⟩ := (hrange _).mp (Λ.add_mem hl hl')
    refine ⟨γ, hγ, b, ?_⟩
    rw [hQ, hs', hb, two_nsmul_eq_smul, pow_one, smul_add]
    abel

end FurioLombardo.M3a
