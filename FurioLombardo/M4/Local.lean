import Mathlib
import FurioLombardo.M4.Lattice
import FurioLombardo.M4.Stoll

/-!
# Stoll's criterion at one place for a saturated submodule

`stoll_sat` applies `FurioLombardo.M4.stoll_log` with `Γ'` the preimage of `S`: the logarithms of `Γ'` form a subgroup
closed under halving whose span is saturated, so the halving step needs no iteration. The
conditions `hsat`, `htf`, `hkrull` of `stoll_log` are proved (Krull's intersection theorem over `ℤ_[2]`).
-/

namespace FurioLombardo.M4

section Local

variable {V : Type*} [AddCommGroup V] [Module ℤ_[2] V]

/-- Krull's intersection theorem over `ℤ_[2]`: in a finitely generated module, an element divisible by every
power of 2 is zero. -/
theorem krull_two {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] [Module.Finite ℤ_[2] M] (m : M)
    (h : ∀ n : ℕ, ∃ z : M, m = (2 ^ n : ℕ) • z) : m = 0 := by
  have hI : IsLocalRing.maximalIdeal ℤ_[2] ≠ ⊤ := Ideal.IsMaximal.ne_top inferInstance
  have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) _ hI
  have hm : m ∈ (⨅ i : ℕ, (IsLocalRing.maximalIdeal ℤ_[2]) ^ i • ⊤ : Submodule ℤ_[2] M) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨z, hz⟩ := h i
    rw [hz, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
    have e : ((2 ^ i : ℕ) • z) = ((((2 : ℕ) : ℤ_[2])) ^ i) • z := by
      rw [← Nat.cast_smul_eq_nsmul ℤ_[2]]; push_cast; rfl
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  rw [key] at hm
  exact (Submodule.mem_bot _).mp hm

/-- The quotient `Λ/S` (for `S ≤ Λ`) as a quotient of the subtype `Λ`. -/
abbrev QuotLS (Λ S : Submodule ℤ_[2] V) := ↥Λ ⧸ S.comap Λ.subtype

/-- `Λ/S` has no 2-torsion when `S` is saturated in `Λ`. -/
theorem quotLS_tf {Λ S : Submodule ℤ_[2] V} (hS : Saturated Λ S) (m : QuotLS Λ S)
    (hm : (2 : ℕ) • m = 0) : m = 0 := by
  induction m using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
    rw [Submodule.Quotient.mk_eq_zero]
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hm ⊢
    apply hS.2 z z.2
    rw [← Nat.cast_smul_eq_nsmul ℤ_[2]] at hm
    simpa using hm

/-- Parity reduction in a span: every element of the `ℤ_[2]`-span of an additive subgroup `G` is `g + 2y`
with `g ∈ G` and `y` in the span (the coefficients reduced modulo 2). -/
theorem span_parity {G : AddSubgroup V} {x : V} (hx : x ∈ Submodule.span ℤ_[2] (G : Set V)) :
    ∃ g ∈ G, ∃ y ∈ Submodule.span ℤ_[2] (G : Set V), x = g + (2 : ℤ_[2]) • y := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨x, hx, 0, Submodule.zero_mem _, by simp⟩
  | zero => exact ⟨0, G.zero_mem, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨g1, hg1, y1, hy1, rfl⟩ := hx
    obtain ⟨g2, hg2, y2, hy2, rfl⟩ := hy
    exact ⟨g1 + g2, G.add_mem hg1 hg2, y1 + y2, Submodule.add_mem _ hy1 hy2, by rw [smul_add]; abel⟩
  | smul c x hxs hx =>
    obtain ⟨g, hg, y, hy, rfl⟩ := hx
    obtain ⟨n, hn, hc⟩ := PadicInt.exists_mem_range c
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hc
    obtain ⟨c', hc'⟩ := hc
    have hc2 : c = (n : ℤ_[2]) + 2 * c' := by
      have : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
      rw [this] at hc'; linear_combination hc'
    refine ⟨n • g, G.nsmul_mem hg n, (n : ℤ_[2]) • y + c' • (g + (2 : ℤ_[2]) • y), ?_, ?_⟩
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hxs)
    · rw [hc2, ← Nat.cast_smul_eq_nsmul ℤ_[2] n g]
      module

/-- The span of a subgroup `G ⊆ S` that is closed under halving inside `Λ` is saturated in `S`. -/
theorem mem_span_of_two_smul {Λ S : Submodule ℤ_[2] V} {G : AddSubgroup V} (hS : Saturated Λ S)
    (hGS : ∀ g ∈ G, g ∈ S) (hG2 : ∀ g ∈ G, ∀ x ∈ Λ, g = (2 : ℤ_[2]) • x → x ∈ G)
    {x : V} (hx : x ∈ S) (h2 : (2 : ℤ_[2]) • x ∈ Submodule.span ℤ_[2] (G : Set V)) :
    x ∈ Submodule.span ℤ_[2] (G : Set V) := by
  obtain ⟨g, hg, y, hy, he⟩ := span_parity h2
  have hyS : y ∈ S := (Submodule.span_le.mpr (fun g hg => hGS g hg)) hy
  have hxy : x - y ∈ G := hG2 g hg (x - y) (Λ.sub_mem (hS.1 hx) (hS.1 hyS)) (by rw [smul_sub, he]; abel)
  have := Submodule.add_mem _ (Submodule.subset_span hxy) hy
  simpa using this

/-- If `S` is the saturation of `span {a, b}` and `a, b ∈ G ⊆ S` with `G` closed under halving in `Λ`, then
`S` is the span of `G`, hence `S ⊆ G + 2S`. -/
theorem mem_add_two_of_sat {Λ S : Submodule ℤ_[2] V} {a b : V} {G : AddSubgroup V} (hSat : IsSatOf Λ S a b)
    (ha : a ∈ G) (hb : b ∈ G) (hGS : ∀ g ∈ G, g ∈ S)
    (hG2 : ∀ g ∈ G, ∀ x ∈ Λ, g = (2 : ℤ_[2]) • x → x ∈ G) {x : V} (hx : x ∈ S) :
    ∃ g ∈ G, ∃ y ∈ S, x = g + (2 : ℤ_[2]) • y := by
  have hS : Saturated Λ S := saturated_of_isSatOf hSat
  have hab : Submodule.span ℤ_[2] {a, b} ≤ Submodule.span ℤ_[2] (G : Set V) :=
    Submodule.span_mono (by
      intro z hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb)
  have key : ∀ m : ℕ, ∀ z ∈ S, (2 : ℤ_[2]) ^ m • z ∈ Submodule.span ℤ_[2] (G : Set V) →
      z ∈ Submodule.span ℤ_[2] (G : Set V) := by
    intro m
    induction m with
    | zero => intro z _ h; simpa using h
    | succ m ih =>
      intro z hz h
      apply mem_span_of_two_smul hS hGS hG2 hz
      apply ih _ (S.smul_mem _ hz)
      rwa [smul_smul, ← pow_succ]
  obtain ⟨-, m, hm⟩ := (hSat x).1 hx
  obtain ⟨g, hg, y, hy, he⟩ := span_parity (key m x hx (hab hm))
  exact ⟨g, hg, y, (Submodule.span_le.mpr (fun g hg => hGS g hg)) hy, he⟩

theorem condIII_add_mem {Λ S : Submodule ℤ_[2] V} {W : Set V} {y s : V} (hy : CondIII Λ S W y) (hs : s ∈ S) :
    CondIII Λ S W (y + s) := by
  intro n z w hz hw h1 h2
  apply hy n z w hz hw _ h2
  have := S.sub_mem h1 hs
  rwa [show y + s - (2 : ℤ_[2]) ^ n • z - s = y - (2 : ℤ_[2]) ^ n • z by abel] at this

/-- **Stoll's theorem at one place, for a saturated `S`.** `lam : B → V` is the logarithm with image the lattice
`Λ`, `S` the saturation in `Λ` of the span of the logarithms of the global points `φa`, `φb`. Under local
injectivity (`hloc`), the kernel condition (`hker`), `2T = 0`, the Selmer condition `hW` and condition (iii) at the
global point `x`, the logarithm of `x` lies in `S`. The subgroup `Γ'` of the halving step is the
preimage of `S`; conditions `hsat`, `htf`, `hkrull` of `stoll_log` are proved here. -/
theorem stoll_sat {A B : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B) (lam : B →+ V) (T : A)
    (Λ S : Submodule ℤ_[2] V) (W : Set V) (φa φb : A) [Module.Finite ℤ_[2] Λ]
    (htfV : ∀ y : V, (2 : ℕ) • y = 0 → y = 0)
    (hΛ : ∀ y, y ∈ Λ ↔ ∃ b, lam b = y)
    (hSat : IsSatOf Λ S (lam (ι φa)) (lam (ι φb)))
    (hloc : ∀ Q : A, (∃ b : B, ι Q = (2 : ℕ) • b) → ∃ Q' : A, Q = (2 : ℕ) • Q')
    (hker : ∀ b : B, lam b = 0 → ∃ c : B, b = (2 : ℕ) • c ∨ b = ι T + (2 : ℕ) • c)
    (hT2 : (2 : ℕ) • T = 0)
    (hW : ∀ Q : A, ∃ w ∈ W, ∃ b : B, lam (ι Q) = w + (2 : ℕ) • lam b)
    (x : A) (hiii : CondIII Λ S W (lam (ι x))) : lam (ι x) ∈ S := by
  have hS : Saturated Λ S := saturated_of_isSatOf hSat
  have hmem : ∀ b, lam b ∈ Λ := fun b => (hΛ _).2 ⟨b, rfl⟩
  have h2smul : ∀ y : V, (2 : ℕ) • y = (2 : ℤ_[2]) • y := fun y => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[2]]; norm_num
  have hTlam : lam (ι T) = 0 := htfV _ (by rw [← map_nsmul, ← map_nsmul, hT2, map_zero, map_zero])
  -- the lattice-valued logarithm, the quotient and the projection
  let lamΛ : B →+ ↥Λ := AddMonoidHom.codRestrict lam Λ.toAddSubgroup hmem
  let pr : ↥Λ →+ QuotLS Λ S := (S.comap Λ.subtype).mkQ.toAddMonoidHom
  let Γ : AddSubgroup A := AddSubgroup.comap ((lam.comp ι)) S.toAddSubgroup
  let WΛ : Set ↥Λ := {w | (w : V) ∈ W}
  have hlamΛ : ∀ b, ((lamΛ b : ↥Λ) : V) = lam b := fun b => rfl
  have hpr0 : ∀ z : ↥Λ, pr z = 0 ↔ (z : V) ∈ S := fun z => by
    simp [pr, Submodule.Quotient.mk_eq_zero]
  -- G = logarithms of the points of Γ
  let G : AddSubgroup V := AddSubgroup.map (lam.comp ι) Γ
  have hGS : ∀ g ∈ G, g ∈ S := by
    rintro g ⟨γ, hγ, rfl⟩; exact hγ
  have hG2 : ∀ g ∈ G, ∀ y ∈ Λ, g = (2 : ℤ_[2]) • y → y ∈ G := by
    rintro g ⟨γ, hγ, rfl⟩ y hy he
    obtain ⟨b, rfl⟩ := (hΛ y).1 hy
    obtain ⟨R, hR⟩ := halve ι lam T hloc hker hTlam γ ⟨b, by rw [h2smul]; exact he⟩
    have he' : lam (ι γ) = (2 : ℤ_[2]) • lam b := he
    have hRb : lam (ι R) = lam b := by
      have h0 : (2 : ℕ) • (lam (ι R) - lam b) = 0 := by
        rw [smul_sub, ← hR, h2smul (lam b), ← he', sub_self]
      exact sub_eq_zero.mp (htfV _ h0)
    refine ⟨R, ?_, hRb⟩
    show lam (ι R) ∈ S
    rw [hRb]
    apply hS.2 _ hy
    rw [← he]; exact hγ
  have haG : lam (ι φa) ∈ G := ⟨φa, ((hSat _).2 ⟨hmem _, 0, by simpa using Submodule.subset_span (by simp)⟩), rfl⟩
  have hbG : lam (ι φb) ∈ G := ⟨φb, ((hSat _).2 ⟨hmem _, 0, by simpa using Submodule.subset_span (by simp)⟩), rfl⟩
  have key := stoll_log ι lamΛ pr T Γ WΛ x hloc
    (fun b hb => hker b (by simpa [lamΛ] using congrArg Subtype.val hb))
    (show lam (ι T) ∈ S by rw [hTlam]; exact S.zero_mem)
    (fun γ hγ => (hpr0 _).2 hγ)
    (fun Q => by
      obtain ⟨w, hw, b, hb⟩ := hW Q
      have hwΛ : w ∈ Λ := by
        have := Λ.sub_mem (hmem (ι Q)) (Λ.smul_of_tower_mem (2 : ℕ) (hmem b))
        rwa [hb, add_sub_cancel_right] at this
      exact ⟨⟨w, hwΛ⟩, hw, b, Subtype.ext (by simp [lamΛ, hb])⟩)
    (fun Q hQ => by
      obtain ⟨m, hm⟩ := hQ
      induction m using Submodule.Quotient.induction_on with
      | H m =>
        have hs : lam (ι Q) - (2 : ℤ_[2]) • (m : V) ∈ S := by
          have := (Submodule.Quotient.eq _).1 (show pr (lamΛ (ι Q)) = pr ((2 : ℕ) • m) by rw [map_nsmul]; exact hm)
          simpa [lamΛ, h2smul] using this
        obtain ⟨g, ⟨γ, hγ, rfl⟩, y, hy, he⟩ := mem_add_two_of_sat hSat haG hbG hGS hG2 hs
        obtain ⟨b, hb⟩ := (hΛ (y + (m : V))).1 (Λ.add_mem (hS.1 hy) m.2)
        refine ⟨γ, hγ, b, Subtype.ext ?_⟩
        change lam (ι Q) = lam (ι γ) + (2 : ℕ) • lam b
        rw [hb, h2smul, smul_add]
        simp only [AddMonoidHom.coe_comp, Function.comp_apply] at he
        linear_combination (norm := abel) he)
    (quotLS_tf hS)
    (krull_two)
    (fun n z w hz hw hzw => by
      induction z using Submodule.Quotient.induction_on with
      | H z =>
        obtain ⟨m, hm⟩ := hzw
        induction m using Submodule.Quotient.induction_on with
        | H m =>
          have h1 : lam (ι x) - (2 : ℤ_[2]) ^ n • (z : V) ∈ S := by
            have := (Submodule.Quotient.eq _).1 (show pr (lamΛ (ι x)) = pr ((2 ^ n : ℕ) • z) by rw [map_nsmul]; exact hz.symm)
            simpa [lamΛ, ← Nat.cast_smul_eq_nsmul ℤ_[2]] using this
          have h2 : InSL Λ S 1 ((z : V) - (w : V)) := by
            have := (Submodule.Quotient.eq _).1 (show pr (z - w) = pr ((2 : ℕ) • m) by rw [map_sub, map_nsmul]; exact hm)
            refine ⟨(z : V) - w - (2 : ℤ_[2]) • (m : V), by simpa [h2smul] using this, m, m.2, by simp⟩
          obtain ⟨s, hs, l, hl, he⟩ := hiii n z w z.2 hw h1 h2
          refine ⟨Submodule.Quotient.mk ⟨l, hl⟩, ?_⟩
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
          simp only [Submodule.mem_comap, Submodule.subtype_apply, AddSubgroup.coe_sub, Submodule.coe_sub]
          have : (z : V) - (2 : ℕ) • l = s := by rw [he, h2smul]; simp
          simp [this, hs])
  exact (hpr0 _).1 key

end Local

end FurioLombardo.M4
