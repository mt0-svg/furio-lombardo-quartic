import Mathlib
import FurioLombardo.M4.Main
import FurioLombardo.M4.Hypotheses

/-!
# Condition (iii) on every disc of C(Q_2) of twist δ

`qchar_of_cert` builds the lattice layer (QChar for `projO UG`, `4V ⊆ Λ`, the membership test by `G`) from the kernel
checked data and the certified balls; `lead_or_known` gives on every box of the covering either a leading level
outside `pr(W)` or a known lift; `cover_iii` is condition (iii) of Stoll's criterion at every point of twist δ,
except at the known lifts. `hSeries_of_anti` and `hTail_of_anti` derive the series hypotheses from the
antiderivative ones (`FurioLombardo.M4.rescale_spec`).
-/

namespace FurioLombardo.M4

/-- The lattice layer from the data: `Q = projO UG` characterises `S + 2^n Λ` for `n ≤ r`, `4V ⊆ Λ`, and
`Λ ⊇ {x : G x ≡ 0 mod 4}`. -/
theorem qchar_of_cert {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {D : TwistData} (hD : TwistChecks D)
    {ℓ : Fin 7 → Fin 6 → ℤ_[2]} {a b : Fin 6 → ℤ_[2]} (hGen : HGen Λ ℓ) (hBD : HBallD D ℓ)
    (hBP : HBallPhi D a b) (hSat : HSat Λ S a b) :
    QChar Λ S (projO D.UG) D.r ∧ (∀ x, DvdV 2 x → x ∈ Λ) ∧
      (∀ x, (∀ j, (4 : ℤ_[2]) ∣ imv D.G x j) → x ∈ Λ) := by
  have h24 : ((2 : ℤ_[2]) ^ 2) = 4 := by norm_num
  have hl3 : ∀ i, DvdV 3 (ℓ i - icast (D.lD i)) := fun i => dvdV_mono (hD.hqD i) (hBD i)
  have hl2 : ∀ i, DvdV 2 (ℓ i - icast (D.lD i)) := fun i => dvdV_mono (by norm_num) (hl3 i)
  have h4 : ∀ x, DvdV 2 x → x ∈ Λ := nakayama_four (fun k => four_single_mem ℓ hGen D.lD hl3 D.C hD.hC k)
  have hcolH : ∀ k : Fin 6, icast (fun j => D.H j k) ∈ Λ := fun k => col_mem ℓ hGen h4 D.lD hl2 D.H D.Cp hD.hCp k
  have hmemG : ∀ x, (∀ j, (4 : ℤ_[2]) ∣ imv D.G x j) → x ∈ Λ := fun x hx => mem_of_imv_dvd D.H D.G hD.hHG hcolH hx
  have hG4 : ∀ x ∈ Λ, ∀ j, (4 : ℤ_[2]) ∣ imv D.G x j := fun x hx j =>
    four_dvd_imv_of_mem ℓ hGen D.lD hl2 D.G hD.hGl hx j
  have hUG4 : ∀ x ∈ Λ, ∀ j, (4 : ℤ_[2]) ∣ imv D.UG x j := by
    intro x hx j
    have h := dvdV_imv D.U (B := 2) (x := imv D.G x) (fun i => by rw [h24]; exact hG4 x hx i) j
    rw [← hD.hUG, imv_mul]; rwa [h24] at h
  have hcol : ∀ k : Fin 6, icast (fun j => (D.H * D.Ui) j k) ∈ Λ := by
    intro k
    apply hmemG
    intro j
    rw [imv_icast]
    have hc : D.G.mulVec (fun j => (D.H * D.Ui) j k) j = (D.G * (D.H * D.Ui)) j k := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have := (intCast_two_pow_dvd_iff 2 ((D.G * (D.H * D.Ui)) j k)).mpr (by
      have := hD.hGcol j k; norm_num; exact this)
    simp only [icast, hc]; rwa [h24] at this
  -- the approximations of the Q-values of a and b
  have hA : ∀ o, (2 : ℤ_[2]) ^ D.qa ∣ imv D.UG a o - icast (D.UG.mulVec D.la) o := by
    intro o
    have := dvdV_imv D.UG hBP.1 o
    rwa [imv_sub, imv_icast] at this
  have hB : ∀ o, (2 : ℤ_[2]) ^ D.qb ∣ imv D.UG b o - icast (D.UG.mulVec D.lb) o := by
    intro o
    have := dvdV_imv D.UG hBP.2 o
    rwa [imv_sub, imv_icast] at this
  obtain ⟨u, hu, hΔ⟩ := eq_two_pow_mul_unit_of_approx hD.hdl.1 hD.hdl.2 hD.hr.2
    (det_approx D.UG hBP.1 hBP.2 hD.hDel)
  set J := min D.Jab (min D.qa D.qb) with hJ
  have hab : ∀ o : Fin 6, 2 ≤ o.val → (2 : ℤ_[2]) ^ J ∣ imv D.UG a o ∧ (2 : ℤ_[2]) ^ J ∣ imv D.UG b o := by
    intro o ho
    obtain ⟨ha, hb⟩ := hD.hJab o ho
    have ha' : (2 : ℤ_[2]) ^ D.Jab ∣ icast (D.UG.mulVec D.la) o := (intCast_two_pow_dvd_iff _ _).mpr ha
    have hb' : (2 : ℤ_[2]) ^ D.Jab ∣ icast (D.UG.mulVec D.lb) o := (intCast_two_pow_dvd_iff _ _).mpr hb
    have e1 : J ≤ D.Jab := min_le_left _ _
    have e2 : J ≤ D.qa := le_trans (min_le_right _ _) (min_le_left _ _)
    have e3 : J ≤ D.qb := le_trans (min_le_right _ _) (min_le_right _ _)
    constructor
    · have := dvd_add ((pow_dvd_pow 2 e2).trans (hA o)) ((pow_dvd_pow 2 e1).trans ha')
      rwa [sub_add_cancel] at this
    · have := dvd_add ((pow_dvd_pow 2 e3).trans (hB o)) ((pow_dvd_pow 2 e1).trans hb')
      rwa [sub_add_cancel] at this
  have hJr : J + 2 - D.dl = D.r + 2 := by have := hD.hr.1; omega
  have hSQ : ∀ s ∈ S, ∀ o : Fin 6, 2 ≤ o.val → (2 : ℤ_[2]) ^ (D.r + 2) ∣ imv D.UG s o := by
    intro s hs o ho
    rw [← hJr]
    exact dvd_Q_of_mem_S hSat D.UG hUG4 hu hΔ (by omega) hab hs o ho
  have hsigS : ∀ k : Fin 6, k.val < 2 → ∀ n ≤ D.r, InSL Λ S n (icast (fun j => (D.H * D.Ui) j k)) := by
    intro k hk n hn
    apply inSL_mono hn
    set j : Fin 2 := ⟨k.val, hk⟩
    have hkj : Fin.castLE (by omega) j = k := Fin.ext rfl
    obtain ⟨hqa, hqb⟩ := hD.hsigq j
    apply inSL_of_cert hSat h4 (hcol k) D.r (D.sigE j) (D.sigA j : ℤ_[2]) (D.sigB j : ℤ_[2])
    intro i
    have h1 : (2 : ℤ_[2]) ^ (D.r + D.sigE j + 2) ∣
        (((2 ^ D.sigE j * (D.H * D.Ui) i k - D.sigA j * D.la i - D.sigB j * D.lb i : ℤ)) : ℤ_[2]) := by
      rw [intCast_two_pow_dvd_iff]; have := hD.hsig j i; rwa [hkj] at this
    have h2 : (2 : ℤ_[2]) ^ (D.r + D.sigE j + 2) ∣ a i - icast D.la i :=
      (pow_dvd_pow 2 hqa).trans (hBP.1 i)
    have h3 : (2 : ℤ_[2]) ^ (D.r + D.sigE j + 2) ∣ b i - icast D.lb i :=
      (pow_dvd_pow 2 hqb).trans (hBP.2 i)
    have e : ((2 : ℤ_[2]) ^ D.sigE j • icast (fun j => (D.H * D.Ui) j k) - (D.sigA j : ℤ_[2]) • a -
        (D.sigB j : ℤ_[2]) • b) i =
        (((2 ^ D.sigE j * (D.H * D.Ui) i k - D.sigA j * D.la i - D.sigB j * D.lb i : ℤ)) : ℤ_[2]) -
          (D.sigA j : ℤ_[2]) * (a i - icast D.la i) - (D.sigB j : ℤ_[2]) * (b i - icast D.lb i) := by
      simp only [icast, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; push_cast; ring
    rw [e]
    exact dvd_sub (dvd_sub h1 (Dvd.dvd.mul_left h2 _)) (Dvd.dvd.mul_left h3 _)
  have hD1 : IsUnit ((1 : ℤ) : ℤ_[2]) := by simp
  refine ⟨⟨fun x hx => ((hSat x).mp hx).1, ?_⟩, h4, hmemG⟩
  intro n hn x hx
  constructor
  · rintro ⟨s, hs, l, hl, rfl⟩ i
    rw [projO_apply, imv_add, imv_smul]
    have ho : 2 ≤ (⟨i.val + 2, by omega⟩ : Fin 6).val := by simp
    apply dvd_add ((pow_dvd_pow 2 (by omega)).trans (hSQ s hs _ ho))
    rw [Pi.smul_apply, smul_eq_mul, pow_add]
    exact mul_dvd_mul_left _ (by rw [h24]; exact hUG4 l hl _)
  · intro hQ
    apply inSL_of_Q D.H D.Ui D.UG 1 hD1 hD.hid hcol hsigS hUG4 hn hx
    intro o ho
    have := hQ ⟨o.val - 2, by omega⟩
    rw [projO_apply] at this
    have e : (⟨o.val - 2 + 2, by omega⟩ : Fin 6) = o := Fin.ext (by simp; omega)
    rwa [e] at this

/-- Every point of twist δ in the disc `d` either is a known lift (`λ ∈ S`) or has a leading level and class. -/
theorem lead_or_known {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {D : TwistData} (hD : TwistChecks D)
    {ℓ : Fin 7 → Fin 6 → ℤ_[2]} {a b : Fin 6 → ℤ_[2]} {lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} (hGen : HGen Λ ℓ) (hBD : HBallD D ℓ) (hBP : HBallPhi D a b)
    (hSat : HSat Λ S a b) (hCe : HCentre D lam) (hSe : HSeries D lam) (hTa : HTail D lam)
    (hKn : HKnown D S lam) (hEx : HExcl D Twist) (d : ℕ) (hd : d ∈ [1, 2, 3, 4, 5]) (X : ℤ_[2])
    (hX : Twist d X) :
    (lam d X ∈ S ∧ ∃ t ∈ D.tails, t.disc = d ∧ X = (t.Xi : ℤ_[2])) ∨
      ∃ ν, Leading Λ S (Wset D.W) ν (lam d X) := by
  obtain ⟨hQ, h4, hmemG⟩ := qchar_of_cert hD hGen hBD hBP hSat
  have hS : Saturated Λ S := saturated_of_isSatOf hSat
  obtain ⟨p, hp, hXp⟩ := cover_of_coverCheck _ 12 (hD.cover d hd) X
  rcases mem_boxesOf hp with ⟨e, he, hed, rfl⟩ | ⟨c, hc, hcd, rfl⟩ | ⟨t, ht, htd, rfl⟩
  · exact absurd (hed ▸ hX) (hEx e he X hXp)
  · -- a constant box
    right
    obtain ⟨hok, hq, hν, -, hslack, -⟩ := hD.centres c hc
    obtain ⟨Y, rfl⟩ := hXp
    refine ⟨c.nu, ?_⟩
    have hball := hCe c hc
    have hlc : lam c.disc c.c ∈ Λ := by
      apply hmemG
      intro j
      have e : lam c.disc c.c = icast c.y + (lam c.disc c.c - icast c.y) := by abel
      rw [e, imv_add, imv_icast, Pi.add_apply]
      apply dvd_add
      · have := (intCast_two_pow_dvd_iff 2 (D.G.mulVec c.y j)).mpr (by norm_num; exact hD.centresMem c hc j)
        norm_num at this; exact this
      · have := dvdV_imv D.G (dvdV_mono (show 2 ≤ c.q by omega) hball) j
        norm_num at this; exact this
    have hlead := centre_leading hQ hν hq hok hlc hball
    obtain ⟨α, hα, hsum⟩ := hSe c hc
    rw [← hcd]
    exact const_box_leading h4 hlead hslack hα (hsum Y)
  · -- a tail box
    obtain ⟨hok, hq, hν, -, hs0, hs0s, hthr, hmod⟩ := hD.tailsOK t ht
    obtain ⟨g, α, hg, ha0, hα, hsum⟩ := hTa t ht
    obtain ⟨y, rfl⟩ := hXp
    obtain ⟨k, hk⟩ : (2 : ℤ) ^ t.s ∣ (t.c : ℤ) - t.Xi := Int.ModEq.dvd hmod.symm
    set Y : ℤ_[2] := 2 ^ (t.s - t.s0) * ((k : ℤ_[2]) + y) with hY
    have hX : ((t.c : ℕ) : ℤ_[2]) + 2 ^ t.s * y = (t.Xi : ℤ_[2]) + 2 ^ t.s0 * Y := by
      have hk' : ((t.c : ℕ) : ℤ_[2]) = (t.Xi : ℤ_[2]) + 2 ^ t.s * (k : ℤ_[2]) := by
        have := congrArg (fun m : ℤ => (m : ℤ_[2])) hk
        push_cast at this
        linear_combination this
      rw [hk', hY, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hs0s]
      ring
    rw [hX, ← htd]
    rcases eq_zero_or_two_pow_mul_unit ((k : ℤ_[2]) + y) with h0 | ⟨j, u, hu, hju⟩
    · left
      have hY0 : Y = 0 := by rw [hY, h0, mul_zero]
      rw [hY0, mul_zero, add_zero]
      exact ⟨hKn t ht, t, ht, rfl, rfl⟩
    · right
      have hgΛ : g ∈ Λ := by
        apply h4
        have h0 := hα 0
        rw [ha0] at h0
        have h1 : DvdV (t.vM / 3 + 1 + (t.s0 - 1)) ((2 : ℤ_[2]) ^ (t.s0 - 1) • g) := by
          have e : t.vM / 3 + 1 + (t.s0 - 1) = t.vM / 3 + t.s0 + 0 := by omega
          rw [e]; simpa using h0
        exact dvdV_mono (by have := hD.tailsVM t ht; omega) (dvdV_cancel h1)
      have hLg := centre_leading hQ hν hq hok hgΛ hg
      have hYu : Y = (2 : ℤ_[2]) ^ (t.s - t.s0 + j) * u := by rw [hY, hju, pow_add, mul_assoc]
      have hs := hsum Y
      rw [hYu] at hs ⊢
      exact ⟨_, tail_leading (B := t.vM / 3 + t.s0) (t := t.s - t.s0 + j) hS h4 hs0 (by omega) hLg (hKn t ht)
        hα ha0 hu hs⟩

/-- **M4, per twist.** At every point of twist δ of `C(Q_2)`, of parameter `X` in the disc `d`, the value
`λ = log φ(x)` of either lift satisfies condition (iii) (the hypothesis `hiii` of
`FurioLombardo.M4.stoll_log` for `M = Λ/S`), and `λ ∈ S` only at the known lifts. -/
theorem cover_iii {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {D : TwistData} (hD : TwistChecks D)
    {ℓ : Fin 7 → Fin 6 → ℤ_[2]} {a b : Fin 6 → ℤ_[2]} {lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} (hGen : HGen Λ ℓ) (hBD : HBallD D ℓ) (hBP : HBallPhi D a b)
    (hSat : HSat Λ S a b) (hCe : HCentre D lam) (hSe : HSeries D lam) (hTa : HTail D lam)
    (hKn : HKnown D S lam) (hEx : HExcl D Twist) (d : ℕ) (hd : d ∈ [1, 2, 3, 4, 5]) (X : ℤ_[2])
    (hX : Twist d X) :
    CondIII Λ S (Wset D.W) (lam d X) ∧ CondIII Λ S (Wset D.W) (-lam d X) ∧
      (lam d X ∈ S → ∃ t ∈ D.tails, t.disc = d ∧ X = (t.Xi : ℤ_[2])) := by
  have hS : Saturated Λ S := saturated_of_isSatOf hSat
  rcases lead_or_known hD hGen hBD hBP hSat hCe hSe hTa hKn hEx d hd X hX with ⟨hm, hk⟩ | ⟨ν, hl⟩
  · have h3 := condIII_of_mem (W := Wset D.W) hS hm
    exact ⟨h3, condIII_neg h3, fun _ => hk⟩
  · have h3 := condIII_of_leading hS hl
    exact ⟨h3, condIII_neg h3, fun hm => absurd hm (not_mem_of_leading hS hl)⟩

/-- The series form on the constant boxes from the antiderivative form on their parent discs. -/
theorem hSeries_of_anti {D : TwistData} (hD : TwistChecks D) {lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    (h : HAntiConst D lam) : HSeries D lam := by
  intro c hc
  obtain ⟨w, hw⟩ := h c hc
  have hs : c.s - 1 + 1 = c.s := Nat.sub_add_cancel (hD.centres c hc).2.2.2.2.2
  obtain ⟨α, h1, h2, -⟩ := rescale_spec hw
  rw [hs] at h1 h2
  exact ⟨α, h1, h2⟩

/-- The series form around the known lifts from the antiderivative form. -/
theorem hTail_of_anti {D : TwistData} (hD : TwistChecks D) {lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    (h : HAntiTail D lam) : HTail D lam := by
  intro t ht
  obtain ⟨w, hw, g, hg, hg0⟩ := h t ht
  have hs0 : t.s0 - 1 + 1 = t.s0 := Nat.sub_add_cancel (hD.tailsOK t ht).2.2.2.2.1
  obtain ⟨α, h1, h2, h0⟩ := rescale_spec hw
  rw [hs0] at h1 h2
  refine ⟨g, α, hg, ?_, h1, h2⟩
  funext i
  apply Subtype.ext
  change ((α 0 i : ℤ_[2]) : ℚ_[2]) = (((2 : ℤ_[2]) ^ (t.s0 - 1) * g i : ℤ_[2]) : ℚ_[2])
  have h2c : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := rfl
  rw [h0 i, PadicInt.coe_mul, ← hg0 i, PadicInt.coe_pow, h2c]
  ring

end FurioLombardo.M4
