import Mathlib
import FurioLombardo.Discharge.M4Box.Weak
import FurioLombardo.M4.Instances

/-!
# Lane M4's covering argument with the box inputs in the weak form

A copy of `FurioLombardo.M4.lead_or_known`, `cover_iii` and `cover_lifts` where the analytic box
hypotheses `HAntiConst`, `HAntiTail` are replaced by the two bounds they are used for,
`HConstLip` and `HTailQuad` (Weak.lean):

* `const_box_leading_w`, `tail_leading_w`: the lemmas `const_box_leading`, `tail_leading` taking the
  bound on `λ(X) - λ(centre)` directly instead of the series;
* on a tail box, `g ∈ Λ` comes from its certified ball `DvdV t.q (g - icast t.g)` (`q ≥ 2`) and the
  data check `TailsFour D` (every coordinate of every `t.g` is divisible by 4), checked by
  `decide +kernel` for both twists (`T0_tailsFour`, `T1_tailsFour`);
* `lead_or_known_w`, `cover_iii_w`, `cover_lifts_w`: the chain.
-/

namespace FurioLombardo.Discharge.M4Box

open FurioLombardo.M4

/-- Every coordinate of the centre `g` of every tail box is divisible by 4. -/
def TailsFour (D : TwistData) : Prop := ∀ t ∈ D.tails, ∀ i : Fin 6, (4 : ℤ) ∣ t.g i

theorem T0_tailsFour_data : ∀ b ∈ FurioLombardo.M4.T0.tails, ∀ i : Fin 6, (4 : ℤ) ∣ b.g i := by
  decide +kernel

theorem T1_tailsFour_data : ∀ b ∈ FurioLombardo.M4.T1.tails, ∀ i : Fin 6, (4 : ℤ) ∣ b.g i := by
  decide +kernel

theorem T0_tailsFour : TailsFour FurioLombardo.M4.T0.data := T0_tailsFour_data

theorem T1_tailsFour : TailsFour FurioLombardo.M4.T1.data := T1_tailsFour_data

/-- `const_box_leading` with the bound on `lX - lc` given directly. -/
theorem const_box_leading_w {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])}
    {W : Set (Fin 6 → ℤ_[2])} (h4 : ∀ x, DvdV 2 x → x ∈ Λ) {ν B : ℕ} {lc lX : Fin 6 → ℤ_[2]}
    (hlead : Leading Λ S W ν lc) (hB : B = ν + 3) (hlip : DvdV B (lX - lc)) :
    Leading Λ S W ν lX := by
  have hlip' : DvdV (2 + (ν + 1)) (lX - lc) := by rw [show 2 + (ν + 1) = B by omega]; exact hlip
  obtain ⟨l, hl, heq⟩ := mem_of_dvdV h4 hlip'
  exact leading_perturb hlead hl heq

/-- `tail_leading` with the first order bound `h1` given directly. -/
theorem tail_leading_w {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])}
    {W : Set (Fin 6 → ℤ_[2])} (hS : Saturated Λ S) (h4 : ∀ x, DvdV 2 x → x ∈ Λ) {ν B s0 t : ℕ}
    (hs0 : 1 ≤ s0) (ht : ν + 2 + s0 ≤ B + t) {g yi : Fin 6 → ℤ_[2]} (hg : Leading Λ S W ν g)
    (hyi : yi ∈ S) {u : ℤ_[2]} (hu : IsUnit u) {lX : Fin 6 → ℤ_[2]}
    (h1 : DvdV (B + 2 * t) (lX - yi - ((2 : ℤ_[2]) ^ t * u) • ((2 : ℤ_[2]) ^ (s0 - 1) • g))) :
    Leading Λ S W (ν + (t + s0 - 1)) lX := by
  set j := t + s0 - 1 with hj
  have h2 : DvdV (2 + (ν + j + 1)) (lX - yi - ((2 : ℤ_[2]) ^ t * u) • ((2 : ℤ_[2]) ^ (s0 - 1) • g)) :=
    dvdV_mono (by omega) h1
  obtain ⟨l, hl, hle⟩ := mem_of_dvdV h4 h2
  have hpow : ((2 : ℤ_[2]) ^ t * u) • ((2 : ℤ_[2]) ^ (s0 - 1) • g) = (2 : ℤ_[2]) ^ j • (u • g) := by
    rw [smul_smul, smul_smul, hj, show t + s0 - 1 = t + (s0 - 1) by omega, pow_add]
    congr 1
    ring
  obtain ⟨w, hw⟩ := unit_eq_one_add_two hu
  have hlX : lX = yi + (2 : ℤ_[2]) ^ j • (u • g) + (2 : ℤ_[2]) ^ (ν + j + 1) • l := by
    rw [← hpow, ← hle]; abel
  rw [hlX]
  exact leading_tail hS hg hyi u w hw hl

/-- A vector in the ball of radius `2^-q`, `q ≥ 2`, around an integer vector divisible by 4 is in
`Λ` when `Λ ⊇ 4 ℤ_2^6`. -/
theorem mem_of_ball_four {Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2])}
    (h4 : ∀ x, DvdV 2 x → x ∈ Λ) {q : ℕ} (hq : 2 ≤ q) {y : Fin 6 → ℤ} (hy : ∀ i, (4 : ℤ) ∣ y i)
    {g : Fin 6 → ℤ_[2]} (hg : DvdV q (g - icast y)) : g ∈ Λ := by
  apply h4
  have hy2 : DvdV 2 (icast y) := fun i =>
    (intCast_two_pow_dvd_iff 2 (y i)).mpr (by norm_num; exact hy i)
  have := dvdV_add (dvdV_mono hq hg) hy2
  rwa [sub_add_cancel] at this

/-- `lead_or_known` with the box inputs `HConstLip`, `HTailQuad` and the data check `TailsFour`. -/
theorem lead_or_known_w {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {D : TwistData}
    (hD : TwistChecks D) (hg4 : TailsFour D)
    {ℓ : Fin 7 → Fin 6 → ℤ_[2]} {a b : Fin 6 → ℤ_[2]} {lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} (hGen : HGen Λ ℓ) (hBD : HBallD D ℓ) (hBP : HBallPhi D a b)
    (hSat : HSat Λ S a b) (hCe : HCentre D lam) (hCL : HConstLip D lam) (hTQ : HTailQuad D lam)
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
      · have := (intCast_two_pow_dvd_iff 2 (D.G.mulVec c.y j)).mpr
          (by norm_num; exact hD.centresMem c hc j)
        norm_num at this; exact this
      · have := dvdV_imv D.G (dvdV_mono (show 2 ≤ c.q by omega) hball) j
        norm_num at this; exact this
    have hlead := centre_leading hQ hν hq hok hlc hball
    rw [← hcd]
    exact const_box_leading_w h4 hlead hslack (hCL c hc Y)
  · -- a tail box
    obtain ⟨hok, hq, hν, -, hs0, hs0s, hthr, hmod⟩ := hD.tailsOK t ht
    obtain ⟨g, hg, hquad⟩ := hTQ t ht
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
      have hgΛ : g ∈ Λ := mem_of_ball_four h4 (by omega) (hg4 t ht) hg
      have hLg := centre_leading hQ hν hq hok hgΛ hg
      have hYu : Y = (2 : ℤ_[2]) ^ (t.s - t.s0 + j) * u := by rw [hY, hju, pow_add, mul_assoc]
      rw [hYu]
      exact ⟨_, tail_leading_w (B := t.vM / 3 + t.s0) (t := t.s - t.s0 + j) hS h4 hs0 (by omega)
        hLg (hKn t ht) hu (hquad _ u (Nat.le_add_right _ _) hu)⟩

/-- `cover_iii` with the box inputs `HConstLip`, `HTailQuad` and the data check `TailsFour`. -/
theorem cover_iii_w {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {D : TwistData} (hD : TwistChecks D)
    (hg4 : TailsFour D)
    {ℓ : Fin 7 → Fin 6 → ℤ_[2]} {a b : Fin 6 → ℤ_[2]} {lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} (hGen : HGen Λ ℓ) (hBD : HBallD D ℓ) (hBP : HBallPhi D a b)
    (hSat : HSat Λ S a b) (hCe : HCentre D lam) (hCL : HConstLip D lam) (hTQ : HTailQuad D lam)
    (hKn : HKnown D S lam) (hEx : HExcl D Twist) (d : ℕ) (hd : d ∈ [1, 2, 3, 4, 5]) (X : ℤ_[2])
    (hX : Twist d X) :
    CondIII Λ S (Wset D.W) (lam d X) ∧ CondIII Λ S (Wset D.W) (-lam d X) ∧
      (lam d X ∈ S → ∃ t ∈ D.tails, t.disc = d ∧ X = (t.Xi : ℤ_[2])) := by
  have hS : Saturated Λ S := saturated_of_isSatOf hSat
  rcases lead_or_known_w hD hg4 hGen hBD hBP hSat hCe hCL hTQ hKn hEx d hd X hX with
    ⟨hm, hk⟩ | ⟨ν, hl⟩
  · have h3 := condIII_of_mem (W := Wset D.W) hS hm
    exact ⟨h3, condIII_neg h3, fun _ => hk⟩
  · have h3 := condIII_of_leading hS hl
    exact ⟨h3, condIII_neg h3, fun hm => absurd hm (not_mem_of_leading hS hl)⟩

/-- `cover_lifts` (the interface with lane M3a) with the box inputs `HConstLip`, `HTailQuad` and
the data check `TailsFour`. -/
theorem cover_lifts_w {Dk : Type*} {D : TwistData} (hD : TwistChecks D) (hg4 : TailsFour D)
    {ℓ : Fin 7 → Fin 6 → ℤ_[2]}
    {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {a b : Fin 6 → ℤ_[2]} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Dk → ℕ} {par : Dk → ℤ_[2]} {y : Dk → Fin 6 → ℤ_[2]}
    (hGen : HGen Λ ℓ) (hBD : HBallD D ℓ) (hBP : HBallPhi D a b) (hSat : HSat Λ S a b)
    (hCe : HCentre D lamD) (hCL : HConstLip D lamD) (hTQ : HTailQuad D lamD)
    (hKn : HKnown D S lamD) (hEx : HExcl D Twist)
    (hy : ∀ x, disc x ∈ [1, 2, 3, 4, 5] ∧ Twist (disc x) (par x) ∧
      (y x - lamD (disc x) (par x) ∈ S ∨ y x + lamD (disc x) (par x) ∈ S)) :
    (∀ x, CondIII Λ S (Wset D.W) (y x)) ∧
      ∀ x, y x ∈ S → ∃ t ∈ D.tails, t.disc = disc x ∧ par x = (t.Xi : ℤ_[2]) := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · obtain ⟨hd, htw, hbr⟩ := hy x
    obtain ⟨h3, h3n, -⟩ :=
      cover_iii_w hD hg4 hGen hBD hBP hSat hCe hCL hTQ hKn hEx (disc x) hd (par x) htw
    rcases hbr with h | h
    · have := condIII_add_mem h3 h
      rwa [add_sub_cancel] at this
    · have := condIII_add_mem h3n h
      rwa [show -lamD (disc x) (par x) + (y x + lamD (disc x) (par x)) = y x by abel] at this
  · obtain ⟨hd, htw, hbr⟩ := hy x
    obtain ⟨-, -, hknown⟩ :=
      cover_iii_w hD hg4 hGen hBD hBP hSat hCe hCL hTQ hKn hEx (disc x) hd (par x) htw
    apply hknown
    rcases hbr with h | h
    · have := S.sub_mem hx h
      rwa [sub_sub_cancel] at this
    · have := S.sub_mem h hx
      rwa [add_sub_cancel_left] at this

end FurioLombardo.Discharge.M4Box
