import Mathlib
import FurioLombardo.M4.Cover
import FurioLombardo.M4.Local

/-!
# Lane M4: every global point of one twist lies over a known point

`twist_local` combines the covering (`cover_iii`), Stoll's criterion (`stoll_sat`) and the Selmer condition
(`hW_of_selLoc`) for the kernel checked data of one twist. `twist_local_anti` is the same statement with the analytic
input in antiderivative form (`HAntiConst`, `HAntiTail`). The instances for δ0 and δ1 are in
`FurioLombardo.M4.Instances`.
-/

namespace FurioLombardo.M4

section TwistLocal

/-- `V = Fin 6 → ℤ_[2]` has no 2-torsion. -/
theorem two_nsmul_eq_zero_V {y : Fin 6 → ℤ_[2]} (h : (2 : ℕ) • y = 0) : y = 0 := by
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-- The Selmer condition `hW` of `stoll_log` from `HSelLoc` and the balls of the `log D_i`. -/
theorem hW_of_selLoc {A B : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B)
    (lam : B →+ (Fin 6 → ℤ_[2])) (Dpt : Fin 7 → B) {D : TwistData} (hD : TwistChecks D)
    (hLam : HLam lam Dpt) (hBD : HBallD D (fun i => lam (Dpt i)))
    (h4 : ∀ x, DvdV 2 x → x ∈ Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i)))
    (hSel : HSelLoc ι Dpt D) :
    ∀ Q : A, ∃ w ∈ Wset D.W, ∃ b : B, lam (ι Q) = w + (2 : ℕ) • lam b := by
  intro Q
  obtain ⟨m, b, hb⟩ := hSel Q
  -- the error of the integer representative
  set e : Fin 6 → ℤ_[2] := ∑ i, (selc D.SB m i : ℤ_[2]) • (lam (Dpt i) - icast (D.lD i)) with he
  have hWm : icast (D.W m) = ∑ i, (selc D.SB m i : ℤ_[2]) • icast (D.lD i) := by
    funext o
    simp only [icast, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hD.hWc m o]
    push_cast; rfl
  have he3 : DvdV 3 e := by
    intro o
    simp only [he, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.dvd_sum (fun i _ => Dvd.dvd.mul_left
      ((pow_dvd_pow 2 (hD.hqD i)).trans (hBD i o)) _)
  obtain ⟨t, ht⟩ := exists_eq_two_pow_smul he3
  have h4t : DvdV 2 ((4 : ℤ_[2]) • t) := by
    intro o; simp only [Pi.smul_apply, smul_eq_mul]; exact ⟨t o, by norm_num⟩
  obtain ⟨b', hb'⟩ := (hLam _).2 (h4 _ h4t)
  refine ⟨icast (D.W m), ⟨m, rfl⟩, b + b', ?_⟩
  rw [hb, map_add, map_sum, map_nsmul, map_add, smul_add, hb']
  have hsum : ∑ i, lam (selc D.SB m i • Dpt i) = icast (D.W m) + e := by
    rw [hWm, he, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_zsmul, ← smul_add, add_sub_cancel, Int.cast_smul_eq_zsmul]
  rw [hsum, ht]
  have e8 : (2 : ℤ_[2]) ^ 3 • t = (2 : ℕ) • ((4 : ℤ_[2]) • t) := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[2], smul_smul]; norm_num
  rw [e8]; abel

/-- **M4, one twist.** Every global point `x` of `D_δ(k)` lies over a known point: its parameter is that of
a known lift `x_i`. Inputs: the kernel checked data `D` (`hD`), the analytic and computed facts at `v` as named
hypotheses (`HLam`, `HBallD`, `HBallPhi`, `HCentre`, `HSeries`, `HTail`, `HKnown`, `HExcl`, `HDisc`), the
global facts `hloc` (local injectivity, from `σ_v` injective), `hker` (kernel of the logarithm), `2T = 0` and
`HSelLoc`. `S` is the saturation in `Λ` of the span of the logarithms of `φ(x_a)`, `φ(x_b)`. -/
theorem twist_local {A B Dk : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B)
    (lam : B →+ (Fin 6 → ℤ_[2])) (T : A) (Dpt : Fin 7 → B) {D : TwistData} (hD : TwistChecks D)
    (S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])) (φ : Dk → A) (xa xb : Dk)
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) (Twist : ℕ → ℤ_[2] → Prop) (disc : Dk → ℕ) (par : Dk → ℤ_[2])
    (hLam : HLam lam Dpt) (hBD : HBallD D (fun i => lam (Dpt i)))
    (hBP : HBallPhi D (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hSat : HSat (Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i))) S (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hCe : HCentre D lamD) (hSe : HSeries D lamD) (hTa : HTail D lamD) (hKn : HKnown D S lamD)
    (hEx : HExcl D Twist) (hDi : HDisc ι lam S φ xa disc par lamD Twist)
    (hloc : ∀ Q : A, (∃ b : B, ι Q = (2 : ℕ) • b) → ∃ Q' : A, Q = (2 : ℕ) • Q')
    (hker : ∀ b : B, lam b = 0 → ∃ c : B, b = (2 : ℕ) • c ∨ b = ι T + (2 : ℕ) • c)
    (hT2 : (2 : ℕ) • T = 0) (hSel : HSelLoc ι Dpt D) (x : Dk) :
    ∃ t ∈ D.tails, t.disc = disc x ∧ par x = (t.Xi : ℤ_[2]) := by
  set Λ := Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i)) with hΛdef
  have hGen : HGen Λ (fun i => lam (Dpt i)) := rfl
  obtain ⟨-, h4, -⟩ := qchar_of_cert hD hGen hBD hBP hSat
  have hS : Saturated Λ S := saturated_of_isSatOf hSat
  obtain ⟨hd, htw, hbr⟩ := hDi x
  obtain ⟨h3, h3n, hknown⟩ := cover_iii hD hGen hBD hBP hSat hCe hSe hTa hKn hEx (disc x) hd (par x) htw
  have hfin : Module.Finite ℤ_[2] Λ := Module.Finite.span_of_finite ℤ_[2] (Set.finite_range _)
  have hW := hW_of_selLoc ι lam Dpt hD hLam hBD h4 hSel
  -- condition (iii) at y = log φ(x) - log φ(x_a)
  have hiii : CondIII Λ S (Wset D.W) (lam (ι (φ x - φ xa))) := by
    rcases hbr with h | h
    · have := condIII_add_mem h3 h
      rwa [add_sub_cancel] at this
    · have := condIII_add_mem h3n h
      rwa [show -lamD (disc x) (par x) + (lam (ι (φ x - φ xa)) + lamD (disc x) (par x)) =
        lam (ι (φ x - φ xa)) by abel] at this
  have hmem := stoll_sat ι lam T Λ S (Wset D.W) (φ xa) (φ xb) (fun y hy => two_nsmul_eq_zero_V hy)
    (fun y => (hLam y).symm) hSat hloc hker hT2 hW (φ x - φ xa) hiii
  apply hknown
  rcases hbr with h | h
  · have := S.sub_mem hmem h
    rwa [sub_sub_cancel] at this
  · have := S.sub_mem h hmem
    rwa [add_sub_cancel_left] at this

/-- Local injectivity from the injectivity of `σ_v`: `κ : A → Sel` is the global Kummer map (kernel `2A`),
`ρ : B → H` the local one into a group killed by 2, and `ρ ∘ ι = σ ∘ κ`. -/
theorem hLocInj_of_sigma {A B Sel H : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup Sel] [AddCommGroup H]
    (ι : A →+ B) (κ : A →+ Sel) (ρ : B →+ H) (σ : Sel →+ H)
    (hκ : ∀ Q : A, κ Q = 0 → ∃ Q' : A, Q = (2 : ℕ) • Q') (hH : ∀ h : H, (2 : ℕ) • h = 0)
    (hcomm : ∀ Q : A, ρ (ι Q) = σ (κ Q)) (hσ : ∀ s, σ s = 0 → s = 0) : HLocInj ι := by
  rintro Q ⟨b, hb⟩
  apply hκ
  apply hσ
  rw [← hcomm, hb, map_nsmul, hH]

/-- `twist_local` with the analytic input in antiderivative form on the parent discs. -/
theorem twist_local_anti {A B Dk : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B)
    (lam : B →+ (Fin 6 → ℤ_[2])) (T : A) (Dpt : Fin 7 → B) {D : TwistData} (hD : TwistChecks D)
    (S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])) (φ : Dk → A) (xa xb : Dk)
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) (Twist : ℕ → ℤ_[2] → Prop) (disc : Dk → ℕ) (par : Dk → ℤ_[2])
    (hLam : HLam lam Dpt) (hBD : HBallD D (fun i => lam (Dpt i)))
    (hBP : HBallPhi D (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hSat : HSat (Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i))) S (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hCe : HCentre D lamD) (hAC : HAntiConst D lamD) (hAT : HAntiTail D lamD) (hKn : HKnown D S lamD)
    (hEx : HExcl D Twist) (hDi : HDisc ι lam S φ xa disc par lamD Twist)
    (hloc : HLocInj ι) (hker : HKer ι lam T) (hSel : HSelLoc ι Dpt D) (x : Dk) :
    ∃ t ∈ D.tails, t.disc = disc x ∧ par x = (t.Xi : ℤ_[2]) :=
  twist_local ι lam T Dpt hD S φ xa xb lamD Twist disc par hLam hBD hBP hSat hCe (hSeries_of_anti hD hAC)
    (hTail_of_anti hD hAT) hKn hEx hDi hloc hker.1 hker.2 hSel x

/-- **Interface with lane M3a** (its `CoverIII` and `KnownZero`, FurioLombardo.M3a.Hypotheses): for a family `y` of
logarithms that are, modulo `S`, `±` the analytic branch at points of twist δ, condition (iii) holds at every `y x`,
and `y x ∈ S` only over a known lift. `Λ` is the span of the `ℓ i`, `S` the saturation of `span {a, b}` in it. -/
theorem cover_lifts {Dk : Type*} {D : TwistData} (hD : TwistChecks D) {ℓ : Fin 7 → Fin 6 → ℤ_[2]}
    {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {a b : Fin 6 → ℤ_[2]} {lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]}
    {Twist : ℕ → ℤ_[2] → Prop} {disc : Dk → ℕ} {par : Dk → ℤ_[2]} {y : Dk → Fin 6 → ℤ_[2]}
    (hGen : HGen Λ ℓ) (hBD : HBallD D ℓ) (hBP : HBallPhi D a b) (hSat : HSat Λ S a b)
    (hCe : HCentre D lamD) (hAC : HAntiConst D lamD) (hAT : HAntiTail D lamD) (hKn : HKnown D S lamD)
    (hEx : HExcl D Twist)
    (hy : ∀ x, disc x ∈ [1, 2, 3, 4, 5] ∧ Twist (disc x) (par x) ∧
      (y x - lamD (disc x) (par x) ∈ S ∨ y x + lamD (disc x) (par x) ∈ S)) :
    (∀ x, CondIII Λ S (Wset D.W) (y x)) ∧
      ∀ x, y x ∈ S → ∃ t ∈ D.tails, t.disc = disc x ∧ par x = (t.Xi : ℤ_[2]) := by
  have hSe := hSeries_of_anti hD hAC
  have hTa := hTail_of_anti hD hAT
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · obtain ⟨hd, htw, hbr⟩ := hy x
    obtain ⟨h3, h3n, -⟩ := cover_iii hD hGen hBD hBP hSat hCe hSe hTa hKn hEx (disc x) hd (par x) htw
    rcases hbr with h | h
    · have := condIII_add_mem h3 h
      rwa [add_sub_cancel] at this
    · have := condIII_add_mem h3n h
      rwa [show -lamD (disc x) (par x) + (y x + lamD (disc x) (par x)) = y x by abel] at this
  · obtain ⟨hd, htw, hbr⟩ := hy x
    obtain ⟨-, -, hknown⟩ := cover_iii hD hGen hBD hBP hSat hCe hSe hTa hKn hEx (disc x) hd (par x) htw
    apply hknown
    rcases hbr with h | h
    · have := S.sub_mem hx h
      rwa [sub_sub_cancel] at this
    · have := S.sub_mem h hx
      rwa [add_sub_cancel_left] at this

end TwistLocal

end FurioLombardo.M4
