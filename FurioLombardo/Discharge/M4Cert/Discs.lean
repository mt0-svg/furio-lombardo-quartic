import Mathlib
import FurioLombardo.Discharge.M4Cert.Curve
import FurioLombardo.M3a.Hypotheses
import FurioLombardo.M4.Instances

/-!
# The disc covering of `C(ℚ_2)`, the twist at the lifts, and the tail centres

* `exists_disc`: every nonzero point of `C(ℚ_2)` is, up to a nonzero factor, `discPt d X Y` for one
  of the five discs `d` and `X, Y ∈ ℤ_[2]` (reduction modulo 2: the residue points `(0:1:1)` and
  `(1:0:0)` are not on `C mod 2`).
* `twist_of_over`: a point of `D_δ(K21)` (M3a's `DPoint`) above a rational point of `C` gives
  `Twist M1 M2 M3 δ d X` at the disc parameters of that point.
* `liftDisc`, `liftPar`: a disc and a parameter for every lift (M3a's `Route.Lift`), with
  `liftTwist` (the first two conjuncts of lane M4's `HDisc` / M3a's `LiftDisc`).
* `tailGood_T0`, `tailGood_T1`: a lift whose disc and parameter are those of a tail centre of
  `T0.data` (`T1.data`) lies over one of the two known points of the twist (M3a's `TailGood`):
  on the four tail centres the equation of `C` has the single root `Y = 0` in `ℤ_[2]`.

The points of the lifts are assumed on `C` (`OnC`): this is the identity `Q1 Q3 - Q2² = c F`
(`FurioLombardo.Discharge.M4Cert.OnCurve`).
-/

namespace FurioLombardo.Discharge.M4Cert

open FurioLombardo.M1 Matrix

local notation "F" => FurioLombardo.F

/-! ## Reduction modulo 2 in `ℚ_[2]` -/

theorem F_smul {R : Type*} [CommRing R] (μ x y z : R) :
    F (μ * x) (μ * y) (μ * z) = μ ^ 4 * F x y z := by
  unfold FurioLombardo.F; ring

/-- An element of the unit ball of `ℚ_[2]` is `b + 2X`, `b ∈ {0, 1}`, `X ∈ ℤ_[2]`. -/
theorem exists_bit {w : ℚ_[2]} (hw : ‖w‖ ≤ 1) :
    ∃ b : ℕ, b < 2 ∧ ∃ X : ℤ_[2], w = (((b : ℤ_[2]) + 2 * X : ℤ_[2]) : ℚ_[2]) := by
  set z : ℤ_[2] := ⟨w, hw⟩ with hz
  refine ⟨z.appr 1, by simpa using PadicInt.appr_lt z 1, ?_⟩
  have h := PadicInt.appr_spec 1 z
  rw [Ideal.mem_span_singleton, pow_one, Nat.cast_ofNat] at h
  obtain ⟨X, hX⟩ := h
  refine ⟨X, ?_⟩
  have e : z = ((z.appr 1 : ℕ) : ℤ_[2]) + 2 * X := by rw [← hX]; ring
  rw [← e]

/-- An element of `ℚ_[2]` of norm `< 1` is `2Y`, `Y ∈ ℤ_[2]`. -/
theorem exists_two_mul {w : ℚ_[2]} (hw : ‖w‖ < 1) : ∃ Y : ℤ_[2], w = ((2 * Y : ℤ_[2]) : ℚ_[2]) := by
  set z : ℤ_[2] := ⟨w, hw.le⟩ with hz
  have h : ‖z‖ < 1 := hw
  rw [PadicInt.norm_lt_one_iff_dvd, Nat.cast_ofNat] at h
  obtain ⟨Y, hY⟩ := h
  exact ⟨Y, by rw [← hY]⟩

theorem F_ne_of_odd {x y z : ℤ_[2]} {a b c : ℤ} (ha : (2 : ℤ_[2]) ∣ x - a)
    (hb : (2 : ℤ_[2]) ∣ y - b) (hc : (2 : ℤ_[2]) ∣ z - c) (hodd : ¬ (2 : ℤ) ∣ F a b c) :
    F x y z ≠ 0 := by
  intro hF
  have := F_dvd_of_congr (n := 1) (p := ![x, y, z]) (q := ![a, b, c])
    (fun i => by fin_cases i <;> simpa using (by assumption)) hF
  exact hodd (by simpa using this)

theorem coe_F (x y z : ℤ_[2]) : ((F x y z : ℤ_[2]) : ℚ_[2]) = F (x : ℚ_[2]) (y : ℚ_[2]) (z : ℚ_[2]) :=
  map_F PadicInt.Coe.ringHom x y z

theorem F_eq_zero_of_coe {x y z : ℤ_[2]} (h : F (x : ℚ_[2]) (y : ℚ_[2]) (z : ℚ_[2]) = 0) :
    F x y z = 0 := by
  have := coe_F x y z
  rw [h] at this
  exact PadicInt.coe_eq_zero.1 this

theorem dvd_bit (b : ℕ) (X : ℤ_[2]) : (2 : ℤ_[2]) ∣ ((b : ℤ_[2]) + 2 * X) - ((b : ℤ) : ℤ_[2]) :=
  ⟨X, by push_cast; ring⟩

theorem dvd_two_mul (Y : ℤ_[2]) : (2 : ℤ_[2]) ∣ 2 * Y - ((0 : ℤ) : ℤ_[2]) := ⟨Y, by push_cast; ring⟩

theorem dvd_one' : (2 : ℤ_[2]) ∣ (1 : ℤ_[2]) - ((1 : ℤ) : ℤ_[2]) := ⟨0, by push_cast; ring⟩

/-! ## The disc covering -/

/-- **Disc covering.** Every nonzero point of `C(ℚ_2)` is, up to a nonzero factor, a point of one of
the five discs. -/
theorem exists_disc (u : Fin 3 → ℚ_[2]) (hu : u ≠ 0) (hF : F (u 0) (u 1) (u 2) = 0) :
    ∃ d ∈ [1, 2, 3, 4, 5], ∃ X Y : ℤ_[2], ∃ μ : ℚ_[2], μ ≠ 0 ∧
      ∀ i, μ * u i = ((discPt d X Y i : ℤ_[2]) : ℚ_[2]) := by
  have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    funext i
    fin_cases i <;> simp [h.1, h.2.1, h.2.2]
  have hFμ : ∀ μ : ℚ_[2], F (μ * u 0) (μ * u 1) (μ * u 2) = 0 := fun μ => by
    rw [F_smul, hF, mul_zero]
  by_cases hz : ‖u 0‖ ≤ ‖u 2‖ ∧ ‖u 1‖ ≤ ‖u 2‖
  · -- the chart z = 1
    have hu2 : u 2 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hz
      rcases hne with h | h | h
      · exact h (norm_le_zero_iff.1 hz.1)
      · exact h (norm_le_zero_iff.1 hz.2)
      · exact h h0
    have hn2 : 0 < ‖u 2‖ := norm_pos_iff.2 hu2
    have hw0 : ‖(u 2)⁻¹ * u 0‖ ≤ 1 := by
      rw [norm_mul, norm_inv, inv_mul_le_one₀ hn2]; exact hz.1
    have hw1 : ‖(u 2)⁻¹ * u 1‖ ≤ 1 := by
      rw [norm_mul, norm_inv, inv_mul_le_one₀ hn2]; exact hz.2
    have h2 : (u 2)⁻¹ * u 2 = 1 := inv_mul_cancel₀ hu2
    obtain ⟨b0, hb0, X, hX⟩ := exists_bit hw0
    obtain ⟨b1, hb1, Y, hY⟩ := exists_bit hw1
    have hFz : F ((b0 : ℤ_[2]) + 2 * X) ((b1 : ℤ_[2]) + 2 * Y) 1 = 0 := by
      apply F_eq_zero_of_coe
      have := hFμ (u 2)⁻¹
      rwa [hX, hY, h2, ← PadicInt.coe_one] at this
    have hμ : (u 2)⁻¹ ≠ 0 := inv_ne_zero hu2
    interval_cases b0 <;> interval_cases b1
    · refine ⟨1, by simp, X, Y, (u 2)⁻¹, hμ, fun i => ?_⟩
      fin_cases i <;> simp [discPt, hX, hY, h2]
    · exact absurd hFz (F_ne_of_odd (a := 0) (b := 1) (c := 1) (by simp)
        (by simp) dvd_one' (by decide))
    · refine ⟨2, by simp, X, Y, (u 2)⁻¹, hμ, fun i => ?_⟩
      fin_cases i <;> simp [discPt, hX, hY, h2]
    · refine ⟨3, by simp, X, Y, (u 2)⁻¹, hμ, fun i => ?_⟩
      fin_cases i <;> simp [discPt, hX, hY, h2]
  · by_cases hy : ‖u 0‖ ≤ ‖u 1‖
    · -- the chart y = 1, z ∈ 2ℤ_2
      have h21 : ‖u 2‖ < ‖u 1‖ := by
        by_contra hc
        push Not at hc
        exact hz ⟨hy.trans hc, hc⟩
      have hu1 : u 1 ≠ 0 := by
        intro h0; rw [h0, norm_zero] at h21; exact absurd h21 (not_lt.2 (norm_nonneg _))
      have hn1 : 0 < ‖u 1‖ := norm_pos_iff.2 hu1
      have hw0 : ‖(u 1)⁻¹ * u 0‖ ≤ 1 := by
        rw [norm_mul, norm_inv, inv_mul_le_one₀ hn1]; exact hy
      have hw2 : ‖(u 1)⁻¹ * u 2‖ < 1 := by
        rw [norm_mul, norm_inv, inv_mul_lt_one₀ hn1]; exact h21
      have h1 : (u 1)⁻¹ * u 1 = 1 := inv_mul_cancel₀ hu1
      obtain ⟨b0, hb0, X, hX⟩ := exists_bit hw0
      obtain ⟨Y, hY⟩ := exists_two_mul hw2
      have hμ : (u 1)⁻¹ ≠ 0 := inv_ne_zero hu1
      interval_cases b0
      · refine ⟨4, by simp, X, Y, (u 1)⁻¹, hμ, fun i => ?_⟩
        fin_cases i <;> simp [discPt, hX, hY, h1]
      · refine ⟨5, by simp, X, Y, (u 1)⁻¹, hμ, fun i => ?_⟩
        fin_cases i <;> simp [discPt, hX, hY, h1]
    · -- x dominant: impossible
      push Not at hy
      have h20 : ‖u 2‖ < ‖u 0‖ := by
        by_contra hc
        push Not at hc
        exact hz ⟨hc, hy.le.trans hc⟩
      have hu0 : u 0 ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hy; exact absurd hy (not_lt.2 (norm_nonneg _))
      have hn0 : 0 < ‖u 0‖ := norm_pos_iff.2 hu0
      have hw1 : ‖(u 0)⁻¹ * u 1‖ < 1 := by
        rw [norm_mul, norm_inv, inv_mul_lt_one₀ hn0]; exact hy
      have hw2 : ‖(u 0)⁻¹ * u 2‖ < 1 := by
        rw [norm_mul, norm_inv, inv_mul_lt_one₀ hn0]; exact h20
      have h0 : (u 0)⁻¹ * u 0 = 1 := inv_mul_cancel₀ hu0
      obtain ⟨Y, hY⟩ := exists_two_mul hw1
      obtain ⟨Z, hZ⟩ := exists_two_mul hw2
      have hFz : F 1 (2 * Y) (2 * Z) = 0 := by
        apply F_eq_zero_of_coe
        have := hFμ (u 0)⁻¹
        rwa [hY, hZ, h0, ← PadicInt.coe_one] at this
      exact absurd hFz (F_ne_of_odd (a := 1) (b := 0) (c := 0) dvd_one' (dvd_two_mul Y)
        (dvd_two_mul Z) (by decide))

/-! ## The twist at the points of `D_δ(K21)` above rational points -/

theorem σ_algebraMap (q : ℚ) : σ (algebraMap ℚ K21 q) = algebraMap ℚ_[2] Kv (q : ℚ_[2]) := by
  rw [eq_ratCast (algebraMap ℚ K21), map_ratCast, map_ratCast]

theorem F_rat_cast (a b c : ℚ) : ((F a b c : ℚ) : ℚ_[2]) = F (a : ℚ_[2]) (b : ℚ_[2]) (c : ℚ_[2]) :=
  map_F (Rat.castHom ℚ_[2]) a b c

/-- The point of `D_δ(K_v)` image of a point of `D_δ(K21)`. -/
noncomputable def DPoint.mapσ {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (x : FurioLombardo.M3a.DPoint K21 M1 M2 M3 δ) :
    FurioLombardo.M3a.DPoint Kv (M1.map σ) (M2.map σ) (M3.map σ) (σ δ) where
  p := fun i => σ (x.p i)
  r := σ x.r
  s := σ x.s
  ne_zero := by
    intro h
    apply x.ne_zero
    funext i
    have := congrFun h i
    exact σ.injective (by simpa using this)
  eq1 := by
    have := congrArg σ x.eq1
    rw [RingHom.map_dotProduct, map_mul, map_pow] at this
    rw [← this]
    congr 1
    funext i
    exact (RingHom.map_mulVec σ M1 x.p i).symm
  eq2 := by
    have := congrArg σ x.eq2
    rw [RingHom.map_dotProduct, map_mul, map_mul] at this
    rw [← this]
    congr 1
    funext i
    exact (RingHom.map_mulVec σ M2 x.p i).symm
  eq3 := by
    have := congrArg σ x.eq3
    rw [RingHom.map_dotProduct, map_mul, map_pow] at this
    rw [← this]
    congr 1
    funext i
    exact (RingHom.map_mulVec σ M3 x.p i).symm

/-- A point of `D_δ(K21)` above a rational point of `C` of disc parameters `(d, X, Y)` gives
`Twist M1 M2 M3 δ d X`. -/
theorem twist_of_over {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (x : FurioLombardo.M3a.DPoint K21 M1 M2 M3 δ) {a b c : ℚ} (hx : x.Over a b c)
    (hF : F a b c = 0) {d : ℕ} {X Y : ℤ_[2]} {μ : ℚ_[2]} (hμ : μ ≠ 0)
    (h0 : μ * (a : ℚ_[2]) = ((discPt d X Y 0 : ℤ_[2]) : ℚ_[2]))
    (h1 : μ * (b : ℚ_[2]) = ((discPt d X Y 1 : ℤ_[2]) : ℚ_[2]))
    (h2 : μ * (c : ℚ_[2]) = ((discPt d X Y 2 : ℤ_[2]) : ℚ_[2])) :
    Twist M1 M2 M3 δ d X := by
  obtain ⟨t0, ht0, hp⟩ := hx
  refine ⟨Y, ?_, DPoint.mapσ x, σ t0 * (algebraMap ℚ_[2] Kv μ)⁻¹, ?_, ?_⟩
  · apply F_eq_zero_of_coe
    rw [← h0, ← h1, ← h2, F_smul, ← F_rat_cast, hF, Rat.cast_zero, mul_zero]
  · refine mul_ne_zero (fun h => ht0 (σ.injective (by simpa using h))) (inv_ne_zero ?_)
    intro h
    exact hμ ((algebraMap ℚ_[2] Kv).injective (by simpa using h))
  · have hμ' : algebraMap ℚ_[2] Kv μ ≠ 0 := fun h =>
      hμ ((algebraMap ℚ_[2] Kv).injective (by simpa using h))
    have key : ∀ (q : ℚ) (i : Fin 3), μ * (q : ℚ_[2]) = ((discPt d X Y i : ℤ_[2]) : ℚ_[2]) →
        σ t0 * σ (algebraMap ℚ K21 q) =
          σ t0 * (algebraMap ℚ_[2] Kv μ)⁻¹ * toKv (discPt d X Y i) := by
      intro q i hq
      have ht : toKv (discPt d X Y i) = algebraMap ℚ_[2] Kv μ * algebraMap ℚ_[2] Kv (q : ℚ_[2]) := by
        rw [← map_mul, hq]; rfl
      rw [ht, σ_algebraMap]
      field_simp
    funext i
    show σ (x.p i) = σ t0 * (algebraMap ℚ_[2] Kv μ)⁻¹ * toKv (discPt d X Y i)
    rw [hp]
    fin_cases i
    · simpa using key a 0 h0
    · simpa using key b 1 h1
    · simpa using key c 2 h2

/-! ## Disc and parameter of a lift -/

/-- The points of `D_δ(K21)` above rational points lie on `C`. -/
def OnC (M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21) (δ : K21) : Prop :=
  ∀ x : FurioLombardo.M3a.DPoint K21 M1 M2 M3 δ, ∀ a b c : ℚ, x.Over a b c → F a b c = 0

/-- A rational point below `x` and its disc parameters. -/
structure DiscData {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (x : FurioLombardo.M3a.DPoint K21 M1 M2 M3 δ) where
  a : ℚ
  b : ℚ
  c : ℚ
  hov : x.Over a b c
  d : ℕ
  hd : d ∈ [1, 2, 3, 4, 5]
  X : ℤ_[2]
  Y : ℤ_[2]
  μ : ℚ_[2]
  hμ : μ ≠ 0
  h0 : μ * (a : ℚ_[2]) = ((discPt d X Y 0 : ℤ_[2]) : ℚ_[2])
  h1 : μ * (b : ℚ_[2]) = ((discPt d X Y 1 : ℤ_[2]) : ℚ_[2])
  h2 : μ * (c : ℚ_[2]) = ((discPt d X Y 2 : ℤ_[2]) : ℚ_[2])

theorem nonempty_discData {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (hC : OnC M1 M2 M3 δ) (x : FurioLombardo.M3a.Route.Lift M1 M2 M3 δ) :
    Nonempty (DiscData x.1) := by
  obtain ⟨a, b, c, hx⟩ := x.2
  have hF := hC x.1 a b c hx
  have hne : ![(a : ℚ_[2]), (b : ℚ_[2]), (c : ℚ_[2])] ≠ 0 := by
    intro h
    obtain ⟨t, -, hp⟩ := hx
    apply x.1.ne_zero
    have ha : a = 0 := by simpa using congrFun h 0
    have hb : b = 0 := by simpa using congrFun h 1
    have hc : c = 0 := by simpa using congrFun h 2
    rw [hp, ha, hb, hc]
    funext i
    fin_cases i <;> simp
  obtain ⟨d, hd, X, Y, μ, hμ, hpt⟩ := exists_disc _ hne (by
    simpa [← F_rat_cast] using hF)
  exact ⟨⟨a, b, c, hx, d, hd, X, Y, μ, hμ, by simpa using hpt 0, by simpa using hpt 1,
    by simpa using hpt 2⟩⟩

open Classical in
/-- The disc of a lift (`0` if the lift has no point of `C` below it, which `OnC` excludes). -/
noncomputable def liftDisc {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (x : FurioLombardo.M3a.Route.Lift M1 M2 M3 δ) : ℕ :=
  if h : Nonempty (DiscData x.1) then (Classical.choice h).d else 0

open Classical in
/-- The parameter of a lift in its disc. -/
noncomputable def liftPar {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (x : FurioLombardo.M3a.Route.Lift M1 M2 M3 δ) : ℤ_[2] :=
  if h : Nonempty (DiscData x.1) then (Classical.choice h).X else 0

theorem liftDisc_eq {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (x : FurioLombardo.M3a.Route.Lift M1 M2 M3 δ) (h : Nonempty (DiscData x.1)) :
    liftDisc x = (Classical.choice h).d := by
  unfold liftDisc; simp [h]

theorem liftPar_eq {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21}
    (x : FurioLombardo.M3a.Route.Lift M1 M2 M3 δ) (h : Nonempty (DiscData x.1)) :
    liftPar x = (Classical.choice h).X := by
  unfold liftPar; simp [h]

/-- **The twist at the lifts** (the first two conjuncts of lane M4's `HDisc` for the lifts). -/
theorem liftTwist {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21} (hC : OnC M1 M2 M3 δ)
    (x : FurioLombardo.M3a.Route.Lift M1 M2 M3 δ) :
    liftDisc x ∈ [1, 2, 3, 4, 5] ∧ Twist M1 M2 M3 δ (liftDisc x) (liftPar x) := by
  have h := nonempty_discData hC x
  rw [liftDisc_eq x h, liftPar_eq x h]
  set D := Classical.choice h
  exact ⟨D.hd, twist_of_over x.1 D.hov (hC x.1 _ _ _ D.hov) D.hμ D.h0 D.h1 D.h2⟩

/-! ## The tail centres -/

theorem eq_zero_of_mul_odd {Y R : ℤ_[2]} {k : ℕ} {o : ℤ} (ho : ¬ (2 : ℤ) ∣ o)
    (h : Y * ((2 : ℤ_[2]) ^ k * ((o : ℤ_[2]) + 2 * R)) = 0) : Y = 0 := by
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · exfalso
    rcases mul_eq_zero.1 h with h | h
    · exact pow_ne_zero k two_ne_zero h
    · apply ho
      have h2 : (2 : ℤ_[2]) ^ 1 ∣ (o : ℤ_[2]) := ⟨-R, by rw [pow_one]; linear_combination h⟩
      simpa using (two_pow_dvd_intCast_iff o 1).1 h2

/-- On the four tail centres of lane M4 (disc, parameter) = (1, 0), (1, 1), (3, 0), (2, -1), the
point of `C` of the disc with that parameter is unique: `Y = 0`. -/
theorem tail_Y_eq_zero {d : ℕ} {Xi : ℤ} (h : (d, Xi) ∈ [(1, 0), (1, 1), (3, 0), (2, -1)])
    (Y : ℤ_[2]) (hF : F (discPt d (Xi : ℤ_[2]) Y 0) (discPt d (Xi : ℤ_[2]) Y 1)
      (discPt d (Xi : ℤ_[2]) Y 2) = 0) : Y = 0 := by
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine eq_zero_of_mul_odd (k := 1) (o := -5) (R := 4 * Y ^ 2 + 16 * Y ^ 3) (by decide) ?_
    rw [← hF]; simp [discPt, FurioLombardo.F]; ring
  · refine eq_zero_of_mul_odd (k := 1) (o := 13) (R := -12 * Y + 28 * Y ^ 2 + 16 * Y ^ 3)
      (by decide) ?_
    rw [← hF]; simp [discPt, FurioLombardo.F]; ring
  · refine eq_zero_of_mul_odd (k := 2) (o := 13) (R := 21 * Y + 24 * Y ^ 2 + 8 * Y ^ 3)
      (by decide) ?_
    rw [← hF]; simp [discPt, FurioLombardo.F]; ring
  · refine eq_zero_of_mul_odd (k := 2) (o := -7) (R := 3 * Y - 4 * Y ^ 2 + 8 * Y ^ 3)
      (by decide) ?_
    rw [← hF]; simp [discPt, FurioLombardo.F]; ring

/-- The rational point of the disc `d` at `X = Xi`, `Y = 0`. -/
def cpt (d : ℕ) (Xi : ℤ) : Fin 3 → ℚ := discPt d (Xi : ℚ) 0

theorem coe_discPt_cpt (d : ℕ) (Xi : ℤ) (i : Fin 3) :
    ((discPt d (Xi : ℤ_[2]) 0 i : ℤ_[2]) : ℚ_[2]) = ((cpt d Xi i : ℚ) : ℚ_[2]) := by
  have h1 := map_discPt PadicInt.Coe.ringHom d (Xi : ℤ_[2]) 0 i
  have h2 := map_discPt (Rat.castHom ℚ_[2]) d (Xi : ℚ) 0 i
  simp only [map_intCast, map_zero, eq_ratCast] at h1 h2
  rw [cpt]
  exact h1.trans h2.symm

/-- Two rational points below the same point of `D_δ` are proportional. -/
theorem over_rat_eq {L : Type*} [Field L] [Algebra ℚ L] {M1 M2 M3 : Matrix (Fin 3) (Fin 3) L}
    {δ : L} (x : FurioLombardo.M3a.DPoint L M1 M2 M3 δ) {a b c a' b' c' : ℚ} (h : x.Over a b c)
    (h' : x.Over a' b' c') (hc : c ≠ 0) : c' ≠ 0 ∧ a' * c = c' * a ∧ b' * c = c' * b := by
  obtain ⟨t, ht, hp⟩ := h
  obtain ⟨t', ht', hp'⟩ := h'
  have e : ∀ i, t * ![algebraMap ℚ L a, algebraMap ℚ L b, algebraMap ℚ L c] i =
      t' * ![algebraMap ℚ L a', algebraMap ℚ L b', algebraMap ℚ L c'] i := fun i => by
    have := congrFun (hp.symm.trans hp') i
    simpa using this
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at e0 e1 e2
  have hinj := (algebraMap ℚ L).injective
  refine ⟨fun h0 => ?_, ?_, ?_⟩
  · rw [h0, map_zero, mul_zero] at e2
    exact hc (hinj (by rw [map_zero]; exact (mul_eq_zero.1 e2).resolve_left ht))
  · apply hinj
    rw [map_mul, map_mul]
    have : t' * (algebraMap ℚ L a' * algebraMap ℚ L c - algebraMap ℚ L c' * algebraMap ℚ L a) = 0 := by
      linear_combination (algebraMap ℚ L c) * e0.symm + (algebraMap ℚ L a) * e2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left ht')
  · apply hinj
    rw [map_mul, map_mul]
    have : t' * (algebraMap ℚ L b' * algebraMap ℚ L c - algebraMap ℚ L c' * algebraMap ℚ L b) = 0 := by
      linear_combination (algebraMap ℚ L c) * e1.symm + (algebraMap ℚ L b) * e2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left ht')

/-- **The tail centres lie over the known points** (M3a's `TailGood`), for twist data whose tail
centres are among the four of lane M4 and are the known points `Pa`, `Pb`. -/
theorem tailGood_of {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21} (hC : OnC M1 M2 M3 δ)
    (D : FurioLombardo.M4.TwistData) (Pa Pb : ℚ × ℚ × ℚ)
    (hT : ∀ t ∈ D.tails, (t.disc, t.Xi) ∈ [(1, 0), (1, 1), (3, 0), (2, -1)] ∧
      ((cpt t.disc t.Xi 0, cpt t.disc t.Xi 1, cpt t.disc t.Xi 2) = Pa ∨
        (cpt t.disc t.Xi 0, cpt t.disc t.Xi 1, cpt t.disc t.Xi 2) = Pb)) :
    ∀ x : FurioLombardo.M3a.Route.Lift M1 M2 M3 δ,
      (∃ t ∈ D.tails, t.disc = liftDisc x ∧ liftPar x = (t.Xi : ℤ_[2])) →
      FurioLombardo.M3a.Route.GoodLift Pa Pb x.1 := by
  rintro x ⟨t, ht, hd, hX⟩
  obtain ⟨hmem, hP⟩ := hT t ht
  have h := nonempty_discData hC x
  rw [liftDisc_eq x h] at hd
  rw [liftPar_eq x h] at hX
  set Dd := Classical.choice h
  have hF0 : F (discPt Dd.d Dd.X Dd.Y 0) (discPt Dd.d Dd.X Dd.Y 1) (discPt Dd.d Dd.X Dd.Y 2) = 0 := by
    apply F_eq_zero_of_coe
    rw [← Dd.h0, ← Dd.h1, ← Dd.h2, F_smul, ← F_rat_cast, hC x.1 _ _ _ Dd.hov, Rat.cast_zero,
      mul_zero]
  rw [← hd, hX] at hF0
  have hY := tail_Y_eq_zero hmem Dd.Y hF0
  have hc2 : cpt t.disc t.Xi 2 = 1 := by
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [cpt, discPt, h1]
  have hq : ∀ i, ((discPt Dd.d Dd.X Dd.Y i : ℤ_[2]) : ℚ_[2]) = ((cpt t.disc t.Xi i : ℚ) : ℚ_[2]) := by
    intro i; rw [← hd, hX, hY]; exact coe_discPt_cpt _ _ i
  have e0 := Dd.h0
  have e1 := Dd.h1
  have e2 := Dd.h2
  rw [hq] at e0 e1 e2
  rw [hc2, Rat.cast_one] at e2
  have hc : Dd.c ≠ 0 := by
    intro h0; rw [h0, Rat.cast_zero, mul_zero] at e2; exact zero_ne_one e2
  -- the rational point is `c • cpt`
  have ha : Dd.a = Dd.c * cpt t.disc t.Xi 0 := by
    apply Rat.cast_injective (α := ℚ_[2])
    push_cast
    linear_combination (-(Dd.a : ℚ_[2])) * e2 + (Dd.c : ℚ_[2]) * e0
  have hb : Dd.b = Dd.c * cpt t.disc t.Xi 1 := by
    apply Rat.cast_injective (α := ℚ_[2])
    push_cast
    linear_combination (-(Dd.b : ℚ_[2])) * e2 + (Dd.c : ℚ_[2]) * e1
  intro a' b' c' hov'
  obtain ⟨hc', ha', hb'⟩ := over_rat_eq x.1 Dd.hov hov' hc
  have hsame : FurioLombardo.SameProjPoint a' b' c'
      (cpt t.disc t.Xi 0, cpt t.disc t.Xi 1, cpt t.disc t.Xi 2) := by
    refine ⟨c', hc', ?_, ?_, ?_⟩
    · apply mul_right_cancel₀ hc
      rw [ha', ha]; ring
    · apply mul_right_cancel₀ hc
      rw [hb', hb]; ring
    · simp [hc2]
  rcases hP with hPa | hPb
  · exact Or.inl (hPa ▸ hsame)
  · exact Or.inr (hPb ▸ hsame)

/-- M3a's `TailGood` for the twist δ0: known points `P0 = (0:0:1)`, `P2 = (2:0:1)`. -/
theorem tailGood_T0 {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21} (hC : OnC M1 M2 M3 δ) :
    ∀ x : FurioLombardo.M3a.Route.Lift M1 M2 M3 δ,
      (∃ t ∈ FurioLombardo.M4.T0.data.tails, t.disc = liftDisc x ∧ liftPar x = (t.Xi : ℤ_[2])) →
      FurioLombardo.M3a.Route.GoodLift (0, 0, 1) (2, 0, 1) x.1 := by
  refine tailGood_of hC _ _ _ ?_
  intro t ht
  simp only [FurioLombardo.M4.T0.data, FurioLombardo.M4.T0.tails, List.mem_cons, List.not_mem_nil,
    or_false] at ht
  rcases ht with rfl | rfl <;> norm_num [cpt, discPt]

/-- M3a's `TailGood` for the twist δ1: known points `P1 = (1:1:1)`, `P3 = (-1:0:1)`. -/
theorem tailGood_T1 {M1 M2 M3 : Matrix (Fin 3) (Fin 3) K21} {δ : K21} (hC : OnC M1 M2 M3 δ) :
    ∀ x : FurioLombardo.M3a.Route.Lift M1 M2 M3 δ,
      (∃ t ∈ FurioLombardo.M4.T1.data.tails, t.disc = liftDisc x ∧ liftPar x = (t.Xi : ℤ_[2])) →
      FurioLombardo.M3a.Route.GoodLift (1, 1, 1) (-1, 0, 1) x.1 := by
  refine tailGood_of hC _ _ _ ?_
  intro t ht
  simp only [FurioLombardo.M4.T1.data, FurioLombardo.M4.T1.tails, List.mem_cons, List.not_mem_nil,
    or_false] at ht
  rcases ht with rfl | rfl <;> norm_num [cpt, discPt]

end FurioLombardo.Discharge.M4Cert
