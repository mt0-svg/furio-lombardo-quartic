import Mathlib
import FurioLombardo.Discharge.M3a.Plug

/-!
# The lattice fact `Quarter` (elementary divisors 1 and 4) from lane M4's data

M3a's `Quarter Λ S a b` asks integers `n`, `m` and `r ∈ Λ` with `4 r = n a + m b` and
`S ≤ span {a, b, r}`, for `Λ = span (log D_i)`, `a = log φ(x_a)`, `b = log φ(x_b)` and `S` the
saturation of `span {a, b}` in `Λ`. It is proved here from the kernel checked data of lane M4
(`TwistChecks`) and the certified balls (`HBallD`, `HBallPhi`), with five more finite facts about
the data (checked per twist by `decide +kernel` in `FurioLombardo.Discharge.M3a.QuarterInst`).

Coordinates: for `x ∈ Λ` the vector `U G x` is divisible by 4, and `E = H U⁻¹` (integer matrix)
satisfies `E (U G) = 4` and `(U G) E = 4`. Let `A0 = (U G la)_0`, `B0 = (U G lb)_0` (integers,
`A0 = 4 A0'` with `A0'` odd, `B0 = 4 B0'`). Then `w = A0 b - B0 a` has `U G w ≡ (0, Del, 0, ...)`
modulo `2^min(qa, qb)` with `v_2(Del) = 6`, so `w = 16 r` with `r = E z ∈ Λ`, `64 z = U G w`,
and `4 r = A0' b - B0' a`. The two by two minor of `a, r` in the rows 0 and 1 of `U G` is 16 times
a unit, so `span {a, r}` is saturated in `Λ`; it contains `b` (`A0'` is a unit), hence it contains
`S`.
-/

open FurioLombardo.M4
open FurioLombardo.Discharge.Analytic (satOf isSatOf_satOf)

namespace FurioLombardo.Discharge.M3a

theorem two_smul_injective_V {x y : Fin 6 → ℤ_[2]} (h : (2 : ℤ_[2]) • x = (2 : ℤ_[2]) • y) : x = y :=
  smul_right_injective (Fin 6 → ℤ_[2]) (two_ne_zero : (2 : ℤ_[2]) ≠ 0) h

theorem pow_smul_injective_V {n : ℕ} {x y : Fin 6 → ℤ_[2]}
    (h : (2 : ℤ_[2]) ^ n • x = (2 : ℤ_[2]) ^ n • y) : x = y :=
  smul_right_injective (Fin 6 → ℤ_[2]) (pow_ne_zero n (two_ne_zero : (2 : ℤ_[2]) ≠ 0)) h

theorem two_dvd_of_mul_unit {α u : ℤ_[2]} (hu : IsUnit u) {k : ℕ}
    (h : (2 : ℤ_[2]) ^ (k + 1) ∣ α * (2 ^ k * u)) : (2 : ℤ_[2]) ∣ α := by
  have h' : (2 : ℤ_[2]) ^ k * 2 ∣ (2 : ℤ_[2]) ^ k * (α * u) := by
    rw [← pow_succ]; convert h using 1; ring
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero k (two_ne_zero : (2 : ℤ_[2]) ≠ 0))).mp h'
  exact (hu.dvd_mul_right).mp h2

/-- **Quarter from lane M4's data.** -/
theorem quarter_of_cert {D : TwistData} (hD : TwistChecks D) {ℓ : Fin 7 → Fin 6 → ℤ_[2]}
    {a b : Fin 6 → ℤ_[2]} (hBD : HBallD D ℓ) (hBP : HBallPhi D a b)
    (ha : a ∈ Submodule.span ℤ_[2] (Set.range ℓ)) (hb : b ∈ Submodule.span ℤ_[2] (Set.range ℓ))
    (hUGE : D.UG * (D.H * D.Ui) = (4 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ))
    (hdl6 : D.dl = 6)
    (hA4 : (4 : ℤ) ∣ D.UG.mulVec D.la 0) (hA8 : ¬ (8 : ℤ) ∣ D.UG.mulVec D.la 0)
    (hB4 : (4 : ℤ) ∣ D.UG.mulVec D.lb 0) :
    FurioLombardo.M3a.Route.Quarter (Submodule.span ℤ_[2] (Set.range ℓ))
      (satOf (Submodule.span ℤ_[2] (Set.range ℓ)) a b) a b := by
  set Λ := Submodule.span ℤ_[2] (Set.range ℓ) with hΛ
  have h24 : ((2 : ℤ_[2]) ^ 2) = 4 := by norm_num
  -- the lattice layer of lane M4
  obtain ⟨-, h4, hmemG⟩ := qchar_of_cert hD rfl hBD hBP (isSatOf_satOf Λ a b)
  have hl2 : ∀ i, DvdV 2 (ℓ i - icast (D.lD i)) :=
    fun i => dvdV_mono (le_trans (by norm_num) (hD.hqD i)) (hBD i)
  have hG4 : ∀ x ∈ Λ, ∀ j, (4 : ℤ_[2]) ∣ imv D.G x j := fun x hx j =>
    four_dvd_imv_of_mem ℓ rfl D.lD hl2 D.G hD.hGl hx j
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
  -- approximations of the U G coordinates of a and b
  have hAa : ∀ o, (2 : ℤ_[2]) ^ D.qa ∣ imv D.UG a o - icast (D.UG.mulVec D.la) o := by
    intro o
    have := dvdV_imv D.UG hBP.1 o
    rwa [imv_sub, imv_icast] at this
  have hBb : ∀ o, (2 : ℤ_[2]) ^ D.qb ∣ imv D.UG b o - icast (D.UG.mulVec D.lb) o := by
    intro o
    have := dvdV_imv D.UG hBP.2 o
    rwa [imv_sub, imv_icast] at this
  have hq7a : 7 ≤ D.qa := by have := hD.hr.2; rw [hdl6] at this; omega
  have hq7b : 7 ≤ D.qb := by have := hD.hr.2; rw [hdl6] at this; omega
  have hJ : 6 ≤ min D.Jab (min D.qa D.qb) := by have := hD.hr.1; rw [hdl6] at this; omega
  have hAa7 : ∀ o, (2 : ℤ_[2]) ^ 7 ∣ imv D.UG a o - icast (D.UG.mulVec D.la) o :=
    fun o => (pow_dvd_pow 2 hq7a).trans (hAa o)
  have hBb7 : ∀ o, (2 : ℤ_[2]) ^ 7 ∣ imv D.UG b o - icast (D.UG.mulVec D.lb) o :=
    fun o => (pow_dvd_pow 2 hq7b).trans (hBb o)
  have hab : ∀ o : Fin 6, 2 ≤ o.val →
      (2 : ℤ_[2]) ^ 6 ∣ imv D.UG a o ∧ (2 : ℤ_[2]) ^ 6 ∣ imv D.UG b o := by
    intro o ho
    obtain ⟨ha', hb'⟩ := hD.hJab o ho
    have e1 : 6 ≤ D.Jab := le_trans hJ (min_le_left _ _)
    have ha'' : (2 : ℤ_[2]) ^ 6 ∣ icast (D.UG.mulVec D.la) o :=
      (pow_dvd_pow 2 e1).trans ((intCast_two_pow_dvd_iff _ _).mpr ha')
    have hb'' : (2 : ℤ_[2]) ^ 6 ∣ icast (D.UG.mulVec D.lb) o :=
      (pow_dvd_pow 2 e1).trans ((intCast_two_pow_dvd_iff _ _).mpr hb')
    constructor
    · have := dvd_add ((pow_dvd_pow 2 (by omega)).trans (hAa7 o)) ha''
      rwa [sub_add_cancel] at this
    · have := dvd_add ((pow_dvd_pow 2 (by omega)).trans (hBb7 o)) hb''
      rwa [sub_add_cancel] at this
  -- the integers A0 = 4 A0', B0 = 4 B0', A1, B1 and Del = 64 D'
  set A0 : ℤ := D.UG.mulVec D.la 0 with hA0def
  set B0 : ℤ := D.UG.mulVec D.lb 0 with hB0def
  set A1 : ℤ := D.UG.mulVec D.la 1 with hA1def
  set B1 : ℤ := D.UG.mulVec D.lb 1 with hB1def
  obtain ⟨A0', hA0'⟩ := hA4
  obtain ⟨B0', hB0'⟩ := hB4
  have hodd : ¬ (2 : ℤ) ∣ A0' := by
    rintro ⟨c, rfl⟩; exact hA8 ⟨c, by rw [hA0']; ring⟩
  obtain ⟨hD64, hD128⟩ := hD.hdl
  rw [hdl6] at hD64 hD128
  obtain ⟨D', hD'⟩ := hD64
  have hD'odd : ¬ (2 : ℤ) ∣ D' := by
    rintro ⟨c, rfl⟩; exact hD128 ⟨c, by rw [hD']; ring⟩
  have hDel : A0 * B1 - A1 * B0 = 2 ^ 6 * D' := by rw [← hD']; exact hD.hDel
  -- the vector w = A0 b - B0 a and its U G coordinates
  set w : Fin 6 → ℤ_[2] := (A0 : ℤ_[2]) • b - (B0 : ℤ_[2]) • a with hw
  have hPw : ∀ j, imv D.UG w j = (A0 : ℤ_[2]) * imv D.UG b j - (B0 : ℤ_[2]) * imv D.UG a j := by
    intro j
    rw [hw, imv_sub, imv_smul, imv_smul]; rfl
  obtain ⟨ε0, hε0⟩ := hAa7 0
  obtain ⟨ε1, hε1⟩ := hAa7 1
  obtain ⟨η0, hη0⟩ := hBb7 0
  obtain ⟨η1, hη1⟩ := hBb7 1
  have hA0c : icast (D.UG.mulVec D.la) 0 = (A0 : ℤ_[2]) := rfl
  have hA1c : icast (D.UG.mulVec D.la) 1 = (A1 : ℤ_[2]) := rfl
  have hB0c : icast (D.UG.mulVec D.lb) 0 = (B0 : ℤ_[2]) := rfl
  have hB1c : icast (D.UG.mulVec D.lb) 1 = (B1 : ℤ_[2]) := rfl
  rw [hA0c] at hε0; rw [hA1c] at hε1; rw [hB0c] at hη0; rw [hB1c] at hη1
  have hA0q : (A0 : ℤ_[2]) = 4 * (A0' : ℤ_[2]) := by rw [hA0']; push_cast; ring
  have hB0q : (B0 : ℤ_[2]) = 4 * (B0' : ℤ_[2]) := by rw [hB0']; push_cast; ring
  have hDelq : (A0 : ℤ_[2]) * B1 - A1 * B0 = 2 ^ 6 * (D' : ℤ_[2]) := by exact_mod_cast hDel
  have h64 : ∀ j, (2 : ℤ_[2]) ^ 6 ∣ imv D.UG w j := by
    intro j
    rw [hPw j]
    fin_cases j
    · show (2 : ℤ_[2]) ^ 6 ∣ (A0 : ℤ_[2]) * imv D.UG b 0 - (B0 : ℤ_[2]) * imv D.UG a 0
      have e : (A0 : ℤ_[2]) * imv D.UG b 0 - (B0 : ℤ_[2]) * imv D.UG a 0 =
          2 ^ 6 * (8 * (A0' : ℤ_[2]) * η0 - 8 * (B0' : ℤ_[2]) * ε0) := by
        have hb0 : imv D.UG b 0 = B0 + 2 ^ 7 * η0 := by rw [← hη0]; ring
        have ha0 : imv D.UG a 0 = A0 + 2 ^ 7 * ε0 := by rw [← hε0]; ring
        rw [hb0, ha0, hA0q, hB0q]; ring
      rw [e]; exact dvd_mul_right _ _
    · show (2 : ℤ_[2]) ^ 6 ∣ (A0 : ℤ_[2]) * imv D.UG b 1 - (B0 : ℤ_[2]) * imv D.UG a 1
      have e : (A0 : ℤ_[2]) * imv D.UG b 1 - (B0 : ℤ_[2]) * imv D.UG a 1 =
          2 ^ 6 * ((D' : ℤ_[2]) + 8 * (A0' : ℤ_[2]) * η1 - 8 * (B0' : ℤ_[2]) * ε1) := by
        have hb1 : imv D.UG b 1 = B1 + 2 ^ 7 * η1 := by rw [← hη1]; ring
        have ha1 : imv D.UG a 1 = A1 + 2 ^ 7 * ε1 := by rw [← hε1]; ring
        rw [hb1, ha1]
        linear_combination hDelq + (2 ^ 7 * η1) * hA0q - (2 ^ 7 * ε1) * hB0q
      rw [e]; exact dvd_mul_right _ _
    all_goals
      first
      | exact dvd_sub (Dvd.dvd.mul_left (hab _ (by decide)).2 _)
          (Dvd.dvd.mul_left (hab _ (by decide)).1 _)
  choose z hz using h64
  -- r = E z
  set E : Matrix (Fin 6) (Fin 6) ℤ := D.H * D.Ui with hE
  set r : Fin 6 → ℤ_[2] := imv E z with hr
  have hrΛ : r ∈ Λ := by
    have hsum : imv E z = ∑ k, z k • icast (fun j => E j k) := by
      funext j
      simp [imv, Matrix.mulVec, dotProduct, Finset.sum_apply, icast, mul_comm]
    rw [hr, hsum]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hcol k))
  have hUGr : imv D.UG r = (4 : ℤ_[2]) • z := by
    rw [hr, ← imv_mul, hUGE, imv_scalar]; norm_num
  have hzv : imv D.UG w = (2 : ℤ_[2]) ^ 6 • z := funext fun j => by rw [hz j]; rfl
  have h16 : (2 : ℤ_[2]) ^ 4 • r = w := by
    have h1 : imv (E * D.UG) w = ((4 : ℤ) : ℤ_[2]) • w := by
      have hid' : E * D.UG = (4 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
        rw [hE, hD.hid]; ext i j; simp [Matrix.smul_apply]
      rw [hid', imv_scalar]
    rw [imv_mul, hzv, imv_smul] at h1
    apply pow_smul_injective_V (n := 2)
    rw [smul_smul, ← pow_add]
    have e4 : (2 : ℤ_[2]) ^ 2 = ((4 : ℤ) : ℤ_[2]) := by norm_num
    rw [e4]
    exact h1
  -- 4 r = A0' b - B0' a
  have h4r : (4 : ℤ_[2]) • r = (A0' : ℤ_[2]) • b - (B0' : ℤ_[2]) • a := by
    apply pow_smul_injective_V (n := 2)
    have e : (2 : ℤ_[2]) ^ 2 * 4 = 2 ^ 4 := by norm_num
    rw [smul_smul, e, h16, hw, hA0q, hB0q, smul_sub, smul_smul, smul_smul, h24]
  -- the minor of a and r in the rows 0 and 1 of U G
  have hP0r : imv D.UG r 0 = 4 * z 0 := by rw [hUGr]; rfl
  have hP1r : imv D.UG r 1 = 4 * z 1 := by rw [hUGr]; rfl
  have hunit : ∃ u : ℤ_[2], IsUnit u ∧
      imv D.UG a 0 * z 1 - imv D.UG a 1 * z 0 = 2 ^ 2 * u := by
    apply eq_two_pow_mul_unit_of_approx (D := A0' * D' * 4) (q := 3)
    · exact ⟨A0' * D', by ring⟩
    · rintro ⟨c, hc⟩
      apply hodd
      have h2 : (2 : ℤ) ∣ A0' * D' := ⟨c, mul_right_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) (by rw [hc]; ring)⟩
      rcases (Int.prime_two.dvd_or_dvd h2) with h | h
      · exact h
      · exact absurd h hD'odd
    · norm_num
    · -- 2^6 (x - A0 D') is divisible by 2^9
      have hz0 : (2 : ℤ_[2]) ^ 6 * z 0 = (A0 : ℤ_[2]) * imv D.UG b 0 - (B0 : ℤ_[2]) * imv D.UG a 0 := by
        rw [← hz 0, hPw 0]
      have hz1 : (2 : ℤ_[2]) ^ 6 * z 1 = (A0 : ℤ_[2]) * imv D.UG b 1 - (B0 : ℤ_[2]) * imv D.UG a 1 := by
        rw [← hz 1, hPw 1]
      have hb0 : imv D.UG b 0 = B0 + 2 ^ 7 * η0 := by rw [← hη0]; ring
      have ha0 : imv D.UG a 0 = A0 + 2 ^ 7 * ε0 := by rw [← hε0]; ring
      have hb1 : imv D.UG b 1 = B1 + 2 ^ 7 * η1 := by rw [← hη1]; ring
      have ha1 : imv D.UG a 1 = A1 + 2 ^ 7 * ε1 := by rw [← hε1]; ring
      have hz0' : z 0 = 8 * ((A0' : ℤ_[2]) * η0 - (B0' : ℤ_[2]) * ε0) := by
        apply mul_left_cancel₀ (pow_ne_zero 6 (two_ne_zero : (2 : ℤ_[2]) ≠ 0))
        rw [hz0, hb0, ha0, hA0q, hB0q]; ring
      have hz1' : z 1 = (D' : ℤ_[2]) + 8 * ((A0' : ℤ_[2]) * η1 - (B0' : ℤ_[2]) * ε1) := by
        apply mul_left_cancel₀ (pow_ne_zero 6 (two_ne_zero : (2 : ℤ_[2]) ≠ 0))
        rw [hz1, hb1, ha1]
        linear_combination hDelq + (2 ^ 7 * η1) * hA0q - (2 ^ 7 * ε1) * hB0q
      have hP1a4 : (4 : ℤ_[2]) ∣ imv D.UG a 1 := hUG4 a ha 1
      obtain ⟨c1, hc1⟩ := hP1a4
      refine ⟨(A0 : ℤ_[2]) * ((A0' : ℤ_[2]) * η1 - (B0' : ℤ_[2]) * ε1)
        + 16 * ε0 * ((D' : ℤ_[2]) + 8 * ((A0' : ℤ_[2]) * η1 - (B0' : ℤ_[2]) * ε1))
        - 4 * c1 * ((A0' : ℤ_[2]) * η0 - (B0' : ℤ_[2]) * ε0), ?_⟩
      rw [ha0, hz0', hz1', hc1]
      push_cast
      rw [hA0q]
      ring
  obtain ⟨u, hu, hxu⟩ := hunit
  -- span {a, r} is saturated in Λ
  set N : Submodule ℤ_[2] (Fin 6 → ℤ_[2]) := Submodule.span ℤ_[2] {a, r} with hN
  have hsatN : ∀ x ∈ Λ, (2 : ℤ_[2]) • x ∈ N → x ∈ N := by
    intro x hx h2x
    obtain ⟨α, β, hαβ⟩ := (Submodule.mem_span_pair (R := ℤ_[2])).mp h2x
    have e0 := congrArg (fun v => imv D.UG v 0) hαβ
    have e1 := congrArg (fun v => imv D.UG v 1) hαβ
    simp only [imv_add, imv_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
    rw [hP0r] at e0; rw [hP1r] at e1
    obtain ⟨p0, hp0⟩ := hUG4 x hx 0
    obtain ⟨p1, hp1⟩ := hUG4 x hx 1
    obtain ⟨q0, hq0⟩ := hUG4 a ha 0
    obtain ⟨q1, hq1⟩ := hUG4 a ha 1
    rw [hp0] at e0; rw [hp1] at e1
    -- Cramer for α and β
    have hα : α * (2 ^ 2 * u) = 2 * (4 * p0 * z 1 - 4 * p1 * z 0) := by
      rw [← hxu]; linear_combination (z 1) * e0 - (z 0) * e1
    have hβ : β * (2 ^ 2 * u) = 2 * (q0 * (4 * p1) - q1 * (4 * p0)) := by
      have h4 : (4 : ℤ_[2]) * (β * (2 ^ 2 * u)) = 4 * (2 * (q0 * (4 * p1) - q1 * (4 * p0))) := by
        rw [← hxu]
        rw [hq0] at e0; rw [hq1] at e1; rw [hq0, hq1]
        linear_combination (4 * q0) * e1 - (4 * q1) * e0
      exact mul_left_cancel₀ (by norm_num : (4 : ℤ_[2]) ≠ 0) h4
    have h2α : (2 : ℤ_[2]) ∣ α := by
      apply two_dvd_of_mul_unit hu (k := 2)
      rw [hα]
      exact ⟨p0 * z 1 - p1 * z 0, by ring⟩
    have h2β : (2 : ℤ_[2]) ∣ β := by
      apply two_dvd_of_mul_unit hu (k := 2)
      rw [hβ]
      exact ⟨q0 * p1 - q1 * p0, by ring⟩
    obtain ⟨α', rfl⟩ := h2α
    obtain ⟨β', rfl⟩ := h2β
    have : x = α' • a + β' • r := by
      apply two_smul_injective_V
      rw [← hαβ, smul_add, smul_smul, smul_smul]
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hsatN' : ∀ m : ℕ, ∀ x ∈ Λ, (2 : ℤ_[2]) ^ m • x ∈ N → x ∈ N := by
    intro m
    induction m with
    | zero => intro x _ hx; simpa using hx
    | succ m ih =>
      intro x hx hxm
      apply ih x hx
      apply hsatN _ (Λ.smul_mem _ hx)
      rwa [smul_smul, ← pow_succ']
  -- b ∈ span {a, r}
  have hbN : b ∈ N := by
    have hu' : IsUnit (A0' : ℤ_[2]) := by
      rw [PadicInt.isUnit_iff]
      by_contra hne
      have h1 : ‖(A0' : ℤ_[2])‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) hne
      exact hodd (by exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd (p := 2) A0').mp h1)
    obtain ⟨v, hv⟩ := hu'
    have hbv : b = (↑v⁻¹ : ℤ_[2]) • ((4 : ℤ_[2]) • r + (B0' : ℤ_[2]) • a) := by
      rw [h4r, sub_add_cancel, smul_smul, ← hv, Units.inv_mul, one_smul]
    rw [hbv]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  have hab_le : Submodule.span ℤ_[2] {a, b} ≤ N := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact hbN
  refine ⟨-B0', A0', r, hrΛ, ?_, ?_⟩
  · rw [h4r, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    rw [← Int.cast_smul_eq_zsmul ℤ_[2], ← Int.cast_smul_eq_zsmul ℤ_[2]]
    rw [neg_smul]; abel
  · intro s hs
    obtain ⟨hsΛ, m, hm⟩ := hs
    have hsN : s ∈ N := hsatN' m s hsΛ (hab_le hm)
    exact Submodule.span_mono (by intro x hx; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx ⊢; tauto) hsN

end FurioLombardo.Discharge.M3a
