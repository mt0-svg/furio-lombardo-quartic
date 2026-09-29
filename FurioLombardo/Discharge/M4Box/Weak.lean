import Mathlib
import FurioLombardo.M4.Cover

/-!
# The box inputs in the form the chain uses

Lane M4's chain (`FurioLombardo.M4.lead_or_known`) uses the analytic box hypotheses `HAntiConst`,
`HAntiTail` only through two consequences:

* on a constant box `{c + 2^s Y}`, `λ(c + 2^s Y) - λ(c)` is divisible by `2^(vM/3 + s)` (the
  bound `hlip` inside `const_box_leading`; `vM/3 + s = ν + 3` is the check `centres` of
  `TwistChecks`);
* around a known lift `Xi`, for `Y = 2^j u` with `u` a unit and `j ≥ s - s0` (the points of the tail box
  `{c + 2^s y}`, the only ones where the chain uses the bound), `λ(Xi + 2^s0 Y) - λ(Xi) - Y 2^(s0-1) g` is divisible
  by `2^(vM/3 + s0 + 2j)`, with `g` in the certified ball of `4 c_1` (the bound `h1` inside `tail_leading`, from
  `tail_sharp`).

`HConstLip` and `HTailQuad` state these two bounds; `hConstLip_of_anti` and `hTailQuad_of_anti`
derive them from `HAntiConst` and `HAntiTail`, so replacing the latter by the former in the chain
loses nothing.
-/

namespace FurioLombardo.Discharge.M4Box

open FurioLombardo.M4

/-- **HConstLip**: on every constant box `{c + 2^s Y}` the branch `λ` differs from its value at the
centre by an element of `2^(vM/3 + s) ℤ_2^6`. -/
def HConstLip (D : TwistData) (lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) : Prop :=
  ∀ c ∈ D.constant, ∀ Y : ℤ_[2],
    DvdV (c.vM / 3 + c.s) (lam c.disc ((c.c : ℤ_[2]) + 2 ^ c.s * Y) - lam c.disc c.c)

/-- **HTailQuad**: around the known lift of parameter `Xi` of every tail box, `λ` has the first order
expansion `λ(Xi + h) = λ(Xi) + h (g / 2) + O(h^2)`, `h = 2^s0 2^j u` (`u` a unit), with remainder
divisible by `2^(vM/3 + s0 + 2j)` and `g` in the certified ball of `4 c_1`. Only the points of the tail box
`{c + 2^s y}` are asked for: `j ≥ s - s0`. -/
def HTailQuad (D : TwistData) (lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) : Prop :=
  ∀ t ∈ D.tails, ∃ g : Fin 6 → ℤ_[2], DvdV t.q (g - icast t.g) ∧
    ∀ (j : ℕ) (u : ℤ_[2]), t.s - t.s0 ≤ j → IsUnit u →
      DvdV (t.vM / 3 + t.s0 + 2 * j)
        (lam t.disc ((t.Xi : ℤ_[2]) + 2 ^ t.s0 * (2 ^ j * u)) - lam t.disc t.Xi -
          ((2 : ℤ_[2]) ^ j * u) • ((2 : ℤ_[2]) ^ (t.s0 - 1) • g))

/-- Divisibility of the terms of a series with `2^(B + n) ∣ (n + 1) α_n`. -/
theorem dvdV_of_succ_smul_dvdV {B : ℕ} {α : ℕ → Fin 6 → ℤ_[2]}
    (ha : ∀ n : ℕ, DvdV (B + n) (((n : ℤ_[2]) + 1) • α n)) (n : ℕ) : DvdV B (α n) := by
  intro i
  have h := ha n i
  obtain ⟨k, hk⟩ := succ_dvd_two_pow n
  rw [pow_add, hk] at h
  have h' : ((n : ℤ_[2]) + 1) * ((2 : ℤ_[2]) ^ B * k) ∣ ((n : ℤ_[2]) + 1) * α n i := by
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h
  have hne : ((n : ℤ_[2]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact (dvd_mul_right _ k).trans ((mul_dvd_mul_iff_left hne).mp h')

/-- `HAntiConst` gives `HConstLip`. -/
theorem hConstLip_of_anti {D : TwistData} (hD : TwistChecks D)
    {lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]} (h : HAntiConst D lam) : HConstLip D lam := by
  intro c hc Y
  obtain ⟨α, hα, hsum⟩ := hSeries_of_anti hD h c hc
  exact dvdV_of_hasSum (fun n => dvdV_smul _ (dvdV_of_succ_smul_dvdV hα n)) (hsum Y)

/-- `HAntiTail` gives `HTailQuad`. -/
theorem hTailQuad_of_anti {D : TwistData} (hD : TwistChecks D)
    {lam : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]} (h : HAntiTail D lam) : HTailQuad D lam := by
  intro t ht
  obtain ⟨g, α, hg, ha0, hα, hsum⟩ := hTail_of_anti hD h t ht
  refine ⟨g, hg, fun j u _ _ => ?_⟩
  have h1 := tail_sharp (B := t.vM / 3 + t.s0) (t := j) u (fun n _ => hα n) (hsum _)
  rwa [ha0] at h1

end FurioLombardo.Discharge.M4Box
