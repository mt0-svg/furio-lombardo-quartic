import Mathlib
import FurioLombardo.M4.Defs

/-!
# The analytic input on a box, in antiderivative form

On the open parent disc of radius `2^(-r)` around `c` the logarithm `λ` is the antiderivative of a power series whose
Gauss norm on the closed disc of radius `2^(-r)` is at most `2^(-B)` (`AntiderivOn`); the `ℚ_2`-points of that open disc are the `c + 2^(r+1) Y`. `rescale` turns this into the series
form on the box `{c + 2^(r+1) Y}` used by `HSeries` and `HTail` (FurioLombardo.M4.Hypotheses): integral coefficients
`α_n` with `2^(B + r + 1 + n) ∣ (n+1) α_n`.
-/

namespace FurioLombardo.M4

/-- `f` is the antiderivative of the power series `w = Σ g_n (X - c)^n` on the open disc `|X - c| < 2^(-r)`, and the
Gauss norm of `w` on the closed disc `|X - c| ≤ 2^(-r)` is at most `2^(-B)` (`‖g_n‖ · 2^(-r n) ≤ 2^(-B)`): for every
`Y`, `f (c + 2^(r+1) Y) - f c = Σ g_n (2^(r+1) Y)^(n+1) / (n+1)` in every coordinate, computed in `ℚ_[2]`. The
identity is only asked on the open disc, where the abelian integral is an antiderivative; on the boundary
`|X - c| = 2^(-r)` the series need not converge. -/
def AntiderivOn {d : ℕ} (f : ℤ_[2] → Fin d → ℤ_[2]) (c : ℤ_[2]) (r B : ℕ) (g : ℕ → Fin d → ℚ_[2]) : Prop :=
  (∀ n i, ‖g n i‖ ≤ (2 : ℝ) ^ ((r * n : ℕ) : ℤ) * (2 : ℝ) ^ (-(B : ℤ))) ∧
  ∀ Y : ℤ_[2], ∀ i, HasSum (fun n : ℕ => ((2 : ℚ_[2]) ^ (r + 1) * (Y : ℚ_[2])) ^ (n + 1) / ((n : ℚ_[2]) + 1) * g n i)
    ((f (c + 2 ^ (r + 1) * Y) i : ℚ_[2]) - (f c i : ℚ_[2]))

end FurioLombardo.M4



open FurioLombardo.M4

theorem FurioLombardo.M4.norm_succ_ge (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) ≤ ‖((n : ℚ_[2]) + 1)‖ := by
  have hpos' : (n + 1 : ℕ) ≠ 0 := by omega
  have hpos : ((n + 1 : ℕ) : ℚ_[2]) ≠ 0 := by
    rwa [Nat.cast_ne_zero]
  have hcast : ((n : ℚ_[2]) + 1) = ((n + 1 : ℕ) : ℚ_[2]) := by push_cast; rfl
  rw [hcast]
  rw [Padic.norm_eq_zpow_neg_valuation (p := 2) hpos]
  rw [Padic.valuation_natCast (p := 2) (n := n + 1)]
  -- Goal: (2 : ℝ) ^ (-(n : ℤ)) ≤ (2 : ℝ) ^ (-(padicValNat 2 (n + 1) : ℤ))
  have hpadic_le_nat : padicValNat 2 (n + 1) ≤ n := by
    have hdvd : 2 ^ padicValNat 2 (n + 1) ∣ n + 1 := pow_padicValNat_dvd
    have hpos_n1 : 0 < n + 1 := by omega
    have hle_nat : 2 ^ padicValNat 2 (n + 1) ≤ n + 1 := Nat.le_of_dvd hpos_n1 hdvd
    have hlt : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
    have h_lt_pow : 2 ^ padicValNat 2 (n + 1) < 2 ^ (n + 1) :=
      lt_of_le_of_lt hle_nat hlt
    have h_lt_succ : padicValNat 2 (n + 1) < n + 1 :=
      ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h_lt_pow)
    omega
  have h_exp_le : (-(n : ℤ)) ≤ (-(padicValNat 2 (n + 1) : ℤ)) := by
    omega
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) h_exp_le

theorem FurioLombardo.M4.dvd_of_norm_le {x : ℤ_[2]} {k : ℕ} (h : ‖(x : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-(k : ℤ))) : (2 : ℤ_[2]) ^ k ∣ x := by
  have hnorm : ‖x‖ ≤ ((2 : ℕ) : ℝ) ^ (-(k : ℤ)) := by
    simpa using h
  have hmem := ((PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) x k).mp hnorm)
  exact (Ideal.mem_span_singleton.mp hmem)

theorem FurioLombardo.M4.hasSum_coe_iff {f : ℕ → ℤ_[2]} {a : ℤ_[2]} : HasSum (fun n => (f n : ℚ_[2])) (a : ℚ_[2]) ↔ HasSum f a := by
  have h_eq : (PadicInt.Coe.ringHom (p := 2) : ℤ_[2] → ℚ_[2]) = Subtype.val := by
    ext x; rfl
  have h_inducing : Topology.IsInducing (PadicInt.Coe.ringHom (p := 2)) :=
    h_eq ▸ PadicInt.isOpenEmbedding_coe.isInducing
  have h := (Topology.IsInducing.hasSum_iff (L := SummationFilter.unconditional ℕ) h_inducing f a)
  exact h

/-- **Rescaling on a box.** If `f` is on the disc `{c + 2^r Y}` the antiderivative of a power series with Gauss norm
at most `2^(-B)`, then on the box `{c + 2^(r+1) Y}` it is `f c + Σ α_n Y^(n+1)` with integral `α_n`,
`2^(B + r + 1 + n) ∣ (n+1) α_n`, and linear coefficient `α_0 = 2^(r+1) g_0`. -/
theorem FurioLombardo.M4.rescale_spec {d : ℕ} {f : ℤ_[2] → Fin d → ℤ_[2]} {c : ℤ_[2]} {r B : ℕ}
    {g : ℕ → Fin d → ℚ_[2]} (hf : AntiderivOn f c r B g) :
    ∃ α : ℕ → Fin d → ℤ_[2], (∀ n : ℕ, DvdV (B + (r + 1) + n) (((n : ℤ_[2]) + 1) • α n)) ∧
      (∀ Y : ℤ_[2], HasSum (fun n => Y ^ (n + 1) • α n) (f (c + 2 ^ (r + 1) * Y) - f c)) ∧
      ∀ i, ((α 0 i : ℤ_[2]) : ℚ_[2]) = 2 ^ (r + 1) * g 0 i := by
  obtain ⟨hg, hs⟩ := hf
  have h2pow : ∀ k : ℕ, ‖(2 : ℚ_[2]) ^ k‖ = (2 : ℝ) ^ (-(k : ℤ)) := by
    intro k
    have := Padic.norm_p_pow (p := 2) k
    simpa using this
  have hsucc0 : ∀ n : ℕ, ((n : ℚ_[2]) + 1) ≠ 0 := fun n => by exact_mod_cast Nat.succ_ne_zero n
  have hsuccpos : ∀ n : ℕ, 0 < ‖((n : ℚ_[2]) + 1)‖ := fun n => norm_pos_iff.mpr (hsucc0 n)
  -- the numerator bound
  have hnum : ∀ n i, ‖(2 : ℚ_[2]) ^ ((r + 1) * (n + 1)) * g n i‖ ≤ (2 : ℝ) ^ (-((B + (r + 1) + n : ℕ) : ℤ)) := by
    intro n i
    rw [norm_mul, h2pow]
    calc (2 : ℝ) ^ (-(((r + 1) * (n + 1) : ℕ) : ℤ)) * ‖g n i‖
        ≤ (2 : ℝ) ^ (-(((r + 1) * (n + 1) : ℕ) : ℤ)) * ((2 : ℝ) ^ ((r * n : ℕ) : ℤ) * (2 : ℝ) ^ (-(B : ℤ))) :=
          mul_le_mul_of_nonneg_left (hg n i) (by positivity)
      _ = (2 : ℝ) ^ (-((B + (r + 1) + n : ℕ) : ℤ)) := by
          rw [← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
          congr 1
          push_cast; ring
  have hβ : ∀ n i, ‖(2 : ℚ_[2]) ^ ((r + 1) * (n + 1)) * g n i / ((n : ℚ_[2]) + 1)‖ ≤ 1 := by
    intro n i
    rw [norm_div, div_le_one (hsuccpos n)]
    refine le_trans (hnum n i) (le_trans ?_ (norm_succ_ge n))
    apply zpow_le_zpow_right₀ (by norm_num)
    push_cast; omega
  let α : ℕ → Fin d → ℤ_[2] := fun n i => ⟨(2 : ℚ_[2]) ^ ((r + 1) * (n + 1)) * g n i / ((n : ℚ_[2]) + 1), hβ n i⟩
  have hαc : ∀ n i, ((α n i : ℤ_[2]) : ℚ_[2]) = (2 : ℚ_[2]) ^ ((r + 1) * (n + 1)) * g n i / ((n : ℚ_[2]) + 1) :=
    fun n i => rfl
  refine ⟨α, ?_, ?_, fun i => by rw [hαc]; simp⟩
  · intro n i
    apply dvd_of_norm_le
    have : ((((n : ℤ_[2]) + 1) • α n) i : ℚ_[2]) = (2 : ℚ_[2]) ^ ((r + 1) * (n + 1)) * g n i := by
      rw [Pi.smul_apply, smul_eq_mul, PadicInt.coe_mul, hαc]
      push_cast
      field_simp [hsucc0 n]
    rw [this]
    exact hnum n i
  · intro Y
    rw [Pi.hasSum]
    intro i
    rw [← hasSum_coe_iff]
    have h := hs Y i
    convert h using 1
    · funext n
      rw [Pi.smul_apply, smul_eq_mul, PadicInt.coe_mul, hαc]
      push_cast
      field_simp [hsucc0 n]
      ring
    · rfl

theorem FurioLombardo.M4.rescale {d : ℕ} {f : ℤ_[2] → Fin d → ℤ_[2]} {c : ℤ_[2]} {r B : ℕ} {g : ℕ → Fin d → ℚ_[2]}
    (hf : AntiderivOn f c r B g) :
    ∃ α : ℕ → Fin d → ℤ_[2], (∀ n : ℕ, DvdV (B + (r + 1) + n) (((n : ℤ_[2]) + 1) • α n)) ∧
      ∀ Y : ℤ_[2], HasSum (fun n => Y ^ (n + 1) • α n) (f (c + 2 ^ (r + 1) * Y) - f c) := by
  obtain ⟨α, h1, h2, -⟩ := rescale_spec hf
  exact ⟨α, h1, h2⟩
