import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Stoll's Selmer group Chabauty at one place, in logarithmic form

Source: M. Stoll, "Chabauty without the Mordell-Weil group", arXiv:1506.04286, Theorem 2.1
(`T:key-general` in the LaTeX source).

We work with abelian groups only:

* `A` stands for `A(k)` (global points of the Prym over `k = K21`),
* `B` for `A(k_v)` (points over the completion at the place `v` above 2 with `e = 3`),
* `ι : A →+ B` the localisation,
* `lam : B →+ V` the logarithm, with values in an abelian group `V` (in the application
  `V = ℤ_[2]^6`, the coordinates of `O_v^2` on the basis `1, π, π²`),
* `pr : V →+ M` the projection to the quotient by the saturation (in the application `M = ℤ_[2]^4`),
* `T : A` the rational 2-torsion point, `W : Set V` a set of representatives of the image of
  `Sel²` in `Λ/2Λ`, `Λ = range lam`.

Stoll's induction `i(P) = T_n + 2^n Q_n` is run only up to the 2-adic valuation of
`pr (lam (ι x))`; so the Mordell-Weil theorem for `A(k)` is not needed, only the fact that a
nonzero element of `M` is not divisible by every power of 2 (Krull's intersection theorem for the
finitely generated `ℤ_[2]`-module `M`, supplied as the hypothesis `hkrull`).

Main results:

* `FurioLombardo.M4.stoll_log`: under local injectivity (`hloc`, the content of condition (1)
  of Stoll's theorem when `σ_v` is injective), the kernel condition on `lam` (`hker`), the
  condition that global classes lie in `W` (`hW`), the saturation condition (`hsat`, condition (ii)
  of the note), and the leading class condition (`hiii`, condition (iii)), the global point `x`
  satisfies `pr (lam (ι x)) = 0`.
* `FurioLombardo.M4.halve`: the halving step (L3): a global point whose logarithm is in `2Λ`
  has a global half up to `T`.
-/

namespace FurioLombardo.M4

variable {A B V M : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup V] [AddCommGroup M]

/-- Cancellation of `2^n` in a group without 2-torsion. -/
theorem two_pow_nsmul_cancel (htf : ∀ m : M, (2 : ℕ) • m = 0 → m = 0) :
    ∀ (n : ℕ) (a b : M), (2 ^ n : ℕ) • a = (2 ^ n : ℕ) • b → a = b := by
  intro n
  induction n with
  | zero => intro a b h; simpa using h
  | succ n ih =>
    intro a b h
    apply ih
    have h2 : (2 : ℕ) • ((2 ^ n : ℕ) • a - (2 ^ n : ℕ) • b) = 0 := by
      rw [smul_sub, ← mul_nsmul', ← mul_nsmul']
      rw [show 2 * 2 ^ n = 2 ^ (n + 1) by ring, h, sub_self]
    exact sub_eq_zero.mp (htf _ h2)

/-- The halving step. If the logarithm of the localisation of a global point
`γ` is twice the logarithm of a local point, then `γ` or `γ - T` is twice a global point `R`,
and `lam (ι γ) = 2 • lam (ι R)` when `lam (ι T) = 0`. -/
theorem halve (ι : A →+ B) (lam : B →+ V) (T : A)
    (hloc : ∀ Q : A, (∃ b : B, ι Q = (2 : ℕ) • b) → ∃ Q' : A, Q = (2 : ℕ) • Q')
    (hker : ∀ b : B, lam b = 0 → ∃ c : B, b = (2 : ℕ) • c ∨ b = ι T + (2 : ℕ) • c)
    (hTlam : lam (ι T) = 0) (γ : A) (hγ : ∃ b : B, lam (ι γ) = (2 : ℕ) • lam b) :
    ∃ R : A, lam (ι γ) = (2 : ℕ) • lam (ι R) := by
  obtain ⟨b, hb⟩ := hγ
  have h0 : lam (ι γ - (2 : ℕ) • b) = 0 := by
    rw [map_sub, map_nsmul, hb, sub_self]
  obtain ⟨c, hc | hc⟩ := hker _ h0
  · obtain ⟨R, hR⟩ := hloc γ ⟨b + c, by
      rw [smul_add, ← hc]; abel⟩
    exact ⟨R, by rw [hR, map_nsmul, map_nsmul]⟩
  · obtain ⟨R, hR⟩ := hloc (γ - T) ⟨b + c, by
      rw [map_sub, smul_add, ← sub_eq_iff_eq_add'.mpr hc]; abel⟩
    refine ⟨R, ?_⟩
    have : γ = (2 : ℕ) • R + T := by rw [← hR]; abel
    rw [this, map_add, map_add, hTlam, add_zero, map_nsmul, map_nsmul]

/-- Stoll's Theorem 2.1 at one place, in logarithmic form.

Hypotheses:
* `hloc`: a global point whose localisation is divisible by 2 is divisible by 2 (from the
  injectivity of `σ_v` on `Sel²` and the injectivity of `A(k)/2A(k) → Sel²`; condition (1)).
* `hker`: the kernel of the logarithm is contained in `2B ∪ (ι T + 2B)` (L1, L2).
* `hT`, `hΓ`: `Γ` contains `T` and is killed by `pr ∘ lam ∘ ι`.
* `hW`: the logarithm of every global point is congruent modulo `2Λ` to an element of `W`.
* `hsat`: condition (ii) of L4: a global point with `pr (lam (ι Q)) ∈ 2M` is congruent modulo
  `2Λ` to a point of `Γ`.
* `htf`, `hkrull`: `M` has no 2-torsion, and no nonzero element of `M` is divisible by every
  power of 2.
* `hiii`: condition (iii) of L4 at the global point `x`: if `pr (lam (ι x)) = 2^n • z` and
  `z ≡ pr w (mod 2M)` with `w ∈ W`, then `z ∈ 2M` (the leading class of `pr (lam (ι x))`
  is not in `pr(W)`).

Conclusion: `pr (lam (ι x)) = 0`. -/
theorem stoll_log (ι : A →+ B) (lam : B →+ V) (pr : V →+ M) (T : A) (Γ : AddSubgroup A)
    (W : Set V) (x : A)
    (hloc : ∀ Q : A, (∃ b : B, ι Q = (2 : ℕ) • b) → ∃ Q' : A, Q = (2 : ℕ) • Q')
    (hker : ∀ b : B, lam b = 0 → ∃ c : B, b = (2 : ℕ) • c ∨ b = ι T + (2 : ℕ) • c)
    (hT : T ∈ Γ) (hΓ : ∀ γ ∈ Γ, pr (lam (ι γ)) = 0)
    (hW : ∀ Q : A, ∃ w ∈ W, ∃ b : B, lam (ι Q) = w + (2 : ℕ) • lam b)
    (hsat : ∀ Q : A, (∃ m : M, pr (lam (ι Q)) = (2 : ℕ) • m) →
      ∃ γ ∈ Γ, ∃ b : B, lam (ι Q) = lam (ι γ) + (2 : ℕ) • lam b)
    (htf : ∀ m : M, (2 : ℕ) • m = 0 → m = 0)
    (hkrull : ∀ m : M, (∀ n : ℕ, ∃ z : M, m = (2 ^ n : ℕ) • z) → m = 0)
    (hiii : ∀ (n : ℕ) (z : M) (w : V), (2 ^ n : ℕ) • z = pr (lam (ι x)) → w ∈ W →
      (∃ m : M, z - pr w = (2 : ℕ) • m) → ∃ m : M, z = (2 : ℕ) • m) :
    pr (lam (ι x)) = 0 := by
  set y := pr (lam (ι x)) with hy
  by_contra hne
  -- a power of 2 that does not divide y
  have hex : ∃ n : ℕ, ¬ ∃ z : M, y = (2 ^ n : ℕ) • z := by
    by_contra h
    push Not at h
    exact hne (hkrull y h)
  classical
  have hNspec : ¬ ∃ z : M, y = (2 ^ Nat.find hex : ℕ) • z := Nat.find_spec hex
  have hNpos : Nat.find hex ≠ 0 := by
    intro h0
    apply hNspec
    exact ⟨y, by rw [h0]; simp⟩
  obtain ⟨ν, hνN⟩ : ∃ ν, Nat.find hex = ν + 1 := Nat.exists_eq_succ_of_ne_zero hNpos
  rw [hνN] at hNspec
  have hν : ∃ z : M, y = (2 ^ ν : ℕ) • z := by
    have := Nat.find_min hex (show ν < Nat.find hex by omega)
    push Not at this
    simpa using this
  obtain ⟨z, hz⟩ := hν
  -- the induction of Stoll's proof, for n ≤ ν
  have key : ∀ n : ℕ, n ≤ ν → ∃ t ∈ Γ, ∃ Q : A, x = t + (2 ^ n : ℕ) • Q := by
    intro n
    induction n with
    | zero => intro _; exact ⟨0, Γ.zero_mem, x, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨t, ht, Q, hxQ⟩ := ih (Nat.le_of_succ_le hn)
      -- pr (lam (ι Q)) = 2^(ν - n) z is divisible by 2
      have hyQ : y = (2 ^ n : ℕ) • pr (lam (ι Q)) := by
        rw [hy, hxQ, map_add, map_add, map_add, hΓ t ht, zero_add, map_nsmul, map_nsmul,
          map_nsmul]
      have hprQ : pr (lam (ι Q)) = (2 ^ (ν - n) : ℕ) • z := by
        apply two_pow_nsmul_cancel htf n
        rw [← hyQ, hz, ← mul_nsmul', ← pow_add, Nat.add_sub_cancel' (Nat.le_of_succ_le hn)]
      have hdiv : ∃ m : M, pr (lam (ι Q)) = (2 : ℕ) • m := by
        refine ⟨(2 ^ (ν - n - 1) : ℕ) • z, ?_⟩
        rw [hprQ, ← mul_nsmul', ← pow_succ']
        congr 2
        omega
      obtain ⟨γ, hγ, b, hb⟩ := hsat Q hdiv
      have h0 : lam (ι (Q - γ) - (2 : ℕ) • b) = 0 := by
        rw [map_sub, map_nsmul, map_sub, map_sub, hb]; abel
      obtain ⟨c, hc | hc⟩ := hker _ h0
      · obtain ⟨Q', hQ'⟩ := hloc (Q - γ) ⟨b + c, by
          rw [smul_add, ← hc]; abel⟩
        refine ⟨t + (2 ^ n : ℕ) • γ, Γ.add_mem ht (Γ.nsmul_mem hγ _), Q', ?_⟩
        have hQ : Q = γ + (2 : ℕ) • Q' := by rw [← hQ']; abel
        rw [hxQ, hQ, smul_add, ← mul_nsmul', ← pow_succ]
        abel
      · obtain ⟨Q', hQ'⟩ := hloc (Q - γ - T) ⟨b + c, by
          rw [map_sub, smul_add, ← sub_eq_iff_eq_add'.mpr hc]; abel⟩
        refine ⟨t + (2 ^ n : ℕ) • (γ + T), Γ.add_mem ht (Γ.nsmul_mem (Γ.add_mem hγ hT) _),
          Q', ?_⟩
        have hQ : Q = γ + T + (2 : ℕ) • Q' := by rw [← hQ']; abel
        rw [hxQ, hQ, smul_add, smul_add, ← mul_nsmul', ← pow_succ]
        abel
  -- at n = ν the class of pr (lam (ι Q)) is the leading class, which lies in pr(W)
  obtain ⟨t, ht, Q, hxQ⟩ := key ν le_rfl
  have hyQ : y = (2 ^ ν : ℕ) • pr (lam (ι Q)) := by
    rw [hy, hxQ, map_add, map_add, map_add, hΓ t ht, zero_add, map_nsmul, map_nsmul, map_nsmul]
  have hzQ : pr (lam (ι Q)) = z := two_pow_nsmul_cancel htf ν _ _ (by rw [← hyQ, hz])
  obtain ⟨w, hwW, b, hb⟩ := hW Q
  have hzw : ∃ m : M, z - pr w = (2 : ℕ) • m :=
    ⟨pr (lam b), by rw [← hzQ, hb, map_add, map_nsmul]; abel⟩
  obtain ⟨m, hm⟩ := hiii ν z w hz.symm hwW hzw
  apply hNspec
  exact ⟨m, by rw [hz, hm, ← mul_nsmul', ← pow_succ]⟩

end FurioLombardo.M4
