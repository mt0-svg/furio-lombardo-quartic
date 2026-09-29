import FurioLombardo.M2.Exponent

/-!
# Soundness of the generator certificates (lane M2)

`genCheck p fac = true` gives `α = elt a`, `c = elt c` in `𝓞 K21` with `α c = p`, `c ∉ P` and
`L(θ) c ∈ p 𝓞 K21` for every prime `P` containing `p` and `L(θ)`; if moreover
`P = (p, L(θ))`, then `P = (α)` (`eq_span_of_cert`).
-/

namespace FurioLombardo.M2

open Polynomial NumberField Ideal

set_option exponentiation.threshold 1024

/-- If `P = (π, g)` is prime, `α c = π`, `c ∉ P` and `g c = π d`, then `P = (α)`. -/
theorem eq_span_of_cert {R : Type*} [CommRing R] [IsDomain R] (P : Ideal R) [hP : P.IsPrime]
    (π g α c d : R) (hPs : P = span {π, g}) (hαc : α * c = π) (hc : c ∉ P)
    (hgc : g * c = π * d) : P = span {α} := by
  have hπ : π ∈ P := hPs ▸ subset_span (by simp)
  have hα : α ∈ P := by
    rcases hP.mem_or_mem (hαc ▸ hπ) with h | h
    · exact h
    · exact absurd h hc
  have hc0 : c ≠ 0 := fun h => hc (h ▸ P.zero_mem)
  apply le_antisymm
  · rw [hPs, span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact mem_span_singleton.mpr ⟨c, hαc.symm⟩
    · have : x = α * d := by
        apply mul_right_cancel₀ hc0
        rw [hgc, ← hαc]; ring
      exact mem_span_singleton.mpr ⟨d, this⟩
  · rw [span_le, Set.singleton_subset_iff]; exact hα

theorem length_addZ : ∀ l m : List ℤ, (addZ l m).length = max l.length m.length
  | [], m => by simp [addZ]
  | a :: l, [] => by simp [addZ]
  | a :: l, b :: m => by simp [addZ, length_addZ l m, Nat.succ_max_succ]

theorem length_smulZ (c : ℤ) : ∀ l : List ℤ, (smulZ c l).length = l.length
  | [] => rfl
  | a :: l => by simp [smulZ, length_smulZ c l]

theorem length_combo_le (n : ℕ) : ∀ (a : List ℤ) (Ws : List (List ℤ)),
    (∀ W ∈ Ws, W.length ≤ n) → (combo a Ws).length ≤ n
  | [], _, _ => by simp [combo]
  | _ :: _, [], _ => by simp [combo]
  | a :: l, W :: Ws, h => by
    simp only [combo, length_addZ, length_smulZ]
    exact max_le (h W (by simp)) (length_combo_le n l Ws (fun W' hW => h W' (by simp [hW])))

theorem WL_prop : ∀ W ∈ WL, W.length = 21 ∧ ∀ x ∈ W, x.natAbs ≤ 2 ^ 77 := by
  intro W hW
  have := List.all_eq_true.mp WL_shape.2.2 W hW
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1, (allBounded_iff _ _).mp this.2⟩

theorem tK_eq : tK = (2 : ℤ) ^ 512 := by unfold tK kK; rw [Nat.cast_pow, Nat.cast_ofNat]

theorem dotZ_omL (b : List ℤ) : dotZ b omL = evalZ ((2 : ℤ) ^ 512) (combo b WL) := by
  rw [omL_eq, tK_eq, show evalI ((2 : ℤ) ^ 512) = evalZ ((2 : ℤ) ^ 512) from
    funext (evalI_eq _), dotZ_map_evalZ]

theorem DD_ne_zero_O : (DD : 𝓞 K21) ≠ 0 := by
  intro h
  apply DD_ne_zero_K
  have := congrArg (algebraMap (𝓞 K21) K21) h
  simpa using this

theorem evalZ_H {R : Type*} [CommRing R] (t : R) (A C : List ℤ) (k : ℤ) :
    evalZ t (addZ (mulZ A C) [k]) = evalZ t A * evalZ t C + k := by
  rw [evalZ_addZ, evalZ_mulZ]; simp

/-- The Kronecker part of `genCheck`: `α c = p` and `DD c = C(θ)`. -/
theorem gen_core (p : ℕ) (hp17 : p < 2 ^ 17) (a c Cl Ql : List ℤ) (ha : a.length = 21)
    (hc : c.length = 21) (hab : ∀ x ∈ a, x.natAbs ≤ 2 ^ 15) (hcb : ∀ x ∈ c, x.natAbs ≤ 2 ^ 27)
    (hClb : ∀ x ∈ Cl, x.natAbs ≤ 2 ^ 112) (hQlb : ∀ x ∈ Ql, x.natAbs ≤ 2 ^ 425)
    (hH : dotZ a omL * dotZ c omL - (p : ℤ) * DD ^ 2 = Fk * evalI tK Ql)
    (hC : evalI tK Cl = dotZ c omL) :
    elt a * elt c = (p : 𝓞 K21) ∧ (DD : 𝓞 K21) * elt c = evalZ θ Cl := by
  have hWb : ∀ W ∈ WL, ∀ x ∈ W, x.natAbs ≤ 2 ^ 77 := fun W hW => (WL_prop W hW).2
  have hcomb := natAbs_combo (2 ^ 27) (2 ^ 77) c WL hcb hWb
  rw [hc] at hcomb
  have hCeq : ∀ t : 𝓞 K21, evalZ t Cl = evalZ t (combo c WL) := fun t =>
    kron_eq 512 (2 ^ 112) (21 * 2 ^ 27 * 2 ^ 77) Cl (combo c WL) hClb hcomb (by norm_num)
      (by rw [← dotZ_omL, ← hC, tK_eq, evalI_eq]) t
  have hDc : (DD : 𝓞 K21) * elt c = evalZ θ Cl := by rw [DD_mul_elt, hCeq]
  refine ⟨?_, hDc⟩
  have hacomb := natAbs_combo (2 ^ 15) (2 ^ 77) a WL hab hWb
  rw [ha] at hacomb
  have hAlen : (combo a WL).length ≤ 21 :=
    length_combo_le 21 a WL (fun W hW => (WL_prop W hW).1.le)
  have hmul := natAbs_mulZ _ _ (combo a WL) Cl hacomb hClb
  have hpD : ((p : ℤ) * DD ^ 2).natAbs ≤ 2 ^ 153 := by
    have h1 : (p : ℤ).natAbs ≤ 2 ^ 17 := by simp; omega
    have h2 : DD.natAbs ≤ 2 ^ 68 := by have := DD_pos; omega
    rw [Int.natAbs_mul, Int.natAbs_pow]
    calc (p : ℤ).natAbs * DD.natAbs ^ 2 ≤ 2 ^ 17 * (2 ^ 68) ^ 2 := by gcongr
      _ = 2 ^ 153 := by norm_num
  have hHb : ∀ x ∈ addZ (mulZ (combo a WL) Cl) [-((p : ℤ) * DD ^ 2)],
      x.natAbs ≤ 21 * (21 * 2 ^ 15 * 2 ^ 77) * 2 ^ 112 + 2 ^ 153 := by
    intro x hx
    have := natAbs_addZ _ (2 ^ 153) _ _ hmul (by simpa using hpD) x hx
    refine this.trans (Nat.add_le_add_right ?_ _)
    gcongr
  have hfL : ∀ x ∈ fL, x.natAbs ≤ 1072 := (allBounded_iff _ _).mp fL_bound.2
  have hfQ := natAbs_mulZ _ _ fL Ql hfL hQlb
  rw [fL_bound.1] at hfQ
  have hv : evalZ ((2 : ℤ) ^ 512) (addZ (mulZ (combo a WL) Cl) [-((p : ℤ) * DD ^ 2)]) =
      evalZ ((2 : ℤ) ^ 512) fL * evalZ ((2 : ℤ) ^ 512) Ql := by
    have e1 : evalZ ((2 : ℤ) ^ 512) (combo a WL) = dotZ a omL := (dotZ_omL a).symm
    have e2 : evalZ ((2 : ℤ) ^ 512) Cl = dotZ c omL := by rw [← hC, tK_eq, evalI_eq]
    have e3 : evalZ ((2 : ℤ) ^ 512) fL * evalZ ((2 : ℤ) ^ 512) Ql = Fk * evalI tK Ql := by
      rw [Fk_eq, tK_eq, evalI_eq, evalI_eq]
    rw [evalZ_H, e1, e2, e3, ← hH, Int.cast_neg, Int.cast_id]; ring
  have key := kron_mul 512 _ _ _ fL Ql hHb hfQ (by norm_num) hv θ
  rw [evalZ_θ_fL, zero_mul] at key
  rw [evalZ_H] at key
  rw [← DD_mul_elt, ← hDc] at key
  have h2 : (DD : 𝓞 K21) ^ 2 * (elt a * elt c - p) = 0 := by
    push_cast at key
    linear_combination key
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) DD_ne_zero_O
  · exact sub_eq_zero.mp h

theorem mul_eq_p_mul_of_DD (p : ℕ) (hp : p.Prime) (hpDD : ¬ (p : ℤ) ∣ DD) (x y : 𝓞 K21)
    (h : (DD : 𝓞 K21) * x = p * y) : ∃ d, x = p * d := by
  obtain ⟨u, v, huv⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hpDD
  refine ⟨u * x + v * y, ?_⟩
  have : ((u * p + v * DD : ℤ) : 𝓞 K21) = 1 := by rw [huv]; simp
  push_cast at this
  linear_combination (-x) * this + v * h

/-- The degree one case: `L = X + l0`. -/
theorem lin_case (p : ℕ) (hp : p.Prime) (hpDD : ¬ (p : ℤ) ∣ DD) (P : Ideal (𝓞 K21)) [P.IsPrime]
    (hPZ : ∀ n : ℤ, (n : 𝓞 K21) ∈ P → (p : ℤ) ∣ n) (l0 : ℕ) (Cl : List ℤ) (c : 𝓞 K21)
    (hCc : (DD : 𝓞 K21) * c = evalZ θ Cl) (hLP : (l0 : 𝓞 K21) + θ ∈ P)
    (h : linCheck p [l0, 1] Cl = true) :
    c ∉ P ∧ ∃ d, ((l0 : 𝓞 K21) + θ) * c = p * d := by
  unfold linCheck at h
  simp only [List.headD_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [hornerMod_eq] at h1
  constructor
  · intro hc
    have hCP : evalZ θ Cl ∈ P := hCc ▸ P.mul_mem_left _ hc
    obtain ⟨q, hq⟩ := sub_dvd_evalZ_sub θ (((-(l0 : ℤ)) : ℤ) : 𝓞 K21) Cl
    have hdiff : evalZ θ Cl - evalZ (((-(l0 : ℤ)) : ℤ) : 𝓞 K21) Cl ∈ P := by
      rw [hq]; apply P.mul_mem_right; convert hLP using 1; push_cast; ring
    have hval : evalZ (((-(l0 : ℤ)) : ℤ) : 𝓞 K21) Cl = ((evalZ (-(l0 : ℤ)) Cl : ℤ) : 𝓞 K21) := by
      have := evalZ_map (Int.castRingHom (𝓞 K21)) (-(l0 : ℤ)) Cl
      simpa using this.symm
    have hmem : ((evalZ (-(l0 : ℤ)) Cl : ℤ) : 𝓞 K21) ∈ P := by
      rw [← hval]
      have := P.sub_mem hCP hdiff
      simpa using this
    exact h1 (Int.emod_eq_zero_of_dvd (hPZ _ hmem))
  · have hE := evalZ_of_allDvd θ p _ h2
    simp only [evalZ_addZ, evalZ_smulZ, evalZ_cons, evalZ_θ_fL, mul_zero, add_zero,
      Int.cast_zero, zero_add, Int.cast_natCast] at hE
    obtain ⟨y, hy⟩ : ∃ y, θ * evalZ θ Cl + (l0 : 𝓞 K21) * evalZ θ Cl = p * y := ⟨_, hE⟩
    exact mul_eq_p_mul_of_DD p hp hpDD _ y (by rw [mul_left_comm, hCc]; linear_combination hy)

/-- The case of degree at least 2. -/
theorem hi_case (p : ℕ) (hp : p.Prime) (hpDD : ¬ (p : ℤ) ∣ DD) (P : Ideal (𝓞 K21)) [hP : P.IsPrime]
    (L : List ℕ) (Cl : List ℤ) (sp up : List ℕ) (c : 𝓞 K21)
    (hCc : (DD : 𝓞 K21) * c = evalZ θ Cl) (hLP : evalZ θ (L.map fun x : ℕ => (x : ℤ)) ∈ P)
    (hpP : (p : 𝓞 K21) ∈ P) (h : hiCheck p L Cl sp up = true) :
    c ∉ P ∧ ∃ d, evalZ θ (L.map fun x : ℕ => (x : ℤ)) * c = p * d := by
  unfold hiCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have e1 := evalZ_of_allDvd θ p _ h1
  rw [evalZ_redZ θ fLow (root_fLow θ evalZ_θ_fL), evalZ_mulZ] at e1
  have e2 := evalZ_of_allDvd θ p _ h2
  simp only [evalZ_addZ, evalZ_mulZ, evalZ_cons, evalZ_nil, mul_zero, add_zero,
    Int.cast_neg, Int.cast_one, Int.cast_natCast] at e2
  constructor
  · intro hc
    have hCP : evalZ θ Cl ∈ P := hCc ▸ P.mul_mem_left _ hc
    have h1P : (1 : 𝓞 K21) ∈ P := by
      have : (1 : 𝓞 K21) = evalZ θ Cl * evalZ θ (sp.map fun x : ℕ => (x : ℤ)) +
          evalZ θ (L.map fun x : ℕ => (x : ℤ)) * evalZ θ (up.map fun x : ℕ => (x : ℤ)) -
          p * evalZ θ ((addZ (addZ (mulZ Cl (sp.map fun x : ℕ => (x : ℤ)))
            (mulZ (L.map fun x : ℕ => (x : ℤ)) (up.map fun x : ℕ => (x : ℤ)))) [-1]).map
              fun x => x / p) := by
        linear_combination -e2
      rw [this]
      exact P.sub_mem (P.add_mem (P.mul_mem_right _ hCP) (P.mul_mem_right _ hLP))
        (P.mul_mem_right _ hpP)
    exact hP.ne_top ((eq_top_iff_one _).mpr h1P)
  · have hy : ∃ y, (DD : 𝓞 K21) * (evalZ θ (L.map fun x : ℕ => (x : ℤ)) * c) = p * y :=
      ⟨_, by rw [mul_left_comm, hCc]; exact e1⟩
    obtain ⟨y, hy⟩ := hy
    exact mul_eq_p_mul_of_DD p hp hpDD _ y hy

/-- Soundness of `genCheck`: `(p, L(θ))`, if prime, is principal. -/
theorem genCheck_sound (p : ℕ) (hp : p.Prime) (hp17 : p < 2 ^ 17) (hpDD : ¬ (p : ℤ) ∣ DD)
    (fac : Fac) (hok : facOK p fac = true) (hg : genCheck p fac = true) (P : Ideal (𝓞 K21))
    [P.IsPrime] (hPZ : ∀ n : ℤ, (n : 𝓞 K21) ∈ P → (p : ℤ) ∣ n)
    (hPs : P = span {(p : 𝓞 K21), evalZ θ (fac.L.map fun x : ℕ => (x : ℤ))}) :
    Submodule.IsPrincipal P := by
  unfold genCheck at hg
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨ha, hc⟩, hab⟩, hcb⟩, ⟨⟨⟨⟨⟨hHv, hQv⟩, hQb⟩, hCk⟩, hClb⟩, hbr⟩⟩ := hg
  obtain ⟨hαc, hDc⟩ := gen_core p hp17 fac.a fac.c _ _ ha hc ((allBounded_iff _ _).mp hab)
    ((allBounded_iff _ _).mp hcb) ((allBounded_iff _ _).mp hClb) ((allBounded_iff _ _).mp hQb)
    (by rw [hQv]; exact hHv) hCk
  have hLP : evalZ θ (fac.L.map fun x : ℕ => (x : ℤ)) ∈ P := hPs ▸ subset_span (by simp)
  have hpP : (p : 𝓞 K21) ∈ P := hPs ▸ subset_span (by simp)
  have hcase : elt fac.c ∉ P ∧
      ∃ d, evalZ θ (fac.L.map fun x : ℕ => (x : ℤ)) * elt fac.c = p * d := by
    split_ifs at hbr with hdeg
    · unfold facOK at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hok
      obtain ⟨⟨⟨_, hlen⟩, hlast⟩, _⟩ := hok
      rw [hdeg] at hlen
      obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
      rw [hxy] at hlast hbr hLP ⊢
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      have hval : evalZ θ ([x, 1].map fun x : ℕ => (x : ℤ)) = (x : 𝓞 K21) + θ := by simp
      rw [hval] at hLP ⊢
      exact lin_case p hp hpDD P hPZ x _ _ hDc hLP hbr
    · exact hi_case p hp hpDD P fac.L _ fac.sp fac.up _ hDc hLP hpP hbr
  obtain ⟨hcP, d, hd⟩ := hcase
  exact ⟨⟨elt fac.a, eq_span_of_cert P _ _ _ _ d hPs hαc hcP hd⟩⟩

end FurioLombardo.M2
