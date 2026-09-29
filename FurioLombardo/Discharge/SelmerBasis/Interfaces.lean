import Mathlib
import FurioLombardo.M3a.XminusT

/-!
# Interfaces of lane SelmerBasisK21 (frozen 2026-09-28)

The sub-lanes of `SelmerBasisK21` prove these Props for the concrete data; the two generic lemmas
below assemble them.

* `CountBound f n`: the image of `μ` on `A(K)` is finite with at most `2^n` elements (the count at a
  p-adic place: a finite index subgroup of `A(K_w)` isomorphic to `O_w²`, and `#A(K_w)[2]`).
* `IndepImage f D`: the images of the points `D i` are independent modulo squares (the echelon
  certificates; at `v` this is `SelmerSpan.indep_Dpt`).
* `ImageIn f W`: the image of `μ` lies in the subgroup `W` (at a p-adic place from the two above by
  `imageIn_closure_of_count_indep`; at a real place from the ordering argument).
* `CoordCond φ f g W C`: in coordinates on the global generators `g s`, the local condition
  `Hmap φ (∏ g s ^ a s) ∈ W` forces `C a = 0` over `ZMod 2` (the echelon coordinates at the place).
* `GlobalSpan f g`: every `μ(Q)`, `Q ∈ A(K21)`, is a product of the global generators (Schaefer, the
  class groups, the S-unit span).
* `SUnitSpan F gens`: every element of `F` with even valuation at every prime not above 2 or 7 is a
  product of the `gens s` times a square (vacuous if some `gens s = 0`: the brick counts as done
  together with `gens s ≠ 0` for every `s`).
* `RelAtV σ f g β D SB`: the images at `σ` of the products `∏ s, g s ^ β j s` are the columns of
  `SB` on the points `D i` (what makes `SelmerBasisK21` exact at `v`).
-/

open Polynomial FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.SelmerBasis

section Abstract

/-- In a group of exponent 2, `n` independent elements in a subgroup with at most `2^n`
elements generate it. -/
theorem closure_of_card_indep {H : Type*} [CommGroup H] (hH : ∀ h : H, h ^ 2 = 1) {n : ℕ}
    (s : Finset H) (hcard : s.card ≤ 2 ^ n) (d : Fin n → H) (hd : ∀ e : Fin n → ℕ, ∏ i, d i ^ e i ∈ s)
    (hi : ∀ c : Fin n → ℕ, ∏ i, d i ^ c i = 1 → ∀ i, 2 ∣ c i) :
    ∀ x ∈ s, ∃ e : Fin n → ℕ, x = ∏ i, d i ^ e i := by
  classical
  let E : (Fin n → ZMod 2) → H := λ c => ∏ i, d i ^ ((c i).val)
  have hE_inj : Function.Injective E := by
    intro c c' h
    have h_prod : E c * E c' = 1 := by
      calc
        E c * E c' = E c * E c := by rw [h]
        _ = (E c) ^ 2 := by rw [pow_two]
        _ = 1 := hH (E c)
    have h_prod' : ∏ i, d i ^ ((c i).val + (c' i).val) = 1 := by
      calc
        ∏ i, d i ^ ((c i).val + (c' i).val) = ∏ i, (d i ^ ((c i).val) * d i ^ ((c' i).val)) := by
          refine Finset.prod_congr rfl (λ i _ => ?_)
          rw [pow_add]
        _ = (∏ i, d i ^ ((c i).val)) * (∏ i, d i ^ ((c' i).val)) := by
          rw [Finset.prod_mul_distrib]
        _ = E c * E c' := rfl
        _ = 1 := h_prod
    have h_even : ∀ i, 2 ∣ ((c i).val + (c' i).val) :=
      hi (λ i => (c i).val + (c' i).val) h_prod'
    have h_val_eq : ∀ i, (c i).val = (c' i).val := by
      intro i
      have h_fin : ∀ (a b : ZMod 2), 2 ∣ (a.val + b.val) → a.val = b.val := by
        decide
      exact h_fin (c i) (c' i) (h_even i)
    ext i
    apply ZMod.val_injective
    exact h_val_eq i
  have h_image_subset : Finset.image E Finset.univ ⊆ s := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨c, _, rfl⟩
    apply hd
  have h_card_image : (Finset.image E Finset.univ).card = 2 ^ n := by
    calc
      (Finset.image E Finset.univ).card = (Finset.univ : Finset (Fin n → ZMod 2)).card :=
        Finset.card_image_of_injective _ hE_inj
      _ = Fintype.card (Fin n → ZMod 2) := by simp
      _ = Fintype.card (ZMod 2) ^ n := by simp [Fintype.card_pi_const (ZMod 2) n]
      _ = 2 ^ n := by simp [ZMod.card]
  have h_eq : Finset.image E Finset.univ = s :=
    Finset.eq_of_subset_of_card_le h_image_subset (by
      rw [h_card_image]
      exact hcard)
  intro x hx
  have hx' : x ∈ Finset.image E Finset.univ := by
    rw [h_eq]
    exact hx
  rcases Finset.mem_image.1 hx' with ⟨c, _, hx_eq⟩
  refine ⟨λ i => (c i).val, ?_⟩
  simpa [E] using hx_eq.symm

/-- The F₂ linear algebra of the Selmer bound, in an abstract group of exponent 2. -/
theorem span_of_local {H : Type*} [CommGroup H] (hH : ∀ h : H, h ^ 2 = 1) {m p nr : ℕ}
    (g : Fin m → H) {ι : Type*} [Fintype ι] (Hw : ι → Type*) [∀ w, CommGroup (Hw w)]
    (ψ : ∀ w, H →* Hw w) (W : ∀ w, Subgroup (Hw w)) (c : ι → ℕ)
    (C : ∀ w, Matrix (Fin (c w)) (Fin m) (ZMod 2))
    (hC : ∀ w, ∀ a : Fin m → ℕ, ψ w (∏ s, g s ^ a s) ∈ W w →
      (C w).mulVec (fun s => (a s : ZMod 2)) = 0)
    (β : Fin p → Fin m → ℕ) (κ : Fin nr → Fin m → ℕ) (hκ : ∀ t, ∏ s, g s ^ κ t s = 1)
    (hX : ∀ a : Fin m → ZMod 2, (∀ w, (C w).mulVec a = 0) →
      ∃ e : Fin p → ZMod 2, ∃ ε : Fin nr → ZMod 2,
        a = ∑ j, e j • (fun s => (β j s : ZMod 2)) + ∑ t, ε t • (fun s => (κ t s : ZMod 2)))
    (x : H) (hx : ∃ a : Fin m → ℕ, x = ∏ s, g s ^ a s) (hxW : ∀ w, ψ w x ∈ W w) :
    ∃ e : Fin p → ℤ, x = ∏ j, (∏ s, g s ^ β j s) ^ e j := by
  rcases hx with ⟨a, hx_eq⟩
  -- Lemma: h^2 = 1 implies h^n = h^(n % 2)
  have pow_mod_two : ∀ (h : H) (n : ℕ), h ^ n = h ^ (n % 2) := by
    intro h n
    conv =>
      lhs
      rw [← Nat.mod_add_div n 2]
    rw [pow_add, pow_mul, hH h, one_pow, mul_one]
  -- For each w, (C w).mulVec (fun s => (a s : ZMod 2)) = 0
  have hC' : ∀ w, (C w).mulVec (fun s => (a s : ZMod 2)) = 0 := by
    intro w
    apply hC w a
    rw [← hx_eq]
    exact hxW w
  -- Apply hX to get decomposition mod 2
  rcases hX (fun s => (a s : ZMod 2)) hC' with ⟨e', ε', h_decomp⟩
  -- Define r(v) = ∏ s, g s ^ (v s).val
  let r := fun (v : Fin m → ZMod 2) => ∏ s : Fin m, g s ^ (v s).val
  -- r(0) = 1
  have r_zero : r 0 = 1 := by
    simp [r]
  -- r(v + w) = r(v) * r(w)
  have r_add : ∀ (v w : Fin m → ZMod 2), r (v + w) = r v * r w := by
    intro v w
    dsimp [r]
    calc
      ∏ s : Fin m, g s ^ ((v + w) s).val = ∏ s : Fin m, g s ^ ((v s + w s).val) := rfl
      _ = ∏ s : Fin m, g s ^ (((v s).val + (w s).val) % 2) := by
        refine Finset.prod_congr rfl (fun s _ => ?_)
        rw [ZMod.val_add]
      _ = ∏ s : Fin m, g s ^ ((v s).val + (w s).val) := by
        refine Finset.prod_congr rfl (fun s _ => ?_)
        rw [pow_mod_two (g s) ((v s).val + (w s).val)]
      _ = ∏ s : Fin m, (g s ^ (v s).val * g s ^ (w s).val) := by
        refine Finset.prod_congr rfl (fun s _ => ?_)
        rw [pow_add]
      _ = (∏ s : Fin m, g s ^ (v s).val) * (∏ s : Fin m, g s ^ (w s).val) := by
        rw [Finset.prod_mul_distrib]
  -- r(c • v) = r(v) ^ c.val
  have r_smul : ∀ (c : ZMod 2) (v : Fin m → ZMod 2), r (c • v) = r v ^ c.val := by
    intro c v
    have h_cases : c.val = 0 ∨ c.val = 1 := by
      have h_lt : c.val < 2 := ZMod.val_lt c
      omega
    rcases h_cases with (h_val | h_val)
    · -- c.val = 0
      have hc : c = 0 := by
        simpa [h_val] using (ZMod.natCast_val (R := ZMod 2) c).symm
      rw [hc, zero_smul, r_zero]
      simp [ZMod.val_zero]
    · -- c.val = 1
      have hc : c = 1 := by
        simpa [h_val] using (ZMod.natCast_val (R := ZMod 2) c).symm
      rw [hc, one_smul]
      simp [ZMod.val_one]
  -- r(sum over Finset) = product of r (for both Fin p and Fin nr)
  have r_sum_p : ∀ (s : Finset (Fin p)) (f : Fin p → (Fin m → ZMod 2)),
      r (∑ i ∈ s, f i) = ∏ i ∈ s, r (f i) := by
    intro s f
    induction' s using Finset.induction with i s his ih
    · simp [r_zero]
    · simp [Finset.sum_insert his, Finset.prod_insert his, r_add, ih]
  have r_sum_nr : ∀ (s : Finset (Fin nr)) (f : Fin nr → (Fin m → ZMod 2)),
      r (∑ i ∈ s, f i) = ∏ i ∈ s, r (f i) := by
    intro s f
    induction' s using Finset.induction with i s his ih
    · simp [r_zero]
    · simp [Finset.sum_insert his, Finset.prod_insert his, r_add, ih]
  -- Relate r to the product ∏ s, g s ^ n s
  have r_eq_prod : ∀ (n : Fin m → ℕ), r (fun s => (n s : ZMod 2)) = ∏ s : Fin m, g s ^ n s := by
    intro n
    dsimp [r]
    refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [ZMod.val_natCast]
    rw [← pow_mod_two (g s) (n s)]
  -- x = r(a_mod2)
  have hx_r : x = r (fun s => (a s : ZMod 2)) := by
    rw [hx_eq, ← r_eq_prod a]
  -- r(βj_mod2) = ∏ s, g s ^ β j s
  have hβj_r : ∀ j, r (fun s => (β j s : ZMod 2)) = ∏ s : Fin m, g s ^ β j s := by
    intro j
    rw [r_eq_prod (β j)]
  -- r(κt_mod2) = 1
  have hκt_r : ∀ t, r (fun s => (κ t s : ZMod 2)) = 1 := by
    intro t
    rw [r_eq_prod (κ t), hκ t]
  -- Now compute r(a_mod2) using the decomposition
  have h_main : r (fun s => (a s : ZMod 2)) = ∏ j : Fin p, (∏ s : Fin m, g s ^ β j s) ^ ((e' j).val : ℤ) := by
    rw [h_decomp]
    -- r(∑ j, e' j • βj_mod2 + ∑ t, ε' t • κt_mod2)
    rw [r_add]
    -- Now we have r(∑ j, ...) * r(∑ t, ...)
    have hsum1 : r (∑ j : Fin p, e' j • (fun s => (β j s : ZMod 2))) =
        ∏ j : Fin p, r (e' j • (fun s => (β j s : ZMod 2))) := by
      simpa using r_sum_p Finset.univ (fun j => e' j • (fun s => (β j s : ZMod 2)))
    have hsum2 : r (∑ t : Fin nr, ε' t • (fun s => (κ t s : ZMod 2))) =
        ∏ t : Fin nr, r (ε' t • (fun s => (κ t s : ZMod 2))) := by
      simpa using r_sum_nr Finset.univ (fun t => ε' t • (fun s => (κ t s : ZMod 2)))
    rw [hsum1, hsum2]
    -- Apply r_smul to each term
    have hterms1 : (∏ j : Fin p, r (e' j • (fun s => (β j s : ZMod 2)))) =
        ∏ j : Fin p, (r (fun s => (β j s : ZMod 2))) ^ ((e' j).val : ℤ) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [r_smul (e' j) (fun s => (β j s : ZMod 2)), zpow_natCast]
    have hterms2 : (∏ t : Fin nr, r (ε' t • (fun s => (κ t s : ZMod 2)))) =
        ∏ t : Fin nr, (r (fun s => (κ t s : ZMod 2))) ^ ((ε' t).val : ℤ) := by
      refine Finset.prod_congr rfl (fun t _ => ?_)
      rw [r_smul (ε' t) (fun s => (κ t s : ZMod 2)), zpow_natCast]
    rw [hterms1, hterms2]
    -- Use hβj_r and hκt_r to replace r(...)
    have hprod1 : (∏ j : Fin p, (r (fun s => (β j s : ZMod 2))) ^ ((e' j).val : ℤ)) =
        ∏ j : Fin p, (∏ s : Fin m, g s ^ β j s) ^ ((e' j).val : ℤ) := by
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [hβj_r j]
    have hprod2 : (∏ t : Fin nr, (r (fun s => (κ t s : ZMod 2))) ^ ((ε' t).val : ℤ)) = 1 := by
      calc
        (∏ t : Fin nr, (r (fun s => (κ t s : ZMod 2))) ^ ((ε' t).val : ℤ)) =
            (∏ t : Fin nr, 1 ^ ((ε' t).val : ℤ)) := by
          refine Finset.prod_congr rfl (fun t _ => ?_)
          rw [hκt_r t]
        _ = ∏ t : Fin nr, 1 := by simp
        _ = 1 := by simp
    rw [hprod1, hprod2]
    simp
  -- Final step: combine hx_r and h_main
  rw [hx_r, h_main]
  -- Produce e : Fin p → ℤ
  refine ⟨fun j => ((e' j).val : ℤ), rfl⟩

end Abstract

section Local

variable {K : Type*} [Field K]

/-- `H f = L^× / K^× (L^×)²` has exponent 2 (as `SelmerSpan`'s `H_sq_eq_one`, restated here to
keep the imports small). -/
theorem H_sq (f : K[X]) (h : H f) : h ^ 2 = 1 := by
  induction h using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_sup_right ⟨u, rfl⟩

/-- **Count at a place.** The image of `μ` on `A(K)` is finite with at most `2^n` elements. -/
def CountBound (f : K[X]) [GoodSextic f] (n : ℕ) : Prop :=
  ∃ s : Finset (H f), (∀ Q : Jac f, muJ f Q ∈ s) ∧ s.card ≤ 2 ^ n

/-- **Independence of local points.** A relation among the `μ(D i)` has only even exponents. -/
def IndepImage (f : K[X]) [GoodSextic f] {r : ℕ} (D : Fin r → Jac f) : Prop :=
  ∀ c : Fin r → ℕ, ∏ i, muJ f (D i) ^ c i = 1 → ∀ i, 2 ∣ c i

/-- **Local image.** The image of `μ` on `A(K)` lies in `W`. -/
def ImageIn (f : K[X]) [GoodSextic f] (W : Subgroup (H f)) : Prop :=
  ∀ Q : Jac f, muJ f Q ∈ W

/-- **Local condition in coordinates.** For the global classes `g s` over `K` and a place
`φ : K → K'`, if the image of `∏ g s ^ a s` lies in `W` then `C a = 0`. -/
def CoordCond {K' : Type*} [Field K'] (φ : K →+* K') (f : K[X]) {m c : ℕ} (g : Fin m → H f)
    (W : Subgroup (H (f.map φ))) (C : Matrix (Fin c) (Fin m) (ZMod 2)) : Prop :=
  ∀ a : Fin m → ℕ, Hmap φ f (∏ s, g s ^ a s) ∈ W → C.mulVec (fun s => (a s : ZMod 2)) = 0

/-- **Global span.** Every `μ(Q)` is a product of the classes `g s`. -/
def GlobalSpan (f : K[X]) [GoodSextic f] {m : ℕ} (g : Fin m → H f) : Prop :=
  ∀ Q : Jac f, ∃ a : Fin m → ℕ, muJ f Q = ∏ s, g s ^ a s

/-- With `n` independent points and at most `2^n` classes, the image of `μ` is spanned by the
images of the points. -/
theorem imageIn_closure_of_count_indep (f : K[X]) [GoodSextic f] {n : ℕ} (D : Fin n → Jac f)
    (hc : CountBound f n) (hi : IndepImage f D) :
    ImageIn f (Subgroup.closure (Set.range fun i => muJ f (D i))) := by
  intro Q
  obtain ⟨s, hs, hcard⟩ := hc
  obtain ⟨e, he⟩ := closure_of_card_indep (H_sq f) s hcard (fun i => muJ f (D i))
    (fun e => by simpa only [map_prod, map_pow] using hs (∏ i, D i ^ e i)) hi _ (hs Q)
  rw [he]
  refine Subgroup.prod_mem (Subgroup.closure (Set.range fun i => muJ f (D i))) fun i _ => ?_
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

/-- **Assembly of the Selmer span.** A global span by `m` classes, local conditions at finitely
many places whose coordinate conditions cut `F₂^m` down to the span of the columns `β j` plus
relation vectors `κ t` that are trivial in `H f`, give the span by the four classes
`∏ s, g s ^ β j s`. -/
theorem selmerSpan_of_interfaces (f : K[X]) [GoodSextic f] {m p nr : ℕ} (g : Fin m → H f)
    (hg : GlobalSpan f g) {ι : Type*} [Fintype ι] (K' : ι → Type*) [∀ w, Field (K' w)]
    (φ : ∀ w, K →+* K' w) [∀ w, GoodSextic (f.map (φ w))] (W : ∀ w, Subgroup (H (f.map (φ w))))
    (hW : ∀ w, ImageIn (f.map (φ w)) (W w)) (c : ι → ℕ)
    (C : ∀ w, Matrix (Fin (c w)) (Fin m) (ZMod 2)) (hC : ∀ w, CoordCond (φ w) f g (W w) (C w))
    (β : Fin p → Fin m → ℕ) (κ : Fin nr → Fin m → ℕ) (hκ : ∀ t, ∏ s, g s ^ κ t s = 1)
    (hX : ∀ a : Fin m → ZMod 2, (∀ w, (C w).mulVec a = 0) →
      ∃ e : Fin p → ZMod 2, ∃ ε : Fin nr → ZMod 2,
        a = ∑ j, e j • (fun s => (β j s : ZMod 2)) + ∑ t, ε t • (fun s => (κ t s : ZMod 2))) :
    ∀ Q : Jac f, ∃ e : Fin p → ℤ, muJ f Q = ∏ j, (∏ s, g s ^ β j s) ^ e j := by
  intro Q
  refine span_of_local (H_sq f) g (fun w => H (f.map (φ w))) (fun w => Hmap (φ w) f) W c C
    (fun w a ha => hC w a ha) β κ hκ hX (muJ f Q) (hg Q) (fun w => ?_)
  rw [← muJ_jacMap]
  exact hW w _

/-- **Relation at `v`**. The image at `σ` of each assembled class `∏ s, g s ^ β j s` is the class
`∏ i, μ(D i) ^ SB i j` of the local points `D i`. -/
def RelAtV {K' : Type*} [Field K'] (σ : K →+* K') (f : K[X]) [GoodSextic (f.map σ)] {m r : ℕ}
    (g : Fin m → H f) (β : Fin 4 → Fin m → ℕ) (D : Fin r → Jac (f.map σ))
    (SB : Matrix (Fin r) (Fin 4) ℤ) : Prop :=
  ∀ j, Hmap σ f (∏ s, g s ^ β j s) = ∏ i, muJ (f.map σ) (D i) ^ SB i j

/-- **Assembly of the Selmer basis.** `selmerSpan_of_interfaces` with four columns `β j` and the
relation at `v`: the four classes `G j = ∏ s, g s ^ β j s` span the image of `μ` (the conclusion
is `SelmerSpan f G` unfolded) and have the prescribed images at `σ`. -/
theorem selmerBasis_of_interfaces (f : K[X]) [GoodSextic f] {m nr : ℕ} (g : Fin m → H f)
    (hg : GlobalSpan f g) {ι : Type*} [Fintype ι] (K' : ι → Type*) [∀ w, Field (K' w)]
    (φ : ∀ w, K →+* K' w) [∀ w, GoodSextic (f.map (φ w))] (W : ∀ w, Subgroup (H (f.map (φ w))))
    (hW : ∀ w, ImageIn (f.map (φ w)) (W w)) (c : ι → ℕ)
    (C : ∀ w, Matrix (Fin (c w)) (Fin m) (ZMod 2)) (hC : ∀ w, CoordCond (φ w) f g (W w) (C w))
    (β : Fin 4 → Fin m → ℕ) (κ : Fin nr → Fin m → ℕ) (hκ : ∀ t, ∏ s, g s ^ κ t s = 1)
    (hX : ∀ a : Fin m → ZMod 2, (∀ w, (C w).mulVec a = 0) →
      ∃ e : Fin 4 → ZMod 2, ∃ ε : Fin nr → ZMod 2,
        a = ∑ j, e j • (fun s => (β j s : ZMod 2)) + ∑ t, ε t • (fun s => (κ t s : ZMod 2)))
    {K'' : Type*} [Field K''] (σ : K →+* K'') [GoodSextic (f.map σ)] {r : ℕ}
    (D : Fin r → Jac (f.map σ)) (SB : Matrix (Fin r) (Fin 4) ℤ) (hR : RelAtV σ f g β D SB) :
    ∃ G : Fin 4 → H f, (∀ Q : Jac f, ∃ e : Fin 4 → ℤ, muJ f Q = ∏ j, G j ^ e j) ∧
      ∀ j, Hmap σ f (G j) = ∏ i, muJ (f.map σ) (D i) ^ SB i j :=
  ⟨fun j => ∏ s, g s ^ β j s,
    selmerSpan_of_interfaces f g hg K' φ W hW c C hC β κ hκ hX, hR⟩

end Local

section Global

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

/-- **S-unit span.** Every nonzero `x` of `F` with even valuation at every prime not above 2 or 7
is, up to a square, a product of the `gens s`. -/
def SUnitSpan (F : Type*) [Field F] [NumberField F] {m : ℕ} (gens : Fin m → F) : Prop :=
  ∀ x : F, x ≠ 0 →
    (∀ P : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∉ P.asIdeal → (7 : 𝓞 F) ∉ P.asIdeal →
      Even (FractionalIdeal.count F P (FractionalIdeal.spanSingleton (𝓞 F)⁰ x))) →
    ∃ a : Fin m → ℕ, IsSquare (x * ∏ s, gens s ^ a s)

end Global

end FurioLombardo.Discharge.SelmerBasis
