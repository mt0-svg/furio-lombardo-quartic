import Mathlib
import FurioLombardo.Discharge.KvArith.Comp.Ops

/-!
# Straight line programs over any arithmetic (lane lean-kv-arith, generic layer)

A program is written once as a Lean function over `o : Ops A` (sum, difference, negation, product, a
partial inverse, integer constants) and run on three carriers: exact values in a field (`fieldOps`, the
inverse fails exactly at `0`), balls (`KvArith.ballOps`) and Taylor models (`KvArith.tmOps`). Soundness
is relational: `Ops.Rel o p R` says that every operation of `p` follows the operation of `o` along `R`,
and that when `p` inverts `a` successfully, `o` inverts every `R`-related `x`. A program is related to
itself along `R` (its `_rel` lemma, one per program), so the certified run bounds the exact run, and a
successful certified run certifies every inverse of the exact run (`OptRel`). Relations compose
(`Ops.Rel.comp`); pointwise functions `D → K` (`funOps`) evaluate to the field at each point of `H`
(`rel_fieldOps_funOps`).

Generic programs (`Comp/Ops.lean`): `Ops.zero`, `Ops.horner`, `Ops.hornerZ` (integer coefficients), `Ops.hornerZ2`
(bivariate), `Ops.zipAdd`, `Ops.zipSub`, `Ops.conv` (list polynomials), here with their `_rel` lemmas and their exact values over a field. The programs themselves live in
`Comp/Ops.lean`, which has no Mathlib import.
-/

namespace FurioLombardo.Discharge.KvArith

/-- `p` follows `o` along `R`: operations preserve `R`, and a successful inverse of `p` forces a
successful inverse of `o`. -/
structure Ops.Rel {A B : Type*} (o : Ops A) (p : Ops B) (R : A → B → Prop) : Prop where
  add : ∀ {x y : A} {a b : B}, R x a → R y b → R (o.add x y) (p.add a b)
  sub : ∀ {x y : A} {a b : B}, R x a → R y b → R (o.sub x y) (p.sub a b)
  neg : ∀ {x : A} {a : B}, R x a → R (o.neg x) (p.neg a)
  mul : ∀ {x y : A} {a b : B}, R x a → R y b → R (o.mul x y) (p.mul a b)
  inv : ∀ {x : A} {a b : B}, R x a → p.inv a = some b → ∃ y, o.inv x = some y ∧ R y b
  ofInt : ∀ z : ℤ, R (o.ofInt z) (p.ofInt z)

/-- Relation of optional results: whenever the second succeeds, so does the first, related. -/
def OptRel {A B : Type*} (R : A → B → Prop) (x : Option A) (y : Option B) : Prop :=
  ∀ b, y = some b → ∃ a, x = some a ∧ R a b

theorem Ops.Rel.comp {A B C : Type*} {o : Ops A} {p : Ops B} {q : Ops C} {R : A → B → Prop}
    {S : B → C → Prop} (h1 : Ops.Rel o p R) (h2 : Ops.Rel p q S) :
    Ops.Rel o q (fun x c => ∃ b, R x b ∧ S b c) := by
  refine {
    add := ?_
    sub := ?_
    neg := ?_
    mul := ?_
    inv := ?_
    ofInt := ?_
  }
  · intro x y a b hx hy
    rcases hx with ⟨b1, hR1, hS1⟩
    rcases hy with ⟨b2, hR2, hS2⟩
    exact ⟨p.add b1 b2, h1.add hR1 hR2, h2.add hS1 hS2⟩
  · intro x y a b hx hy
    rcases hx with ⟨b1, hR1, hS1⟩
    rcases hy with ⟨b2, hR2, hS2⟩
    exact ⟨p.sub b1 b2, h1.sub hR1 hR2, h2.sub hS1 hS2⟩
  · intro x a hx
    rcases hx with ⟨b1, hR1, hS1⟩
    exact ⟨p.neg b1, h1.neg hR1, h2.neg hS1⟩
  · intro x y a b hx hy
    rcases hx with ⟨b1, hR1, hS1⟩
    rcases hy with ⟨b2, hR2, hS2⟩
    exact ⟨p.mul b1 b2, h1.mul hR1 hR2, h2.mul hS1 hS2⟩
  · intro x a b hx hq
    rcases hx with ⟨b1, hR1, hS1⟩
    rcases h2.inv hS1 hq with ⟨b2, hpb2, hS2⟩
    rcases h1.inv hR1 hpb2 with ⟨y, hoya, hR2⟩
    exact ⟨y, hoya, b2, hR2, hS2⟩
  · intro z
    exact ⟨p.ofInt z, h1.ofInt z, h2.ofInt z⟩

/-- Exact arithmetic in a field; the inverse fails exactly at `0`. -/
noncomputable def fieldOps (K : Type*) [Field K] : Ops K where
  add := (· + ·)
  sub := (· - ·)
  neg := Neg.neg
  mul := (· * ·)
  inv x := by classical exact if x = 0 then none else some x⁻¹
  ofInt z := (z : K)

theorem fieldOps_inv_eq_some {K : Type*} [Field K] {x y : K} (h : (fieldOps K).inv x = some y) :
    x ≠ 0 ∧ y = x⁻¹ := by
  have hx : x ≠ 0 := by
    intro hzero
    have : (fieldOps K).inv x = none := by
      simp [fieldOps, hzero]
    rw [this] at h
    simp at h
  have hy : y = x⁻¹ := by
    have : (fieldOps K).inv x = some x⁻¹ := by
      simp [fieldOps, hx]
    rw [this] at h
    exact (Option.some.inj h).symm
  exact And.intro hx hy

/-- Pointwise arithmetic of functions `D → K`; the inverse fails unless the function has no zero
on `H`. -/
noncomputable def funOps {D K : Type*} [Field K] (H : Set D) : Ops (D → K) where
  add F G := fun h => F h + G h
  sub F G := fun h => F h - G h
  neg F := fun h => -F h
  mul F G := fun h => F h * G h
  inv F := by classical exact if ∀ h ∈ H, F h ≠ 0 then some (fun h => (F h)⁻¹) else none
  ofInt z := fun _ => (z : K)

/-- Evaluation at a point of `H`. -/
theorem rel_fieldOps_funOps {D K : Type*} [Field K] {H : Set D} {h : D} (hh : h ∈ H) :
    Ops.Rel (fieldOps K) (funOps (K := K) H) (fun x F => F h = x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y F G hF hG
    simp [fieldOps, funOps, hF, hG]
  · intro x y F G hF hG
    simp [fieldOps, funOps, hF, hG]
  · intro x F hF
    simp [fieldOps, funOps, hF]
  · intro x y F G hF hG
    simp [fieldOps, funOps, hF, hG]
  · intro x F G hF hinv
    subst hF
    simp [funOps] at hinv
    rcases hinv with ⟨hcond, hG⟩
    have hF_ne_zero : F h ≠ 0 := hcond h hh
    refine ⟨(F h)⁻¹, ?_, ?_⟩
    · dsimp [fieldOps]
      simp [hF_ne_zero]
    · rw [← hG]
  · intro z
    simp [fieldOps, funOps]

/-- Exact arithmetic in a commutative ring, with no inverse (for inverse-free programs such as
`hornerZ2` over `K[X]`). -/
def ringOps (R : Type*) [CommRing R] : Ops R where
  add := (· + ·)
  sub := (· - ·)
  neg := Neg.neg
  mul := (· * ·)
  inv _ := none
  ofInt z := (z : R)

/-- The polynomial `Σ cᵢ Xⁱ` of a coefficient list. -/
noncomputable def polyOf {K : Type*} [CommRing K] (cs : List K) : Polynomial K :=
  (cs.mapIdx fun i c => Polynomial.monomial i c).sum

section RelLemmas

variable {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}

theorem Ops.Rel.zero (h : Ops.Rel o p R) : R o.zero p.zero := h.ofInt 0

theorem Ops.Rel.horner (h : Ops.Rel o p R) {cs : List A} {ds : List B}
    (hc : List.Forall₂ R cs ds) {x : A} {a : B} (hx : R x a) : R (o.horner cs x) (p.horner ds a) := by
  induction hc with
  | nil =>
      simp only [Ops.horner, List.foldr, Ops.zero]
      exact h.ofInt 0
  | cons hab _ ih =>
      simp only [Ops.horner, List.foldr, Ops.zero]
      exact h.add hab (h.mul hx ih)

theorem Ops.Rel.hornerZ (h : Ops.Rel o p R) (cs : List ℤ) {x : A} {a : B} (hx : R x a) :
    R (o.hornerZ cs x) (p.hornerZ cs a) := by
  induction cs with
  | nil =>
      simp [Ops.hornerZ, Ops.zero]
      exact h.ofInt 0
  | cons c cs ih =>
      simp [Ops.hornerZ, List.foldr]
      exact h.add (h.ofInt c) (h.mul hx ih)

theorem Ops.Rel.hornerZ2 (h : Ops.Rel o p R) (cs : List (List ℤ)) {x y : A} {a b : B}
    (hx : R x a) (hy : R y b) : R (o.hornerZ2 cs x y) (p.hornerZ2 cs a b) := by
  induction cs with
  | nil =>
      simp [Ops.hornerZ2, Ops.zero]
      exact h.ofInt 0
  | cons c cs ih =>
      simp [Ops.hornerZ2, Ops.zero]
      apply h.add
      · -- R (o.hornerZ c y) (p.hornerZ c b)
        induction c with
        | nil =>
            simp [Ops.hornerZ, Ops.zero]
            exact h.ofInt 0
        | cons d ds ih2 =>
            simp [Ops.hornerZ, Ops.zero]
            apply h.add
            · exact h.ofInt d
            · apply h.mul hy ih2
      · apply h.mul hx ih

theorem Ops.Rel.zipAdd (h : Ops.Rel o p R) {p1 p2 : List A} {q1 q2 : List B}
    (h1 : List.Forall₂ R p1 q1) (h2 : List.Forall₂ R p2 q2) :
    List.Forall₂ R (o.zipAdd p1 p2) (p.zipAdd q1 q2) := by
  induction h1 generalizing p2 q2 with
  | nil =>
      simp [Ops.zipAdd]
      exact h2
  | cons hab h1 ih =>
      cases h2 with
      | nil =>
          simp only [Ops.zipAdd]
          exact List.Forall₂.cons hab h1
      | cons hcd h2 =>
          simp only [Ops.zipAdd]
          exact List.Forall₂.cons (h.add hab hcd) (ih h2)

theorem Ops.Rel.zipSub (h : Ops.Rel o p R) {p1 p2 : List A} {q1 q2 : List B}
    (h1 : List.Forall₂ R p1 q1) (h2 : List.Forall₂ R p2 q2) :
    List.Forall₂ R (o.zipSub p1 p2) (p.zipSub q1 q2) := by
  induction h1 generalizing p2 q2 with
  | nil =>
      simpa [Ops.zipSub] using (h2.imp (fun x a hx => h.neg hx))
  | @cons a b l₁ l₂ h1a h1rest ih =>
      cases h2 with
      | nil =>
          simpa [Ops.zipSub] using List.Forall₂.cons h1a h1rest
      | @cons c d p2' q2' h2a h2rest =>
          have hsub : R (o.sub a c) (p.sub b d) := h.sub h1a h2a
          have ih' : List.Forall₂ R (o.zipSub l₁ p2') (p.zipSub l₂ q2') := ih h2rest
          simpa [Ops.zipSub] using List.Forall₂.cons hsub ih'

theorem Ops.Rel.conv (h : Ops.Rel o p R) {p1 p2 : List A} {q1 q2 : List B}
    (h1 : List.Forall₂ R p1 q1) (h2 : List.Forall₂ R p2 q2) :
    List.Forall₂ R (o.conv p1 p2) (p.conv q1 q2) := by
  induction h1 with
  | nil =>
      simp [Ops.conv]
  | @cons a b p1' q1' h_rel hl ih =>
      have h_map : List.Forall₂ R (p2.map (o.mul a)) (q2.map (p.mul b)) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact h2.imp fun x y hxy => h.mul h_rel hxy
      have h_cons : List.Forall₂ R (o.zero :: o.conv p1' p2) (p.zero :: p.conv q1' q2) :=
        List.Forall₂.cons (h.ofInt 0) ih
      simp [Ops.conv]
      exact h.zipAdd h_map h_cons

theorem Ops.Rel.pmul (h : Ops.Rel o p R) (n : ℕ) {p1 p2 : List A} {q1 q2 : List B}
    (h1 : List.Forall₂ R p1 q1) (h2 : List.Forall₂ R p2 q2) :
    List.Forall₂ R (o.pmul n p1 p2) (p.pmul n q1 q2) := by
  have hconv : List.Forall₂ R (o.conv p1 p2) (p.conv q1 q2) := Ops.Rel.conv h h1 h2
  have htake : List.Forall₂ R ((o.conv p1 p2).take (n + 1)) ((p.conv q1 q2).take (n + 1)) :=
    List.forall₂_take (n + 1) hconv
  unfold Ops.pmul
  exact htake

-- Helper lemma: getD of Forall₂-related lists with related defaults is related
theorem Ops_Rel_sqrtSeries_aux1 {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (i : ℕ) (fallback₁ : α) (fallback₂ : β)
    (hfallback : R fallback₁ fallback₂) : R (l₁.getD i fallback₁) (l₂.getD i fallback₂) := by
  have hlen : l₁.length = l₂.length := h.length_eq
  by_cases hi : i < l₁.length
  · have hi' : i < l₂.length := by
      rw [← hlen]
      exact hi
    have hget := h.get hi hi'
    rw [show l₁.getD i fallback₁ = l₁[i] by simp [hi],
      show l₂.getD i fallback₂ = l₂[i] by simp [hi']]
    exact hget
  · have hi' : ¬ i < l₂.length := by
      rw [← hlen]
      exact hi
    rw [show l₁.getD i fallback₁ = fallback₁ by simp [hi],
      show l₂.getD i fallback₂ = fallback₂ by simp [hi']]
    exact hfallback

-- Helper lemma: foldr preserves the relation
theorem Ops_Rel_sqrtSeries_aux2 {α β γ δ : Type*} {R : α → β → Prop} {P : γ → δ → Prop} {l : List α} {l' : List β} {init : γ} {init' : δ}
    (h : List.Forall₂ R l l') (f : α → γ → γ) (g : β → δ → δ)
    (hfg : ∀ (a : α) (c : γ) (a' : β) (c' : δ), R a a' → P c c' → P (f a c) (g a' c'))
    (hinit : P init init') : P (List.foldr f init l) (List.foldr g init' l') := by
  induction h generalizing init init' with
  | nil => exact hinit
  | cons hab hrest ih =>
    simp [List.foldr]
    apply hfg _ _ _ _ hab
    apply ih hinit

section Ops_Rel_invSeries_aux
-- Helper lemma: the step function of sqrtSeries preserves the relation

-- Helper lemma: map over range preserves the relation
lemma Ops_Rel_invSeries_aux1 {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}
    {g : List A} {g' : List B} {ds : List A} {ds' : List B}
    (h : Ops.Rel o p R) (hg : List.Forall₂ R g g') (hds : List.Forall₂ R ds ds') (j : ℕ) :
    List.Forall₂ R
      ((List.range j).map (fun i => o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)))
      ((List.range j).map (fun i => p.mul (g'.getD (i + 1) p.zero) (ds'.getD (j - 1 - i) p.zero))) := by
  have h_range : List.Forall₂ (· = ·) (List.range j) (List.range j) :=
    List.forall₂_refl _
  refine List.rel_map (R := (· = ·)) (P := R) ?_ ?_
  · intro a b heq
    subst heq
    have hg_getd : R (g.getD (a + 1) o.zero) (g'.getD (a + 1) p.zero) :=
      Ops_Rel_sqrtSeries_aux1 hg (a + 1) o.zero p.zero (h.ofInt 0)
    have hds_getd : R (ds.getD (j - 1 - a) o.zero) (ds'.getD (j - 1 - a) p.zero) :=
      Ops_Rel_sqrtSeries_aux1 hds (j - 1 - a) o.zero p.zero (h.ofInt 0)
    exact h.mul hg_getd hds_getd
  · exact h_range

-- Helper lemma: the step function preserves the relation
lemma Ops_Rel_invSeries_aux2 {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}
    {g : List A} {g' : List B} {d0 : A} {d0' : B}
    (h : Ops.Rel o p R) (hg : List.Forall₂ R g g') (hRd0 : R d0 d0') (j : ℕ) (ds : List A) (ds' : List B)
    (hds : List.Forall₂ R ds ds') :
    List.Forall₂ R
      (let s := ((List.range j).map fun i =>
        o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)).foldr o.add o.zero
      ds ++ [o.neg (o.mul s d0)])
      (let s := ((List.range j).map fun i =>
        p.mul (g'.getD (i + 1) p.zero) (ds'.getD (j - 1 - i) p.zero)).foldr p.add p.zero
      ds' ++ [p.neg (p.mul s d0')]) := by
  -- We need to show: List.Forall₂ R (ds ++ [x]) (ds' ++ [y])
  -- where x = o.neg (o.mul s ds d0) and y = p.neg (p.mul s' ds' d0')
  apply List.rel_append hds
  apply List.Forall₂.cons
  · -- Goal: R (o.neg (o.mul s ds d0)) (p.neg (p.mul s' ds' d0'))
    apply h.neg
    -- Goal: R (o.mul s ds d0) (p.mul s' ds' d0')
    apply h.mul
    · -- Goal: R s s'
      -- s and s' are foldr results
      -- Use List.rel_foldr with P = R
      apply List.rel_foldr (R := R) (P := R)
      · -- hfg : Relator.LiftFun R (Relator.LiftFun R R) o.add p.add
        intro a b ha c d hc
        exact h.add ha hc
      · -- hinit : R o.zero p.zero
        exact h.ofInt 0
      · -- h : List.Forall₂ R (mapped list) (mapped list)
        exact Ops_Rel_invSeries_aux1 h hg hds j
    · -- Goal: R d0 d0' (given)
      exact hRd0
  · -- Tail: List.Forall₂ R [] []
    exact List.Forall₂.nil

-- Main induction lemma for foldl
lemma Ops_Rel_invSeries_aux3 {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}
    {g : List A} {g' : List B} {d0 : A} {d0' : B}
    (h : Ops.Rel o p R) (hg : List.Forall₂ R g g') (hRd0 : R d0 d0') (js : List ℕ) (ds : List A) (ds' : List B)
    (hds : List.Forall₂ R ds ds') :
    List.Forall₂ R (js.foldl (fun ds j =>
      let s := ((List.range j).map fun i =>
        o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)).foldr o.add o.zero
      ds ++ [o.neg (o.mul s d0)]) ds)
      (js.foldl (fun ds' j =>
      let s := ((List.range j).map fun i =>
        p.mul (g'.getD (i + 1) p.zero) (ds'.getD (j - 1 - i) p.zero)).foldr p.add p.zero
      ds' ++ [p.neg (p.mul s d0')]) ds') := by
  induction js generalizing ds ds' with
  | nil => exact hds
  | cons j js ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      apply Ops_Rel_invSeries_aux2 h hg hRd0 j ds ds' hds
end Ops_Rel_invSeries_aux

-- Helper lemma: the step function of sqrtSeries preserves the relation
theorem Ops.Rel.invSeries (h : Ops.Rel o p R) (n : ℕ) {g : List A} {g' : List B}
    (hg : List.Forall₂ R g g') :
    OptRel (List.Forall₂ R) (o.invSeries n g) (p.invSeries n g') := by
  intro b hb
  -- Unfold the do block in hb
  unfold Ops.invSeries at hb
  simp at hb
  rw [Option.bind_eq_some_iff] at hb
  rcases hb with ⟨d0', hd0', hrest⟩
  -- hd0' : p.inv (g'.head?.getD p.zero) = some d0'
  -- hrest : some ((List.range' 1 n).foldl step [d0']) = some b
  -- Get b from hrest
  have hb_eq : ((List.range' 1 n).foldl (fun (ds' : List B) (j : ℕ) =>
    let s := ((List.range j).map fun i =>
      p.mul (g'.getD (i + 1) p.zero) (ds'.getD (j - 1 - i) p.zero)).foldr p.add p.zero
    ds' ++ [p.neg (p.mul s d0')]) [d0']) = b := by
    simpa using Option.some_inj.mp hrest
  -- Get the head relation from hg
  have hhead : R (g.headD o.zero) (g'.headD p.zero) := by
    cases hg with
    | nil =>
      have hzero : R o.zero p.zero := h.ofInt 0
      simpa [List.headD_eq_head?_getD] using hzero
    | cons hxy _ =>
      simpa using hxy
  -- Get d0 from h.inv
  -- hd0' uses head?.getD, but h.inv expects headD
  have hd0'_headD : p.inv (g'.headD p.zero) = some d0' := by
    simpa [List.headD_eq_head?_getD] using hd0'
  have hinv := h.inv hhead hd0'_headD
  rcases hinv with ⟨d0, hd0, hRd0⟩
  -- hd0 : o.inv (g.headD o.zero) = some d0
  -- Now compute o.invSeries n g
  have h_result_o : o.invSeries n g = some ((List.range' 1 n).foldl (fun (ds : List A) (j : ℕ) =>
    let s := ((List.range j).map fun i =>
      o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)).foldr o.add o.zero
    ds ++ [o.neg (o.mul s d0)]) [d0]) := by
    unfold Ops.invSeries
    -- After unfold, the goal has a do block with o.inv (g.headD o.zero)
    -- We can use hd0 directly after rewriting headD to head?.getD
    have hd0_head : o.inv (g.head?.getD o.zero) = some d0 := by
      simpa [List.headD_eq_head?_getD] using hd0
    simp [hd0_head]
  -- Use the Ops_Rel_invSeries_aux3 lemma to show the results are related
  have h_foldl : List.Forall₂ R ((List.range' 1 n).foldl (fun (ds : List A) (j : ℕ) =>
    let s := ((List.range j).map fun i =>
      o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)).foldr o.add o.zero
    ds ++ [o.neg (o.mul s d0)]) [d0])
    ((List.range' 1 n).foldl (fun (ds' : List B) (j : ℕ) =>
    let s := ((List.range j).map fun i =>
      p.mul (g'.getD (i + 1) p.zero) (ds'.getD (j - 1 - i) p.zero)).foldr p.add p.zero
    ds' ++ [p.neg (p.mul s d0')]) [d0']) := by
    have h_init : List.Forall₂ R [d0] [d0'] := by
      simpa using List.Forall₂.cons hRd0 List.Forall₂.nil
    exact Ops_Rel_invSeries_aux3 h hg hRd0 (List.range' 1 n) [d0] [d0'] h_init
  -- Combine everything
  refine ⟨((List.range' 1 n).foldl (fun (ds : List A) (j : ℕ) =>
    let s := ((List.range j).map fun i =>
      o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)).foldr o.add o.zero
    ds ++ [o.neg (o.mul s d0)]) [d0]), h_result_o, ?_⟩
  -- Need to show: List.Forall₂ R a b where a = ... and b = ...
  -- We have h_foldl : List.Forall₂ R a (foldl ... [d0'])
  -- And hb_eq : (foldl ... [d0']) = b
  -- So we rewrite b to the foldl expression
  rw [← hb_eq]
  exact h_foldl

theorem Ops_Rel_sqrtSeries_aux3 {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}
    (h : Ops.Rel o p R) {g : List A} {g' : List B}
    (hg : List.Forall₂ R g g') (i2 : A) (i2' : B) (hi2 : R i2 i2')
    (ps : List A) (ps' : List B) (hps : List.Forall₂ R ps ps') (j : ℕ) :
    List.Forall₂ R
      (let s := ((List.range (j - 1)).map fun i =>
        o.mul (ps.getD (i + 1) o.zero) (ps.getD (j - 1 - i) o.zero)).foldr o.add o.zero
      ps ++ [o.mul (o.sub (g.getD j o.zero) s) i2])
      (let s := ((List.range (j - 1)).map fun i =>
        p.mul (ps'.getD (i + 1) p.zero) (ps'.getD (j - 1 - i) p.zero)).foldr p.add p.zero
      ps' ++ [p.mul (p.sub (g'.getD j p.zero) s) i2']) := by
  -- First, show that the mapped lists are related
  have h_map : List.Forall₂ R
    ((List.range (j - 1)).map fun i =>
      o.mul (ps.getD (i + 1) o.zero) (ps.getD (j - 1 - i) o.zero))
    ((List.range (j - 1)).map fun i =>
      p.mul (ps'.getD (i + 1) p.zero) (ps'.getD (j - 1 - i) p.zero)) := by
    rw [List.forall₂_map_left_iff]
    induction List.range (j - 1) with
    | nil => exact List.Forall₂.nil
    | cons i is ih =>
      apply List.Forall₂.cons
      · apply h.mul
        · apply Ops_Rel_sqrtSeries_aux1 hps (i + 1) o.zero p.zero (h.ofInt 0)
        · apply Ops_Rel_sqrtSeries_aux1 hps (j - 1 - i) o.zero p.zero (h.ofInt 0)
      · exact ih
  -- Now show that the foldr sums are related
  have h_sum : R
    (((List.range (j - 1)).map fun i =>
      o.mul (ps.getD (i + 1) o.zero) (ps.getD (j - 1 - i) o.zero)).foldr o.add o.zero)
    (((List.range (j - 1)).map fun i =>
      p.mul (ps'.getD (i + 1) p.zero) (ps'.getD (j - 1 - i) p.zero)).foldr p.add p.zero) := by
    apply Ops_Rel_sqrtSeries_aux2 h_map o.add p.add
    · intro a b a' b' hR_aa' hR_bb'
      exact h.add hR_aa' hR_bb'
    · exact h.ofInt 0
  -- Now combine using rel_append
  apply List.rel_append hps
  -- Goal: List.Forall₂ R [o.mul ...] [p.mul ...]
  -- This is a singleton list, so we use Forall₂.cons with the single element
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  -- Now the goal is: R (o.mul (o.sub (g.getD j o.zero) s) i2) (p.mul (p.sub (g'.getD j p.zero) s') i2')
  apply h.mul
  · -- Need: R (o.sub (g.getD j o.zero) s) (p.sub (g'.getD j p.zero) s')
    apply h.sub
    · -- Need: R (g.getD j o.zero) (g'.getD j p.zero)
      apply Ops_Rel_sqrtSeries_aux1 hg j
      exact h.ofInt 0
    · -- Need: R s s'
      exact h_sum
  · -- Need: R i2 i2'
    exact hi2

-- Helper lemma: the foldl over range' 1 n preserves the relation
theorem Ops_Rel_sqrtSeries_aux4 {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}
    (h : Ops.Rel o p R) {g : List A} {g' : List B}
    (hg : List.Forall₂ R g g') (i2 : A) (i2' : B) (hi2 : R i2 i2')
    (p0 : A) (p0' : B) (hp : R p0 p0') (n : ℕ) :
    List.Forall₂ R
      ((List.range' 1 n).foldl (fun ps j =>
        let s := ((List.range (j - 1)).map fun i =>
          o.mul (ps.getD (i + 1) o.zero) (ps.getD (j - 1 - i) o.zero)).foldr o.add o.zero
        ps ++ [o.mul (o.sub (g.getD j o.zero) s) i2]) [p0])
      ((List.range' 1 n).foldl (fun ps' j =>
        let s := ((List.range (j - 1)).map fun i =>
          p.mul (ps'.getD (i + 1) p.zero) (ps'.getD (j - 1 - i) p.zero)).foldr p.add p.zero
        ps' ++ [p.mul (p.sub (g'.getD j p.zero) s) i2']) [p0']) := by
  -- Define the step function for convenience
  let f : List A → ℕ → List A := fun ps j =>
    let s := ((List.range (j - 1)).map fun i =>
      o.mul (ps.getD (i + 1) o.zero) (ps.getD (j - 1 - i) o.zero)).foldr o.add o.zero
    ps ++ [o.mul (o.sub (g.getD j o.zero) s) i2]
  let g : List B → ℕ → List B := fun ps' j =>
    let s := ((List.range (j - 1)).map fun i =>
      p.mul (ps'.getD (i + 1) p.zero) (ps'.getD (j - 1 - i) p.zero)).foldr p.add p.zero
    ps' ++ [p.mul (p.sub (g'.getD j p.zero) s) i2']
  have h_step : ∀ (ps : List A) (ps' : List B), List.Forall₂ R ps ps' → ∀ (j : ℕ),
    List.Forall₂ R (f ps j) (g ps' j) := by
    intro ps ps' hps j
    unfold f g
    apply Ops_Rel_sqrtSeries_aux3 h hg i2 i2' hi2 ps ps' hps j
  -- Now we use the fact that foldl can be expressed via foldr on the reversed list
  -- Or we can use the lemma we proved earlier (Ops_Rel_sqrtSeries_aux2) by converting foldl to foldr
  -- Actually, let's use a direct induction on the list using the Forall₂ relation
  -- We need to prove: Forall₂ R (foldl f [p0] (range' 1 n)) (foldl g [p0'] (range' 1 n))
  -- Let's use the lemma that foldl preserves Forall₂
  -- We'll prove this by induction on the list range' 1 n
  -- Now we need to prove: Forall₂ R (foldl f [p0] (range' 1 n)) (foldl g [p0'] (range' 1 n))
  -- We'll prove this by induction on n
  induction n with
  | zero =>
    simpa using List.Forall₂.cons hp List.Forall₂.nil
  | succ n ih =>
    have h_range : List.range' 1 n ++ [n + 1] = List.range' 1 (n + 1) := by
      simpa [add_comm] using List.range'_append (s := 1) (m := n) (n := 1) (step := 1)
    rw [← h_range]
    have h_left := List.foldl_append (f := f) (b := [p0]) (l := List.range' 1 n) (l' := [n + 1])
    have h_right := List.foldl_append (f := g) (b := [p0']) (l := List.range' 1 n) (l' := [n + 1])
    rw [h_left, h_right]
    apply h_step
    exact ih

-- Main proof

theorem Ops.Rel.sqrtSeries (h : Ops.Rel o p R) (n : ℕ) {g : List A} {g' : List B}
    (hg : List.Forall₂ R g g') {p0 : A} {p0' : B} (hp : R p0 p0') :
    OptRel (List.Forall₂ R) (o.sqrtSeries n g p0) (p.sqrtSeries n g' p0') := by
  intro b hb
  unfold FurioLombardo.Discharge.KvArith.Ops.sqrtSeries at hb
  simp at hb
  cases hp_inv : p.inv (p.add p0' p0') with
  | none => simp [hp_inv] at hb
  | some i2' =>
    simp [hp_inv] at hb
    have h_inv := h.inv (h.add hp hp) hp_inv
    rcases h_inv with ⟨i2, hi2, hi2_rel⟩
    -- Define the step functions
    set o_step : List A → ℕ → List A := fun ps j =>
      let s := ((List.range (j - 1)).map fun i =>
        o.mul (ps.getD (i + 1) o.zero) (ps.getD (j - 1 - i) o.zero)).foldr o.add o.zero
      ps ++ [o.mul (o.sub (g.getD j o.zero) s) i2]
    with ho_step
    set p_step : List B → ℕ → List B := fun ps' j =>
      let s := ((List.range (j - 1)).map fun i =>
        p.mul (ps'.getD (i + 1) p.zero) (ps'.getD (j - 1 - i) p.zero)).foldr p.add p.zero
      ps' ++ [p.mul (p.sub (g'.getD j p.zero) s) i2']
    with hp_step
    -- Show that o.sqrtSeries = some (foldl o_step [p0] (range' 1 n))
    have ho_sqrt : o.sqrtSeries n g p0 = some ((List.range' 1 n).foldl o_step [p0]) := by
      unfold FurioLombardo.Discharge.KvArith.Ops.sqrtSeries
      simp [hi2, ho_step]
    -- hb : ((List.range' 1 n).foldl p_step [p0']) = b
    -- So b = foldl p_step [p0'] (range' 1 n)
    have hb_eq : b = ((List.range' 1 n).foldl p_step [p0']) := by
      simpa [hp_step] using hb.symm
    -- Now we need to prove: ∃ a, o.sqrtSeries n g p0 = some a ∧ List.Forall₂ R a b
    -- Take a = foldl o_step [p0] (range' 1 n)
    refine ⟨((List.range' 1 n).foldl o_step [p0]), ho_sqrt, ?_⟩
    -- Need: List.Forall₂ R (foldl o_step [p0] (range' 1 n)) b
    -- Since b = foldl p_step [p0'] (range' 1 n), we need:
    -- List.Forall₂ R (foldl o_step [p0] (range' 1 n)) (foldl p_step [p0'] (range' 1 n))
    rw [hb_eq]
    -- Now use the helper lemma
    simpa [ho_step, hp_step] using Ops_Rel_sqrtSeries_aux4 h hg i2 i2' hi2_rel p0 p0' hp n

/-- Helper lemma: `hornerZ` preserves the relation. -/
theorem Ops_Rel_ddZ_aux {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}
    (h : Ops.Rel o p R) (cs : List ℤ) {x : A} {a : B} (hx : R x a) :
    R (o.hornerZ cs x) (p.hornerZ cs a) := by
  induction cs with
  | nil =>
      simp [Ops.hornerZ, Ops.zero]
      exact h.ofInt 0
  | cons c cs ih =>
      simp [Ops.hornerZ]
      apply h.add
      · exact h.ofInt c
      · apply h.mul hx ih

theorem Ops.Rel.ddZ (h : Ops.Rel o p R) (cs : List ℤ) {x y : A} {a b : B} (hx : R x a)
    (hy : R y b) : R (o.ddZ cs x y) (p.ddZ cs a b) := by
  induction cs with
  | nil =>
      simp [Ops.ddZ, Ops.zero]
      exact h.ofInt 0
  | cons c cs ih =>
      simp [Ops.ddZ]
      apply h.add
      · exact Ops_Rel_ddZ_aux h cs hx
      · apply h.mul hy ih

theorem Ops.Rel.ddZ2 (h : Ops.Rel o p R) (cs : List (List ℤ)) {x y z : A} {a b c : B}
    (hx : R x a) (hy : R y b) (hz : R z c) : R (o.ddZ2 cs x y z) (p.ddZ2 cs a b c) := by
  induction cs generalizing x y z a b c with
  | nil =>
      simp [Ops.ddZ2, Ops.zero, h.ofInt 0]
  | cons d ds ih =>
      simp [Ops.ddZ2]
      apply h.add
      · apply h.ddZ d hy hz
      · apply h.mul hx (ih hx hy hz)

/-- Truncated series follow coefficientwise. -/
theorem Ops.Rel.polyOps (h : Ops.Rel o p R) (n : ℕ) :
    Ops.Rel (polyOps o n) (polyOps p n) (List.Forall₂ R) := by
  refine ⟨?add, ?sub, ?neg, ?mul, ?inv, ?ofInt⟩
  · -- add
    intro x y a b hx hy
    exact h.zipAdd hx hy
  · -- sub
    intro x y a b hx hy
    exact h.zipSub hx hy
  · -- neg
    intro x a hx
    induction hx with
    | nil => exact List.Forall₂.nil
    | cons hr hx' ih =>
      exact List.Forall₂.cons (h.neg hr) ih
  · -- mul
    intro x y a b hx hy
    exact h.pmul n hx hy
  · -- inv
    intro x a b hx h_eq
    exact h.invSeries n hx b h_eq
  · -- ofInt
    intro z
    exact List.Forall₂.cons (h.ofInt z) List.Forall₂.nil

lemma Ops_Rel_rootSeries_fold {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}
    (h : Ops.Rel o p R) (n : ℕ) (F : List (List ℤ)) {t0 t1 : A} {t0' t1' : B}
    (ht0 : R t0 t0') (ht1 : R t1 t1') (c : A) (c' : B) (hc : R c c')
    (ys : List A) (ys' : List B) (hys : List.Forall₂ R ys ys') :
    List.Forall₂ R
      ((List.range' 1 n).foldl (fun (P : List A) (k : Nat) =>
        let r := (polyOps o n).hornerZ2 F [t0, t1] P
        P ++ [o.neg (o.mul (r.getD k o.zero) c)]
      ) ys)
      ((List.range' 1 n).foldl (fun (P' : List B) (k : Nat) =>
        let r' := (polyOps p n).hornerZ2 F [t0', t1'] P'
        P' ++ [p.neg (p.mul (r'.getD k p.zero) c')]
      ) ys') := by
  induction List.range' 1 n generalizing ys ys' with
  | nil =>
      simp [List.foldl_nil]
      exact hys
  | cons k ks ih =>
      simp [List.foldl_cons]
      apply ih
      have h_pair : List.Forall₂ R [t0, t1] [t0', t1'] := by
        rw [List.forall₂_cons]
        exact ⟨ht0, by rw [List.forall₂_cons]; exact ⟨ht1, List.Forall₂.nil⟩⟩
      have h_horner := (h.polyOps n).hornerZ2 F h_pair hys
      rw [List.forall₂_iff_get] at h_horner
      rcases h_horner with ⟨hlen, hget⟩
      by_cases hk : k < ((polyOps o n).hornerZ2 F [t0, t1] ys).length
      · have hk' : k < ((polyOps p n).hornerZ2 F [t0', t1'] ys').length := by
          rw [← hlen]
          exact hk
        have hrel := hget k hk hk'
        have h_elem_rel : R (o.neg (o.mul (((polyOps o n).hornerZ2 F [t0, t1] ys).get ⟨k, hk⟩) c))
                              (p.neg (p.mul (((polyOps p n).hornerZ2 F [t0', t1'] ys').get ⟨k, hk'⟩) c')) :=
          h.neg (h.mul hrel hc)
        have h_cons : List.Forall₂ R (ys ++ [o.neg (o.mul (((polyOps o n).hornerZ2 F [t0, t1] ys).get ⟨k, hk⟩) c)])
                                  (ys' ++ [p.neg (p.mul (((polyOps p n).hornerZ2 F [t0', t1'] ys').get ⟨k, hk'⟩) c')]) :=
          List.rel_append hys (List.Forall₂.cons h_elem_rel List.Forall₂.nil)
        -- Use List.getD_eq_get which works with .getD (which is [k]?.getD)
        have h_getD_r : ((polyOps o n).hornerZ2 F [t0, t1] ys)[k]?.getD o.zero = ((polyOps o n).hornerZ2 F [t0, t1] ys).get ⟨k, hk⟩ := by
          have := List.getD_eq_get ((polyOps o n).hornerZ2 F [t0, t1] ys) o.zero ⟨k, hk⟩
          simpa using this
        have h_getD_r' : ((polyOps p n).hornerZ2 F [t0', t1'] ys')[k]?.getD p.zero = ((polyOps p n).hornerZ2 F [t0', t1'] ys').get ⟨k, hk'⟩ := by
          have := List.getD_eq_get ((polyOps p n).hornerZ2 F [t0', t1'] ys') p.zero ⟨k, hk'⟩
          simpa using this
        rw [h_getD_r, h_getD_r']
        exact h_cons
      · -- k is not in bounds
        have hlen_le : ((polyOps o n).hornerZ2 F [t0, t1] ys).length ≤ k := by omega
        have hlen_le' : ((polyOps p n).hornerZ2 F [t0', t1'] ys').length ≤ k :=
          hlen ▸ hlen_le
        have h_elem_rel : R (o.neg (o.mul o.zero c)) (p.neg (p.mul p.zero c')) :=
          h.neg (h.mul (h.ofInt 0) hc)
        have h_cons : List.Forall₂ R (ys ++ [o.neg (o.mul o.zero c)])
                                  (ys' ++ [p.neg (p.mul p.zero c')]) :=
          List.rel_append hys (List.Forall₂.cons h_elem_rel List.Forall₂.nil)
        have h_getD_r : ((polyOps o n).hornerZ2 F [t0, t1] ys)[k]?.getD o.zero = o.zero := by
          have := List.getD_eq_default ((polyOps o n).hornerZ2 F [t0, t1] ys) o.zero hlen_le
          simpa using this
        have h_getD_r' : ((polyOps p n).hornerZ2 F [t0', t1'] ys')[k]?.getD p.zero = p.zero := by
          have := List.getD_eq_default ((polyOps p n).hornerZ2 F [t0', t1'] ys') p.zero hlen_le'
          simpa using this
        rw [h_getD_r, h_getD_r']
        exact h_cons

theorem Ops.Rel.rootSeries (h : Ops.Rel o p R) (n : ℕ) (F : List (List ℤ)) {t0 t1 y0 : A}
    {t0' t1' y0' : B} (ht0 : R t0 t0') (ht1 : R t1 t1') (hy0 : R y0 y0') :
    OptRel (List.Forall₂ R) (o.rootSeries n F t0 t1 y0) (p.rootSeries n F t0' t1' y0') := by
  intro b hb
  simp [Ops.rootSeries] at hb
  rcases Option.bind_eq_some_iff.mp hb with ⟨c', hc'_inv, hc'_fold⟩
  simp at hc'_fold
  have h_init : R (o.hornerZ2 (derivY F) t0 y0) (p.hornerZ2 (derivY F) t0' y0') :=
    h.hornerZ2 (derivY F) ht0 hy0
  rcases h.inv h_init hc'_inv with ⟨c, hc_inv, hc_rel⟩
  simp [Ops.rootSeries, hc_inv]
  have hfold := FurioLombardo.Discharge.KvArith.Ops_Rel_rootSeries_fold h n F ht0 ht1 c c' hc_rel [y0] [y0'] (by
    simpa using hy0)
  rw [← hc'_fold]
  exact hfold

theorem Ops.Rel.prod {A' B' : Type*} {o' : Ops A'} {p' : Ops B'} {R' : A' → B' → Prop}
    (h : Ops.Rel o p R) (h' : Ops.Rel o' p' R') :
    Ops.Rel (o.prod o') (p.prod p') (fun x y => R x.1 y.1 ∧ R' x.2 y.2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y a b ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨h.add hx hy, h'.add hx' hy'⟩
  · intro x y a b ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨h.sub hx hy, h'.sub hx' hy'⟩
  · intro x a ⟨hx, hx'⟩
    exact ⟨h.neg hx, h'.neg hx'⟩
  · intro x y a b ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨h.mul hx hy, h'.mul hx' hy'⟩
  · intro x a b hrel hbinv
    rcases hrel with ⟨hr, hr'⟩
    simp [Ops.prod] at hbinv
    cases h1 : p.inv a.1
    · simp [h1] at hbinv
    · cases h2 : p'.inv a.2
      · simp [h2] at hbinv
      · simp [h1, h2] at hbinv
        rcases hbinv with ⟨rfl, rfl⟩
        rcases h.inv hr h1 with ⟨y1, hy1inv, hy1rel⟩
        rcases h'.inv hr' h2 with ⟨y2, hy2inv, hy2rel⟩
        refine ⟨(y1, y2), ?_, hy1rel, hy2rel⟩
        simp [Ops.prod, hy1inv, hy2inv]
  · intro z
    exact ⟨h.ofInt z, h'.ofInt z⟩

/-- The second component of a pair carrier follows its own carrier. -/
theorem rel_prod_snd (o : Ops A) (p : Ops B) : Ops.Rel p (o.prod p) (fun b ab => ab.2 = b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y a b hx hy
    simp [Ops.prod, hx, hy]
  · intro x y a b hx hy
    simp [Ops.prod, hx, hy]
  · intro x a hx
    simp [Ops.prod, hx]
  · intro x y a b hx hy
    simp [Ops.prod, hx, hy]
  · intro x a b hx h_inv
    revert h_inv
    cases h1 : o.inv a.1 with
    | none => intro h_inv; simp [Ops.prod, h1] at h_inv
    | some v1 =>
      cases h2 : p.inv a.2 with
      | none => intro h_inv; simp [Ops.prod, h1, h2] at h_inv
      | some v2 =>
        intro h_inv
        simp [Ops.prod, h1, h2] at h_inv
        cases h_inv
        refine ⟨v2, ?_, ?_⟩
        · rw [← hx]; exact h2
        · rfl
  · intro z
    simp [Ops.prod]

/-- The first component of a pair carrier follows its own carrier. -/
theorem rel_prod_fst (o : Ops A) (p : Ops B) : Ops.Rel o (o.prod p) (fun a ab => ab.1 = a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y a b hx hy
    simp [Ops.prod, hx, hy]
  · intro x y a b hx hy
    simp [Ops.prod, hx, hy]
  · intro x a hx
    simp [Ops.prod, hx]
  · intro x y a b hx hy
    simp [Ops.prod, hx, hy]
  · intro x a b hx h_inv
    revert h_inv
    cases h1 : o.inv a.1 with
    | none => intro h_inv; simp [Ops.prod, h1] at h_inv
    | some v1 =>
      cases h2 : p.inv a.2 with
      | none => intro h_inv; simp [Ops.prod, h1, h2] at h_inv
      | some v2 =>
        intro h_inv
        simp [Ops.prod, h1, h2] at h_inv
        cases h_inv
        refine ⟨v1, ?_, ?_⟩
        · rw [← hx]; exact h1
        · rfl
  · intro z
    simp [Ops.prod]

end RelLemmas

theorem Ops_invSeries_take_aux {A : Type*} (o : Ops A) (g : List A) (n i j : ℕ)
    (hij : i < j) (hj : j ≤ n) : (g.take (n + 1)).getD (i + 1) o.zero = g.getD (i + 1) o.zero := by
  have hi : i + 1 < n + 1 := by omega
  simp [List.getD, hi]

/-- `invSeries` reads the coefficients of degree `≤ n` only. -/
theorem Ops.invSeries_take {A : Type*} (o : Ops A) (n : ℕ) (g : List A) :
    o.invSeries n (g.take (n + 1)) = o.invSeries n g := by
  unfold Ops.invSeries
  simp
  have hhead : (g.take (n + 1)).head?.getD o.zero = g.head?.getD o.zero := by
    cases g
    · simp
    · rename_i a as
      simp
  rw [hhead]
  cases h : o.inv (g.head?.getD o.zero) with
  | none =>
      simp
  | some d0 =>
      simp
      set step1 := (fun (ds : List A) (j : ℕ) =>
        ds ++ [o.neg (o.mul
          (List.foldr o.add o.zero
            (List.map (fun i => o.mul ((g.take (n + 1)).getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero))
              (List.range j)))
          d0)]) with hstep1
      set step2 := (fun (ds : List A) (j : ℕ) =>
        ds ++ [o.neg (o.mul
          (List.foldr o.add o.zero
            (List.map (fun i => o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero))
              (List.range j)))
          d0)]) with hstep2
      have hstep_eq : ∀ (ds : List A) (j : ℕ), j ∈ List.range' 1 n → step1 ds j = step2 ds j := by
        intro ds j hj
        rcases List.mem_range'.mp hj with ⟨h1, h2⟩
        have hj_le_n : j ≤ n := by omega
        unfold step1 step2
        simp
        have hmap : (List.map (fun i => o.mul ((g.take (n + 1)).getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)) (List.range j)) =
                    (List.map (fun i => o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)) (List.range j)) := by
          apply List.ext_get
          · simp
          · intro i hi1 hi2
            have hi_j : i < j := by
              have : (List.map (fun i => o.mul ((g.take (n + 1)).getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)) (List.range j)).length = j := by
                simp
              rw [this] at hi1
              exact hi1
            have h_eq : (g.take (n + 1)).getD (i + 1) o.zero = g.getD (i + 1) o.zero :=
              Ops_invSeries_take_aux o g n i j hi_j hj_le_n
            have h1 : (List.map (fun i => o.mul ((g.take (n + 1)).getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)) (List.range j)).get ⟨i, hi1⟩ =
                     o.mul ((g.take (n + 1)).getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero) := by
              simp
            have h2 : (List.map (fun i => o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)) (List.range j)).get ⟨i, hi2⟩ =
                     o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero) := by
              simp
            rw [h1, h2]
            rw [h_eq]
        simpa [List.getD] using congrArg (fun x => o.neg (o.mul (List.foldr o.add o.zero x) d0)) hmap
      apply List.foldl_ext step1 step2 [d0]
      exact hstep_eq

/-- `sqrtSeries` reads the coefficients of degree `≤ n` only. -/
theorem Ops.sqrtSeries_take {A : Type*} (o : Ops A) (n : ℕ) (g : List A) (p0 : A) :
    o.sqrtSeries n (g.take (n + 1)) p0 = o.sqrtSeries n g p0 := by
  simp [Ops.sqrtSeries]
  cases h : o.inv (o.add p0 p0) with
  | none => rfl
  | some i2 =>
    simp
    apply List.foldl_ext
    intro ps j hj
    rcases List.mem_range'.mp hj with ⟨i, hi, rfl⟩
    have hj_bound : 1 + i < n + 1 := by
      omega
    have h_take_get : (List.take (n + 1) g)[1 + 1 * i]?.getD o.zero = g[1 + 1 * i]?.getD o.zero := by
      rw [List.getElem?_take]
      simp [hj_bound]
    rw [h_take_get]

/-! ## Exact values over a field -/

section Exact

variable {K : Type*} [Field K]

theorem fieldOps_horner_nil (x : K) : (fieldOps K).horner [] x = 0 := by
  simp [Ops.horner, Ops.zero, fieldOps]

theorem fieldOps_horner_cons (c : K) (cs : List K) (x : K) :
    (fieldOps K).horner (c :: cs) x = c + x * (fieldOps K).horner cs x := by
  simp [Ops.horner, fieldOps]

theorem mapIdx_monomial_succ (cs : List K) :
    (cs.mapIdx fun i c => Polynomial.monomial (i + 1) c) =
      (cs.mapIdx fun i c => Polynomial.monomial i c).map (Polynomial.X * ·) := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [Polynomial.X_mul_monomial]

theorem polyOf_nil : polyOf ([] : List K) = 0 := by simp [polyOf]

open Polynomial in
theorem polyOf_cons (c : K) (cs : List K) : polyOf (c :: cs) = C c + X * polyOf cs := by
  rw [polyOf, polyOf, List.mapIdx_cons, List.sum_cons, monomial_zero_left, mapIdx_monomial_succ,
    List.sum_map_mul_left, List.map_id']

open Polynomial in
theorem polyOf_map_mul (a : K) (p : List K) : polyOf (p.map (a * ·)) = C a * polyOf p := by
  induction p with
  | nil => simp [polyOf_nil]
  | cons c p ih => rw [List.map_cons, polyOf_cons, polyOf_cons, ih, C_mul]; ring

open Polynomial in
theorem fieldOps_horner_eq_polyOf (cs : List K) (x : K) :
    (fieldOps K).horner cs x = (polyOf cs).eval x := by
  induction cs with
  | nil => simp [polyOf_nil, Ops.horner, Ops.zero, fieldOps]
  | cons c cs ih =>
    rw [polyOf_cons, eval_add, eval_C, eval_mul, eval_X, ← ih]
    simp [Ops.horner, fieldOps]

theorem polyOf_map_neg (p : List K) : polyOf (p.map Neg.neg) = -polyOf p := by
  induction p with
  | nil => simp [polyOf_nil]
  | cons c p ih => rw [List.map_cons, polyOf_cons, polyOf_cons, ih, Polynomial.C_neg]; ring

theorem polyOf_zipAdd (p q : List K) : polyOf ((fieldOps K).zipAdd p q) = polyOf p + polyOf q := by
  induction p generalizing q with
  | nil => simp [Ops.zipAdd, polyOf_nil]
  | cons a p ih =>
    cases q with
    | nil => simp [Ops.zipAdd, polyOf_nil]
    | cons b q =>
      rw [Ops.zipAdd, polyOf_cons, polyOf_cons, polyOf_cons, ih]
      simp only [fieldOps, Polynomial.C_add]
      ring

theorem polyOf_zipSub (p q : List K) : polyOf ((fieldOps K).zipSub p q) = polyOf p - polyOf q := by
  induction p generalizing q with
  | nil =>
    rw [Ops.zipSub, polyOf_nil, zero_sub]
    exact polyOf_map_neg q
  | cons a p ih =>
    cases q with
    | nil => simp [Ops.zipSub, polyOf_nil]
    | cons b q =>
      rw [Ops.zipSub, polyOf_cons, polyOf_cons, polyOf_cons, ih]
      simp only [fieldOps, Polynomial.C_sub]
      ring

theorem polyOf_conv (p q : List K) : polyOf ((fieldOps K).conv p q) = polyOf p * polyOf q := by
  induction p with
  | nil => simp [Ops.conv, polyOf_nil]
  | cons a p ih =>
    rw [Ops.conv, polyOf_zipAdd, polyOf_cons, polyOf_cons, ih]
    have : (fieldOps K).mul a = (a * ·) := rfl
    rw [this, polyOf_map_mul]
    simp only [Ops.zero, fieldOps, Int.cast_zero, Polynomial.C_0]
    ring

open Polynomial in
theorem polyOf_split (p : List K) (j : ℕ) : polyOf p = polyOf (p.take j) + X ^ j * polyOf (p.drop j) := by
  induction p generalizing j with
  | nil => simp [polyOf_nil]
  | cons c p ih =>
    cases j with
    | zero => simp [polyOf_nil]
    | succ j =>
      rw [List.take_succ_cons, List.drop_succ_cons, polyOf_cons, polyOf_cons, ih j]
      ring

/-- The Horner value is the evaluation of the polynomial of the list. -/
theorem fieldOps_horner_eq_eval (cs : List K) (x : K) :
    (fieldOps K).horner cs x = ((cs.mapIdx fun i c => Polynomial.monomial i c).sum).eval x :=
  fieldOps_horner_eq_polyOf cs x

theorem fieldOps_hornerZ (cs : List ℤ) (x : K) :
    (fieldOps K).hornerZ cs x = (fieldOps K).horner (cs.map (fun z : ℤ => (z : K))) x := by
  simp [Ops.hornerZ, Ops.horner, fieldOps, List.foldr_map]

theorem fieldOps_horner_zipAdd (p q : List K) (x : K) :
    (fieldOps K).horner ((fieldOps K).zipAdd p q) x =
      (fieldOps K).horner p x + (fieldOps K).horner q x := by
  rw [fieldOps_horner_eq_polyOf, fieldOps_horner_eq_polyOf, fieldOps_horner_eq_polyOf, polyOf_zipAdd,
    Polynomial.eval_add]

theorem fieldOps_horner_zipSub (p q : List K) (x : K) :
    (fieldOps K).horner ((fieldOps K).zipSub p q) x =
      (fieldOps K).horner p x - (fieldOps K).horner q x := by
  rw [fieldOps_horner_eq_polyOf, fieldOps_horner_eq_polyOf, fieldOps_horner_eq_polyOf, polyOf_zipSub,
    Polynomial.eval_sub]

theorem fieldOps_horner_conv (p q : List K) (x : K) :
    (fieldOps K).horner ((fieldOps K).conv p q) x =
      (fieldOps K).horner p x * (fieldOps K).horner q x := by
  rw [fieldOps_horner_eq_polyOf, fieldOps_horner_eq_polyOf, fieldOps_horner_eq_polyOf, polyOf_conv,
    Polynomial.eval_mul]

/-- Splitting a Horner value after `j` coefficients. -/
theorem fieldOps_horner_split (cs : List K) (j : ℕ) (x : K) :
    (fieldOps K).horner cs x =
      (fieldOps K).horner (cs.take j) x + x ^ j * (fieldOps K).horner (cs.drop j) x := by
  rw [fieldOps_horner_eq_polyOf, fieldOps_horner_eq_polyOf, fieldOps_horner_eq_polyOf,
    polyOf_split cs j, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

open Polynomial in
theorem coeff_polyOf (cs : List K) (m : ℕ) : (polyOf cs).coeff m = cs.getD m 0 := by
  induction cs generalizing m with
  | nil => simp [polyOf_nil]
  | cons c cs ih =>
    rw [polyOf_cons]
    cases m with
    | zero => simp
    | succ m => simp [coeff_X_mul, ih m]

open Polynomial in
theorem degree_polyOf_lt (cs : List K) : (polyOf cs).degree < cs.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_polyOf, List.getD_eq_default _ _ (by exact_mod_cast hm)]

open Polynomial in
theorem X_pow_dvd_polyOf_sub_take (p : List K) (j : ℕ) : X ^ j ∣ polyOf p - polyOf (p.take j) :=
  ⟨polyOf (p.drop j), by rw [polyOf_split p j]; ring⟩

open Polynomial in
theorem X_pow_dvd_polyOf_pmul (n : ℕ) (p q : List K) :
    X ^ (n + 1) ∣ polyOf ((fieldOps K).pmul n p q) - polyOf p * polyOf q := by
  refine ⟨-polyOf (((fieldOps K).conv p q).drop (n + 1)), ?_⟩
  rw [Ops.pmul, ← polyOf_conv, polyOf_split ((fieldOps K).conv p q) (n + 1)]
  ring

theorem fieldOps_hornerZ2_eq_ringOps (F : List (List ℤ)) (x y : K) :
    (fieldOps K).hornerZ2 F x y = (ringOps K).hornerZ2 F x y := by
  simp [Ops.hornerZ2, Ops.hornerZ, Ops.zero, fieldOps, ringOps]

theorem fieldOps_ddZ2_eq_ringOps_aux1 (cs : List ℤ) (a : K) :
    (fieldOps K).hornerZ cs a = (ringOps K).hornerZ cs a := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show (fieldOps K).add ((fieldOps K).ofInt c) ((fieldOps K).mul a ((fieldOps K).hornerZ cs a)) =
           (ringOps K).add ((ringOps K).ofInt c) ((ringOps K).mul a ((ringOps K).hornerZ cs a))
      rw [ih]
      rfl

theorem fieldOps_ddZ2_eq_ringOps_aux2 (cs : List ℤ) (a b : K) :
    (fieldOps K).ddZ cs a b = (ringOps K).ddZ cs a b := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show (fieldOps K).add ((fieldOps K).hornerZ cs a) ((fieldOps K).mul b ((fieldOps K).ddZ cs a b)) =
           (ringOps K).add ((ringOps K).hornerZ cs a) ((ringOps K).mul b ((ringOps K).ddZ cs a b))
      rw [fieldOps_ddZ2_eq_ringOps_aux1 cs a, ih]
      rfl

theorem fieldOps_ddZ2_eq_ringOps (F : List (List ℤ)) (x a b : K) :
    (fieldOps K).ddZ2 F x a b = (ringOps K).ddZ2 F x a b := by
  induction F with
  | nil => rfl
  | cons c cs ih =>
      show (fieldOps K).add ((fieldOps K).ddZ c a b) ((fieldOps K).mul x ((fieldOps K).ddZ2 cs x a b)) =
           (ringOps K).add ((ringOps K).ddZ c a b) ((ringOps K).mul x ((ringOps K).ddZ2 cs x a b))
      rw [fieldOps_ddZ2_eq_ringOps_aux2 c a b, ih]
      rfl

/-- Evaluation of `hornerZ2` under a ring map. -/
theorem map_hornerZ2 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (F : List (List ℤ))
    (x y : R) : φ ((ringOps R).hornerZ2 F x y) = (ringOps S).hornerZ2 F (φ x) (φ y) := by
  have h_hornerZ : ∀ (c : List ℤ) (y : R), φ ((ringOps R).hornerZ c y) = (ringOps S).hornerZ c (φ y) := by
    intro c y
    induction' c with z cs ih
    · simp [Ops.hornerZ, Ops.zero, ringOps]
    · have h := congrArg (fun t => (z : S) + φ y * t) ih
      simpa [Ops.hornerZ, List.foldr, ringOps, map_add, map_mul, map_intCast] using h
  induction' F with c cs ih
  · simp [Ops.hornerZ2, Ops.zero, ringOps]
  · simpa [Ops.hornerZ2, List.foldr, ringOps, map_add, map_mul] using
      (calc
        φ ((ringOps R).hornerZ c y) + φ x * φ ((ringOps R).hornerZ2 cs x y)
            = (ringOps S).hornerZ c (φ y) + φ x * φ ((ringOps R).hornerZ2 cs x y) := by rw [h_hornerZ c y]
        _ = (ringOps S).hornerZ c (φ y) + φ x * (ringOps S).hornerZ2 cs (φ x) (φ y) := by rw [ih]
      )

lemma hornerZ_sub_hornerZ {R : Type*} [CommRing R] (cs : List ℤ) (a b : R) :
    (ringOps R).hornerZ cs a - (ringOps R).hornerZ cs b = (a - b) * (ringOps R).ddZ cs a b := by
  induction' cs with c cs ih
  · simp [Ops.hornerZ, Ops.ddZ, Ops.zero, ringOps]
  · have h_horner_cons_a : (ringOps R).hornerZ (c :: cs) a = (c : R) + a * (ringOps R).hornerZ cs a := by
      simp [Ops.hornerZ, Ops.zero, ringOps]
    have h_horner_cons_b : (ringOps R).hornerZ (c :: cs) b = (c : R) + b * (ringOps R).hornerZ cs b := by
      simp [Ops.hornerZ, Ops.zero, ringOps]
    have h_ddZ_cons : (ringOps R).ddZ (c :: cs) a b = (ringOps R).hornerZ cs a + b * (ringOps R).ddZ cs a b := by
      simp [Ops.ddZ, ringOps]
    rw [h_horner_cons_a, h_horner_cons_b, h_ddZ_cons]
    calc
      ↑c + a * (ringOps R).hornerZ cs a - (↑c + b * (ringOps R).hornerZ cs b)
          = a * (ringOps R).hornerZ cs a - b * (ringOps R).hornerZ cs b := by ring
      _ = (a - b) * (ringOps R).hornerZ cs a + b * ((ringOps R).hornerZ cs a - (ringOps R).hornerZ cs b) := by ring
      _ = (a - b) * (ringOps R).hornerZ cs a + b * ((a - b) * (ringOps R).ddZ cs a b) := by rw [ih]
      _ = (a - b) * ((ringOps R).hornerZ cs a + b * (ringOps R).ddZ cs a b) := by ring

/-- The divided difference: `F(x, a) - F(x, b) = (a - b) dd(x, a, b)`. -/
theorem hornerZ2_sub_hornerZ2 {R : Type*} [CommRing R] (F : List (List ℤ)) (x a b : R) :
    (ringOps R).hornerZ2 F x a - (ringOps R).hornerZ2 F x b = (a - b) * (ringOps R).ddZ2 F x a b := by
  induction' F with c F ih
  · simp [Ops.hornerZ2, Ops.ddZ2, Ops.zero, ringOps]
  · have h_hornerZ2_cons_a : (ringOps R).hornerZ2 (c :: F) x a = (ringOps R).hornerZ c a + x * (ringOps R).hornerZ2 F x a := by
      simp [Ops.hornerZ2, Ops.zero, ringOps]
    have h_hornerZ2_cons_b : (ringOps R).hornerZ2 (c :: F) x b = (ringOps R).hornerZ c b + x * (ringOps R).hornerZ2 F x b := by
      simp [Ops.hornerZ2, Ops.zero, ringOps]
    have h_ddZ2_cons : (ringOps R).ddZ2 (c :: F) x a b = (ringOps R).ddZ c a b + x * (ringOps R).ddZ2 F x a b := by
      simp [Ops.ddZ2, Ops.zero, ringOps]
    rw [h_hornerZ2_cons_a, h_hornerZ2_cons_b, h_ddZ2_cons]
    calc
      (ringOps R).hornerZ c a + x * (ringOps R).hornerZ2 F x a - ((ringOps R).hornerZ c b + x * (ringOps R).hornerZ2 F x b)
          = ((ringOps R).hornerZ c a - (ringOps R).hornerZ c b) + x * ((ringOps R).hornerZ2 F x a - (ringOps R).hornerZ2 F x b) := by ring
      _ = ((a - b) * (ringOps R).ddZ c a b) + x * ((a - b) * (ringOps R).ddZ2 F x a b) := by rw [hornerZ_sub_hornerZ c a b, ih]
      _ = (a - b) * ((ringOps R).ddZ c a b + x * (ringOps R).ddZ2 F x a b) := by ring

theorem X_pow_dvd_polyOf_hornerZ_aux (n : ℕ) (c : List ℤ) (Q : List K) :
    Polynomial.X ^ (n + 1) ∣ polyOf ((polyOps (fieldOps K) n).hornerZ c Q) -
      (ringOps (Polynomial K)).hornerZ c (polyOf Q) := by
  induction' c with z cs ih
  · -- base case: c = []
    have hleft : (polyOps (fieldOps K) n).hornerZ [] Q = (polyOps (fieldOps K) n).zero := rfl
    have hright : (ringOps (Polynomial K)).hornerZ [] (polyOf Q) = (ringOps (Polynomial K)).zero := rfl
    have hleft_zero : (polyOps (fieldOps K) n).zero = [(0 : K)] := by simp [polyOps, Ops.zero, fieldOps]
    have hright_zero : (ringOps (Polynomial K)).zero = (0 : Polynomial K) := by simp [ringOps, Ops.zero]
    have hpolyOf_zero : polyOf [(0 : K)] = (0 : Polynomial K) := by simp [polyOf]
    rw [hleft, hright, hleft_zero, hright_zero, hpolyOf_zero]
    simp
  · -- inductive case: z :: cs
    have hleft : (polyOps (fieldOps K) n).hornerZ (z :: cs) Q =
      (polyOps (fieldOps K) n).add ((polyOps (fieldOps K) n).ofInt z)
        ((polyOps (fieldOps K) n).mul Q ((polyOps (fieldOps K) n).hornerZ cs Q)) := rfl
    have hright : (ringOps (Polynomial K)).hornerZ (z :: cs) (polyOf Q) =
      (ringOps (Polynomial K)).add ((ringOps (Polynomial K)).ofInt z)
        ((ringOps (Polynomial K)).mul (polyOf Q) ((ringOps (Polynomial K)).hornerZ cs (polyOf Q))) := rfl
    have hadd_poly : (polyOps (fieldOps K) n).add = (fieldOps K).zipAdd := rfl
    have hmul_poly : (polyOps (fieldOps K) n).mul = (fieldOps K).pmul n := rfl
    have hofInt_poly (z : ℤ) : (polyOps (fieldOps K) n).ofInt z = [(z : K)] := rfl
    have hadd_ring : (ringOps (Polynomial K)).add = (· + ·) := rfl
    have hmul_ring : (ringOps (Polynomial K)).mul = (· * ·) := rfl
    have hofInt_ring (z : ℤ) : (ringOps (Polynomial K)).ofInt z = (z : Polynomial K) := rfl
    have hzero_ring : (ringOps (Polynomial K)).zero = (0 : Polynomial K) := by simp [ringOps, Ops.zero]
    rw [hleft, hright, hadd_poly, hmul_poly, hofInt_poly, hadd_ring, hmul_ring, hofInt_ring]
    rw [polyOf_zipAdd]
    have hz : polyOf [(z : K)] = (z : Polynomial K) := by simp [polyOf]
    rw [hz]
    have h_sub : ((z : Polynomial K) + polyOf ((fieldOps K).pmul n Q ((polyOps (fieldOps K) n).hornerZ cs Q))) -
      ((z : Polynomial K) + polyOf Q * (ringOps (Polynomial K)).hornerZ cs (polyOf Q)) =
      polyOf ((fieldOps K).pmul n Q ((polyOps (fieldOps K) n).hornerZ cs Q)) -
      polyOf Q * (ringOps (Polynomial K)).hornerZ cs (polyOf Q) := by
      ring
    rw [h_sub]
    have h_eq : polyOf ((fieldOps K).pmul n Q ((polyOps (fieldOps K) n).hornerZ cs Q)) -
        polyOf Q * (ringOps (Polynomial K)).hornerZ cs (polyOf Q) =
        (polyOf ((fieldOps K).pmul n Q ((polyOps (fieldOps K) n).hornerZ cs Q)) -
          polyOf Q * polyOf ((polyOps (fieldOps K) n).hornerZ cs Q)) +
        (polyOf Q * (polyOf ((polyOps (fieldOps K) n).hornerZ cs Q) -
          (ringOps (Polynomial K)).hornerZ cs (polyOf Q))) := by
      ring
    rw [h_eq]
    apply dvd_add
    · exact X_pow_dvd_polyOf_pmul n Q ((polyOps (fieldOps K) n).hornerZ cs Q)
    · rw [mul_comm]; exact dvd_mul_of_dvd_left ih (polyOf Q)

open Polynomial in
/-- Truncated series evaluate `hornerZ2` modulo `X^(n+1)`. -/
theorem X_pow_dvd_polyOf_hornerZ2 (n : ℕ) (F : List (List ℤ)) (P Q : List K) :
    X ^ (n + 1) ∣ polyOf ((polyOps (fieldOps K) n).hornerZ2 F P Q) -
      (ringOps K[X]).hornerZ2 F (polyOf P) (polyOf Q) := by
  induction' F with c cs ih
  · -- base case: F = []
    have hleft : (polyOps (fieldOps K) n).hornerZ2 [] P Q = (polyOps (fieldOps K) n).zero := rfl
    have hright : (ringOps (Polynomial K)).hornerZ2 [] (polyOf P) (polyOf Q) = (ringOps (Polynomial K)).zero := rfl
    have hleft_zero : (polyOps (fieldOps K) n).zero = [(0 : K)] := by simp [polyOps, Ops.zero, fieldOps]
    have hright_zero : (ringOps (Polynomial K)).zero = (0 : Polynomial K) := by simp [ringOps, Ops.zero]
    have hpolyOf_zero : polyOf [(0 : K)] = (0 : Polynomial K) := by simp [polyOf]
    rw [hleft, hright, hleft_zero, hright_zero, hpolyOf_zero]
    simp
  · -- inductive case: c :: cs
    have hleft : (polyOps (fieldOps K) n).hornerZ2 (c :: cs) P Q =
      (polyOps (fieldOps K) n).add ((polyOps (fieldOps K) n).hornerZ c Q)
        ((polyOps (fieldOps K) n).mul P ((polyOps (fieldOps K) n).hornerZ2 cs P Q)) := rfl
    have hright : (ringOps (Polynomial K)).hornerZ2 (c :: cs) (polyOf P) (polyOf Q) =
      (ringOps (Polynomial K)).add ((ringOps (Polynomial K)).hornerZ c (polyOf Q))
        ((ringOps (Polynomial K)).mul (polyOf P) ((ringOps (Polynomial K)).hornerZ2 cs (polyOf P) (polyOf Q))) := rfl
    have hadd_poly : (polyOps (fieldOps K) n).add = (fieldOps K).zipAdd := rfl
    have hmul_poly : (polyOps (fieldOps K) n).mul = (fieldOps K).pmul n := rfl
    have hadd_ring : (ringOps (Polynomial K)).add = (· + ·) := rfl
    have hmul_ring : (ringOps (Polynomial K)).mul = (· * ·) := rfl
    have hzero_ring : (ringOps (Polynomial K)).zero = (0 : Polynomial K) := by simp [ringOps, Ops.zero]
    rw [hleft, hright, hadd_poly, hmul_poly, hadd_ring, hmul_ring]
    rw [polyOf_zipAdd]
    have h_eq : (polyOf ((polyOps (fieldOps K) n).hornerZ c Q) +
        polyOf ((fieldOps K).pmul n P ((polyOps (fieldOps K) n).hornerZ2 cs P Q))) -
        ((ringOps (Polynomial K)).hornerZ c (polyOf Q) +
          polyOf P * (ringOps (Polynomial K)).hornerZ2 cs (polyOf P) (polyOf Q)) =
        (polyOf ((polyOps (fieldOps K) n).hornerZ c Q) - (ringOps (Polynomial K)).hornerZ c (polyOf Q)) +
        (polyOf ((fieldOps K).pmul n P ((polyOps (fieldOps K) n).hornerZ2 cs P Q)) -
          polyOf P * polyOf ((polyOps (fieldOps K) n).hornerZ2 cs P Q)) +
        (polyOf P * (polyOf ((polyOps (fieldOps K) n).hornerZ2 cs P Q) -
          (ringOps (Polynomial K)).hornerZ2 cs (polyOf P) (polyOf Q))) := by
      ring
    rw [h_eq]
    apply dvd_add
    · apply dvd_add
      · exact X_pow_dvd_polyOf_hornerZ_aux n c Q
      · exact X_pow_dvd_polyOf_pmul n P ((polyOps (fieldOps K) n).hornerZ2 cs P Q)
    · rw [mul_comm]; exact dvd_mul_of_dvd_left ih (polyOf P)

/-! ### The formal series: step functions and helpers -/

/-- The step of `Ops.invSeries`. -/
def Ops.invStep {A : Type*} (o : Ops A) (g : List A) (d0 : A) (ds : List A) (j : ℕ) : List A :=
  ds ++ [o.neg (o.mul (((List.range j).map fun i =>
    o.mul (g.getD (i + 1) o.zero) (ds.getD (j - 1 - i) o.zero)).foldr o.add o.zero) d0)]

/-- The step of `Ops.sqrtSeries`. -/
def Ops.sqrtStep {A : Type*} (o : Ops A) (a : List A) (i2 : A) (ps : List A) (j : ℕ) : List A :=
  ps ++ [o.mul (o.sub (a.getD j o.zero) (((List.range (j - 1)).map fun i =>
    o.mul (ps.getD (i + 1) o.zero) (ps.getD (j - 1 - i) o.zero)).foldr o.add o.zero)) i2]

/-- The step of `Ops.rootSeries`. -/
def Ops.rootStep {A : Type*} (o : Ops A) (n : ℕ) (F : List (List ℤ)) (t0 t1 c : A) (P : List A)
    (k : ℕ) : List A :=
  P ++ [o.neg (o.mul (((polyOps o n).hornerZ2 F [t0, t1] P).getD k o.zero) c)]

theorem Ops.invSeries_eq {A : Type*} (o : Ops A) (n : ℕ) (g : List A) :
    o.invSeries n g =
      (o.inv (g.headD o.zero)).map fun d0 => (List.range' 1 n).foldl (o.invStep g d0) [d0] := by
  unfold Ops.invSeries
  cases o.inv (g.headD o.zero) <;> rfl

theorem Ops.sqrtSeries_eq {A : Type*} (o : Ops A) (n : ℕ) (a : List A) (p0 : A) :
    o.sqrtSeries n a p0 =
      (o.inv (o.add p0 p0)).map fun i2 => (List.range' 1 n).foldl (o.sqrtStep a i2) [p0] := by
  unfold Ops.sqrtSeries
  cases o.inv (o.add p0 p0) <;> rfl

theorem Ops.rootSeries_eq {A : Type*} (o : Ops A) (n : ℕ) (F : List (List ℤ)) (t0 t1 y0 : A) :
    o.rootSeries n F t0 t1 y0 =
      (o.inv (o.hornerZ2 (derivY F) t0 y0)).map fun c =>
        (List.range' 1 n).foldl (o.rootStep n F t0 t1 c) [y0] := by
  unfold Ops.rootSeries
  cases o.inv (o.hornerZ2 (derivY F) t0 y0) <;> rfl

theorem foldl_range'_one_succ {A : Type*} (step : List A → ℕ → List A) (init : List A) (m : ℕ) :
    (List.range' 1 (m + 1)).foldl step init = step ((List.range' 1 m).foldl step init) (m + 1) := by
  rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.one_mul,
    Nat.add_comm 1 m]

theorem fieldOps_foldr_add_range (f : ℕ → K) (j : ℕ) :
    ((List.range j).map f).foldr (fieldOps K).add (fieldOps K).zero = ∑ i ∈ Finset.range j, f i := by
  have key : ∀ (l : List K) (s : K), l.foldr (fieldOps K).add s = l.sum + s := by
    intro l s
    induction l with
    | nil => simp
    | cons a l ih => rw [List.foldr_cons, ih, List.sum_cons]; simp only [fieldOps]; ring
  rw [key]
  simp only [Ops.zero, fieldOps, Int.cast_zero, add_zero]
  induction j with
  | zero => simp
  | succ j ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

open Polynomial in
theorem polyOf_append_singleton (ds : List K) (x : K) :
    polyOf (ds ++ [x]) = polyOf ds + C x * X ^ ds.length := by
  induction ds with
  | nil => simp [polyOf_cons, polyOf_nil]
  | cons c ds ih => rw [List.cons_append, polyOf_cons, polyOf_cons, ih, List.length_cons, pow_succ]; ring

open Polynomial in
theorem coeff_polyOf_mul_succ {m : ℕ} (g ds : List K) (hds : ds.length = m + 1) :
    (polyOf g * polyOf ds).coeff (m + 1) =
      ∑ i ∈ Finset.range (m + 1), g.getD (i + 1) 0 * ds.getD (m - i) 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
  simp only [coeff_polyOf, Nat.sub_zero]
  rw [List.getD_eq_default ds (0 : K) (show ds.length ≤ m + 1 by omega), mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.add_sub_add_right]

open Polynomial in
theorem coeff_polyOf_sq_succ {m : ℕ} (ps : List K) (hps : ps.length = m + 1) :
    (polyOf ps ^ 2).coeff (m + 1) = ∑ i ∈ Finset.range m, ps.getD (i + 1) 0 * ps.getD (m - i) 0 := by
  rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ',
    Finset.sum_range_succ]
  simp only [coeff_polyOf, Nat.sub_zero, Nat.sub_self]
  rw [List.getD_eq_default ps (0 : K) (show ps.length ≤ m + 1 by omega), mul_zero, zero_mul, add_zero,
    add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.add_sub_add_right]

open Polynomial in
theorem polyOf_eval_zero (ps : List K) : (polyOf ps).eval 0 = ps.headD 0 := by
  cases ps with
  | nil => simp [polyOf_nil]
  | cons c ps => simp [polyOf_cons]

open Polynomial in
theorem polyOf_eq_zero_of_dvd {n : ℕ} {cs : List K} (hl : cs.length ≤ n + 1)
    (hd : X ^ (n + 1) ∣ polyOf cs) : polyOf cs = 0 := by
  refine eq_zero_of_dvd_of_degree_lt hd (lt_of_lt_of_le (degree_polyOf_lt cs) ?_)
  rw [degree_X_pow]
  exact_mod_cast hl

theorem length_zipAdd {A : Type*} (o : Ops A) (p q : List A) :
    (o.zipAdd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [Ops.zipAdd]
  | cons a p ih =>
    cases q with
    | nil => simp [Ops.zipAdd]
    | cons b q => simp [Ops.zipAdd, ih]

theorem length_zipSub_le {A : Type*} (o : Ops A) (p q : List A) :
    (o.zipSub p q).length ≤ max p.length q.length := by
  induction p generalizing q with
  | nil => simp [Ops.zipSub]
  | cons a p ih =>
    cases q with
    | nil => simp [Ops.zipSub]
    | cons b q => simpa [Ops.zipSub] using ih q

theorem length_pmul_le {A : Type*} (o : Ops A) (n : ℕ) (p q : List A) :
    (o.pmul n p q).length ≤ n + 1 := List.length_take_le _ _

theorem length_polyOps_hornerZ2_le {A : Type*} (o : Ops A) (n : ℕ) (F : List (List ℤ))
    (P Q : List A) : ((polyOps o n).hornerZ2 F P Q).length ≤ n + 1 := by
  have hz : ((polyOps o n).zero).length ≤ n + 1 := by simp [Ops.zero, polyOps]
  have hZ : ∀ c : List ℤ, ((polyOps o n).hornerZ c Q).length ≤ n + 1 := by
    intro c
    induction c with
    | nil => exact hz
    | cons z c ih =>
      show (o.zipAdd [o.ofInt z] (o.pmul n Q _)).length ≤ n + 1
      rw [length_zipAdd]
      exact max_le (by simp) (length_pmul_le o n _ _)
  induction F with
  | nil => exact hz
  | cons c F ih =>
    show (o.zipAdd _ (o.pmul n P _)).length ≤ n + 1
    rw [length_zipAdd]
    exact max_le (hZ c) (length_pmul_le o n _ _)


theorem getD_zero_eq_headD (l : List K) : l.getD 0 0 = l.headD 0 := by cases l <;> rfl

open Polynomial in
theorem invStep_spec {m : ℕ} {g ds : List K} {d0 : K} (hd0 : g.headD 0 * d0 = 1)
    (hl : ds.length = m + 1) (hdvd : X ^ (m + 1) ∣ polyOf g * polyOf ds - 1) :
    ((fieldOps K).invStep g d0 ds (m + 1)).length = m + 2 ∧
      X ^ (m + 2) ∣ polyOf g * polyOf ((fieldOps K).invStep g d0 ds (m + 1)) - 1 := by
  set s := ∑ i ∈ Finset.range (m + 1), g.getD (i + 1) 0 * ds.getD (m - i) 0 with hs
  have hstep : (fieldOps K).invStep g d0 ds (m + 1) = ds ++ [-(s * d0)] := by
    rw [Ops.invStep, fieldOps_foldr_add_range]
    simp only [fieldOps, Ops.zero, Int.cast_zero, Nat.add_sub_cancel, hs]
  rw [hstep]
  refine ⟨by simp [hl], ?_⟩
  have e : polyOf g * polyOf (ds ++ [-(s * d0)]) - 1 =
      (polyOf g * polyOf ds - 1) + X ^ (m + 1) * (C (-(s * d0)) * polyOf g) := by
    rw [polyOf_append_singleton, hl]; ring
  rw [e, X_pow_dvd_iff]
  intro d hd
  rw [coeff_add, coeff_X_pow_mul']
  rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | rfl
  · rw [X_pow_dvd_iff.mp hdvd d hd, ite_eq_right (by omega), add_zero]
  · rw [ite_eq_left le_rfl, Nat.sub_self, coeff_sub, coeff_one, ite_eq_right (by omega), sub_zero,
      coeff_polyOf_mul_succ g ds hl, coeff_C_mul, coeff_polyOf, getD_zero_eq_headD, ← hs]
    linear_combination (-s) * hd0

open Polynomial in
theorem sqrtStep_spec {m : ℕ} {a ps : List K} {p0 i2 : K} (hi2 : (p0 + p0) * i2 = 1)
    (hl : ps.length = m + 1) (hh : ps.headD 0 = p0) (hdvd : X ^ (m + 1) ∣ polyOf a - polyOf ps ^ 2) :
    ((fieldOps K).sqrtStep a i2 ps (m + 1)).length = m + 2 ∧
      ((fieldOps K).sqrtStep a i2 ps (m + 1)).headD 0 = p0 ∧
      X ^ (m + 2) ∣ polyOf a - polyOf ((fieldOps K).sqrtStep a i2 ps (m + 1)) ^ 2 := by
  set s := ∑ i ∈ Finset.range m, ps.getD (i + 1) 0 * ps.getD (m - i) 0 with hs
  set x := (a.getD (m + 1) 0 - s) * i2 with hx
  have hstep : (fieldOps K).sqrtStep a i2 ps (m + 1) = ps ++ [x] := by
    rw [Ops.sqrtStep, fieldOps_foldr_add_range]
    simp only [fieldOps, Ops.zero, Int.cast_zero, Nat.add_sub_cancel, hs, hx]
  rw [hstep]
  obtain ⟨c, cs, rfl⟩ : ∃ c cs, ps = c :: cs := by
    cases ps with
    | nil => simp at hl
    | cons c cs => exact ⟨c, cs, rfl⟩
  refine ⟨by simp only [List.length_append, List.length_singleton, hl], by simpa using hh, ?_⟩
  have e : polyOf a - polyOf (c :: cs ++ [x]) ^ 2 =
      (polyOf a - polyOf (c :: cs) ^ 2) +
        X ^ (m + 1) * (-(C (2 * x) * polyOf (c :: cs)) - X ^ (m + 1) * C (x ^ 2)) := by
    rw [polyOf_append_singleton, hl]; simp only [map_mul, map_pow, map_ofNat]; ring
  rw [e, X_pow_dvd_iff]
  intro d hd
  rw [coeff_add, coeff_X_pow_mul']
  rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | rfl
  · rw [X_pow_dvd_iff.mp hdvd d hd, ite_eq_right (by omega), add_zero]
  · rw [ite_eq_left le_rfl, Nat.sub_self, coeff_sub, coeff_sub, coeff_neg, coeff_C_mul, coeff_X_pow_mul',
      ite_eq_right (by omega), sub_zero, coeff_polyOf, coeff_polyOf, getD_zero_eq_headD, hh,
      coeff_polyOf_sq_succ _ hl, ← hs, hx]
    linear_combination (-(a.getD (m + 1) 0 - s)) * hi2

theorem map_hornerZ {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (c : List ℤ) (y : R) :
    φ ((ringOps R).hornerZ c y) = (ringOps S).hornerZ c (φ y) := by
  induction c with
  | nil => simp [Ops.hornerZ, Ops.zero, ringOps]
  | cons z cs ih =>
    show φ ((z : R) + y * (ringOps R).hornerZ cs y) = (z : S) + φ y * (ringOps S).hornerZ cs (φ y)
    rw [map_add, map_mul, map_intCast, ih]

theorem map_ddZ {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (c : List ℤ) (a b : R) :
    φ ((ringOps R).ddZ c a b) = (ringOps S).ddZ c (φ a) (φ b) := by
  induction c with
  | nil => simp [Ops.ddZ, Ops.zero, ringOps]
  | cons z cs ih =>
    show φ ((ringOps R).hornerZ cs a + b * (ringOps R).ddZ cs a b) =
      (ringOps S).hornerZ cs (φ a) + φ b * (ringOps S).ddZ cs (φ a) (φ b)
    rw [map_add, map_mul, map_hornerZ, ih]

/-- Divided differences under a ring map. -/
theorem map_ddZ2 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (F : List (List ℤ))
    (x a b : R) : φ ((ringOps R).ddZ2 F x a b) = (ringOps S).ddZ2 F (φ x) (φ a) (φ b) := by
  induction F with
  | nil => simp [Ops.ddZ2, Ops.zero, ringOps]
  | cons c F ih =>
    show φ ((ringOps R).ddZ c a b + x * (ringOps R).ddZ2 F x a b) =
      (ringOps S).ddZ c (φ a) (φ b) + φ x * (ringOps S).ddZ2 F (φ x) (φ a) (φ b)
    rw [map_add, map_mul, map_ddZ, ih]

theorem ringOps_hornerZ_cons {R : Type*} [CommRing R] (z : ℤ) (l : List ℤ) (a : R) :
    (ringOps R).hornerZ (z :: l) a = (z : R) + a * (ringOps R).hornerZ l a := rfl

theorem ringOps_hornerZ_nil {R : Type*} [CommRing R] (a : R) : (ringOps R).hornerZ [] a = 0 := by
  simp [Ops.hornerZ, Ops.zero, ringOps]

theorem hornerZ_mapIdx_succ {R : Type*} [CommRing R] (a : R) (k : ℕ) (l : List ℤ) :
    (ringOps R).hornerZ (l.mapIdx fun i z => ((i + (k + 1) : ℕ) : ℤ) * z) a =
      (ringOps R).hornerZ (l.mapIdx fun i z => ((i + k : ℕ) : ℤ) * z) a + (ringOps R).hornerZ l a := by
  induction l generalizing k with
  | nil => simp [ringOps_hornerZ_nil]
  | cons w ws ih =>
    rw [List.mapIdx_cons, List.mapIdx_cons]
    have e1 : (fun i z => (((i + 1) + (k + 1) : ℕ) : ℤ) * z) =
        (fun i z => ((i + (k + 1 + 1) : ℕ) : ℤ) * z) := by
      funext i z; congr 2; omega
    have e2 : (fun i z => (((i + 1) + k : ℕ) : ℤ) * z) = (fun i z => ((i + (k + 1) : ℕ) : ℤ) * z) := by
      funext i z; congr 2; omega
    simp only [e1, e2, ringOps_hornerZ_cons]
    rw [ih (k + 1)]
    push_cast
    ring

theorem ddZ_self {R : Type*} [CommRing R] (c : List ℤ) (a : R) :
    (ringOps R).ddZ c a a =
      (ringOps R).hornerZ ((c.drop 1).mapIdx fun i z => ((i + 1 : ℕ) : ℤ) * z) a := by
  induction c with
  | nil => simp [Ops.ddZ, Ops.hornerZ]
  | cons z cs ih =>
    show (ringOps R).hornerZ cs a + a * (ringOps R).ddZ cs a a = _
    rw [ih]
    simp only [List.drop_one, List.tail_cons]
    cases cs with
    | nil => simp [ringOps_hornerZ_nil]
    | cons w ws =>
      simp only [List.tail_cons, List.mapIdx_cons]
      have e1 : (fun i z => (((i + 1) + 1 : ℕ) : ℤ) * z) =
          (fun i z => ((i + (1 + 1) : ℕ) : ℤ) * z) := rfl
      rw [e1, ringOps_hornerZ_cons _ (List.mapIdx _ ws), hornerZ_mapIdx_succ a 1 ws,
        ringOps_hornerZ_cons w ws]
      push_cast
      ring

/-- The divided difference on the diagonal is the derivative in `y`. -/
theorem ddZ2_self {R : Type*} [CommRing R] (F : List (List ℤ)) (x a : R) :
    (ringOps R).ddZ2 F x a a = (ringOps R).hornerZ2 (derivY F) x a := by
  induction F with
  | nil => simp [Ops.ddZ2, Ops.hornerZ2, derivY]
  | cons c F ih =>
    show (ringOps R).ddZ c a a + x * (ringOps R).ddZ2 F x a a =
      (ringOps R).hornerZ ((c.drop 1).mapIdx fun i z => ((i + 1 : ℕ) : ℤ) * z) a +
        x * (ringOps R).hornerZ2 (derivY F) x a
    rw [ddZ_self, ih]


open Polynomial in
theorem rootStep_spec {n m : ℕ} (hm : m + 1 ≤ n) {F : List (List ℤ)} {t0 t1 y0 c : K} {P : List K}
    (hc : (fieldOps K).hornerZ2 (derivY F) t0 y0 * c = 1)
    (hl : P.length = m + 1) (hh : P.headD 0 = y0)
    (hdvd : X ^ (m + 1) ∣ (ringOps K[X]).hornerZ2 F (C t0 + C t1 * X) (polyOf P)) :
    ((fieldOps K).rootStep n F t0 t1 c P (m + 1)).length = m + 2 ∧
      ((fieldOps K).rootStep n F t0 t1 c P (m + 1)).headD 0 = y0 ∧
      X ^ (m + 2) ∣ (ringOps K[X]).hornerZ2 F (C t0 + C t1 * X)
        (polyOf ((fieldOps K).rootStep n F t0 t1 c P (m + 1))) := by
  set T : K[X] := C t0 + C t1 * X with hT
  set r := (polyOps (fieldOps K) n).hornerZ2 F [t0, t1] P with hr
  set x := -(r.getD (m + 1) 0 * c) with hx
  have hstep : (fieldOps K).rootStep n F t0 t1 c P (m + 1) = P ++ [x] := by
    rw [Ops.rootStep]
    show P ++ [-(r.getD (m + 1) ((0 : ℤ) : K) * c)] = P ++ [x]
    rw [Int.cast_zero]
  rw [hstep]
  obtain ⟨p, ps, rfl⟩ : ∃ p ps, P = p :: ps := by
    cases P with
    | nil => simp at hl
    | cons p ps => exact ⟨p, ps, rfl⟩
  refine ⟨by simp only [List.length_append, List.length_singleton, hl], by simpa using hh, ?_⟩
  have hTP : polyOf [t0, t1] = T := by rw [polyOf_cons, polyOf_cons, polyOf_nil, hT]; ring
  have h1 := X_pow_dvd_polyOf_hornerZ2 n F [t0, t1] (p :: ps)
  rw [hTP, ← hr] at h1
  have hrc : r.getD (m + 1) 0 = ((ringOps K[X]).hornerZ2 F T (polyOf (p :: ps))).coeff (m + 1) := by
    have := X_pow_dvd_iff.mp h1 (m + 1) (by omega)
    rw [coeff_sub, coeff_polyOf] at this
    exact sub_eq_zero.mp this
  have hsub := hornerZ2_sub_hornerZ2 F T (polyOf (p :: ps ++ [x])) (polyOf (p :: ps))
  set δ := (ringOps K[X]).ddZ2 F T (polyOf (p :: ps ++ [x])) (polyOf (p :: ps)) with hδ
  have hQ' : polyOf (p :: ps ++ [x]) = polyOf (p :: ps) + C x * X ^ (m + 1) := by
    rw [polyOf_append_singleton, hl]
  have e : (ringOps K[X]).hornerZ2 F T (polyOf (p :: ps ++ [x])) =
      (ringOps K[X]).hornerZ2 F T (polyOf (p :: ps)) + X ^ (m + 1) * (C x * δ) := by
    rw [← sub_eq_iff_eq_add', hsub, hQ']
    ring
  have hδ0 : δ.coeff 0 = (fieldOps K).hornerZ2 (derivY F) t0 y0 := by
    rw [coeff_zero_eq_eval_zero]
    have hm := map_ddZ2 (Polynomial.evalRingHom (0 : K)) F T (polyOf (p :: ps ++ [x]))
      (polyOf (p :: ps))
    simp only [coe_evalRingHom] at hm
    rw [hδ, hm, polyOf_eval_zero, polyOf_eval_zero, hT]
    simp only [eval_add, eval_C, eval_mul, eval_X, mul_zero, add_zero, List.cons_append,
      List.headD_cons]
    simp only [List.headD_cons] at hh
    rw [hh, ddZ2_self, fieldOps_hornerZ2_eq_ringOps]
  rw [e, X_pow_dvd_iff]
  intro d hd
  rw [coeff_add, coeff_X_pow_mul']
  rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | rfl
  · rw [X_pow_dvd_iff.mp hdvd d hd, ite_eq_right (by omega), add_zero]
  · rw [ite_eq_left le_rfl, Nat.sub_self, coeff_C_mul, hδ0, ← hrc, hx]
    linear_combination (-(r.getD (m + 1) 0)) * hc

open Polynomial in
/-- **The formal inverse**: `g d ≡ 1 (mod X^(n+1))`. -/
theorem invSeries_spec {n : ℕ} {g ds : List K} (h : (fieldOps K).invSeries n g = some ds) :
    ds.length = n + 1 ∧ X ^ (n + 1) ∣ polyOf g * polyOf ds - 1 := by
  rw [Ops.invSeries_eq, Option.map_eq_some_iff] at h
  obtain ⟨d0, hd0, rfl⟩ := h
  obtain ⟨hne, rfl⟩ := fieldOps_inv_eq_some hd0
  have hz : (fieldOps K).zero = 0 := by simp [Ops.zero, fieldOps]
  rw [hz] at hne ⊢
  have hg : g.headD 0 * (g.headD 0)⁻¹ = 1 := mul_inv_cancel₀ hne
  suffices H : ∀ m, ((List.range' 1 m).foldl ((fieldOps K).invStep g (g.headD 0)⁻¹)
      [(g.headD 0)⁻¹]).length = m + 1 ∧ X ^ (m + 1) ∣ polyOf g * polyOf ((List.range' 1 m).foldl
        ((fieldOps K).invStep g (g.headD 0)⁻¹) [(g.headD 0)⁻¹]) - 1 from H n
  intro m
  induction m with
  | zero =>
    refine ⟨rfl, ?_⟩
    rw [List.range'_zero, List.foldl_nil, zero_add, pow_one, X_dvd_iff, coeff_sub, mul_coeff_zero,
      coeff_polyOf, coeff_polyOf, getD_zero_eq_headD, coeff_one_zero]
    simpa using sub_eq_zero.mpr hg
  | succ m ih =>
    rw [foldl_range'_one_succ]
    exact invStep_spec hg ih.1 ih.2

open Polynomial in
/-- **The formal square root**: `g ≡ p² (mod X^(n+1))` when `p₀² = g₀`. -/
theorem sqrtSeries_spec {n : ℕ} {g ps : List K} {p0 : K} (hp : p0 ^ 2 = g.headD 0)
    (h : (fieldOps K).sqrtSeries n g p0 = some ps) :
    ps.length = n + 1 ∧ ps.headD 0 = p0 ∧ X ^ (n + 1) ∣ polyOf g - polyOf ps ^ 2 := by
  rw [Ops.sqrtSeries_eq, Option.map_eq_some_iff] at h
  obtain ⟨i2, hi2, rfl⟩ := h
  obtain ⟨hne, rfl⟩ := fieldOps_inv_eq_some hi2
  change p0 + p0 ≠ 0 at hne
  have hi : (p0 + p0) * (p0 + p0)⁻¹ = 1 := mul_inv_cancel₀ hne
  suffices H : ∀ m, ((List.range' 1 m).foldl ((fieldOps K).sqrtStep g (p0 + p0)⁻¹) [p0]).length =
      m + 1 ∧ ((List.range' 1 m).foldl ((fieldOps K).sqrtStep g (p0 + p0)⁻¹) [p0]).headD 0 = p0 ∧
      X ^ (m + 1) ∣ polyOf g - polyOf ((List.range' 1 m).foldl
        ((fieldOps K).sqrtStep g (p0 + p0)⁻¹) [p0]) ^ 2 from H n
  intro m
  induction m with
  | zero =>
    refine ⟨rfl, rfl, ?_⟩
    rw [List.range'_zero, List.foldl_nil, zero_add, pow_one, X_dvd_iff, coeff_sub, sq,
      mul_coeff_zero, coeff_polyOf, coeff_polyOf, getD_zero_eq_headD, ← hp]
    simp [sq]
  | succ m ih =>
    rw [foldl_range'_one_succ]
    exact sqrtStep_spec hi ih.1 ih.2.1 ih.2.2

open Polynomial in
/-- **The formal implicit root**: `F(t₀ + t₁ X, P) ≡ 0 (mod X^(n+1))` when `F(t₀, y₀) = 0`. -/
theorem rootSeries_spec {n : ℕ} {F : List (List ℤ)} {t0 t1 y0 : K} {ps : List K}
    (h0 : (fieldOps K).hornerZ2 F t0 y0 = 0) (h : (fieldOps K).rootSeries n F t0 t1 y0 = some ps) :
    ps.length = n + 1 ∧ ps.headD 0 = y0 ∧
      X ^ (n + 1) ∣ (ringOps K[X]).hornerZ2 F (C t0 + C t1 * X) (polyOf ps) := by
  rw [Ops.rootSeries_eq, Option.map_eq_some_iff] at h
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨hne, rfl⟩ := fieldOps_inv_eq_some hc
  have hc1 := mul_inv_cancel₀ hne
  suffices H : ∀ m ≤ n, ((List.range' 1 m).foldl
      ((fieldOps K).rootStep n F t0 t1 ((fieldOps K).hornerZ2 (derivY F) t0 y0)⁻¹) [y0]).length =
      m + 1 ∧ ((List.range' 1 m).foldl
      ((fieldOps K).rootStep n F t0 t1 ((fieldOps K).hornerZ2 (derivY F) t0 y0)⁻¹) [y0]).headD 0 =
      y0 ∧ X ^ (m + 1) ∣ (ringOps K[X]).hornerZ2 F (C t0 + C t1 * X) (polyOf ((List.range' 1 m).foldl
      ((fieldOps K).rootStep n F t0 t1 ((fieldOps K).hornerZ2 (derivY F) t0 y0)⁻¹) [y0])) from
    H n le_rfl
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨rfl, rfl, ?_⟩
    rw [List.range'_zero, List.foldl_nil, zero_add, pow_one, X_dvd_iff, coeff_zero_eq_eval_zero]
    have hm := map_hornerZ2 (Polynomial.evalRingHom (0 : K)) F (C t0 + C t1 * X) (polyOf [y0])
    simp only [coe_evalRingHom] at hm
    rw [hm, polyOf_eval_zero]
    simpa [fieldOps_hornerZ2_eq_ringOps] using h0
  | succ m ih =>
    intro hm
    rw [foldl_range'_one_succ]
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    exact rootStep_spec hm hc1 h1 h2 h3

end Exact

end FurioLombardo.Discharge.KvArith
