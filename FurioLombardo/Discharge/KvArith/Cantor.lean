import Mathlib
import FurioLombardo.Discharge.KvArith.Ops
import FurioLombardo.Discharge.R7.LineStep
import FurioLombardo.Discharge.KvArith.Comp.Cantor

/-!
# Cantor's composition and reduction as straight line programs (lane lean-kv-arith, D5)

Mumford pairs `D = [u, v]` with `u = X² + u₁X + u₀`, `v = v₁X + v₀` on `y² = f`, `f` of degree `≤ 6`
(`Sext`), as coordinates over any `Ops` carrier:

* `compAdd`: for coprime `u, u'` (the norm `N = Res(u', u)` of `u mod u'` is inverted), the cubic `w`
  with `w ≡ v mod u`, `w ≡ v' mod u'` (`w = v + u k`, `k = (v' - v)/(u mod u') mod u'`) and `U = u u'`;
* `compDbl`: for `N(2v mod u)` invertible, `w = v + u k` with `k = ((f - v²)/u mod u)/(2v) mod u`, and
  `U = u²`;
* `reduce4`: from `U` monic quartic and `w` cubic with `U ∣ f - w²`: `q = (f - w²)/U` (from `f₄, f₅, f₆`
  only), its leading coefficient `f₆ - w₃²` inverted, `u'' = q/lc(q)`, `v'' = -w mod u''`;
* `cantorAdd = reduce4 ∘ compAdd`, `cantorDbl = reduce4 ∘ compDbl`, and `revD` (the model
  `X^6 f(1/X)`, `X = 1/x`: `[X² + (u₁/u₀)X + 1/u₀, X³ v(1/X) mod u']`).

Each program has a `_rel` lemma (it is related to itself along any `Ops.Rel`). Over a field (`fieldOps`,
where the program succeeds exactly when its inverses are nonzero) the class statements follow from
R7/LineStep.lean: `cantorAdd_spec` (`[D][E] = [D'']`) and `cantorDbl_spec` (`[D]² = [D'']`) in the ideal
class group of `K[X, Y]/(Y² - f)`, `revD_spec` (the image is on the reversed curve).
-/

namespace FurioLombardo.Discharge.KvArith

open Polynomial FurioLombardo.M3a FurioLombardo.M3a.Genus2

/-! ## Relational soundness -/

/-- Coordinatewise relation of pairs. -/
def Mum.Rel {A B : Type*} (R : A → B → Prop) (D : Mum A) (E : Mum B) : Prop :=
  R D.u0 E.u0 ∧ R D.u1 E.u1 ∧ R D.v0 E.v0 ∧ R D.v1 E.v1

/-- Coordinatewise relation of sextics. -/
def Sext.Rel {A B : Type*} (R : A → B → Prop) (f : Sext A) (g : Sext B) : Prop :=
  R f.f0 g.f0 ∧ R f.f1 g.f1 ∧ R f.f2 g.f2 ∧ R f.f3 g.f3 ∧ R f.f4 g.f4 ∧ R f.f5 g.f5 ∧ R f.f6 g.f6

/-- Coordinatewise relation of quartics. -/
def Quart.Rel {A B : Type*} (R : A → B → Prop) (q : Quart A) (q' : Quart B) : Prop :=
  R q.c0 q'.c0 ∧ R q.c1 q'.c1 ∧ R q.c2 q'.c2 ∧ R q.c3 q'.c3

/-- Relation of the outputs `(U, w)` of the composition. -/
def QQ.Rel {A B : Type*} (R : A → B → Prop) (x : Quart A × Quart A) (y : Quart B × Quart B) :
    Prop :=
  Quart.Rel R x.1 y.1 ∧ Quart.Rel R x.2 y.2

/-- `OptRel` through a bind. -/
theorem OptRel.bind {A B A' B' : Type*} {R : A → B → Prop} {S : A' → B' → Prop} {x : Option A}
    {y : Option B} (hxy : OptRel R x y) {f : A → Option A'} {g : B → Option B'}
    (hfg : ∀ a b, R a b → OptRel S (f a) (g b)) : OptRel S (x.bind f) (y.bind g) := by
  intro c hc
  obtain ⟨b, hb, hgb⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨a, ha, hab⟩ := hxy b hb
  obtain ⟨d, hd, hdc⟩ := hfg a b hab c hgb
  exact ⟨d, by rw [ha, Option.bind_some, hd], hdc⟩

section Rel

variable {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}

theorem Ops.Rel.compAdd (h : Ops.Rel o p R) {D E : Mum A} {D' E' : Mum B} (hD : Mum.Rel R D D')
    (hE : Mum.Rel R E E') : OptRel (QQ.Rel R) (KvArith.compAdd o D E) (KvArith.compAdd p D' E') := by
  intro b hb
  dsimp only [KvArith.compAdd] at hb
  rcases Option.bind_eq_some_iff.mp hb with ⟨Ni, hNi, hrest⟩
  obtain ⟨hD0, hD1, hDv0, hDv1⟩ := hD
  obtain ⟨hE0, hE1, hEv0, hEv1⟩ := hE
  -- Abbreviations for p-side intermediates (using set for equalities)
  set gp0 := p.sub D'.u0 E'.u0 with hgp0_def
  set gp1 := p.sub D'.u1 E'.u1 with hgp1_def
  set N' := p.add (p.sub (p.mul gp0 gp0) (p.mul (p.mul gp0 gp1) E'.u1)) (p.mul (p.mul gp1 gp1) E'.u0) with hN'_def
  set ip0 := p.mul (p.sub gp0 (p.mul gp1 E'.u1)) Ni with hip0_def
  set ip1 := p.neg (p.mul gp1 Ni) with hip1_def
  set dp0 := p.sub E'.v0 D'.v0 with hdp0_def
  set dp1 := p.sub E'.v1 D'.v1 with hdp1_def
  set kp0 := p.sub (p.mul dp0 ip0) (p.mul (p.mul dp1 ip1) E'.u0) with hkp0_def
  set kp1 := p.sub (p.add (p.mul dp0 ip1) (p.mul dp1 ip0)) (p.mul (p.mul dp1 ip1) E'.u1) with hkp1_def
  set U' : Quart B := ⟨p.mul D'.u0 E'.u0, p.add (p.mul D'.u0 E'.u1) (p.mul D'.u1 E'.u0),
    p.add (p.add D'.u0 (p.mul D'.u1 E'.u1)) E'.u0, p.add D'.u1 E'.u1⟩ with hU'_def
  set w' : Quart B := ⟨p.add D'.v0 (p.mul D'.u0 kp0), p.add (p.add D'.v1 (p.mul D'.u1 kp0)) (p.mul D'.u0 kp1),
    p.add kp0 (p.mul D'.u1 kp1), kp1⟩ with hw'_def
  -- From hNi, we have p.inv N' = some Ni
  have hNi' : p.inv N' = some Ni := by
    simpa [hgp0_def, hgp1_def, hN'_def] using hNi
  -- R relations for the p-side intermediates
  have hR_gp0 : R (o.sub D.u0 E.u0) gp0 := by
    simpa [hgp0_def] using h.sub hD0 hE0
  have hR_gp1 : R (o.sub D.u1 E.u1) gp1 := by
    simpa [hgp1_def] using h.sub hD1 hE1
  have hR_gp0_gp0 : R (o.mul (o.sub D.u0 E.u0) (o.sub D.u0 E.u0)) (p.mul gp0 gp0) := by
    simpa [hgp0_def] using h.mul hR_gp0 hR_gp0
  have hR_gp0_gp1 : R (o.mul (o.sub D.u0 E.u0) (o.sub D.u1 E.u1)) (p.mul gp0 gp1) := by
    simpa [hgp0_def, hgp1_def] using h.mul hR_gp0 hR_gp1
  have hR_gp1_gp1 : R (o.mul (o.sub D.u1 E.u1) (o.sub D.u1 E.u1)) (p.mul gp1 gp1) := by
    simpa [hgp1_def] using h.mul hR_gp1 hR_gp1
  have hR_gp0_gp1_E1 : R (o.mul (o.mul (o.sub D.u0 E.u0) (o.sub D.u1 E.u1)) E.u1) (p.mul (p.mul gp0 gp1) E'.u1) := by
    simpa [hgp0_def, hgp1_def] using h.mul hR_gp0_gp1 hE1
  have hR_sub1 : R (o.sub (o.mul (o.sub D.u0 E.u0) (o.sub D.u0 E.u0)) (o.mul (o.mul (o.sub D.u0 E.u0) (o.sub D.u1 E.u1)) E.u1))
    (p.sub (p.mul gp0 gp0) (p.mul (p.mul gp0 gp1) E'.u1)) := by
    simpa [hgp0_def, hgp1_def] using h.sub hR_gp0_gp0 hR_gp0_gp1_E1
  have hR_gp1_gp1_E0 : R (o.mul (o.mul (o.sub D.u1 E.u1) (o.sub D.u1 E.u1)) E.u0) (p.mul (p.mul gp1 gp1) E'.u0) := by
    simpa [hgp1_def] using h.mul hR_gp1_gp1 hE0
  have hN : R (o.add (o.sub (o.mul (o.sub D.u0 E.u0) (o.sub D.u0 E.u0)) (o.mul (o.mul (o.sub D.u0 E.u0) (o.sub D.u1 E.u1)) E.u1))
    (o.mul (o.mul (o.sub D.u1 E.u1) (o.sub D.u1 E.u1)) E.u0))
    N' := by
    simpa [hN'_def] using h.add hR_sub1 hR_gp1_gp1_E0
  rcases h.inv hN hNi' with ⟨y, hy, hRyNi⟩
  -- hy : o.inv (o-side N) = some y
  -- Show that b = (U', w')
  have hb_eq : b = (U', w') := by
    -- hrest : pure (U', w') = some b
    have := hrest
    -- pure (U', w') = some b
    -- So Option.some.inj gives (U', w') = b
    exact (Option.some.inj this).symm
  -- Abbreviations for o-side intermediates
  set g0 := o.sub D.u0 E.u0 with hg0_def
  set g1 := o.sub D.u1 E.u1 with hg1_def
  set i0 := o.mul (o.sub g0 (o.mul g1 E.u1)) y with hi0_def
  set i1 := o.neg (o.mul g1 y) with hi1_def
  set d0 := o.sub E.v0 D.v0 with hd0_def
  set d1 := o.sub E.v1 D.v1 with hd1_def
  set k0 := o.sub (o.mul d0 i0) (o.mul (o.mul d1 i1) E.u0) with hk0_def
  set k1 := o.sub (o.add (o.mul d0 i1) (o.mul d1 i0)) (o.mul (o.mul d1 i1) E.u1) with hk1_def
  set U : Quart A := ⟨o.mul D.u0 E.u0, o.add (o.mul D.u0 E.u1) (o.mul D.u1 E.u0),
    o.add (o.add D.u0 (o.mul D.u1 E.u1)) E.u0, o.add D.u1 E.u1⟩ with hU_def
  set w : Quart A := ⟨o.add D.v0 (o.mul D.u0 k0), o.add (o.add D.v1 (o.mul D.u1 k0)) (o.mul D.u0 k1),
    o.add k0 (o.mul D.u1 k1), k1⟩ with hw_def
  -- The o-side N
  set No := o.add (o.sub (o.mul g0 g0) (o.mul (o.mul g0 g1) E.u1)) (o.mul (o.mul g1 g1) E.u0) with hNo_def
  have hy_No : o.inv No = some y := by
    simpa [hg0_def, hg1_def, hNo_def] using hy
  -- R relations for o-side intermediates
  have hR_g0 : R g0 gp0 := by
    simpa [hg0_def, hgp0_def] using h.sub hD0 hE0
  have hR_g1 : R g1 gp1 := by
    simpa [hg1_def, hgp1_def] using h.sub hD1 hE1
  have hR_d0 : R d0 dp0 := by
    simpa [hd0_def, hdp0_def] using h.sub hEv0 hDv0
  have hR_d1 : R d1 dp1 := by
    simpa [hd1_def, hdp1_def] using h.sub hEv1 hDv1
  have hR_i1_i1' : R i1 ip1 := by
    -- i1 = o.neg (o.mul g1 y), ip1 = p.neg (p.mul gp1 Ni)
    -- First: R (o.mul g1 y) (p.mul gp1 Ni)
    have h_mul : R (o.mul g1 y) (p.mul gp1 Ni) := by
      simpa [hg1_def, hgp1_def] using h.mul hR_g1 hRyNi
    -- Then apply neg
    simpa [hi1_def, hip1_def] using h.neg h_mul
  have hR_sub_g0_mul_g1_E1 : R (o.sub g0 (o.mul g1 E.u1)) (p.sub gp0 (p.mul gp1 E'.u1)) := by
    simpa [hg0_def, hg1_def, hgp0_def, hgp1_def] using h.sub hR_g0 (h.mul hR_g1 hE1)
  have hR_i0_i0' : R i0 ip0 := by
    simpa [hi0_def, hip0_def] using h.mul hR_sub_g0_mul_g1_E1 hRyNi
  have hR_mul_d0_i0 : R (o.mul d0 i0) (p.mul dp0 ip0) :=
    h.mul hR_d0 hR_i0_i0'
  have hR_mul_d1_i1 : R (o.mul (o.mul d1 i1) E.u0) (p.mul (p.mul dp1 ip1) E'.u0) :=
    h.mul (h.mul hR_d1 hR_i1_i1') hE0
  have hR_k0_k0' : R k0 kp0 := by
    simpa [hk0_def, hkp0_def] using h.sub hR_mul_d0_i0 hR_mul_d1_i1
  -- U relations
  have hU0 : R U.c0 U'.c0 := by
    simpa [hU_def, hU'_def] using h.mul hD0 hE0
  have hU1 : R U.c1 U'.c1 := by
    simpa [hU_def, hU'_def] using h.add (h.mul hD0 hE1) (h.mul hD1 hE0)
  have hU2 : R U.c2 U'.c2 := by
    simpa [hU_def, hU'_def] using h.add (h.add hD0 (h.mul hD1 hE1)) hE0
  have hU3 : R U.c3 U'.c3 := by
    simpa [hU_def, hU'_def] using h.add hD1 hE1
  -- w relations
  have hw0 : R w.c0 w'.c0 := by
    simpa [hw_def, hw'_def, hd0_def, hdp0_def] using h.add hDv0 (h.mul hD0 hR_k0_k0')
  have hR_mul_d0_i1 : R (o.mul d0 i1) (p.mul dp0 ip1) :=
    h.mul hR_d0 hR_i1_i1'
  have hR_mul_d1_i0 : R (o.mul d1 i0) (p.mul dp1 ip0) :=
    h.mul hR_d1 hR_i0_i0'
  have hR_add_mul_d0_i1_d1_i0 : R (o.add (o.mul d0 i1) (o.mul d1 i0)) (p.add (p.mul dp0 ip1) (p.mul dp1 ip0)) :=
    h.add hR_mul_d0_i1 hR_mul_d1_i0
  have hR_mul_d1_i1'_for_k1 : R (o.mul (o.mul d1 i1) (o.sub D.u1 E.u1)) (p.mul (p.mul dp1 ip1) (p.sub D'.u1 E'.u1)) :=
    h.mul (h.mul hR_d1 hR_i1_i1') hR_g1
  have hR_k1_k1' : R k1 kp1 := by
    -- k1 = o.sub (o.add (o.mul d0 i1) (o.mul d1 i0)) (o.mul (o.mul d1 i1) E.u1)
    -- kp1 = p.sub (p.add (p.mul dp0 ip1) (p.mul dp1 ip0)) (p.mul (p.mul dp1 ip1) E'.u1)
    -- But hR_mul_d1_i1'_for_k1 uses (o.sub D.u1 E.u1) instead of E.u1
    -- We need R (o.mul (o.mul d1 i1) E.u1) (p.mul (p.mul dp1 ip1) E'.u1)
    have h_mul_d1_i1_E : R (o.mul (o.mul d1 i1) E.u1) (p.mul (p.mul dp1 ip1) E'.u1) :=
      h.mul (h.mul hR_d1 hR_i1_i1') hE1
    simpa [hk1_def, hkp1_def] using h.sub hR_add_mul_d0_i1_d1_i0 h_mul_d1_i1_E
  have hw1 : R w.c1 w'.c1 := by
    have h_inner : R (o.add D.v1 (o.mul D.u1 k0)) (p.add D'.v1 (p.mul D'.u1 kp0)) :=
      h.add hDv1 (h.mul hD1 hR_k0_k0')
    simpa [hw_def, hw'_def] using h.add h_inner (h.mul hD0 hR_k1_k1')
  have hw2 : R w.c2 w'.c2 := by
    simpa [hw_def, hw'_def] using h.add hR_k0_k0' (h.mul hD1 hR_k1_k1')
  have hw3 : R w.c3 w'.c3 := by
    simpa [hw_def, hw'_def] using hR_k1_k1'
  have hQQ : QQ.Rel R (U, w) (U', w') := by
    refine ⟨?_, ?_⟩
    · exact ⟨hU0, hU1, hU2, hU3⟩
    · exact ⟨hw0, hw1, hw2, hw3⟩
  -- Final result
  refine ⟨(U, w), ?_, ?_⟩
  · -- compAdd o D E = some (U, w)
    delta FurioLombardo.Discharge.KvArith.compAdd
    simp [hy_No, g0, g1, No, i0, i1, d0, d1, k0, k1, U, w]
  · -- QQ.Rel R (U, w) b
    rw [hb_eq]
    exact hQQ

theorem Ops.Rel.compDbl (h : Ops.Rel o p R) {f : Sext A} {f' : Sext B} (hf : Sext.Rel R f f')
    {D : Mum A} {D' : Mum B} (hD : Mum.Rel R D D') :
    OptRel (QQ.Rel R) (KvArith.compDbl o f D) (KvArith.compDbl p f' D') := by
  intro b hb
  unfold KvArith.compDbl at hb
  simp at hb
  rcases Option.bind_eq_some_iff.mp hb with ⟨x', hx', hrest⟩
  simp at hrest
  subst hrest
  obtain ⟨hDu0, hDu1, hDv0, hDv1⟩ := hD
  obtain ⟨hff0, hff1, hff2, hff3, hff4, hff5, hff6⟩ := hf
  -- Build the relation for the N expression
  have hN_rel : R (o.add (o.sub (o.mul (o.add D.v0 D.v0) (o.add D.v0 D.v0))
    (o.mul (o.mul (o.add D.v0 D.v0) (o.add D.v1 D.v1)) D.u1))
    (o.mul (o.mul (o.add D.v1 D.v1) (o.add D.v1 D.v1)) D.u0))
    (p.add (p.sub (p.mul (p.add D'.v0 D'.v0) (p.add D'.v0 D'.v0))
    (p.mul (p.mul (p.add D'.v0 D'.v0) (p.add D'.v1 D'.v1)) D'.u1))
    (p.mul (p.mul (p.add D'.v1 D'.v1) (p.add D'.v1 D'.v1)) D'.u0)) := by
    have hb0 : R (o.add D.v0 D.v0) (p.add D'.v0 D'.v0) := h.add hDv0 hDv0
    have hb1 : R (o.add D.v1 D.v1) (p.add D'.v1 D'.v1) := h.add hDv1 hDv1
    have hmul_b0_b0 : R (o.mul (o.add D.v0 D.v0) (o.add D.v0 D.v0))
      (p.mul (p.add D'.v0 D'.v0) (p.add D'.v0 D'.v0)) := h.mul hb0 hb0
    have hmul_b0_b1 : R (o.mul (o.add D.v0 D.v0) (o.add D.v1 D.v1))
      (p.mul (p.add D'.v0 D'.v0) (p.add D'.v1 D'.v1)) := h.mul hb0 hb1
    have hmul_b1_b1 : R (o.mul (o.add D.v1 D.v1) (o.add D.v1 D.v1))
      (p.mul (p.add D'.v1 D'.v1) (p.add D'.v1 D'.v1)) := h.mul hb1 hb1
    have hsub1 : R (o.sub (o.mul (o.add D.v0 D.v0) (o.add D.v0 D.v0))
      (o.mul (o.mul (o.add D.v0 D.v0) (o.add D.v1 D.v1)) D.u1))
      (p.sub (p.mul (p.add D'.v0 D'.v0) (p.add D'.v0 D'.v0))
      (p.mul (p.mul (p.add D'.v0 D'.v0) (p.add D'.v1 D'.v1)) D'.u1)) :=
      h.sub hmul_b0_b0 (h.mul hmul_b0_b1 hDu1)
    have hN_rel' : R (o.mul (o.mul (o.add D.v1 D.v1) (o.add D.v1 D.v1)) D.u0)
      (p.mul (p.mul (p.add D'.v1 D'.v1) (p.add D'.v1 D'.v1)) D'.u0) :=
      h.mul hmul_b1_b1 hDu0
    exact h.add hsub1 hN_rel'
  obtain ⟨y, hy, hRyx'⟩ := h.inv hN_rel hx'
  -- Define abbreviations for the o-side computation
  let g3 : A := f.f3
  let g2 : A := o.sub f.f2 (o.mul D.v1 D.v1)
  let h4 : A := f.f6
  let h3 : A := o.sub f.f5 (o.mul D.u1 h4)
  let h2 : A := o.sub (o.sub f.f4 (o.mul D.u1 h3)) (o.mul D.u0 h4)
  let h1 : A := o.sub (o.sub g3 (o.mul D.u1 h2)) (o.mul D.u0 h3)
  let h0 : A := o.sub (o.sub g2 (o.mul D.u1 h1)) (o.mul D.u0 h2)
  let q1 : A := o.sub h3 (o.mul D.u1 h4)
  let q0 : A := o.sub (o.sub h2 (o.mul D.u1 q1)) (o.mul D.u0 h4)
  let e1 : A := o.sub (o.sub h1 (o.mul D.u1 q0)) (o.mul D.u0 q1)
  let e0 : A := o.sub h0 (o.mul D.u0 q0)
  let b0 : A := o.add D.v0 D.v0
  let b1 : A := o.add D.v1 D.v1
  let N : A := o.add (o.sub (o.mul b0 b0) (o.mul (o.mul b0 b1) D.u1)) (o.mul (o.mul b1 b1) D.u0)
  let Ni : A := y
  let i0 : A := o.mul (o.sub b0 (o.mul b1 D.u1)) Ni
  let i1 : A := o.neg (o.mul b1 Ni)
  let k0 : A := o.sub (o.mul e0 i0) (o.mul (o.mul e1 i1) D.u0)
  let k1 : A := o.sub (o.add (o.mul e0 i1) (o.mul e1 i0)) (o.mul (o.mul e1 i1) D.u1)
  let U : Quart A := ⟨o.mul D.u0 D.u0, o.add (o.mul D.u0 D.u1) (o.mul D.u1 D.u0),
    o.add (o.add D.u0 (o.mul D.u1 D.u1)) D.u0, o.add D.u1 D.u1⟩
  let w : Quart A := ⟨o.add D.v0 (o.mul D.u0 k0), o.add (o.add D.v1 (o.mul D.u1 k0)) (o.mul D.u0 k1),
    o.add k0 (o.mul D.u1 k1), k1⟩
  have h_compDbl_o : KvArith.compDbl o f D = some (U, w) := by
    unfold KvArith.compDbl
    simp [hy, g3, g2, h4, h3, h2, h1, h0, q1, q0, e1, e0, b0, b1, Ni, i0, i1, k0, k1, U, w]
  refine ⟨_, h_compDbl_o, ?_⟩
  -- Build the U relation
  have hU_rel : Quart.Rel R U
    (Quart.mk (p.mul D'.u0 D'.u0) (p.add (p.mul D'.u0 D'.u1) (p.mul D'.u1 D'.u0))
      (p.add (p.add D'.u0 (p.mul D'.u1 D'.u1)) D'.u0) (p.add D'.u1 D'.u1)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact h.mul hDu0 hDu0
    · exact h.add (h.mul hDu0 hDu1) (h.mul hDu1 hDu0)
    · exact h.add (h.add hDu0 (h.mul hDu1 hDu1)) hDu0
    · exact h.add hDu1 hDu1
  -- Define abbreviations for the p-side computation
  let g3' : B := f'.f3
  let g2' : B := p.sub f'.f2 (p.mul D'.v1 D'.v1)
  let h4' : B := f'.f6
  let h3' : B := p.sub f'.f5 (p.mul D'.u1 h4')
  let h2' : B := p.sub (p.sub f'.f4 (p.mul D'.u1 h3')) (p.mul D'.u0 h4')
  let h1' : B := p.sub (p.sub g3' (p.mul D'.u1 h2')) (p.mul D'.u0 h3')
  let h0' : B := p.sub (p.sub g2' (p.mul D'.u1 h1')) (p.mul D'.u0 h2')
  let q1' : B := p.sub h3' (p.mul D'.u1 h4')
  let q0' : B := p.sub (p.sub h2' (p.mul D'.u1 q1')) (p.mul D'.u0 h4')
  let e1' : B := p.sub (p.sub h1' (p.mul D'.u1 q0')) (p.mul D'.u0 q1')
  let e0' : B := p.sub h0' (p.mul D'.u0 q0')
  let b0' : B := p.add D'.v0 D'.v0
  let b1' : B := p.add D'.v1 D'.v1
  let N' : B := p.add (p.sub (p.mul b0' b0') (p.mul (p.mul b0' b1') D'.u1)) (p.mul (p.mul b1' b1') D'.u0)
  let Ni' : B := x'
  let i0' : B := p.mul (p.sub b0' (p.mul b1' D'.u1)) Ni'
  let i1' : B := p.neg (p.mul b1' Ni')
  let k0' : B := p.sub (p.mul e0' i0') (p.mul (p.mul e1' i1') D'.u0)
  let k1' : B := p.sub (p.add (p.mul e0' i1') (p.mul e1' i0')) (p.mul (p.mul e1' i1') D'.u1)
  let U' : Quart B := ⟨p.mul D'.u0 D'.u0, p.add (p.mul D'.u0 D'.u1) (p.mul D'.u1 D'.u0),
    p.add (p.add D'.u0 (p.mul D'.u1 D'.u1)) D'.u0, p.add D'.u1 D'.u1⟩
  let w' : Quart B := ⟨p.add D'.v0 (p.mul D'.u0 k0'), p.add (p.add D'.v1 (p.mul D'.u1 k0')) (p.mul D'.u0 k1'),
    p.add k0' (p.mul D'.u1 k1'), k1'⟩
  -- Build the w relation component by component
  have hw_rel : Quart.Rel R w w' := by
    -- Base relations from hf and hD
    have hg3_rel : R g3 g3' := hff3
    have hg2_rel : R g2 g2' := h.sub hff2 (h.mul hDv1 hDv1)
    have hh4_rel : R h4 h4' := hff6
    have hh3_rel : R h3 h3' := h.sub hff5 (h.mul hDu1 hh4_rel)
    have hh2_rel : R h2 h2' := h.sub (h.sub hff4 (h.mul hDu1 hh3_rel)) (h.mul hDu0 hh4_rel)
    have hh1_rel : R h1 h1' := h.sub (h.sub hg3_rel (h.mul hDu1 hh2_rel)) (h.mul hDu0 hh3_rel)
    have hh0_rel : R h0 h0' := h.sub (h.sub hg2_rel (h.mul hDu1 hh1_rel)) (h.mul hDu0 hh2_rel)
    have hq1_rel : R q1 q1' := h.sub hh3_rel (h.mul hDu1 hh4_rel)
    have hq0_rel : R q0 q0' := h.sub (h.sub hh2_rel (h.mul hDu1 hq1_rel)) (h.mul hDu0 hh4_rel)
    have he1_rel : R e1 e1' := h.sub (h.sub hh1_rel (h.mul hDu1 hq0_rel)) (h.mul hDu0 hq1_rel)
    have he0_rel : R e0 e0' := h.sub hh0_rel (h.mul hDu0 hq0_rel)
    have hb0_rel : R b0 b0' := h.add hDv0 hDv0
    have hb1_rel : R b1 b1' := h.add hDv1 hDv1
    have hNi_rel : R Ni Ni' := hRyx'
    -- i0, i1 relations
    have hi0_rel : R i0 i0' := h.mul (h.sub hb0_rel (h.mul hb1_rel hDu1)) hNi_rel
    have hi1_rel : R i1 i1' := h.neg (h.mul hb1_rel hNi_rel)
    -- k0, k1 relations
    have hk0_rel : R k0 k0' := h.sub (h.mul he0_rel hi0_rel) (h.mul (h.mul he1_rel hi1_rel) hDu0)
    have hk1_rel : R k1 k1' := h.sub (h.add (h.mul he0_rel hi1_rel) (h.mul he1_rel hi0_rel))
      (h.mul (h.mul he1_rel hi1_rel) hDu1)
    -- w component relations
    have hw0_rel : R w.c0 w'.c0 := h.add hDv0 (h.mul hDu0 hk0_rel)
    have hw1_rel : R w.c1 w'.c1 := h.add (h.add hDv1 (h.mul hDu1 hk0_rel)) (h.mul hDu0 hk1_rel)
    have hw2_rel : R w.c2 w'.c2 := h.add hk0_rel (h.mul hDu1 hk1_rel)
    have hw3_rel : R w.c3 w'.c3 := hk1_rel
    exact ⟨hw0_rel, hw1_rel, hw2_rel, hw3_rel⟩
  exact ⟨hU_rel, hw_rel⟩

theorem Ops.Rel.reduce4 (h : Ops.Rel o p R) {f : Sext A} {f' : Sext B} (hf : Sext.Rel R f f')
    {U w : Quart A} {U' w' : Quart B} (hU : Quart.Rel R U U') (hw : Quart.Rel R w w') :
    OptRel (Mum.Rel R) (KvArith.reduce4 o f U w) (KvArith.reduce4 p f' U' w') := by
  intro b hb
  dsimp only [KvArith.reduce4] at hb
  rcases Option.bind_eq_some_iff.mp hb with ⟨li, hli, hrest⟩
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6⟩ := hf
  obtain ⟨hU0, hU1, hU2, hU3⟩ := hU
  obtain ⟨hw0, hw1, hw2, hw3⟩ := hw
  have hg6 : R (o.sub f.f6 (o.mul w.c3 w.c3)) (p.sub f'.f6 (p.mul w'.c3 w'.c3)) :=
    h.sub hf6 (h.mul hw3 hw3)
  rcases h.inv hg6 hli with ⟨li', hli', hRli⟩
  have hreduce4_o : KvArith.reduce4 o f U w = some (let g6 := o.sub f.f6 (o.mul w.c3 w.c3);
    let g5 := o.sub f.f5 (o.add (o.mul w.c2 w.c3) (o.mul w.c3 w.c2));
    let g4 := o.sub f.f4 (o.add (o.add (o.mul w.c1 w.c3) (o.mul w.c3 w.c1)) (o.mul w.c2 w.c2));
    let q1 := o.sub g5 (o.mul g6 U.c3);
    let q0 := o.sub (o.sub g4 (o.mul q1 U.c3)) (o.mul g6 U.c2);
    let s1 := o.mul q1 li';
    let s0 := o.mul q0 li';
    let t1 := o.neg (o.add (o.sub (o.mul w.c3 (o.sub (o.mul s1 s1) s0)) (o.mul w.c2 s1)) w.c1);
    let t0 := o.neg (o.add (o.sub (o.mul w.c3 (o.mul s1 s0)) (o.mul w.c2 s0)) w.c0);
    ⟨s0, s1, t0, t1⟩) := by
    dsimp [KvArith.reduce4]
    rw [hli']
    rfl
  rw [hreduce4_o]
  set a : Mum A := let g6 := o.sub f.f6 (o.mul w.c3 w.c3);
    let g5 := o.sub f.f5 (o.add (o.mul w.c2 w.c3) (o.mul w.c3 w.c2));
    let g4 := o.sub f.f4 (o.add (o.add (o.mul w.c1 w.c3) (o.mul w.c3 w.c1)) (o.mul w.c2 w.c2));
    let q1 := o.sub g5 (o.mul g6 U.c3);
    let q0 := o.sub (o.sub g4 (o.mul q1 U.c3)) (o.mul g6 U.c2);
    let s1 := o.mul q1 li';
    let s0 := o.mul q0 li';
    let t1 := o.neg (o.add (o.sub (o.mul w.c3 (o.sub (o.mul s1 s1) s0)) (o.mul w.c2 s1)) w.c1);
    let t0 := o.neg (o.add (o.sub (o.mul w.c3 (o.mul s1 s0)) (o.mul w.c2 s0)) w.c0);
    ⟨s0, s1, t0, t1⟩ with ha
  refine ⟨a, by rfl, ?_⟩
  have hb_val : (let g6 := p.sub f'.f6 (p.mul w'.c3 w'.c3);
    let g5 := p.sub f'.f5 (p.add (p.mul w'.c2 w'.c3) (p.mul w'.c3 w'.c2));
    let g4 := p.sub f'.f4 (p.add (p.add (p.mul w'.c1 w'.c3) (p.mul w'.c3 w'.c1)) (p.mul w'.c2 w'.c2));
    let q1 := p.sub g5 (p.mul g6 U'.c3);
    let q0 := p.sub (p.sub g4 (p.mul q1 U'.c3)) (p.mul g6 U'.c2);
    let s1 := p.mul q1 li;
    let s0 := p.mul q0 li;
    let t1 := p.neg (p.add (p.sub (p.mul w'.c3 (p.sub (p.mul s1 s1) s0)) (p.mul w'.c2 s1)) w'.c1);
    let t0 := p.neg (p.add (p.sub (p.mul w'.c3 (p.mul s1 s0)) (p.mul w'.c2 s0)) w'.c0);
    ⟨s0, s1, t0, t1⟩) = b := by
    simpa using hrest
  rw [← hb_val]
  dsimp [a, Mum.Rel]
  -- Goal: R s0_o s0_p ∧ R s1_o s1_p ∧ R t0_o t0_p ∧ R t1_o t1_p
  have hg5 : R (o.sub f.f5 (o.add (o.mul w.c2 w.c3) (o.mul w.c3 w.c2)))
      (p.sub f'.f5 (p.add (p.mul w'.c2 w'.c3) (p.mul w'.c3 w'.c2))) :=
    h.sub hf5 (h.add (h.mul hw2 hw3) (h.mul hw3 hw2))
  have hg4 : R (o.sub f.f4 (o.add (o.add (o.mul w.c1 w.c3) (o.mul w.c3 w.c1)) (o.mul w.c2 w.c2)))
      (p.sub f'.f4 (p.add (p.add (p.mul w'.c1 w'.c3) (p.mul w'.c3 w'.c1)) (p.mul w'.c2 w'.c2))) :=
    h.sub hf4 (h.add (h.add (h.mul hw1 hw3) (h.mul hw3 hw1)) (h.mul hw2 hw2))
  have hq1 : R (o.sub (o.sub f.f5 (o.add (o.mul w.c2 w.c3) (o.mul w.c3 w.c2)))
      (o.mul (o.sub f.f6 (o.mul w.c3 w.c3)) U.c3))
      (p.sub (p.sub f'.f5 (p.add (p.mul w'.c2 w'.c3) (p.mul w'.c3 w'.c2)))
      (p.mul (p.sub f'.f6 (p.mul w'.c3 w'.c3)) U'.c3)) :=
    h.sub hg5 (h.mul hg6 hU3)
  -- For hq0, use apply to avoid writing the full type
  have hq0 : R (o.sub (o.sub (o.sub f.f4 (o.add (o.add (o.mul w.c1 w.c3) (o.mul w.c3 w.c1)) (o.mul w.c2 w.c2)))
      (o.mul (o.sub (o.sub f.f5 (o.add (o.mul w.c2 w.c3) (o.mul w.c3 w.c2)))
      (o.mul (o.sub f.f6 (o.mul w.c3 w.c3)) U.c3)) U.c3))
    (o.mul (o.sub f.f6 (o.mul w.c3 w.c3)) U.c2))
    (p.sub (p.sub (p.sub f'.f4 (p.add (p.add (p.mul w'.c1 w'.c3) (p.mul w'.c3 w'.c1)) (p.mul w'.c2 w'.c2)))
      (p.mul (p.sub (p.sub f'.f5 (p.add (p.mul w'.c2 w'.c3) (p.mul w'.c3 w'.c2)))
      (p.mul (p.sub f'.f6 (p.mul w'.c3 w'.c3)) U'.c3)) U'.c3))
    (p.mul (p.sub f'.f6 (p.mul w'.c3 w'.c3)) U'.c2)) := by
    apply h.sub
    · apply h.sub
      · exact hg4
      · apply h.mul
        · exact hq1
        · exact hU3
    · exact h.mul hg6 hU2
  have hs1 : R (o.mul (o.sub (o.sub f.f5 (o.add (o.mul w.c2 w.c3) (o.mul w.c3 w.c2)))
      (o.mul (o.sub f.f6 (o.mul w.c3 w.c3)) U.c3)) li')
      (p.mul (p.sub (p.sub f'.f5 (p.add (p.mul w'.c2 w'.c3) (p.mul w'.c3 w'.c2)))
      (p.mul (p.sub f'.f6 (p.mul w'.c3 w'.c3)) U'.c3)) li) :=
    h.mul hq1 hRli
  have hs0 := h.mul hq0 hRli
  refine ⟨hs0, hs1, ?_, ?_⟩
  · apply h.neg
    apply h.add
    · apply h.sub
      · apply h.mul
        · exact hw3
        · apply h.mul
          · exact hs1
          · exact hs0
      · apply h.mul
        · exact hw2
        · exact hs0
    · exact hw0
  · apply h.neg
    apply h.add
    · apply h.sub
      · apply h.mul
        · exact hw3
        · apply h.sub
          · apply h.mul
            · exact hs1
            · exact hs1
          · exact hs0
      · apply h.mul
        · exact hw2
        · exact hs1
    · exact hw1

theorem Ops.Rel.cantorAdd (h : Ops.Rel o p R) {f : Sext A} {f' : Sext B} (hf : Sext.Rel R f f')
    {D E : Mum A} {D' E' : Mum B} (hD : Mum.Rel R D D') (hE : Mum.Rel R E E') :
    OptRel (Mum.Rel R) (KvArith.cantorAdd o f D E) (KvArith.cantorAdd p f' D' E') :=
  OptRel.bind (h.compAdd hD hE) fun _ _ hx => h.reduce4 hf hx.1 hx.2

theorem Ops.Rel.cantorDbl (h : Ops.Rel o p R) {f : Sext A} {f' : Sext B} (hf : Sext.Rel R f f')
    {D : Mum A} {D' : Mum B} (hD : Mum.Rel R D D') :
    OptRel (Mum.Rel R) (KvArith.cantorDbl o f D) (KvArith.cantorDbl p f' D') :=
  OptRel.bind (h.compDbl hf hD) fun _ _ hx => h.reduce4 hf hx.1 hx.2

theorem Ops.Rel.revD (h : Ops.Rel o p R) {D : Mum A} {D' : Mum B} (hD : Mum.Rel R D D') :
    OptRel (Mum.Rel R) (KvArith.revD o D) (KvArith.revD p D') := by
  intro b hb
  -- Unfold revD to expose the bind structure
  dsimp [KvArith.revD] at hb
  -- hb : (Option.bind (p.inv D'.u0) (fun p0 => ...)) = some b
  rcases Option.bind_eq_some_iff.mp hb with ⟨b0, h_inv, h_rest⟩
  -- h_inv : p.inv D'.u0 = some b0
  -- h_rest : (let p1 := p.mul D'.u1 b0; ...) = some b
  -- From h.inv and hD.1, get the o inverse
  rcases h.inv hD.1 h_inv with ⟨a0, ha0_inv, ha0_rel⟩
  -- ha0_inv : o.inv D.u0 = some a0
  -- ha0_rel : R a0 b0
  -- Extract the components of b from h_rest
  have h_mum_eq : (let p1 := p.mul D'.u1 b0
                   let t1 := p.sub (p.mul D'.v0 (p.sub (p.mul p1 p1) b0)) (p.mul D'.v1 p1)
                   let t0 := p.sub (p.mul D'.v0 (p.mul p1 b0)) (p.mul D'.v1 b0)
                   ⟨b0, p1, t0, t1⟩ : Mum B) = b := by
    simpa using h_rest
  have hb_u0 : b.u0 = b0 := by
    have := congrArg Mum.u0 h_mum_eq
    simpa using this.symm
  have hb_u1 : b.u1 = p.mul D'.u1 b0 := by
    have := congrArg Mum.u1 h_mum_eq
    simpa using this.symm
  have hb_v0 : b.v0 = p.sub (p.mul D'.v0 (p.mul (p.mul D'.u1 b0) b0)) (p.mul D'.v1 b0) := by
    have := congrArg Mum.v0 h_mum_eq
    simpa using this.symm
  have hb_v1 : b.v1 = p.sub (p.mul D'.v0 (p.sub (p.mul (p.mul D'.u1 b0) (p.mul D'.u1 b0)) b0)) (p.mul D'.v1 (p.mul D'.u1 b0)) := by
    have := congrArg Mum.v1 h_mum_eq
    simpa using this.symm
  -- Now build the related Mum a
  set a1 := o.mul D.u1 a0 with ha1_def
  set av0 := o.sub (o.mul D.v0 (o.mul a1 a0)) (o.mul D.v1 a0) with hav0_def
  set av1 := o.sub (o.mul D.v0 (o.sub (o.mul a1 a1) a0)) (o.mul D.v1 a1) with hav1_def
  use ⟨a0, a1, av0, av1⟩
  constructor
  · -- revD o D = some ⟨a0, a1, av0, av1⟩
    dsimp [KvArith.revD]
    simp [ha0_inv, ha1_def, hav0_def, hav1_def]
  · -- Mum.Rel R ⟨a0, a1, av0, av1⟩ b
    have ha1_rel : R a1 (p.mul D'.u1 b0) := by
      rw [ha1_def]
      exact h.mul hD.2.1 ha0_rel
    have h_sq_rel : R (o.mul a1 a1) (p.mul (p.mul D'.u1 b0) (p.mul D'.u1 b0)) := by
      rw [ha1_def]
      exact h.mul (h.mul hD.2.1 ha0_rel) (h.mul hD.2.1 ha0_rel)
    have h_sub1_rel : R (o.sub (o.mul a1 a1) a0) (p.sub (p.mul (p.mul D'.u1 b0) (p.mul D'.u1 b0)) b0) := by
      exact h.sub h_sq_rel ha0_rel
    have hav0_rel : R av0 (p.sub (p.mul D'.v0 (p.mul (p.mul D'.u1 b0) b0)) (p.mul D'.v1 b0)) := by
      rw [hav0_def]
      exact h.sub (h.mul hD.2.2.1 (h.mul ha1_rel ha0_rel)) (h.mul hD.2.2.2 ha0_rel)
    have hav1_rel : R av1 (p.sub (p.mul D'.v0 (p.sub (p.mul (p.mul D'.u1 b0) (p.mul D'.u1 b0)) b0)) (p.mul D'.v1 (p.mul D'.u1 b0))) := by
      rw [hav1_def]
      exact h.sub (h.mul hD.2.2.1 h_sub1_rel) (h.mul hD.2.2.2 ha1_rel)
    have h_rel : Mum.Rel R ⟨a0, a1, av0, av1⟩ b := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [hb_u0] using ha0_rel
      · simpa [hb_u1] using ha1_rel
      · simpa [hb_v0] using hav0_rel
      · simpa [hb_v1] using hav1_rel
    exact h_rel

theorem Ops.Rel.mumNeg (h : Ops.Rel o p R) {D : Mum A} {D' : Mum B} (hD : Mum.Rel R D D') :
    Mum.Rel R (Mum.neg o D) (Mum.neg p D') := by
  obtain ⟨h0, h1, h2, h3⟩ := hD
  exact ⟨h0, h1, h.neg h2, h.neg h3⟩

theorem Ops.Rel.shift (h : Ops.Rel o p R) {a : A} {b : B} (ha : R a b) {D : Mum A} {D' : Mum B}
    (hD : Mum.Rel R D D') : Mum.Rel R (Mum.shift o a D) (Mum.shift p b D') := by
  obtain ⟨h0, h1, h2, h3⟩ := hD
  unfold Mum.shift
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply h.add
    · apply h.add
      · exact h0
      · apply h.mul ha h1
    · apply h.mul ha ha
  · apply h.add
    · exact h1
    · apply h.add ha ha
  · apply h.add
    · exact h2
    · apply h.mul ha h3
  · exact h3

end Rel

/-! ## The class statements over a field -/

section Field

open FurioLombardo.Discharge.R7

variable {K : Type*} [Field K]

/-- `u = X² + u₁X + u₀`. -/
noncomputable def Mum.u (D : Mum K) : K[X] := X ^ 2 + C D.u1 * X + C D.u0

/-- `v = v₁X + v₀`. -/
noncomputable def Mum.v (D : Mum K) : K[X] := C D.v1 * X + C D.v0

theorem Mum.u_monic (D : Mum K) : D.u.Monic := by
  have h_deg : (C D.u1 * X + C D.u0).degree < (X ^ 2 : K[X]).degree := by
    calc
      (C D.u1 * X + C D.u0).degree ≤ 1 := degree_linear_le
      _ < (X ^ 2 : K[X]).degree := by
        simp
  have h_lead : ((C D.u1 * X + C D.u0) + (X ^ 2 : K[X])).leadingCoeff = (X ^ 2 : K[X]).leadingCoeff :=
    leadingCoeff_add_of_degree_lt h_deg
  unfold Mum.u Monic
  calc
    (X ^ 2 + C D.u1 * X + C D.u0).leadingCoeff = (X ^ 2 + (C D.u1 * X + C D.u0)).leadingCoeff := by
      rw [add_assoc]
    _ = ((C D.u1 * X + C D.u0) + X ^ 2).leadingCoeff := by rw [add_comm]
    _ = (X ^ 2 : K[X]).leadingCoeff := h_lead
    _ = 1 := leadingCoeff_X_pow 2

theorem Mum.u_natDegree (D : Mum K) : D.u.natDegree = 2 := by
  have h : D.u = C (1 : K) * X ^ 2 + C D.u1 * X + C D.u0 := by
    dsimp [Mum.u]
    simp
  rw [h]
  apply natDegree_quadratic
  simp

/-- The polynomial of a sextic. -/
noncomputable def Sext.poly (f : Sext K) : K[X] :=
  C f.f0 + C f.f1 * X + C f.f2 * X ^ 2 + C f.f3 * X ^ 3 + C f.f4 * X ^ 4 + C f.f5 * X ^ 5 +
    C f.f6 * X ^ 6

/-- The coefficients of a polynomial of degree at most 6. -/
noncomputable def Sext.ofPoly (fp : K[X]) : Sext K :=
  ⟨fp.coeff 0, fp.coeff 1, fp.coeff 2, fp.coeff 3, fp.coeff 4, fp.coeff 5, fp.coeff 6⟩

theorem Sext.poly_ofPoly {fp : K[X]} (h : fp.natDegree ≤ 6) : (Sext.ofPoly fp).poly = fp := by
  ext n
  simp only [Sext.poly, Sext.ofPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n < 7
  · interval_cases n <;> simp
  · have hcoeff : fp.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    have h2 : n ≠ 2 := by omega
    have h3 : n ≠ 3 := by omega
    have h4 : n ≠ 4 := by omega
    have h5 : n ≠ 5 := by omega
    have h6 : n ≠ 6 := by omega
    simp [hcoeff, h0, h1, h2, h3, h4, h5, h6]

/-- The pair lies on `y² = fp`: `u ∣ fp - v²`. -/
def Mum.OnCurve (fp : K[X]) (D : Mum K) : Prop := D.u ∣ fp - D.v ^ 2

/-- The class of `⟨u, Y - v⟩`. -/
noncomputable def Mum.cls (fp : K[X]) [GoodSextic fp] (D : Mum K) : ClassGroup (CoordRing fp) :=
  ClassGroup.mk0 (mumford0 fp D.u_monic.ne_zero D.v)

/-- The monic quartic `X⁴ + c₃X³ + c₂X² + c₁X + c₀`. -/
noncomputable def Quart.mpoly (U : Quart K) : K[X] :=
  X ^ 4 + C U.c3 * X ^ 3 + C U.c2 * X ^ 2 + C U.c1 * X + C U.c0

/-- The cubic `c₃X³ + c₂X² + c₁X + c₀`. -/
noncomputable def Quart.cpoly (w : Quart K) : K[X] :=
  C w.c3 * X ^ 3 + C w.c2 * X ^ 2 + C w.c1 * X + C w.c0

theorem Quart.mpoly_monic (U : Quart K) : U.mpoly.Monic := by
  unfold Quart.mpoly
  monicity!

theorem Quart.mpoly_natDegree (U : Quart K) : U.mpoly.natDegree = 4 := by
  unfold Quart.mpoly
  compute_degree!

theorem Quart.cpoly_natDegree_le (w : Quart K) : w.cpoly.natDegree ≤ 3 := by
  unfold Quart.cpoly
  compute_degree

theorem Sext.ofPoly_poly (s : Sext K) : Sext.ofPoly s.poly = s := by
  cases s
  simp [Sext.ofPoly, Sext.poly, coeff_X_pow, coeff_X, coeff_C]

theorem Sext.poly_inj {f g : Sext K} (h : f.poly = g.poly) : f = g := by
  rw [← Sext.ofPoly_poly f, ← Sext.ofPoly_poly g, h]

theorem Quart.mpoly_ne_zero (U : Quart K) : U.mpoly ≠ 0 := U.mpoly_monic.ne_zero

/-- A quotient of degree at most 2, written out. -/
theorem eq_quad_of_natDegree_le {Q : K[X]} (h : Q.natDegree ≤ 2) :
    Q = C (Q.coeff 2) * X ^ 2 + C (Q.coeff 1) * X + C (Q.coeff 0) := by
  conv_lhs => rw [Q.as_sum_range' 3 (by omega)]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    ← C_mul_X_pow_eq_monomial, pow_zero, mul_one, pow_one]
  ring

/-- **The reduction step** over a field: `[⟨U, Y - w⟩] = [D'']`. -/
theorem reduce4_spec (fp : K[X]) [GoodSextic fp] {U w : Quart K} {D'' : Mum K}
    (hdvd : U.mpoly ∣ fp - w.cpoly ^ 2)
    (h : reduce4 (fieldOps K) (Sext.ofPoly fp) U w = some D'') :
    D''.OnCurve fp ∧ ClassGroup.mk0 (mumford0 fp U.mpoly_ne_zero w.cpoly) = D''.cls fp := by
  have hfp : (Sext.ofPoly fp).poly = fp := Sext.poly_ofPoly (GoodSextic.natDegree_eq (f := fp)).le
  dsimp only [reduce4] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨li, hli, hD⟩
  obtain ⟨hg6, rfl⟩ := fieldOps_inv_eq_some hli
  simp only [Option.pure_def, Option.some.injEq] at hD
  subst hD
  clear h hli
  simp only [fieldOps] at hg6 ⊢
  set f := Sext.ofPoly fp with hf
  set g6 := f.f6 - w.c3 * w.c3 with hg6d
  set q1 := f.f5 - (w.c2 * w.c3 + w.c3 * w.c2) - g6 * U.c3 with hq1d
  set q0 := f.f4 - (w.c1 * w.c3 + w.c3 * w.c1 + w.c2 * w.c2) - q1 * U.c3 - g6 * U.c2 with hq0d
  set s1 := q1 * g6⁻¹ with hs1
  set s0 := q0 * g6⁻¹ with hs0
  have hs1' : g6 * s1 = q1 := by rw [hs1]; field_simp
  have hs0' : g6 * s0 = q0 := by rw [hs0]; field_simp
  clear_value s1 s0
  set D : Mum K := ⟨s0, s1, -(w.c3 * (s1 * s0) - w.c2 * s0 + w.c0),
    -(w.c3 * (s1 * s1 - s0) - w.c2 * s1 + w.c1)⟩ with hD
  -- the quotient `Q = (f - w²) / U`, of degree at most 2
  obtain ⟨Q, hQ⟩ := hdvd
  have hdeg : (fp - w.cpoly ^ 2).natDegree ≤ 6 := by
    refine (natDegree_sub_le _ _).trans (max_le (GoodSextic.natDegree_eq (f := fp)).le ?_)
    exact natDegree_pow_le.trans (by have := w.cpoly_natDegree_le; omega)
  have hQdeg : Q.natDegree ≤ 2 := by
    by_cases hQ0 : Q = 0
    · simp [hQ0]
    · have := U.mpoly_monic.natDegree_mul' hQ0
      rw [← hQ, U.mpoly_natDegree] at this
      omega
  obtain ⟨Q2, Q1, Q0, hQe⟩ : ∃ a b c : K, Q = C a * X ^ 2 + C b * X + C c :=
    ⟨_, _, _, eq_quad_of_natDegree_le hQdeg⟩
  subst hQe
  -- its coefficients from the top three coefficients of `f - w²`
  have e1 : (Sext.mk (f.f0 - w.c0 * w.c0) (f.f1 - (w.c0 * w.c1 + w.c1 * w.c0))
      (f.f2 - (w.c0 * w.c2 + w.c1 * w.c1 + w.c2 * w.c0))
      (f.f3 - (w.c0 * w.c3 + w.c1 * w.c2 + w.c2 * w.c1 + w.c3 * w.c0))
      (f.f4 - (w.c1 * w.c3 + w.c3 * w.c1 + w.c2 * w.c2)) (f.f5 - (w.c2 * w.c3 + w.c3 * w.c2))
      (f.f6 - w.c3 * w.c3) : Sext K).poly = fp - w.cpoly ^ 2 := by
    rw [← hfp]
    simp only [Sext.poly, Quart.cpoly, map_sub, map_add, map_mul]
    ring
  have e2 : (Sext.mk (U.c0 * Q0) (U.c1 * Q0 + U.c0 * Q1) (U.c2 * Q0 + U.c1 * Q1 + U.c0 * Q2)
      (U.c3 * Q0 + U.c2 * Q1 + U.c1 * Q2) (Q0 + U.c3 * Q1 + U.c2 * Q2) (Q1 + U.c3 * Q2) Q2 :
      Sext K).poly = U.mpoly * (C Q2 * X ^ 2 + C Q1 * X + C Q0) := by
    simp only [Sext.poly, Quart.mpoly, map_add, map_mul]
    ring
  have key := Sext.poly_inj (e1.trans (hQ.trans e2.symm))
  simp only [Sext.mk.injEq] at key
  obtain ⟨-, -, -, -, e4, e5, e6⟩ := key
  clear_value f g6 q1 q0
  have hQ2 : Q2 = g6 := by rw [hg6d]; exact e6.symm
  have hQ1 : Q1 = q1 := by rw [hq1d, ← hQ2]; linear_combination -e5
  have hQ0 : Q0 = q0 := by rw [hq0d, ← hQ1, ← hQ2]; linear_combination -e4
  -- `f - w² = U (g6 u'')`
  have hq : C Q2 * X ^ 2 + C Q1 * X + C Q0 = C g6 * D.u := by
    rw [hQ2, hQ1, hQ0, ← hs1', ← hs0']
    simp only [Mum.u, hD, map_mul]
    ring
  rw [hq] at hQ
  have hwv : D.v + w.cpoly = (C w.c3 * X + C (w.c2 - w.c3 * s1)) * D.u := by
    simp only [Mum.u, Mum.v, hD, Quart.cpoly, map_add, map_sub, map_mul, map_neg]
    ring
  refine ⟨?_, ?_⟩
  · -- `u'' ∣ f - v''²`
    have e : fp - D.v ^ 2 = (fp - w.cpoly ^ 2) + (w.cpoly - D.v) * (D.v + w.cpoly) := by ring
    rw [Mum.OnCurve, e, hQ, hwv]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
      (dvd_mul_of_dvd_right (dvd_mul_left _ _) _)
  · -- the line step `w² - f = -g6 U u''`, then `-w ≡ v'' mod u''`
    have hsq : w.cpoly ^ 2 - fp = C (-g6) * (U.mpoly * D.u) := by
      rw [map_neg]
      linear_combination -hQ
    rw [mk0_mumford_eq_of_sq_sub fp (neg_ne_zero.mpr hg6) U.mpoly_ne_zero D.u_monic.ne_zero hsq,
      Mum.cls]
    exact (mk0_mumford_congr fp D.u_monic.ne_zero ⟨_, by rw [sub_neg_eq_add, hwv, mul_comm]⟩).symm

/-- `g i ≡ 1 mod u'` for the inverse `i` of `g = g₁X + g₀` modulo `u' = X² + e₁X + e₀` by the
norm `N = g₀² - g₀g₁e₁ + g₁²e₀`. -/
theorem inv_mod_quad {g0 g1 e0 e1 Ni : K}
    (hN : (g0 * g0 - g0 * g1 * e1 + g1 * g1 * e0) * Ni = 1) :
    (C g1 * X + C g0) * (C (-(g1 * Ni)) * X + C ((g0 - g1 * e1) * Ni)) - 1 =
      (X ^ 2 + C e1 * X + C e0) * C (g1 * (-(g1 * Ni))) := by
  have hC := congrArg C hN
  simp only [map_mul, map_add, map_sub, map_one] at hC
  simp only [map_mul, map_sub, map_neg]
  linear_combination hC

/-- The product `(d₁X + d₀)(i₁X + i₀)` reduced modulo `X² + e₁X + e₀`. -/
theorem mul_mod_quad (d0 d1 i0 i1 e0 e1 : K) :
    C (d0 * i1 + d1 * i0 - d1 * i1 * e1) * X + C (d0 * i0 - d1 * i1 * e0) -
        (C d1 * X + C d0) * (C i1 * X + C i0) =
      (X ^ 2 + C e1 * X + C e0) * C (-(d1 * i1)) := by
  simp only [map_mul, map_add, map_sub, map_neg]
  ring

/-- **The composition** of two pairs with coprime `u`'s over a field. -/
theorem compAdd_spec {D E : Mum K} {U w : Quart K}
    (h : compAdd (fieldOps K) D E = some (U, w)) :
    U.mpoly = D.u * E.u ∧ D.u ∣ w.cpoly - D.v ∧ E.u ∣ w.cpoly - E.v ∧ IsCoprime D.u E.u := by
  dsimp only [compAdd] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨Ni, hNi, hUw⟩
  obtain ⟨hN, rfl⟩ := fieldOps_inv_eq_some hNi
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hUw
  obtain ⟨rfl, rfl⟩ := hUw
  clear h hNi
  simp only [fieldOps] at hN ⊢
  set g0 := D.u0 - E.u0 with hg0
  set g1 := D.u1 - E.u1 with hg1
  set N := g0 * g0 - g0 * g1 * E.u1 + g1 * g1 * E.u0 with hNd
  have hNN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  set i0 := (g0 - g1 * E.u1) * N⁻¹ with hi0
  set i1 := -(g1 * N⁻¹) with hi1
  set d0 := E.v0 - D.v0 with hd0
  set d1 := E.v1 - D.v1 with hd1
  set k0 := d0 * i0 - d1 * i1 * E.u0 with hk0
  set k1 := d0 * i1 + d1 * i0 - d1 * i1 * E.u1 with hk1
  -- the polynomials
  have hgi := inv_mod_quad (g0 := g0) (g1 := g1) (e0 := E.u0) (e1 := E.u1) hNN
  rw [← hi0, ← hi1] at hgi
  have hki := mul_mod_quad d0 d1 i0 i1 E.u0 E.u1
  rw [← hk0, ← hk1] at hki
  have hEu : E.u = X ^ 2 + C E.u1 * X + C E.u0 := rfl
  have hDu : D.u = E.u + (C g1 * X + C g0) := by
    simp only [Mum.u, hg0, hg1, map_sub]; ring
  have hd : E.v - D.v = C d1 * X + C d0 := by
    simp only [Mum.v, hd0, hd1, map_sub]; ring
  have hw : (Quart.cpoly ⟨D.v0 + D.u0 * k0, D.v1 + D.u1 * k0 + D.u0 * k1, k0 + D.u1 * k1, k1⟩ : K[X]) =
      D.v + D.u * (C k1 * X + C k0) := by
    simp only [Quart.cpoly, Mum.u, Mum.v, map_add, map_mul]; ring
  rw [hw]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Quart.mpoly, Mum.u, map_add, map_mul]; ring
  · exact ⟨C k1 * X + C k0, by ring⟩
  · -- `w - v' = u' k + (g k - d)`, `g k - d = g (k - d i) + d (g i - 1)`
    rw [← hEu] at hgi hki
    have e : D.v + D.u * (C k1 * X + C k0) - E.v =
        E.u * (C k1 * X + C k0) + (C g1 * X + C g0) *
          ((C k1 * X + C k0) - (C d1 * X + C d0) * (C i1 * X + C i0)) +
        (C d1 * X + C d0) * ((C g1 * X + C g0) * (C i1 * X + C i0) - 1) := by
      rw [hDu, ← hd]; ring
    rw [e, hki, hgi]
    exact dvd_add (dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _))
      (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  · -- `g i + u' (-g₁ i₁) = 1`, and `u = u' + g`
    rw [← hEu] at hgi
    have hcop : IsCoprime (C g1 * X + C g0) E.u :=
      ⟨C i1 * X + C i0, -C (g1 * i1), by linear_combination hgi⟩
    rw [hDu, add_comm]
    simpa only [mul_one] using hcop.add_mul_left_left 1
/-- `u u'` divides `f - w²` when `w` agrees with `v`, `v'` modulo the coprime `u`, `u'`. -/
theorem dvd_sub_sq_of_dvd {fp w u v : K[X]} (h1 : u ∣ fp - v ^ 2) (h2 : u ∣ w - v) :
    u ∣ fp - w ^ 2 := by
  have e : fp - w ^ 2 = (fp - v ^ 2) - (w - v) * (w + v) := by ring
  rw [e]
  exact dvd_sub h1 (dvd_mul_of_dvd_left h2 _)

/-- The class of `⟨u, Y - v⟩` does not see how `u ≠ 0` is proved. -/
theorem mk0_mumford_of_eq (fp : K[X]) [GoodSextic fp] {u u' : K[X]} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (h : u = u') (v : K[X]) :
    ClassGroup.mk0 (mumford0 fp hu v) = ClassGroup.mk0 (mumford0 fp hu' v) := by
  subst h
  rfl

/-- The quotient of `f - v²` by `u` from the top coefficients (generic identity). -/
theorem sextic_div_quad (f : Sext K) {u0 u1 v0 v1 h0 h1 h2 h3 h4 : K} (e4 : h4 = f.f6)
    (e3 : h3 = f.f5 - u1 * h4) (e2 : h2 = f.f4 - u1 * h3 - u0 * h4)
    (e1 : h1 = f.f3 - u1 * h2 - u0 * h3) (e0 : h0 = f.f2 - v1 * v1 - u1 * h1 - u0 * h2) :
    f.poly - (C v1 * X + C v0) ^ 2 - (X ^ 2 + C u1 * X + C u0) *
        (C h4 * X ^ 4 + C h3 * X ^ 3 + C h2 * X ^ 2 + C h1 * X + C h0) =
      C (f.f1 - (v0 * v1 + v1 * v0) - u1 * h0 - u0 * h1) * X + C (f.f0 - v0 * v0 - u0 * h0) := by
  subst e0 e1 e2 e3 e4
  simp only [Sext.poly, map_add, map_sub, map_mul]
  ring

/-- A quartic modulo `X² + u₁X + u₀` (generic identity). -/
theorem quartic_mod_quad {u0 u1 h0 h1 h2 h3 h4 q0 q1 e0 e1 : K} (eq1 : q1 = h3 - u1 * h4)
    (eq0 : q0 = h2 - u1 * q1 - u0 * h4) (ee1 : e1 = h1 - u1 * q0 - u0 * q1)
    (ee0 : e0 = h0 - u0 * q0) :
    (C h4 * X ^ 4 + C h3 * X ^ 3 + C h2 * X ^ 2 + C h1 * X + C h0) - (C e1 * X + C e0) =
      (X ^ 2 + C u1 * X + C u0) * (C h4 * X ^ 2 + C q1 * X + C q0) := by
  subst ee0 ee1 eq0 eq1
  simp only [map_sub, map_mul]
  ring

/-- **The composition of a pair with itself** over a field. -/
theorem compDbl_spec (fp : K[X]) [GoodSextic fp] {D : Mum K} {U w : Quart K} (hD : D.OnCurve fp)
    (h : compDbl (fieldOps K) (Sext.ofPoly fp) D = some (U, w)) :
    U.mpoly = D.u * D.u ∧ D.u ∣ w.cpoly - D.v ∧ D.u * D.u ∣ fp - w.cpoly ^ 2 := by
  have hfp : (Sext.ofPoly fp).poly = fp := Sext.poly_ofPoly (GoodSextic.natDegree_eq (f := fp)).le
  dsimp only [compDbl] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨Ni, hNi, hUw⟩
  obtain ⟨hN, rfl⟩ := fieldOps_inv_eq_some hNi
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hUw
  obtain ⟨rfl, rfl⟩ := hUw
  clear h hNi
  simp only [fieldOps] at hN ⊢
  set f := Sext.ofPoly fp with hf
  set h4 := f.f6 with hh4
  set h3 := f.f5 - D.u1 * h4 with hh3
  set h2 := f.f4 - D.u1 * h3 - D.u0 * h4 with hh2
  set h1 := f.f3 - D.u1 * h2 - D.u0 * h3 with hh1
  set h0 := f.f2 - D.v1 * D.v1 - D.u1 * h1 - D.u0 * h2 with hh0
  set q1 := h3 - D.u1 * h4 with hq1
  set q0 := h2 - D.u1 * q1 - D.u0 * h4 with hq0
  set e1 := h1 - D.u1 * q0 - D.u0 * q1 with he1
  set e0 := h0 - D.u0 * q0 with he0
  set b0 := D.v0 + D.v0 with hb0
  set b1 := D.v1 + D.v1 with hb1
  set N := b0 * b0 - b0 * b1 * D.u1 + b1 * b1 * D.u0 with hNd
  have hNN : N * N⁻¹ = 1 := mul_inv_cancel₀ hN
  set i0 := (b0 - b1 * D.u1) * N⁻¹ with hi0
  set i1 := -(b1 * N⁻¹) with hi1
  set k0 := e0 * i0 - e1 * i1 * D.u0 with hk0
  set k1 := e0 * i1 + e1 * i0 - e1 * i1 * D.u1 with hk1
  have hgi := inv_mod_quad (g0 := b0) (g1 := b1) (e0 := D.u0) (e1 := D.u1) hNN
  rw [← hi0, ← hi1] at hgi
  have hki := mul_mod_quad e0 e1 i0 i1 D.u0 D.u1
  rw [← hk0, ← hk1] at hki
  have hDu : D.u = X ^ 2 + C D.u1 * X + C D.u0 := rfl
  rw [← hDu] at hgi hki
  clear_value k0 k1 i0 i1 N b0 b1 e0 e1 q0 q1 h0 h1 h2 h3 h4
  -- `f - v² = u H` exactly
  set H := C h4 * X ^ 4 + C h3 * X ^ 3 + C h2 * X ^ 2 + C h1 * X + C h0 with hH
  have hR := sextic_div_quad f (u0 := D.u0) (u1 := D.u1) (v0 := D.v0) (v1 := D.v1) hh4 hh3 hh2 hh1
    hh0
  rw [hfp, ← hDu, ← hH] at hR
  have hexact : fp - D.v ^ 2 = D.u * H := by
    have hdv : D.u ∣ C (f.f1 - (D.v0 * D.v1 + D.v1 * D.v0) - D.u1 * h0 - D.u0 * h1) * X +
        C (f.f0 - D.v0 * D.v0 - D.u0 * h0) := by
      rw [← hR]
      exact dvd_sub hD (dvd_mul_right _ _)
    have h0' := Polynomial.eq_zero_of_dvd_of_degree_lt hdv (by
      rw [degree_eq_natDegree D.u_monic.ne_zero, D.u_natDegree]
      exact (degree_linear_le).trans_lt (by exact_mod_cast (by norm_num : (1 : ℕ) < 2)))
    rw [h0'] at hR
    exact sub_eq_zero.mp hR
  have hHe := quartic_mod_quad (u0 := D.u0) (u1 := D.u1) hq1 hq0 he1 he0
  rw [← hH, ← hDu] at hHe
  have hb : C b1 * X + C b0 = D.v + D.v := by
    simp only [Mum.v, hb0, hb1, map_add]; ring
  have hw : (Quart.cpoly ⟨D.v0 + D.u0 * k0, D.v1 + D.u1 * k0 + D.u0 * k1, k0 + D.u1 * k1, k1⟩ : K[X]) =
      D.v + D.u * (C k1 * X + C k0) := by
    simp only [Quart.cpoly, Mum.u, Mum.v, map_add, map_mul]; ring
  rw [hw]
  refine ⟨?_, ⟨C k1 * X + C k0, by ring⟩, ?_⟩
  · simp only [Quart.mpoly, Mum.u, map_add, map_mul]; ring
  · -- `f - w² = u (H - b k) - u² k²` and `u ∣ H - b k`
    set k := C k1 * X + C k0
    set η := C e1 * X + C e0
    set i := C i1 * X + C i0
    have hdk : D.u ∣ H - (D.v + D.v) * k := by
      have e : H - (D.v + D.v) * k = (H - η) - η * ((D.v + D.v) * i - 1) -
          (D.v + D.v) * (k - η * i) := by ring
      rw [e, ← hb, hHe, hgi, hki]
      exact dvd_sub (dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _))
        (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
    obtain ⟨s, hs⟩ := hdk
    refine ⟨s - k ^ 2, ?_⟩
    have e : fp - (D.v + D.u * k) ^ 2 = D.u * (H - (D.v + D.v) * k) - D.u * D.u * k ^ 2 := by
      linear_combination hexact
    rw [e, hs]
    ring

/-- **Cantor's addition** over a field. -/
theorem cantorAdd_spec (fp : K[X]) [GoodSextic fp] {D E D'' : Mum K} (hD : D.OnCurve fp)
    (hE : E.OnCurve fp) (h : cantorAdd (fieldOps K) (Sext.ofPoly fp) D E = some D'') :
    D''.OnCurve fp ∧ D.cls fp * E.cls fp = D''.cls fp := by
  dsimp only [cantorAdd] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨⟨U, w⟩, hc, hr⟩
  obtain ⟨hU, hDw, hEw, hcop⟩ := compAdd_spec hc
  have hUd : U.mpoly ∣ fp - w.cpoly ^ 2 := by
    rw [hU]
    exact hcop.mul_dvd (dvd_sub_sq_of_dvd hD hDw) (dvd_sub_sq_of_dvd hE hEw)
  obtain ⟨hon, hcls⟩ := reduce4_spec fp hUd hr
  refine ⟨hon, ?_⟩
  rw [← hcls]
  obtain ⟨r, hr'⟩ := hUd
  have hsq : w.cpoly ^ 2 - fp = D.u * E.u * (-r) := by rw [← hU]; linear_combination -hr'
  unfold Mum.cls
  rw [← mk0_mumford_congr fp D.u_monic.ne_zero hDw, ← mk0_mumford_congr fp E.u_monic.ne_zero hEw,
    mk0_mumford_mul fp D.u_monic.ne_zero E.u_monic.ne_zero hsq]
  exact mk0_mumford_of_eq fp _ _ hU.symm _

/-- **Cantor's doubling** over a field. -/
theorem cantorDbl_spec (fp : K[X]) [GoodSextic fp] {D D'' : Mum K} (hD : D.OnCurve fp)
    (h : cantorDbl (fieldOps K) (Sext.ofPoly fp) D = some D'') :
    D''.OnCurve fp ∧ D.cls fp * D.cls fp = D''.cls fp := by
  dsimp only [cantorDbl] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨⟨U, w⟩, hc, hr⟩
  obtain ⟨hU, hDw, hUd⟩ := compDbl_spec fp hD hc
  rw [← hU] at hUd
  obtain ⟨hon, hcls⟩ := reduce4_spec fp hUd hr
  refine ⟨hon, ?_⟩
  rw [← hcls]
  obtain ⟨r, hr'⟩ := hUd
  have hsq : w.cpoly ^ 2 - fp = D.u * D.u * (-r) := by rw [← hU]; linear_combination -hr'
  unfold Mum.cls
  rw [← mk0_mumford_congr fp D.u_monic.ne_zero hDw,
    mk0_mumford_mul fp D.u_monic.ne_zero D.u_monic.ne_zero hsq]
  exact mk0_mumford_of_eq fp _ _ hU.symm _

/-- **Opposite**: `[u, -v]` is on the curve and its class is the inverse. -/
theorem mumNeg_spec (fp : K[X]) [GoodSextic fp] {D : Mum K} (hD : D.OnCurve fp) :
    (Mum.neg (fieldOps K) D).OnCurve fp ∧ D.cls fp * (Mum.neg (fieldOps K) D).cls fp = 1 := by
  have hv : (Mum.neg (fieldOps K) D).v = -D.v := by
    simp only [Mum.v, Mum.neg, fieldOps, map_neg]; ring
  have hu : (Mum.neg (fieldOps K) D).u = D.u := rfl
  refine ⟨?_, ?_⟩
  · rw [Mum.OnCurve, hv, hu, neg_sq]
    exact hD
  · unfold Mum.cls
    rw [hv]
    have hdvd : D.u ∣ D.v ^ 2 - fp := by
      rw [← neg_sub]; exact dvd_neg.mpr hD
    change ClassGroup.mk0 (mumford0 fp D.u_monic.ne_zero D.v) *
      ClassGroup.mk0 (mumford0 fp D.u_monic.ne_zero (-D.v)) = 1
    rw [mk0_mumford_neg_of_dvd fp D.u_monic.ne_zero hdvd, mul_inv_cancel]

/-- A linear polynomial divisible by a monic quadratic vanishes. -/
theorem linear_eq_zero_of_quad_dvd {u0 u1 a b : K} (h : X ^ 2 + C u1 * X + C u0 ∣ C a * X + C b) :
    a = 0 ∧ b = 0 := by
  have hu : (X ^ 2 + C u1 * X + C u0 : K[X]).degree = 2 := by
    have hm : (X ^ 2 + C u1 * X + C u0 : K[X]).Monic := Mum.u_monic (⟨u0, u1, 0, 0⟩ : Mum K)
    have hn : (X ^ 2 + C u1 * X + C u0 : K[X]).natDegree = 2 :=
      Mum.u_natDegree (⟨u0, u1, 0, 0⟩ : Mum K)
    rw [degree_eq_natDegree hm.ne_zero, hn]
    rfl
  have hlt : (C a * X + C b).degree < (X ^ 2 + C u1 * X + C u0 : K[X]).degree := by
    rw [hu]
    exact lt_of_le_of_lt degree_linear_le (by decide)
  have h0 := eq_zero_of_dvd_of_degree_lt h hlt
  have ha := congrArg (fun p => p.coeff 1) h0
  have hb := congrArg (fun p => p.coeff 0) h0
  simp at ha hb
  exact ⟨ha, hb⟩

/-- **Reversal**: the image of a pair on `y² = f` lies on `Y² = X^6 f(1/X)`. -/
theorem revD_spec (f : Sext K) {D D' : Mum K} (hD : D.OnCurve f.poly)
    (h : revD (fieldOps K) D = some D') : D'.OnCurve f.rev.poly := by
  obtain ⟨u0, u1, v0, v1⟩ := D
  obtain ⟨f0, f1, f2, f3, f4, f5, f6⟩ := f
  unfold revD at h
  obtain ⟨p0, hp0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hu0, rfl⟩ := fieldOps_inv_eq_some hp0
  simp only [pure, Option.some.injEq] at h
  subst h
  obtain ⟨q3, rfl⟩ : ∃ q3, f5 = q3 + u1 * f6 := ⟨f5 - u1 * f6, by ring⟩
  obtain ⟨q2, rfl⟩ : ∃ q2, f4 = q2 + u1 * q3 + u0 * f6 := ⟨f4 - u1 * q3 - u0 * f6, by ring⟩
  obtain ⟨q1, rfl⟩ : ∃ q1, f3 = q1 + u1 * q2 + u0 * q3 := ⟨f3 - u1 * q2 - u0 * q3, by ring⟩
  obtain ⟨q0, rfl⟩ : ∃ q0, f2 = q0 + v1 ^ 2 + u1 * q1 + u0 * q2 :=
    ⟨f2 - v1 ^ 2 - u1 * q1 - u0 * q2, by ring⟩
  obtain ⟨r1, rfl⟩ : ∃ r1, f1 = r1 + 2 * v0 * v1 + u1 * q0 + u0 * q1 :=
    ⟨f1 - 2 * v0 * v1 - u1 * q0 - u0 * q1, by ring⟩
  obtain ⟨r0, rfl⟩ : ∃ r0, f0 = r0 + v0 ^ 2 + u0 * q0 := ⟨f0 - v0 ^ 2 - u0 * q0, by ring⟩
  simp only [Mum.OnCurve, Mum.u, Mum.v, Sext.poly, Sext.rev, fieldOps] at hD ⊢
  have hL : X ^ 2 + C u1 * X + C u0 ∣ C r1 * X + C r0 := by
    have e : C r1 * X + C r0 = (C (r0 + v0 ^ 2 + u0 * q0) + C (r1 + 2 * v0 * v1 + u1 * q0 + u0 * q1) * X +
        C (q0 + v1 ^ 2 + u1 * q1 + u0 * q2) * X ^ 2 + C (q1 + u1 * q2 + u0 * q3) * X ^ 3 +
        C (q2 + u1 * q3 + u0 * f6) * X ^ 4 + C (q3 + u1 * f6) * X ^ 5 + C f6 * X ^ 6 -
        (C v1 * X + C v0) ^ 2) - (X ^ 2 + C u1 * X + C u0) *
        (C f6 * X ^ 4 + C q3 * X ^ 3 + C q2 * X ^ 2 + C q1 * X + C q0) := by
      simp only [map_add, map_mul, map_pow, map_ofNat]
      ring
    rw [e]
    exact dvd_sub hD (dvd_mul_right _ _)
  obtain ⟨rfl, rfl⟩ := linear_eq_zero_of_quad_dvd hL
  have hp : C u0 * C u0⁻¹ = (1 : K[X]) := by rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
  refine ⟨C u0 * (C q0 * X ^ 4 + C q1 * X ^ 3 + C q2 * X ^ 2 + C q3 * X + C f6) +
    (C v0 * X + C (v1 - v0 * (u1 * u0⁻¹))) * ((C v0 * X ^ 3 + C v1 * X ^ 2) +
      (C (v0 * (u1 * u0⁻¹ * (u1 * u0⁻¹) - u0⁻¹) - v1 * (u1 * u0⁻¹)) * X +
        C (v0 * (u1 * u0⁻¹ * u0⁻¹) - v1 * u0⁻¹))), ?_⟩
  simp only [map_add, map_mul, map_pow, map_ofNat, map_sub, map_zero]
  linear_combination (-(1 + C u1 * X) * (C q0 * X ^ 4 + C q1 * X ^ 3 + C q2 * X ^ 2 + C q3 * X + C f6)) * hp

end Field

end FurioLombardo.Discharge.KvArith
