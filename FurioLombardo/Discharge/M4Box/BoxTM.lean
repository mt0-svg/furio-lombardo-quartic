import Mathlib
import FurioLombardo.Discharge.M4Box.Comp.BoxTM
import FurioLombardo.Discharge.M4Box.BoxCert
import FurioLombardo.Discharge.M4Box.CentreValue
import FurioLombardo.Discharge.KvArith.TM

/-!
# The per box statements from the Taylor model runs (lane lean-m4box, D9)

For a box `{c + 2^s Y}` the variable of the Taylor models is `h = 2^s Y`, in `boxH s ⊆ pv^(3s) O_v`. A
successful `boxRun` (M4Box/Comp/BoxTM.lean) gives, through three carriers:

* on `tmOpsF`, the computation itself;
* on truncated series times functions on `boxH s` (`PC`), the exact coefficients, fixed over the box
  (`rel_tmOpsF`: `rel_tmOps` with the recomputed valuation bounds);
* on `K_v` at each `h` (`rel_evalAt`), the exact run at the point `x(h)` over `pKv d (c + 2^s Y)`: the
  root `u(h) = discY d (c + 2^s Y)` (`EnclC.root`, `boxU_spec`), the lift `y(h)` on the branch
  (`EnclC.sqrt` and `nearOK`), `φ_v(x(h))` (`phiV_eq_cls`), the pair `R` of `E0 - φ_v(x(0))` (a ball run
  on the constant coefficients, which hold the exact values at `h = 0`) and `Q(h) = φ_v(x(h)) + R`.

The class of `Q(h)` is `(φ_v(x(h)) - φ_v(x(0))) + E0`, so `Q(h)` read in the chart is the chart point of
the arc (`chart_of_pair`, from `psi_chartPt`): `boxEncl`. The checks then give `ConstCert`
(`constCert_of_run`: the balls of `t` and `Amat t` over the box) and `TailCert` (`tailCert_of_run`: the
split `t = c0 + h c1 + h² S` of the fixed coefficients, `NS = aS` since `Amat` is integral).
-/

open Polynomial
open scoped Matrix
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv FurioLombardo.Discharge.KvArith
open FurioLombardo.Discharge.M3a.Bruin (fRev Mmat δ dL)

namespace FurioLombardo.Discharge.M4Box

/-! ## The parameter of a box -/

/-- The parameters `h = 2^s Y` of a box of size `s`. -/
def boxH (s : ℕ) : Set Kv := {h | ∃ Y : ℤ_[2], h = toKv (2 ^ s * Y)}

theorem boxH_dom (k : Ctx) (B : BoxSpec) (n : ℕ) : (B.ctx k n).Dom (boxH B.s) := by
  rintro h ⟨Y, rfl⟩
  exact norm_toKv_two_pow_mul_le Y B.s

theorem toKv_mem_boxH (s : ℕ) (Y : ℤ_[2]) : toKv (2 ^ s * Y) ∈ boxH s := ⟨Y, rfl⟩

theorem zero_mem_boxH (s : ℕ) : (0 : Kv) ∈ boxH s := ⟨0, by simp⟩

theorem toKv_injective : Function.Injective toKv := by
  intro a b h
  simp only [toKv, RingHom.comp_apply] at h
  exact Subtype.ext ((algebraMap ℚ_[2] Kv).injective h)

/-- A left inverse of `toKv`. -/
noncomputable def ofKv : Kv → ℤ_[2] := Function.invFun toKv

theorem ofKv_toKv (z : ℤ_[2]) : ofKv (toKv z) = z := Function.leftInverse_invFun toKv_injective z

theorem toKv_ofKv {s : ℕ} {h : Kv} (hh : h ∈ boxH s) : toKv (ofKv h) = h := by
  obtain ⟨Y, rfl⟩ := hh
  rw [ofKv_toKv]

/-! ## The carriers -/

/-- Truncated series times functions on `H`: the carrier that the Taylor models follow. -/
noncomputable abbrev PC (T : TCtx) (H : Set Kv) : Ops (List Kv × (Kv → Kv)) :=
  (polyOps (fieldOps Kv) T.n).prod (funOps H)

/-- A constant of `PC`. -/
noncomputable def cstPC (x : Kv) : List Kv × (Kv → Kv) := ([x], fun _ => x)

theorem EnclC.fresh {T : TCtx} {H : Set Kv} (hk : T.k.Ok) {M : TM} {cs : List Kv} {F : Kv → Kv}
    (h : EnclC T H M cs F) : EnclC T H (TM.fresh T M) cs F := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun x hx => ?_⟩
  · dsimp [TM.fresh]
    rw [List.forall₂_map_right_iff]
    exact h1.imp fun _ _ hb => Ball.mem_fresh hk hb
  · obtain ⟨ρ, hρ, e⟩ := h2 x hx
    refine ⟨ρ, ?_, e⟩
    dsimp [TM.fresh]
    exact Ball.mem_fresh hk hρ

/-- **The Taylor models with recomputed valuation bounds follow `PC`.** -/
theorem rel_tmOpsF {T : TCtx} {H : Set Kv} (hk : T.k.Ok) (hH : T.Dom H) :
    Ops.Rel (PC T H) (tmOpsF T) (fun cF M => EnclC T H M cF.1 cF.2) := by
  have r := rel_tmOps (T := T) (H := H) hk hH
  refine
    { add := fun {x y} {a b} hx hy => EnclC.fresh hk (r.add hx hy)
      sub := fun {x y} {a b} hx hy => EnclC.fresh hk (r.sub hx hy)
      neg := fun {x} {a} hx => r.neg hx
      mul := fun {x y} {a b} hx hy => EnclC.fresh hk (r.mul hx hy)
      inv := by
        intro x a b hx hb
        simp only [tmOpsF, Option.map_eq_some_iff] at hb
        obtain ⟨b0, hb0, rfl⟩ := hb
        obtain ⟨y, hy, hyb⟩ := r.inv (EnclC.fresh hk hx) hb0
        exact ⟨y, hy, EnclC.fresh hk hyb⟩
      ofInt := fun z => r.ofInt z }

/-- **Evaluation at a point of `H`.** -/
theorem rel_evalAt {T : TCtx} {H : Set Kv} {h : Kv} (hh : h ∈ H) :
    Ops.Rel (fieldOps Kv) (PC T H) (fun x cF => cF.2 h = x) := by
  unfold PC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- add
    intro x y a b hx hy
    simp [Ops.prod, funOps, fieldOps] at hx hy ⊢
    simp [hx, hy]
  · -- sub
    intro x y a b hx hy
    simp [Ops.prod, funOps, fieldOps] at hx hy ⊢
    simp [hx, hy]
  · -- neg
    intro x a hx
    simp [Ops.prod, funOps, fieldOps] at hx ⊢
    simp [hx]
  · -- mul
    intro x y a b hx hy
    simp [Ops.prod, funOps, fieldOps] at hx hy ⊢
    simp [hx, hy]
  · -- inv
    intro x a b hx hinv
    subst hx
    simp only [Ops.prod] at hinv
    cases h1 : (polyOps (fieldOps Kv) T.n).inv a.1
    · simp [h1] at hinv
    · case _ val1 =>
      cases h2 : (funOps H).inv a.2
      · simp [h1, h2] at hinv
      · case _ val2 =>
        simp [h1, h2] at hinv
        -- hinv : (val1, val2) = b
        -- h2 : (funOps H).inv a.2 = some val2
        simp [funOps] at h2
        -- h2 : (∀ h ∈ H, ¬a.2 h = 0) ∧ (fun h => (a.2 h)⁻¹) = val2
        rcases h2 with ⟨hne, hval⟩
        -- hne : ∀ h ∈ H, ¬a.2 h = 0
        -- hval : (fun h => (a.2 h)⁻¹) = val2
        have h0 : a.2 h ≠ 0 := by
          intro heq
          apply hne h hh
          exact heq
        -- from hinv : (val1, val2) = b, we get b = (val1, val2)
        -- so b.2 = val2
        have hb2 : b.2 = val2 := by
          have := congrArg Prod.snd hinv.symm
          simpa using this
        refine ⟨(a.2 h)⁻¹, ?_, ?_⟩
        · -- goal: (fieldOps Kv).inv (a.2 h) = some (a.2 h)⁻¹
          classical
            simp [fieldOps, h0]
        · -- goal: b.2 h = (a.2 h)⁻¹
          rw [hb2, ← hval]
  · -- ofInt
    intro z
    rfl

/-- The constant coefficient ball holds the value at `0`. -/
theorem EnclC.mem_headD {T : TCtx} {H : Set Kv} (hk : T.k.Ok) {M : TM} {cs : List Kv} {F : Kv → Kv}
    (h : EnclC T H M cs F) (h0 : (0 : Kv) ∈ H) : (M.cs.headD (TM.zeroB T)).Mem (F 0) := by
  rcases h with ⟨hrel, hF⟩
  rcases hF 0 h0 with ⟨ρ, hρ, hF0⟩
  have hF0' : F 0 = (fieldOps Kv).horner cs (0 : Kv) := by
    rw [hF0]
    simp
  rw [hF0']
  have hhead : (M.cs.headD (TM.zeroB T)).Mem (cs.headD 0) := forall₂_headD_mem hk hrel
  have hhorner : (fieldOps Kv).horner cs (0 : Kv) = cs.headD 0 := by
    cases cs with
    | nil => simp [Ops.horner, fieldOps, Ops.zero]
    | cons a l => simp [Ops.horner, fieldOps, Ops.zero]
  rw [hhorner]
  exact hhead

theorem EnclC.cstPC {T : TCtx} {H : Set Kv} (hk : T.k.Ok) {b : Ball} {x : Kv} (hx : b.Mem x) :
    EnclC T H (TM.cst T b) (cstPC x).1 (cstPC x).2 :=
  EnclC.cst hk hx

/-! ## Relations of the records -/

theorem Sym3.rel_cmap {A B A' B' : Type*} {R : A → B → Prop} {S : A' → B' → Prop} {f : A → A'}
    {g : B → B'} (hfg : ∀ {x y}, R x y → S (f x) (g y)) {m : Sym3 A} {m' : Sym3 B}
    (h : Sym3.Rel R m m') : Sym3.Rel S (m.cmap f) (m'.cmap g) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨hfg h1, hfg h2, hfg h3, hfg h4, hfg h5, hfg h6⟩

theorem Mum.rel_cmap {A B A' B' : Type*} {R : A → B → Prop} {S : A' → B' → Prop} {f : A → A'}
    {g : B → B'} (hfg : ∀ {x y}, R x y → S (f x) (g y)) {m : Mum A} {m' : Mum B}
    (h : Mum.Rel R m m') : Mum.Rel S (m.cmap f) (m'.cmap g) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨hfg h1, hfg h2, hfg h3, hfg h4⟩

theorem Sext.rel_cmap {A B A' B' : Type*} {R : A → B → Prop} {S : A' → B' → Prop} {f : A → A'}
    {g : B → B'} (hfg : ∀ {x y}, R x y → S (f x) (g y)) {m : Sext A} {m' : Sext B}
    (h : Sext.Rel R m m') : Sext.Rel S (m.cmap f) (m'.cmap g) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  simp only [Sext.Rel, Sext.cmap]
  exact ⟨hfg h0, hfg h1, hfg h2, hfg h3, hfg h4, hfg h5, hfg h6⟩

/-! ## The programs follow the relations -/

theorem rel_boxP {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop} (h : Ops.Rel o p R) (d : ℕ) (wh : Bool) {m0 m1 m2 : Sym3 A}
    {m0' m1' m2' : Sym3 B} (h0 : Sym3.Rel R m0 m0') (h1 : Sym3.Rel R m1 m1') (h2 : Sym3.Rel R m2 m2')
    {idl X Y : A} {idl' X' Y' : B} (hi : R idl idl') (hX : R X X') (hY : R Y Y') :
    Trip.Rel R (boxP o d wh m0 m1 m2 idl X Y).1 (boxP p d wh m0' m1' m2' idl' X' Y').1 ∧
      R (boxP o d wh m0 m1 m2 idl X Y).2.1 (boxP p d wh m0' m1' m2' idl' X' Y').2.1 ∧
      R (boxP o d wh m0 m1 m2 idl X Y).2.2 (boxP p d wh m0' m1' m2' idl' X' Y').2.2 := by
  have hw := rel_discPtO h d hX hY
  have hq1 := rel_quad h h0 hw.1 hw.2.1 hw.2.2
  have hq2 := rel_quad h h1 hw.1 hw.2.1 hw.2.2
  have hq3 := rel_quad h h2 hw.1 hw.2.1 hw.2.2
  unfold boxP
  refine ⟨hw, ?_, h.mul hq2 hi⟩
  cases wh with
  | false => simp [h.mul hq3 hi]
  | true => simp [h.mul hq1 hi]

theorem rel_boxPhi {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop} (h : Ops.Rel o p R) (wh : Bool) (prm : APPrm) {m0 m1 m2 : Sym3 A}
    {m0' m1' m2' : Sym3 B} (h0 : Sym3.Rel R m0 m0') (h1 : Sym3.Rel R m1 m1') (h2 : Sym3.Rel R m2 m2')
    {dl : A} {dl' : B} (hdl : R dl dl') {w : A × A × A} {w' : B × B × B} (hw : Trip.Rel R w w')
    {q y : A} {q' y' : B} (hq : R q q') (hy : R y y') :
    OptRel (Mum.Rel R) (boxPhi o wh prm m0 m1 m2 dl w q y) (boxPhi p wh prm m0' m1' m2' dl' w' q' y') := by
  intro b hb
  unfold boxPhi at hb ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
  obtain ⟨iy', hiy', hb⟩ := hb
  obtain ⟨iy, hiy, hr⟩ := h.inv hy hiy'
  rw [hiy]
  simp only [Option.bind_some]
  have hz := h.mul hq hr
  cases wh
  · simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
    exact rel_apPhi h prm ⟨h2, h1, h0, hdl, hw.1, hw.2.1, hw.2.2, hy, hz⟩ b hb
  · simp only [↓reduceIte] at hb ⊢
    exact rel_apPhi h prm ⟨h2, h1, h0, hdl, hw.1, hw.2.1, hw.2.2, hz, hy⟩ b hb

theorem rel_boxChart {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop} (h : Ops.Rel o p R)
    {f : Sext A} {f' : Sext B} (hf : Sext.Rel R f f') {a : A}
    {a' : B} (ha : R a a') {Am : Mat2 A} {Am' : Mat2 B}
    (hAm : R Am.a00 Am'.a00 ∧ R Am.a01 Am'.a01 ∧ R Am.a10 Am'.a10 ∧ R Am.a11 Am'.a11)
    {m R0 : Mum A} {m' R0' : Mum B} (hm : Mum.Rel R m m') (hR : Mum.Rel R R0 R0') :
    OptRel (fun x y => Mum.Rel R x.1 y.1 ∧ R x.2.1 y.2.1 ∧ R x.2.2 y.2.2) (boxChart o f a Am m R0)
      (boxChart p f' a' Am' m' R0') := by
  intro b hb
  unfold boxChart at hb ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
  obtain ⟨Q', hQ', rfl⟩ := hb
  obtain ⟨Q, hQ, hQQ⟩ := Ops.Rel.cantorAdd h hf hm hR Q' hQ'
  rw [hQ]
  have hs := Ops.Rel.shift h ha hQQ
  refine ⟨_, rfl, hs, ?_, ?_⟩
  · have hz1 := hs.2.1
    have hz0 := hs.1
    have hmul1 := h.mul hAm.1 hz1
    have hmul2 := h.mul hAm.2.1 hz0
    exact h.add hmul1 hmul2
  · have hz1 := hs.2.1
    have hz0 := hs.1
    have hmul1 := h.mul hAm.2.2.1 hz1
    have hmul2 := h.mul hAm.2.2.2 hz0
    exact h.add hmul1 hmul2

/-! ## The exact runs -/

/-- The exact first stage: the point, `Q1/δ` or `Q3/δ`, and `Q2/δ`. -/
theorem boxP_field (kk : Fin 2) (d : ℕ) (wh : Bool) (X Y : Kv) :
    boxP (fieldOps Kv) d wh (Sym3.ofMatrix ((Mmat 0).map σ)) (Sym3.ofMatrix ((Mmat 1).map σ))
        (Sym3.ofMatrix ((Mmat 2).map σ)) (σ (δ kk))⁻¹ X Y =
      ((discPt d X Y 0, discPt d X Y 1, discPt d X Y 2),
        (if wh then discPt d X Y ⬝ᵥ ((Mmat 0).map σ *ᵥ discPt d X Y)
          else discPt d X Y ⬝ᵥ ((Mmat 2).map σ *ᵥ discPt d X Y)) * (σ (δ kk))⁻¹,
        discPt d X Y ⬝ᵥ ((Mmat 1).map σ *ᵥ discPt d X Y) * (σ (δ kk))⁻¹) := by
  unfold boxP
  rw [discPtO_field]
  dsimp only
  simp only [quad_ofMatrix (Mmat_map_symm 0), quad_ofMatrix (Mmat_map_symm 1), quad_ofMatrix (Mmat_map_symm 2)]
  cases wh <;> rfl

/-- The exact second stage is the Abel-Prym program at the input with the coordinate `y`. -/
theorem boxPhi_field {wh : Bool} {prm : APPrm} {m0 m1 m2 : Sym3 Kv} {dl : Kv} {w : Kv × Kv × Kv}
    {q y : Kv} {m : Mum Kv} (h : boxPhi (fieldOps Kv) wh prm m0 m1 m2 dl w q y = some m) :
    y ≠ 0 ∧ apPhi (fieldOps Kv) prm (if wh then ⟨m2, m1, m0, dl, w.1, w.2.1, w.2.2, q * y⁻¹, y⟩
      else ⟨m2, m1, m0, dl, w.1, w.2.1, w.2.2, y, q * y⁻¹⟩) = some m := by
  unfold boxPhi at h
  simp [fieldOps] at h
  split at h
  · -- case y = 0: h : none = some m
    simp at h
  · -- case y ≠ 0: h : apPhi ... = some m
    rename_i hy
    cases wh
    · simp at h
      exact ⟨hy, h⟩
    · simp at h
      exact ⟨hy, h⟩

/-- The exact third stage: the sum, translated, and `Amat t`. -/
theorem boxChart_field {f : Sext Kv} {a : Kv} {Am : Mat2 Kv} {m R : Mum Kv} {out : Mum Kv × Kv × Kv}
    (h : boxChart (fieldOps Kv) f a Am m R = some out) :
    ∃ Q, cantorAdd (fieldOps Kv) f m R = some Q ∧ out.1 = Mum.shift (fieldOps Kv) a Q ∧
      out.2.1 = Am.a00 * out.1.u1 + Am.a01 * out.1.u0 ∧ out.2.2 = Am.a10 * out.1.u1 + Am.a11 * out.1.u0 := by
  simp only [boxChart, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨Q, hQ, rfl⟩ := h
  exact ⟨Q, hQ, rfl, rfl, rfl⟩

theorem apInV_ptR (kk : Fin 2) {p : Fin 3 → Kv} (hp : p ≠ 0)
    (hF : FurioLombardo.F (p 0) (p 1) (p 2) = 0) {y : Kv} (hy : y ≠ 0)
    (h1 : y ^ 2 = p ⬝ᵥ ((Mmat 0).map σ *ᵥ p) * (σ (δ kk))⁻¹) :
    apInV kk (ptR kk hp hF hy h1) =
      ⟨Sym3.ofMatrix ((Mmat 2).map σ), Sym3.ofMatrix ((Mmat 1).map σ), Sym3.ofMatrix ((Mmat 0).map σ),
        σ (δ kk), p 0, p 1, p 2, p ⬝ᵥ ((Mmat 1).map σ *ᵥ p) * (σ (δ kk))⁻¹ * y⁻¹, y⟩ := by
  rfl

theorem apInV_ptS (kk : Fin 2) {p : Fin 3 → Kv} (hp : p ≠ 0)
    (hF : FurioLombardo.F (p 0) (p 1) (p 2) = 0) {y : Kv} (hy : y ≠ 0)
    (h3 : y ^ 2 = p ⬝ᵥ ((Mmat 2).map σ *ᵥ p) * (σ (δ kk))⁻¹) :
    apInV kk (ptS kk hp hF hy h3) =
      ⟨Sym3.ofMatrix ((Mmat 2).map σ), Sym3.ofMatrix ((Mmat 1).map σ), Sym3.ofMatrix ((Mmat 0).map σ),
        σ (δ kk), p 0, p 1, p 2, y, p ⬝ᵥ ((Mmat 1).map σ *ᵥ p) * (σ (δ kk))⁻¹ * y⁻¹⟩ := by
  rfl

/-! ## The disc point over the box -/

theorem hornerZ2_G1L {d : ℕ} (hd : IsDisc d) (x y : Kv) :
    (fieldOps Kv).hornerZ2 (G1L d) x y = G1 d x y := by
  rcases hd with rfl | rfl | rfl | rfl | rfl <;>
    simp only [G1L, G1, fieldOps, Ops.hornerZ2, Ops.hornerZ, Ops.zero, List.foldr] <;> push_cast <;> ring

theorem approx_discY_int {d : ℕ} (hd : IsDisc d) (c : ℤ) {Y0 : ℤ} {N : ℕ}
    (hY : (2 : ℤ) ^ N ∣ G1 d c Y0) : (2 : ℤ_[2]) ^ N ∣ discY d (c : ℤ_[2]) - (Y0 : ℤ_[2]) := by
  have hG0 : G1 d (c : ℤ_[2]) (discY d (c : ℤ_[2])) = 0 :=
    (G1_eq_zero_iff hd _ _).mp (discY_spec hd _).1
  have hsub := G1_sub hd (c : ℤ_[2]) (discY d (c : ℤ_[2])) (Y0 : ℤ_[2])
  rw [hG0, zero_sub] at hsub
  have hmap := map_G1 (Int.castRingHom ℤ_[2]) hd c Y0
  simp only [eq_intCast] at hmap
  have h1 : (2 : ℤ_[2]) ^ N ∣ G1 d (c : ℤ_[2]) (Y0 : ℤ_[2]) := by
    rw [← hmap]; exact (two_pow_dvd_intCast_iff (G1 d c Y0) N).mpr hY
  have h2 : (2 : ℤ_[2]) ^ N ∣ (discY d (c : ℤ_[2]) - Y0) * Hd d (c : ℤ_[2]) (discY d (c : ℤ_[2])) Y0 := by
    rw [← hsub]; exact (dvd_neg).mpr h1
  exact (isUnit_Hd hd _ _ _).dvd_mul_right.mp h2

/-- The root over the box: `u(h) = discY d (c + h)`. -/
noncomputable def boxU (d : ℕ) (c : ℤ) (h : Kv) : Kv := toKv (discY d ((c : ℤ_[2]) + ofKv h))

theorem boxU_spec {k : Ctx} (hk : k.Ok) {d : ℕ} (hd : IsDisc d) {c Y0 : ℤ} {N : ℕ}
    (hY : (2 : ℤ) ^ N ∣ G1 d c Y0) (s : ℕ) :
    ∀ h ∈ boxH s, (fieldOps Kv).hornerZ2 (G1L d) ((c : Kv) + 1 * h) (boxU d c h) = 0 ∧
      (Ball.ofApprox k (Y0, 0, 0) (min N s)).Mem (boxU d c h) := by
  intro h hh
  obtain ⟨Y, rfl⟩ := hh
  have hof : ofKv (toKv (2 ^ s * Y)) = 2 ^ s * Y := ofKv_toKv _
  have hbox : boxU d c (toKv (2 ^ s * Y)) = toKv (discY d ((c : ℤ_[2]) + 2 ^ s * Y)) := by
    rw [boxU, hof]
  have hcx : (c : Kv) + 1 * toKv (2 ^ s * Y) = toKv ((c : ℤ_[2]) + 2 ^ s * Y) := by
    rw [one_mul, map_add, map_intCast]
  refine ⟨?_, ?_⟩
  · rw [hbox, hcx, hornerZ2_G1L hd, ← map_G1 toKv hd,
      (G1_eq_zero_iff hd _ _).mp (discY_spec hd _).1, map_zero]
  · rw [hbox]
    apply Ball.mem_ofApprox hk
    apply approx_toKv
    have h1 : (2 : ℤ_[2]) ^ s ∣ discY d ((c : ℤ_[2]) + 2 ^ s * Y) - discY d (c : ℤ_[2]) :=
      discY_sub_dvd hd ⟨Y, by ring⟩
    have h2 := approx_discY_int hd c hY
    have := dvd_add (dvd_trans (pow_dvd_pow 2 (min_le_right N s)) h1)
      (dvd_trans (pow_dvd_pow 2 (min_le_left N s)) h2)
    rwa [sub_add_sub_cancel] at this

theorem boxU_centre {k : Ctx} (hk : k.Ok) {d : ℕ} (hd : IsDisc d) {c Y0 : ℤ} {N : ℕ}
    (hY : (2 : ℤ) ^ N ∣ G1 d c Y0) :
    (fieldOps Kv).hornerZ2 (G1L d) (c : Kv) (toKv (discY d (c : ℤ_[2]))) = 0 ∧
      (Ball.ofApprox k (Y0, 0, 0) N).Mem (toKv (discY d (c : ℤ_[2]))) := by
  refine ⟨?_, Ball.mem_ofApprox hk (approx_toKv (approx_discY_int hd c hY))⟩
  rw [hornerZ2_G1L hd, show (c : Kv) = toKv (c : ℤ_[2]) by rw [map_intCast], ← map_G1 toKv hd,
    (G1_eq_zero_iff hd _ _).mp (discY_spec hd _).1, map_zero]

/-- The point over the box is `pKv d (c + h)`. -/
theorem discPt_boxU {d : ℕ} {c : ℤ} {s : ℕ} {h : Kv} (hh : h ∈ boxH s) (i : Fin 3) :
    discPt d ((c : Kv) + h) (boxU d c h) i = pKv d ((c : ℤ_[2]) + ofKv h) i := by
  obtain ⟨Y, rfl⟩ := hh
  unfold boxU pKv
  rw [ofKv_toKv]
  have h : (c : Kv) + toKv (2 ^ s * Y) = toKv ((c : ℤ_[2]) + (2 ^ s * Y)) := by
    simpa [map_add, map_intCast] using (toKv.map_add (c : ℤ_[2]) (2 ^ s * Y)).symm
  rw [h]
  rw [← map_discPt toKv d ((c : ℤ_[2]) + (2 ^ s * Y)) (discY d ((c : ℤ_[2]) + (2 ^ s * Y))) i]

/-! ## The chart point of a pair -/

/-- **The chart point of `X` from a pair of class `X + E0`.** -/
theorem chart_of_pair (k : Fin 2) {Q : Mum Kv} {X : Additive (Jac ((fRev k).map σ))}
    (hQ : Q.OnCurve ((fRev k).map σ))
    (hQc : Q.cls ((fRev k).map σ) =
      ((Additive.toMul X : Jac ((fRev k).map σ)) : Pic ((fRev k).map σ)) *
        (E0Mum k).cls ((fRev k).map σ))
    {D : ℕ} (hD : M0 k + 4 ≤ D) (hD7 : 7 + 2 * IntModelKv.aa k ≤ D)
    (ht : ∀ j, ‖Q.chartT (aK k) j‖ ≤ ‖pv‖ ^ D)
    (hw0 : ‖(Q.chartW (aK k)).coeff 0 - bK k‖ < ‖2 * bK k‖)
    (hw1 : ‖(Q.chartW (aK k)).coeff 1‖ * ‖pv‖ ^ IntModelKv.aa k ≤ ‖bK k‖) :
    ∃ z : (fgl k (IntModelKv.admM0 k)).Points, chart k (IntModelKv.admM0 k) z = X ∧
      tK k (IntModelKv.admM0 k) z = Q.chartT (aK k) := by
  set a := aK k
  have hle : ‖pv‖ ≤ 1 := norm_pv_le_one
  have ht4 : ∀ j, ‖Q.chartT a j‖ ≤ ‖pv‖ ^ (M0 k + 4) := fun j =>
    (ht j).trans (pow_le_pow_of_le_one (norm_nonneg _) hle hD)
  have ht0 : ‖Q.chartT a 0‖ ≤ ‖pv‖ ^ (7 + IntModelKv.aa k) :=
    (ht 0).trans (pow_le_pow_of_le_one (norm_nonneg _) hle (by omega))
  have ht1 : ‖Q.chartT a 1‖ ≤ ‖pv‖ ^ (7 + 2 * IntModelKv.aa k) :=
    (ht 1).trans (pow_le_pow_of_le_one (norm_nonneg _) hle hD7)
  have hres := resQ_chain_ne_zero k ht4 ht0 ht1 hw0 hw1
  refine ⟨chartPt (M0 k) (Q.chartT a) ht4, ?_, ?_⟩
  · have hQ' : clsA ((fRev k).map σ) a (Q.chartT a) (Q.chartW a) =
        ((Additive.toMul X : Jac ((fRev k).map σ)) : Pic ((fRev k).map σ)) *
          clsA ((fRev k).map σ) a 0 (baseKv k).toSetup.v0 := by
      rw [← Mum.cls_eq_clsA (F := (fRev k).map σ) a Q, hQc, E0Mum_cls k]
    have h_psi := psi_chartPt (baseKv k) (hF k) (IntModelKv.admM0 k) ht4 (Mum.chartW_degree a Q)
      (Mum.dvd_chart (hF k) hQ) hres hQ'
    exact Additive.toMul.injective (Subtype.ext h_psi)
  · dsimp [tK]
    rw [tPt_chartPt (baseKv k) (M0 k) (Q.chartT a) ht4]

theorem ArcChart.mono {k : Fin 2} {h : AdmM0 k} {e : BranchBox} {X X0 : ℤ_[2]}
    {P P' : (Fin 2 → Kv) → Prop} (hP : ∀ t, P t → P' t) (hA : ArcChart k h e X X0 P) :
    ArcChart k h e X X0 P' := by
  obtain ⟨x, x0, h1, h2, h3, h4, z, hz, ht⟩ := hA
  exact ⟨x, x0, h1, h2, h3, h4, z, hz, hP _ ht⟩

end FurioLombardo.Discharge.M4Box
