import Mathlib
import FurioLombardo.Discharge.M4Box.DValue
import FurioLombardo.Discharge.KvArith.DCert
import FurioLombardo.Discharge.KvArith.Sigma
import FurioLombardo.Discharge.M4Box.Comp.Cert

/-!
# The input balls of the D_i value certificate (lane lean-m4box)

Balls, computed from the exact data of lane SelmerSpan and lane R7, of the inputs of the chain
`2^J N D_i + E0` (`M4Box/DValue.lean`) at the working precision `dCtx` (600 bits):

* `FvBall kk`: the coefficients `Fv kk j = σ(4 coeff_j fRev)` (`sigmaBall`), `gBall`: those of
  `g = (fRev kk)^σ = F/4`;
* `DBall kk i`: the Mumford pair `DptMum kk i`, through `σ(p)`, `σ(r)` (`sigQ`), `Z1`, `Z0`, the two
  square roots `n`, `a` of `SelmerSpan.Dpt` (`Ball.sqrt` at candidates `sN`, `sA`, identified with
  `SelmerSpan.nv`, `SelmerSpan.av` by `Ball.nearOK` against their low precision certificates), `b`, `c`;
* `bKBall kk`: the ordinate `bK kk` of the base point (square root of `f_k(0)`, sign by `bT kk`);
* `E0Ball kk`: the base pair `E0Mum kk`; `AmatBall kk`: the entries of `Amat kk`.

Each ball stage returns `none` unless its checks pass; soundness: `mem_DBall`, `mem_E0Ball`, ...
-/

open Polynomial
open scoped Matrix
open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv FurioLombardo.Discharge.KvArith
open FurioLombardo.Discharge.M3a.Bruin (fRev goodSextic_fRev_Kv)

namespace FurioLombardo.Discharge.M4Box

theorem dCtx_ok : dCtx.Ok := Ctx.ofP_ok 600

/-! ## Images under `σ` -/

theorem mem_sigQ {k : Ctx} (hk : k.Ok) {l : List ℤ} {m : ℕ} {b : Ball} (h : sigQ k l m = some b) :
    b.Mem (σ ((m : K21)⁻¹ * zkE l)) := by
  -- Unfold sigQ in h to get s, i, and b = (ballOpsF k).mul i s
  simp only [sigQ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  rcases h with ⟨s, hs, i, hi, hb⟩
  -- hs : sigmaBall k l = some s
  -- hi : (ballOpsF k).inv (Ball.ofInt k m) = some i
  -- hb : (ballOpsF k).mul i s = b
  have hs_mem : s.Mem (σ (zkE l)) := mem_sigmaBall hk hs
  have hi_mem_raw : (Ball.ofInt k m).Mem ((m : ℤ) : Kv) := Ball.mem_ofInt hk (m : ℤ)
  rcases (rel_ballOpsF hk).inv hi_mem_raw hi with ⟨y, hy_inv, hy⟩
  -- hy_inv : (fieldOps Kv).inv ((m : ℤ) : Kv) = some y
  -- hy : i.Mem y
  rcases fieldOps_inv_eq_some hy_inv with ⟨h_ne_zero, hy_eq⟩
  -- hy_eq : y = ((m : ℤ) : Kv)⁻¹
  have hy_val : y = ((m : ℕ) : Kv)⁻¹ := by
    rw [hy_eq]
    simp [Int.cast_natCast]
  have h_mul : ((ballOpsF k).mul i s).Mem ((fieldOps Kv).mul y (σ (zkE l))) :=
    (rel_ballOpsF hk).mul hy hs_mem
  rw [hb] at h_mul
  -- h_mul : b.Mem ((fieldOps Kv).mul y (σ (zkE l)))
  -- (fieldOps Kv).mul y (σ (zkE l)) = y * σ (zkE l)
  simp only [fieldOps] at h_mul
  -- h_mul : b.Mem (y * σ (zkE l))
  rw [hy_val] at h_mul
  -- h_mul : b.Mem (((m : ℕ) : Kv)⁻¹ * σ (zkE l))
  -- Now rewrite the target using ring hom properties of σ
  simpa [map_mul, map_inv, map_natCast] using h_mul

/-- The exact `Fv kk j`, `j = 0, ..., 6`, as a sextic. -/
noncomputable def FvSext (kk : ℕ) : Sext Kv :=
  ⟨SelmerSpan.Fv kk 0, SelmerSpan.Fv kk 1, SelmerSpan.Fv kk 2, SelmerSpan.Fv kk 3, SelmerSpan.Fv kk 4,
    SelmerSpan.Fv kk 5, SelmerSpan.Fv kk 6⟩

theorem mem_FvBall {k : Ctx} (hk : k.Ok) {kk : ℕ} {F : Sext Ball} (h : FvBall k kk = some F) :
    Sext.Rel (fun x b => b.Mem x) (FvSext kk) F := by
  simp only [FvBall, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨b0, hb0, h⟩ := h
  obtain ⟨b1, hb1, h⟩ := h
  obtain ⟨b2, hb2, h⟩ := h
  obtain ⟨b3, hb3, h⟩ := h
  obtain ⟨b4, hb4, h⟩ := h
  obtain ⟨b5, hb5, h⟩ := h
  obtain ⟨b6, hb6, h⟩ := h
  have hmem0 : b0.Mem (SelmerSpan.Fv kk 0) := by
    rw [show SelmerSpan.Fv kk 0 = σ (zkE (SelmerSpan.FL kk 0)) from rfl]
    exact mem_sigmaBall hk hb0
  have hmem1 : b1.Mem (SelmerSpan.Fv kk 1) := by
    rw [show SelmerSpan.Fv kk 1 = σ (zkE (SelmerSpan.FL kk 1)) from rfl]
    exact mem_sigmaBall hk hb1
  have hmem2 : b2.Mem (SelmerSpan.Fv kk 2) := by
    rw [show SelmerSpan.Fv kk 2 = σ (zkE (SelmerSpan.FL kk 2)) from rfl]
    exact mem_sigmaBall hk hb2
  have hmem3 : b3.Mem (SelmerSpan.Fv kk 3) := by
    rw [show SelmerSpan.Fv kk 3 = σ (zkE (SelmerSpan.FL kk 3)) from rfl]
    exact mem_sigmaBall hk hb3
  have hmem4 : b4.Mem (SelmerSpan.Fv kk 4) := by
    rw [show SelmerSpan.Fv kk 4 = σ (zkE (SelmerSpan.FL kk 4)) from rfl]
    exact mem_sigmaBall hk hb4
  have hmem5 : b5.Mem (SelmerSpan.Fv kk 5) := by
    rw [show SelmerSpan.Fv kk 5 = σ (zkE (SelmerSpan.FL kk 5)) from rfl]
    exact mem_sigmaBall hk hb5
  have hmem6 : b6.Mem (SelmerSpan.Fv kk 6) := by
    rw [show SelmerSpan.Fv kk 6 = σ (zkE (SelmerSpan.FL kk 6)) from rfl]
    exact mem_sigmaBall hk hb6
  subst h
  exact ⟨hmem0, hmem1, hmem2, hmem3, hmem4, hmem5, hmem6⟩

open FurioLombardo.Discharge.SelmerSpan in
theorem mem_gBall {k : Ctx} (hk : k.Ok) (kk : Fin 2) {F g : Sext Ball}
    (hF : Sext.Rel (fun x b => b.Mem x) (FvSext kk) F) (h : gBall k F = some g) :
    Sext.Rel (fun x b => b.Mem x) (Sext.ofPoly ((fRev kk).map σ)) g := by
  -- Unfold gBall in h to extract the intermediate ball i
  unfold gBall at h
  -- h : (ballOpsF k).inv (Ball.ofInt k 4) >>= (fun i => ...) = some g
  -- Expand Option.bind
  dsimp [Option.bind] at h
  -- h : match (ballOpsF k).inv (Ball.ofInt k 4) with | none => none | some i => ... = some g
  -- Now case split on the match
  cases hg_inv : (ballOpsF k).inv (Ball.ofInt k 4) with
  | none =>
    -- h : none = some g, contradiction
    simp [hg_inv] at h
  | some i =>
    -- h : (let m := (ballOpsF k).mul; ⟨m F.f0 i, ...⟩) = some g
    simp [hg_inv] at h
    -- h : g = ⟨(ballOpsF k).mul F.f0 i, ..., (ballOpsF k).mul F.f6 i⟩
    have hg := h.symm
    -- hg : ⟨..., ...⟩ = g
    -- Extract the equalities for each component
    have hg0 : ((ballOpsF k).mul F.f0 i) = g.f0 := by
      have := congrArg Sext.f0 hg
      simpa using this.symm
    have hg1 : ((ballOpsF k).mul F.f1 i) = g.f1 := by
      have := congrArg Sext.f1 hg
      simpa using this.symm
    have hg2 : ((ballOpsF k).mul F.f2 i) = g.f2 := by
      have := congrArg Sext.f2 hg
      simpa using this.symm
    have hg3 : ((ballOpsF k).mul F.f3 i) = g.f3 := by
      have := congrArg Sext.f3 hg
      simpa using this.symm
    have hg4 : ((ballOpsF k).mul F.f4 i) = g.f4 := by
      have := congrArg Sext.f4 hg
      simpa using this.symm
    have hg5 : ((ballOpsF k).mul F.f5 i) = g.f5 := by
      have := congrArg Sext.f5 hg
      simpa using this.symm
    have hg6 : ((ballOpsF k).mul F.f6 i) = g.f6 := by
      have := congrArg Sext.f6 hg
      simpa using this.symm

    -- From hF, get the 7 component relations
    rcases hF with ⟨hF0, hF1, hF2, hF3, hF4, hF5, hF6⟩

    -- Unfold FvSext in the hF components
    simp [FvSext] at hF0 hF1 hF2 hF3 hF4 hF5 hF6

    -- The relation between fieldOps and ballOpsF
    have hrel := rel_ballOpsF hk

    -- From the inverse relation, get that i is in the inverse of (4 : ℤ) : Kv
    have hmem_ofInt : (Ball.ofInt k 4).Mem ((4 : ℤ) : Kv) := Ball.mem_ofInt hk 4
    have hinv := hrel.inv hmem_ofInt hg_inv
    rcases hinv with ⟨y, hy_inv, hy_mem⟩
    -- hy_inv : (fieldOps Kv).inv ((4 : ℤ) : Kv) = some y
    -- hy_mem : i.Mem y

    have hfield_inv := fieldOps_inv_eq_some hy_inv
    rcases hfield_inv with ⟨h4_ne_zero, hy_eq⟩
    -- hy_eq : y = ((4 : ℤ) : Kv)⁻¹

    have hi_mem : i.Mem (((4 : ℤ) : Kv)⁻¹) := by
      rw [hy_eq] at hy_mem
      exact hy_mem

    -- For each coefficient j = 0,...,6, prove the component relation
    have hcoeff0 : ((fRev kk).map σ).coeff 0 = Fv kk 0 / 4 := by
      have := g_coeff kk (by norm_num : (0 : ℕ) ≤ 6)
      simpa [div_eq_inv_mul] using this
    have hcoeff1 : ((fRev kk).map σ).coeff 1 = Fv kk 1 / 4 := by
      have := g_coeff kk (by norm_num : (1 : ℕ) ≤ 6)
      simpa [div_eq_inv_mul] using this
    have hcoeff2 : ((fRev kk).map σ).coeff 2 = Fv kk 2 / 4 := by
      have := g_coeff kk (by norm_num : (2 : ℕ) ≤ 6)
      simpa [div_eq_inv_mul] using this
    have hcoeff3 : ((fRev kk).map σ).coeff 3 = Fv kk 3 / 4 := by
      have := g_coeff kk (by norm_num : (3 : ℕ) ≤ 6)
      simpa [div_eq_inv_mul] using this
    have hcoeff4 : ((fRev kk).map σ).coeff 4 = Fv kk 4 / 4 := by
      have := g_coeff kk (by norm_num : (4 : ℕ) ≤ 6)
      simpa [div_eq_inv_mul] using this
    have hcoeff5 : ((fRev kk).map σ).coeff 5 = Fv kk 5 / 4 := by
      have := g_coeff kk (by norm_num : (5 : ℕ) ≤ 6)
      simpa [div_eq_inv_mul] using this
    have hcoeff6 : ((fRev kk).map σ).coeff 6 = Fv kk 6 / 4 := by
      have := g_coeff kk (by norm_num : (6 : ℕ) ≤ 6)
      simpa [div_eq_inv_mul] using this

    -- Helper to prove each component
    have hcomp0 : g.f0.Mem ((Sext.ofPoly ((fRev kk).map σ)).f0) := by
      -- (Sext.ofPoly p).f0 = p.coeff 0
      have htarget : ((Sext.ofPoly ((fRev kk).map σ)).f0) = ((fRev kk).map σ).coeff 0 := rfl
      rw [htarget, hcoeff0]
      -- Goal: g.f0.Mem (Fv kk 0 / 4)
      -- g.f0 = (ballOpsF k).mul F.f0 i
      rw [← hg0]
      -- Goal: ((ballOpsF k).mul F.f0 i).Mem (Fv kk 0 / 4)
      -- hrel.mul hF0 hi_mem : ((ballOpsF k).mul F.f0 i).Mem ((fieldOps Kv).mul (Fv kk 0) ((4 : ℤ) : Kv)⁻¹)
      have hmem_mul := hrel.mul hF0 hi_mem
      -- hmem_mul : ((ballOpsF k).mul F.f0 i).Mem ((fieldOps Kv).mul (Fv kk 0) ((4 : ℤ) : Kv)⁻¹)
      -- (fieldOps Kv).mul is field multiplication, and ((4 : ℤ) : Kv)⁻¹ = (4⁻¹ : Kv)
      -- So the RHS simplifies to Fv kk 0 * (4⁻¹ : Kv) = Fv kk 0 / 4
      simpa [div_eq_mul_inv, ← hy_eq, fieldOps] using hmem_mul

    have hcomp1 : g.f1.Mem ((Sext.ofPoly ((fRev kk).map σ)).f1) := by
      have htarget : ((Sext.ofPoly ((fRev kk).map σ)).f1) = ((fRev kk).map σ).coeff 1 := rfl
      rw [htarget, hcoeff1, ← hg1]
      have hmem_mul := hrel.mul hF1 hi_mem
      simpa [div_eq_mul_inv, ← hy_eq, fieldOps] using hmem_mul

    have hcomp2 : g.f2.Mem ((Sext.ofPoly ((fRev kk).map σ)).f2) := by
      have htarget : ((Sext.ofPoly ((fRev kk).map σ)).f2) = ((fRev kk).map σ).coeff 2 := rfl
      rw [htarget, hcoeff2, ← hg2]
      have hmem_mul := hrel.mul hF2 hi_mem
      simpa [div_eq_mul_inv, ← hy_eq, fieldOps] using hmem_mul

    have hcomp3 : g.f3.Mem ((Sext.ofPoly ((fRev kk).map σ)).f3) := by
      have htarget : ((Sext.ofPoly ((fRev kk).map σ)).f3) = ((fRev kk).map σ).coeff 3 := rfl
      rw [htarget, hcoeff3, ← hg3]
      have hmem_mul := hrel.mul hF3 hi_mem
      simpa [div_eq_mul_inv, ← hy_eq, fieldOps] using hmem_mul

    have hcomp4 : g.f4.Mem ((Sext.ofPoly ((fRev kk).map σ)).f4) := by
      have htarget : ((Sext.ofPoly ((fRev kk).map σ)).f4) = ((fRev kk).map σ).coeff 4 := rfl
      rw [htarget, hcoeff4, ← hg4]
      have hmem_mul := hrel.mul hF4 hi_mem
      simpa [div_eq_mul_inv, ← hy_eq, fieldOps] using hmem_mul

    have hcomp5 : g.f5.Mem ((Sext.ofPoly ((fRev kk).map σ)).f5) := by
      have htarget : ((Sext.ofPoly ((fRev kk).map σ)).f5) = ((fRev kk).map σ).coeff 5 := rfl
      rw [htarget, hcoeff5, ← hg5]
      have hmem_mul := hrel.mul hF5 hi_mem
      simpa [div_eq_mul_inv, ← hy_eq, fieldOps] using hmem_mul

    have hcomp6 : g.f6.Mem ((Sext.ofPoly ((fRev kk).map σ)).f6) := by
      have htarget : ((Sext.ofPoly ((fRev kk).map σ)).f6) = ((fRev kk).map σ).coeff 6 := rfl
      rw [htarget, hcoeff6, ← hg6]
      have hmem_mul := hrel.mul hF6 hi_mem
      simpa [div_eq_mul_inv, ← hy_eq, fieldOps] using hmem_mul

    -- Assemble the 7 component proofs
    exact ⟨hcomp0, hcomp1, hcomp2, hcomp3, hcomp4, hcomp5, hcomp6⟩

/-! ## The pairs `D_i` -/

/-- **The ball of the pair `D_i`.** -/
theorem mem_DBall {k : Ctx} (hk : k.Ok) (kk : Fin 2) (i : Fin 7) {F : Sext Ball}
    (hF : Sext.Rel (fun x b => b.Mem x) (FvSext kk) F) {sN sA : N3} {eN eA : ℕ} {d : Mum Ball}
    (h : DBall k kk i F sN eN sA eA = some d) :
    Mum.Rel (fun x b => b.Mem x) (DptMum kk i) d := by
  set R := fun x b => Ball.Mem b x
  have hO := rel_ballOpsF hk
  -- Unfold DBall and simplify
  unfold DBall at h
  simp at h
  -- h : (sigQ ...).bind (fun p => (sigQ ...).bind (fun r => ...)) = some d
  -- Now expand the bind chain step by step using Option.bind_eq_some_iff
  -- First bind: sigQ ...
  rw [Option.bind_eq_some_iff] at h
  -- h : ∃ (p : Ball), sigQ k (SelmerSpan.pLi ↑kk ↑i) (SelmerSpan.pMi ↑kk ↑i) = some p ∧
  --   (sigQ k (SelmerSpan.rLi ↑kk ↑i) (SelmerSpan.rMi ↑kk ↑i)).bind (fun r => ...) p = some d
  obtain ⟨p, hp, h⟩ := h
  -- hp : sigQ k (SelmerSpan.pLi ↑kk ↑i) (SelmerSpan.pMi ↑kk ↑i) = some p
  -- h : (sigQ k (SelmerSpan.rLi ↑kk ↑i) (SelmerSpan.rMi ↑kk ↑i)).bind (fun r => ...) p = some d
  -- But wait, the bind doesn't depend on p! The first bind is just a pure value.
  -- Actually, looking at the expression, the first bind is:
  -- (sigQ ...).bind (fun p => (sigQ ...).bind (fun r => ...))
  -- So the first bind binds p, and the rest doesn't depend on p.
  -- Let me check: after dsimp, the expression is:
  -- ((sigQ ...).bind fun p => (sigQ ...).bind fun r => ...)
  -- So the first bind is on sigQ, and the function ignores p.
  -- This means we can get a proof about p from hp, and then h is the rest.
  -- Now expand the second bind
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨r, hr, h⟩ := h
  -- hr : sigQ k (SelmerSpan.rLi ↑kk ↑i) (SelmerSpan.rMi ↑kk ↑i) = some r
  -- h : (Ball.sqrt k ...).bind (fun n => ...) r = some d
  -- Now expand the third bind (sqrt)
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, h⟩ := h
  -- hn : Ball.sqrt k (o.normN p r ...) sN eN = some n
  -- h : (if ... then ... else none) = some d
  -- Now split on the if condition
  by_cases hne1 : Ball.nearOK k n (Ball.ofApprox k (SelmerSpan.hb1 (kk : ℕ) (i : ℕ)) (SelmerSpan.P1 (kk : ℕ) (i : ℕ))) = true
  · -- true branch
    simp only [hne1, ite_true] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    -- ha : Ball.sqrt k (o.normA p ... n) sA eA = some a
    -- h : (if ... then ... else none) = some d
    by_cases hne2 : Ball.nearOK k a (Ball.ofApprox k (SelmerSpan.hb2 (kk : ℕ) (i : ℕ)) (SelmerSpan.P2 (kk : ℕ) (i : ℕ))) = true
    · -- true branch
      simp only [hne2, ite_true] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨b, hb, h⟩ := h
      -- hb : (ballOpsF k).sqB Z1 a = some b
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, h⟩ := h
      -- hc : (ballOpsF k).sqC p a b = some c
      -- h : some { u0 := r, u1 := p, v0 := c, v1 := b } = some d
      have hd : d = { u0 := r, u1 := p, v0 := c, v1 := b } := by
        simpa [Option.some.injEq] using h.symm
      rw [hd]
      -- Goal: Mum.Rel R (DptMum kk i) { u0 := r, u1 := p, v0 := c, v1 := b }
      unfold DptMum Mum.Rel
      -- Goal: (r.Mem (σ (SelmerSpan.rG kk i))) ∧ (p.Mem (σ (SelmerSpan.pG kk i))) ∧
      --   (c.Mem (SelmerSpan.sqC (σ (SelmerSpan.pG kk i)) (SelmerSpan.Z1v kk i) (SelmerSpan.av kk i))) ∧
      --   (b.Mem (SelmerSpan.sqB (SelmerSpan.Z1v kk i) (SelmerSpan.av kk i)))
      -- Now prove each component
      rcases hF with ⟨hF0, hF1, hF2, hF3, hF4, hF5, hF6⟩
      -- 1. r.Mem (σ (rG kk i))
      have hr_mem : R (σ (SelmerSpan.rG (kk : ℕ) (i : ℕ))) r := by
        simpa [SelmerSpan.rG, R] using mem_sigQ hk hr
      -- 2. p.Mem (σ (pG kk i))
      have hp_mem : R (σ (SelmerSpan.pG (kk : ℕ) (i : ℕ))) p := by
        simpa [SelmerSpan.pG, R] using mem_sigQ hk hp
      -- Extract Z1 and Z0 from hn
      set Z1 := (ballOpsF k).divR1 p r F.f0 F.f1 F.f2 F.f3 F.f4 F.f5 F.f6
      set Z0 := (ballOpsF k).divR0 p r F.f0 F.f1 F.f2 F.f3 F.f4 F.f5 F.f6
      have hZ1 : (ballOpsF k).divR1 p r F.f0 F.f1 F.f2 F.f3 F.f4 F.f5 F.f6 = Z1 := rfl
      have hZ0 : (ballOpsF k).divR0 p r F.f0 F.f1 F.f2 F.f3 F.f4 F.f5 F.f6 = Z0 := rfl
      -- Now hn : Ball.sqrt k ((ballOpsF k).normN p r Z1 Z0) sN eN = some n
      -- and ha : Ball.sqrt k ((ballOpsF k).normA p Z1 Z0 n) sA eA = some a
      -- Use hO to relate the ball operations to field operations
      -- hO.divR1 gives us that the ball of divR1 is related to the field divR1
      have hZ1_mem : R ((fieldOps Kv).divR1 (σ (SelmerSpan.pG (kk : ℕ) (i : ℕ))) (σ (SelmerSpan.rG (kk : ℕ) (i : ℕ))) (SelmerSpan.Fv (kk : ℕ) 0) (SelmerSpan.Fv (kk : ℕ) 1) (SelmerSpan.Fv (kk : ℕ) 2) (SelmerSpan.Fv (kk : ℕ) 3) (SelmerSpan.Fv (kk : ℕ) 4) (SelmerSpan.Fv (kk : ℕ) 5) (SelmerSpan.Fv (kk : ℕ) 6)) Z1 := by
        -- hO.divR1 hp_mem hr_mem hF0 hF1 hF2 hF3 hF4 hF5 hF6
        -- But hO.divR1 expects 9 arguments (h0..h8)
        -- Actually, hO.divR1 : R (o.divR1 x0..x8) (p.divR1 y0..y8)
        -- given R xj yj for j=0..8
        -- We have: hp_mem : R (σ pG) p, hr_mem : R (σ rG) r, hFj : R (Fv kk j) F.fj
        -- But we need the arguments in the right order
        -- The divR1 in the do block uses: o.divR1 p r F.f0 ... F.f6
        -- where o = ballOpsF k
        -- So we need: R ((ballOpsF k).divR1 p r F.f0 ... F.f6) ((fieldOps Kv).divR1 (σ pG) (σ rG) (Fv kk 0) ... (Fv kk 6))
        -- hO.divR1 gives: R (o.divR1 x0..x8) (p.divR1 y0..y8) given R xj yj
        -- Here o = ballOpsF k, p = fieldOps Kv
        -- x0 = p, y0 = σ pG
        -- x1 = r, y1 = σ rG
        -- x2 = F.f0, y2 = Fv kk 0
        -- etc.
        apply hO.divR1 hp_mem hr_mem hF0 hF1 hF2 hF3 hF4 hF5 hF6
      -- Similarly for divR0
      have hZ0_mem : R ((fieldOps Kv).divR0 (σ (SelmerSpan.pG (kk : ℕ) (i : ℕ))) (σ (SelmerSpan.rG (kk : ℕ) (i : ℕ))) (SelmerSpan.Fv (kk : ℕ) 0) (SelmerSpan.Fv (kk : ℕ) 1) (SelmerSpan.Fv (kk : ℕ) 2) (SelmerSpan.Fv (kk : ℕ) 3) (SelmerSpan.Fv (kk : ℕ) 4) (SelmerSpan.Fv (kk : ℕ) 5) (SelmerSpan.Fv (kk : ℕ) 6)) Z0 := by
        apply hO.divR0 hp_mem hr_mem hF0 hF1 hF2 hF3 hF4 hF5 hF6
      -- Now use fieldOps_divR1 and fieldOps_divR0 to relate to SelmerSpan
      -- fieldOps_divR1 : (fieldOps F).divR1 p r g0..g6 = SelmerSpan.divR1 p r g0..g6
      -- So (fieldOps Kv).divR1 (σ pG) (σ rG) (Fv kk 0) ... (Fv kk 6) = SelmerSpan.divR1 (σ pG) (σ rG) (Fv kk 0) ... (Fv kk 6)
      -- And SelmerSpan.divR1 (σ pG) (σ rG) (Fv kk 0) ... = Z1v kk i (by definition)
      -- Let's check: Z1v kk i = divR1 (σ (pG k i)) (σ (rG k i)) (Fv k 0) ... (Fv k 6)
      -- So we can rewrite
      have hZ1v : (fieldOps Kv).divR1 (σ (SelmerSpan.pG (kk : ℕ) (i : ℕ))) (σ (SelmerSpan.rG (kk : ℕ) (i : ℕ))) (SelmerSpan.Fv (kk : ℕ) 0) (SelmerSpan.Fv (kk : ℕ) 1) (SelmerSpan.Fv (kk : ℕ) 2) (SelmerSpan.Fv (kk : ℕ) 3) (SelmerSpan.Fv (kk : ℕ) 4) (SelmerSpan.Fv (kk : ℕ) 5) (SelmerSpan.Fv (kk : ℕ) 6) = SelmerSpan.Z1v (kk : ℕ) (i : ℕ) := by
        simp [SelmerSpan.Z1v, fieldOps_divR1]
      have hZ0v : (fieldOps Kv).divR0 (σ (SelmerSpan.pG (kk : ℕ) (i : ℕ))) (σ (SelmerSpan.rG (kk : ℕ) (i : ℕ))) (SelmerSpan.Fv (kk : ℕ) 0) (SelmerSpan.Fv (kk : ℕ) 1) (SelmerSpan.Fv (kk : ℕ) 2) (SelmerSpan.Fv (kk : ℕ) 3) (SelmerSpan.Fv (kk : ℕ) 4) (SelmerSpan.Fv (kk : ℕ) 5) (SelmerSpan.Fv (kk : ℕ) 6) = SelmerSpan.Z0v (kk : ℕ) (i : ℕ) := by
        simp [SelmerSpan.Z0v, fieldOps_divR0]
      -- Now we have: R (SelmerSpan.Z1v kk i) Z1 and R (SelmerSpan.Z0v kk i) Z0
      have hZ1_mem' : R (SelmerSpan.Z1v kk i) Z1 := by
        simpa [hZ1v] using hZ1_mem
      have hZ0_mem' : R (SelmerSpan.Z0v kk i) Z0 := by
        simpa [hZ0v] using hZ0_mem
      -- Now use hO.normN to get the ball for Nv
      have hN_mem : R ((fieldOps Kv).normN (σ (SelmerSpan.pG (kk : ℕ) (i : ℕ))) (σ (SelmerSpan.rG (kk : ℕ) (i : ℕ))) (SelmerSpan.Z1v (kk : ℕ) (i : ℕ)) (SelmerSpan.Z0v (kk : ℕ) (i : ℕ))) ((ballOpsF k).normN p r Z1 Z0) := by
        apply hO.normN hp_mem hr_mem hZ1_mem' hZ0_mem'
      -- Relate to SelmerSpan.Nv
      have hNv_eq : (fieldOps Kv).normN (σ (SelmerSpan.pG (kk : ℕ) (i : ℕ))) (σ (SelmerSpan.rG (kk : ℕ) (i : ℕ))) (SelmerSpan.Z1v (kk : ℕ) (i : ℕ)) (SelmerSpan.Z0v (kk : ℕ) (i : ℕ)) = SelmerSpan.Nv (kk : ℕ) (i : ℕ) := by
        simp [fieldOps_normN, SelmerSpan.Nv]
      have hN_mem' : R (SelmerSpan.Nv kk i) ((ballOpsF k).normN p r Z1 Z0) := by
        simpa [hNv_eq] using hN_mem
      -- Now hn : Ball.sqrt k ((ballOpsF k).normN p r Z1 Z0) sN eN = some n
      -- Use Ball.exists_mem_sqrt
      have h_sqrt_n := Ball.exists_mem_sqrt hk hN_mem' hn
      rcases h_sqrt_n with ⟨y, hy_sq, hy_mem⟩
      -- hy_sq : y ^ 2 = SelmerSpan.Nv kk i
      -- hy_mem : n.Mem y
      -- Now use Ball.mem_ofApprox to get that SelmerSpan.nv kk i is in the certificate ball
      have h_nv_mem : (Ball.ofApprox k (SelmerSpan.hb1 kk i) (SelmerSpan.P1 kk i)).Mem (SelmerSpan.nv kk i) := by
        apply Ball.mem_ofApprox hk
        exact SelmerSpan.approx_n kk i
      -- Now use Ball.eq_of_nearOK to show y = nv kk i
      have hnv_sq : (SelmerSpan.nv kk i) ^ 2 = SelmerSpan.Nv kk i := by
        simpa using SelmerSpan.nv_sq kk i
      have hy_eq_nv : y = SelmerSpan.nv kk i := by
        apply Ball.eq_of_nearOK hk hy_mem h_nv_mem ?_ hne1
        rw [hy_sq, hnv_sq]
      -- So n.Mem (SelmerSpan.nv kk i)
      have hn_mem_nv : n.Mem (SelmerSpan.nv kk i) := by
        rwa [hy_eq_nv] at hy_mem
      -- Now use hO.normA to get the ball for the second sqrt
      have hA_mem : R ((fieldOps Kv).normA (σ (SelmerSpan.pG kk i)) (SelmerSpan.Z1v kk i) (SelmerSpan.Z0v kk i) (SelmerSpan.nv kk i)) ((ballOpsF k).normA p Z1 Z0 n) := by
        apply hO.normA hp_mem hZ1_mem' hZ0_mem' hn_mem_nv
      -- Relate to the radicand for av
      have hA_eq : (fieldOps Kv).normA (σ (SelmerSpan.pG kk i)) (SelmerSpan.Z1v kk i) (SelmerSpan.Z0v kk i) (SelmerSpan.nv kk i) = 2 * SelmerSpan.Z0v kk i - σ (SelmerSpan.pG kk i) * SelmerSpan.Z1v kk i + 2 * SelmerSpan.nv kk i := by
        simp [fieldOps_normA]
      have hA_mem' : R (2 * SelmerSpan.Z0v kk i - σ (SelmerSpan.pG kk i) * SelmerSpan.Z1v kk i + 2 * SelmerSpan.nv kk i) ((ballOpsF k).normA p Z1 Z0 n) := by
        simpa [hA_eq] using hA_mem
      -- Now ha : Ball.sqrt k ((ballOpsF k).normA p Z1 Z0 n) sA eA = some a
      have h_sqrt_a := Ball.exists_mem_sqrt hk hA_mem' ha
      rcases h_sqrt_a with ⟨z, hz_sq, hz_mem⟩
      -- hz_sq : z ^ 2 = 2*Z0v - pG*Z1v + 2*nv
      -- hz_mem : a.Mem z
      -- We also have av_sq and approx_a
      have hav_sq : (SelmerSpan.av kk i) ^ 2 = 2 * SelmerSpan.Z0v kk i - σ (SelmerSpan.pG kk i) * SelmerSpan.Z1v kk i + 2 * SelmerSpan.nv kk i := by
        simpa using SelmerSpan.av_sq kk i
      have h_av_mem : (Ball.ofApprox k (SelmerSpan.hb2 kk i) (SelmerSpan.P2 kk i)).Mem (SelmerSpan.av kk i) := by
        apply Ball.mem_ofApprox hk
        exact SelmerSpan.approx_a kk i
      have hz_eq_av : z = SelmerSpan.av kk i := by
        apply Ball.eq_of_nearOK hk hz_mem h_av_mem ?_ hne2
        rw [hz_sq, hav_sq]
      have ha_mem_av : a.Mem (SelmerSpan.av kk i) := by
        rwa [hz_eq_av] at hz_mem
      -- Now use hO.sqB to get the ball for sqB
      -- hO.sqB : OptRel R (o.sqB x0 x1) (p.sqB y0 y1)
      -- where o = fieldOps Kv, p = ballOpsF k
      -- So: OptRel R ((fieldOps Kv).sqB ...) ((ballOpsF k).sqB ...)
      have h_sqB_rel : OptRel R ((fieldOps Kv).sqB (SelmerSpan.Z1v kk i) (SelmerSpan.av kk i)) ((ballOpsF k).sqB Z1 a) := by
        apply hO.sqB hZ1_mem' ha_mem_av
      -- hb : (ballOpsF k).sqB Z1 a = some b
      -- OptRel R x y := ∀ b, y = some b → ∃ a, x = some a ∧ R a b
      -- So h_sqB_rel b hb : ∃ a', (fieldOps Kv).sqB ... = some a' ∧ R a' b
      rcases h_sqB_rel b hb with ⟨b', hb'_eq, hb_mem⟩
      -- hb'_eq : (fieldOps Kv).sqB (Z1v kk i) (av kk i) = some b'
      -- Use fieldOps_sqB
      have hb'_formula : b' = SelmerSpan.sqB (SelmerSpan.Z1v kk i) (SelmerSpan.av kk i) := by
        apply fieldOps_sqB hb'_eq
      -- So b.Mem (SelmerSpan.sqB (Z1v kk i) (av kk i))
      have hb_mem_sqB : b.Mem (SelmerSpan.sqB (SelmerSpan.Z1v kk i) (SelmerSpan.av kk i)) := by
        rw [hb'_formula] at hb_mem
        exact hb_mem
      -- Now use hO.sqC to get the ball for sqC
      -- hO.sqC : OptRel R (o.sqC x0 x1 x2) (p.sqC y0 y1 y2)
      -- where o = fieldOps Kv, p = ballOpsF k
      -- So: OptRel R ((fieldOps Kv).sqC ...) ((ballOpsF k).sqC ...)
      have h_sqC_rel : OptRel R ((fieldOps Kv).sqC (σ (SelmerSpan.pG kk i)) (SelmerSpan.av kk i) (SelmerSpan.sqB (SelmerSpan.Z1v kk i) (SelmerSpan.av kk i))) ((ballOpsF k).sqC p a b) := by
        apply hO.sqC hp_mem ha_mem_av hb_mem_sqB
      -- hc : (ballOpsF k).sqC p a b = some c
      -- So h_sqC_rel c hc : ∃ a', (fieldOps Kv).sqC ... = some a' ∧ R a' c
      rcases h_sqC_rel c hc with ⟨c', hc'_eq, hc_mem⟩
      -- hc'_eq : (fieldOps Kv).sqC (σ pG) (av kk i) (sqB (Z1v kk i) (av kk i)) = some c'
      -- Use fieldOps_sqC
      have hc'_formula : c' = SelmerSpan.sqC (σ (SelmerSpan.pG kk i)) (SelmerSpan.Z1v kk i) (SelmerSpan.av kk i) := by
        apply fieldOps_sqC hc'_eq
      -- So c.Mem (SelmerSpan.sqC (σ pG) (Z1v) (av))
      have hc_mem_sqC : c.Mem (SelmerSpan.sqC (σ (SelmerSpan.pG kk i)) (SelmerSpan.Z1v kk i) (SelmerSpan.av kk i)) := by
        rw [hc'_formula] at hc_mem
        exact hc_mem
      -- Now assemble the final result
      exact ⟨hr_mem, hp_mem, hc_mem_sqC, hb_mem_sqB⟩
    · -- false branch: hne2 is false
      rw [ite_eq_right hne2] at h
      simp at h
  · -- false branch: hne1 is false
    rw [ite_eq_right hne1] at h
    simp at h

/-! ## The base pair and `Amat` -/

theorem mem_bKBall {k : Ctx} (hk : k.Ok) (kk : Fin 2) {g : Sext Ball}
    (hg : Sext.Rel (fun x b => b.Mem x) (Sext.ofPoly ((fRev kk).map σ)) g) {sB : N3} {eB : ℕ}
    {b : Ball} (h : bKBall k kk g sB eB = some b) : b.Mem (bK kk) := by
  -- Unfold bKBall in h
  unfold bKBall at h
  -- h : (let o := ballOpsF k; ...).bind (fun b => ...) = some b
  -- Simplify the let
  simp at h
  -- Now h : ((ballOpsF k).transC0 ((kk : ℕ) : ℤ) g).sqrt k sB eB |>.bind (fun b => ...) = some b
  -- From h, the bind must have succeeded, so the sqrt must have returned some b0
  -- and the if condition must have been true for b0, and b = b0
  rcases Option.bind_eq_some_iff.mp h with ⟨b0, h_sqrt, h_rest⟩
  -- h_sqrt : ((ballOpsF k).transC0 ((kk : ℕ) : ℤ) g).sqrt k sB eB = some b0
  -- h_rest : (if Ball.nearOK k ((ballOpsF k).mul ((ballOpsF k).ofInt 2) b0) (Ball.ofApprox k (bT kk) 3) then some b0 else none) = some b
  split_ifs at h_rest with hcond
  · -- h_rest : some b0 = some b, so b = b0
    injection h_rest with hb_eq
    -- hb_eq : b0 = b
    rw [← hb_eq]
    -- Goal: b0.Mem (bK kk)
    -- Now we have h_sqrt : sqrt returned some b0
    -- We need to show that the radicand ball contains (fK kk).coeff 0
    have h_radicand : ((ballOpsF k).transC0 ((kk : ℕ) : ℤ) g).Mem ((fK kk).coeff 0) := by
      -- From rel_ballOpsF hk, we know that the ball computation is related to the field computation
      have h_rel := (rel_ballOpsF hk).transC0 ((kk : ℕ) : ℤ) hg
      -- h_rel : ((ballOpsF k).transC0 ((kk : ℕ) : ℤ) g).Mem ((fieldOps Kv).transC0 ((kk : ℕ) : ℤ) (Sext.ofPoly ((fRev kk).map σ)))
      -- And fieldOps_transC0 says that equals (fK kk).coeff 0
      have h_exact : (fieldOps Kv).transC0 ((kk : ℕ) : ℤ) (Sext.ofPoly ((fRev kk).map σ)) = (fK kk).coeff 0 := by
        have h_deg : ((fRev kk).map σ).natDegree ≤ 6 := by
          have h_eq := natDegree_FK kk
          -- h_eq : ((fRev kk).map σ).natDegree = 6
          linarith
        exact fieldOps_transC0 ((kk : ℕ) : ℤ) h_deg
      -- Now rewrite using h_exact
      rw [h_exact] at h_rel
      exact h_rel
    -- Now use Ball.exists_mem_sqrt to get a square root y
    have h_mem_sqrt := Ball.exists_mem_sqrt hk h_radicand h_sqrt
    rcases h_mem_sqrt with ⟨y, hy_sq, hy_mem⟩
    -- hy_sq : y ^ 2 = (fK kk).coeff 0
    -- hy_mem : b0.Mem y
    -- Now we need to show that y = bK kk
    -- We know that 2*y is in o.mul (o.ofInt 2) b0
    have hy2_mem : ((ballOpsF k).mul (Ball.ofInt k 2) b0).Mem (2 * y) := by
      -- Using rel_ballOpsF hk and Ball.mem_ofInt
      have h_mul := (rel_ballOpsF hk).mul (Ball.mem_ofInt hk 2) hy_mem
      -- h_mul : ((ballOpsF k).mul (Ball.ofInt k 2) b0).Mem ((fieldOps Kv).mul 2 y)
      -- (fieldOps Kv).mul 2 y = 2 * y
      simpa [fieldOps, mul_comm] using h_mul
    -- We also know that 2 * bK kk is in Ball.ofApprox k (bT kk) 3
    have h_bK_mem : (Ball.ofApprox k (bT kk) 3).Mem (2 * bK kk) := by
      have h_approx := bK_approx kk
      -- h_approx : Approx (2 * bK kk) (bT kk) 3
      exact Ball.mem_ofApprox hk h_approx
    -- Now we have hcond : Ball.nearOK k ((ballOpsF k).mul ((ballOpsF k).ofInt 2) b0) (Ball.ofApprox k (bT kk) 3) = true
    -- This means 2*y and 2*bK kk are close
    -- Using Ball.eq_of_nearOK, we can deduce 2*y = 2*bK kk
    have h_eq : 2 * y = 2 * bK kk := by
      -- Ball.eq_of_nearOK hk hx hy h2 h
      -- hx : x.Mem bx, hy : y.Mem bY, h2 : x^2 = y^2, h : Ball.nearOK k bx bY = true
      -- We need: (2*y)^2 = (2*bK kk)^2
      -- Since y^2 = (fK kk).coeff 0 and bK kk^2 = (fK kk).coeff 0
      have h_sq_eq : (2 * y) ^ 2 = (2 * bK kk) ^ 2 := by
        calc
          (2 * y) ^ 2 = 4 * (y ^ 2) := by ring
          _ = 4 * ((fK kk).coeff 0) := by rw [hy_sq]
          _ = 4 * (bK kk ^ 2) := by rw [bK_sq kk]
          _ = (2 * bK kk) ^ 2 := by ring
      exact Ball.eq_of_nearOK hk hy2_mem h_bK_mem h_sq_eq hcond
    -- Now cancel 2
    have h_y_eq : y = bK kk := by
      -- From 2*y = 2*bK kk, cancel 2
      -- Using mul_left_cancel₀ KvArith.two_ne_zero_Kv
      refine mul_left_cancel₀ KvArith.two_ne_zero_Kv ?_
      -- Need: 2 * y = 2 * bK kk
      -- h_eq is exactly that
      exact h_eq
    -- Now we have hy_mem : b0.Mem y and h_y_eq : y = bK kk
    -- So b0.Mem (bK kk)
    rw [h_y_eq] at hy_mem
    exact hy_mem

/-- The coefficients 0 and 1 of the base branch `v0 = V0 mod X²`: `b` and `b f₁/(2 f₀)`. -/
theorem v0_coeff_baseKv (kk : Fin 2) :
    (baseKv kk).toSetup.v0.coeff 0 = bK kk ∧
      (baseKv kk).toSetup.v0.coeff 1 = bK kk * ((fK kk).coeff 1 / (2 * (fK kk).coeff 0)) := by
  have hV0_def : (baseKv kk).toSetup.v0 = ((baseKv kk).toSetup.V0) %ₘ (X ^ 2) := rfl
  have hV0_eq : (baseKv kk).toSetup.V0 = C (bK kk) * FurioLombardo.Vendor.Toolbox.G2Formal.Taylor.tβ (fK kk) := rfl
  have h_mod_add_div : ((baseKv kk).toSetup.V0) %ₘ (X ^ 2) + (X ^ 2) * (((baseKv kk).toSetup.V0) /ₘ (X ^ 2)) = (baseKv kk).toSetup.V0 := by
    rw [modByMonic_add_div]
  have hcoeff0 : (((baseKv kk).toSetup.V0) %ₘ (X ^ 2)).coeff 0 = ((baseKv kk).toSetup.V0).coeff 0 := by
    have h := congrArg (fun p : Kv[X] => p.coeff 0) h_mod_add_div
    rw [coeff_add, coeff_X_pow_mul' ((baseKv kk).toSetup.V0 /ₘ (X ^ 2)) 2 0, ite_eq_right (by decide : ¬ 2 ≤ 0)] at h
    simpa using h
  have hcoeff1 : (((baseKv kk).toSetup.V0) %ₘ (X ^ 2)).coeff 1 = ((baseKv kk).toSetup.V0).coeff 1 := by
    have h := congrArg (fun p : Kv[X] => p.coeff 1) h_mod_add_div
    rw [coeff_add, coeff_X_pow_mul' ((baseKv kk).toSetup.V0 /ₘ (X ^ 2)) 2 1, ite_eq_right (by decide : ¬ 2 ≤ 1)] at h
    simpa using h
  have hV0_coeff0 : ((baseKv kk).toSetup.V0).coeff 0 = bK kk := by
    rw [hV0_eq, coeff_C_mul, FurioLombardo.Vendor.Toolbox.G2Formal.Taylor.tβ_coeff_zero, mul_one]
  have hV0_coeff1 : ((baseKv kk).toSetup.V0).coeff 1 = bK kk * ((fK kk).coeff 1 / (2 * (fK kk).coeff 0)) := by
    rw [hV0_eq, coeff_C_mul]
    have h_tβ_coeff1 : (FurioLombardo.Vendor.Toolbox.G2Formal.Taylor.tβ (fK kk)).coeff 1 = (fK kk).coeff 1 / (2 * (fK kk).coeff 0) := by
      simp [FurioLombardo.Vendor.Toolbox.G2Formal.Taylor.tβ, FurioLombardo.Vendor.Toolbox.G2Formal.Taylor.tb1, coeff_add, coeff_C_mul, coeff_X_pow, coeff_one]
    rw [h_tβ_coeff1]
  rw [hV0_def, hcoeff0, hV0_coeff0, hcoeff1, hV0_coeff1]
  exact And.intro rfl rfl

theorem mem_E0Ball {k : Ctx} (hk : k.Ok) (kk : Fin 2) {g : Sext Ball}
    (hg : Sext.Rel (fun x b => b.Mem x) (Sext.ofPoly ((fRev kk).map σ)) g) {b : Ball}
    (hb : b.Mem (bK kk)) {e : Mum Ball} (h : E0Ball k kk g b = some e) :
    Mum.Rel (fun x b => b.Mem x) (E0Mum kk) e := by
  let o := ballOpsF k
  let a : ℤ := (kk : ℕ)
  -- Unfold E0Ball in h
  simp only [E0Ball, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨i, hi, h⟩ := h
  -- h : ⟨o.ofInt (a * a), o.ofInt (-(2 * a)), ...⟩ = e
  rw [← h]
  -- Now goal: Mum.Rel (fun x b => b.Mem x) (E0Mum kk) ⟨...⟩
  unfold E0Mum
  -- Goal: 4 memberships
  have h_natDegree : ((fRev kk).map σ).natDegree ≤ 6 := by
    have hgood : GoodSextic ((fRev kk).map σ) := goodSextic_fRev_Kv kk
    have hdeg := hgood.natDegree_eq
    rw [hdeg]
  -- Helper: relate (fieldOps Kv).transC0 to the polynomial coefficient
  have h_field_transC0 : (fieldOps Kv).transC0 a (Sext.ofPoly ((fRev kk).map σ)) = (ConcreteKv.fK kk).coeff 0 := by
    rw [fieldOps_transC0 a h_natDegree, ConcreteKv.fK]
    simp [aK, a]
  -- Helper: relate (fieldOps Kv).transC1 to the polynomial coefficient
  have h_field_transC1 : (fieldOps Kv).transC1 a (Sext.ofPoly ((fRev kk).map σ)) = (ConcreteKv.fK kk).coeff 1 := by
    rw [fieldOps_transC1 a h_natDegree, ConcreteKv.fK]
    simp [aK, a]
  -- Relate the ball operations via rel_ballOpsF
  have h_rel_transC0_field : (o.transC0 a g).Mem ((fieldOps Kv).transC0 a (Sext.ofPoly ((fRev kk).map σ))) :=
    (rel_ballOpsF hk).transC0 a hg
  have h_rel_transC1_field : (o.transC1 a g).Mem ((fieldOps Kv).transC1 a (Sext.ofPoly ((fRev kk).map σ))) :=
    (rel_ballOpsF hk).transC1 a hg
  -- Get i.Mem ((2 * (ConcreteKv.fK kk).coeff 0)⁻¹) using (rel_ballOpsF hk).inv
  let f0 := (ConcreteKv.fK kk).coeff 0
  let f1 := (ConcreteKv.fK kk).coeff 1
  -- Show that the ball a = o.mul (o.ofInt 2) (o.transC0 a g) is related to the field value 2 * f0
  let x := (fieldOps Kv).mul ((fieldOps Kv).ofInt 2) ((fieldOps Kv).transC0 a (Sext.ofPoly ((fRev kk).map σ)))
  have hx : (o.mul (o.ofInt 2) (o.transC0 a g)).Mem x := by
    exact (rel_ballOpsF hk).mul ((rel_ballOpsF hk).ofInt 2) h_rel_transC0_field
  have hi_mem : i.Mem ((2 * f0)⁻¹) := by
    obtain ⟨y, hy_inv, hy_mem⟩ := (rel_ballOpsF hk).inv hx hi
    -- hy_inv : (fieldOps Kv).inv x = some y
    -- hy_mem : i.Mem y
    -- From fieldOps_inv_eq_some, y = x⁻¹
    have hy_eq : y = x⁻¹ := (fieldOps_inv_eq_some hy_inv).2
    have hx_inv : x⁻¹ = (2 * f0)⁻¹ := by
      calc
        x⁻¹ = (((fieldOps Kv).mul ((fieldOps Kv).ofInt 2) ((fieldOps Kv).transC0 a (Sext.ofPoly ((fRev kk).map σ))))⁻¹) := rfl
        _ = ((2 : Kv) * ((fieldOps Kv).transC0 a (Sext.ofPoly ((fRev kk).map σ))))⁻¹ := by
          simp [fieldOps]
        _ = ((2 : Kv) * f0)⁻¹ := by rw [h_field_transC0]
        _ = (2 * f0)⁻¹ := by ring
    rw [hy_eq, hx_inv] at hy_mem
    exact hy_mem
  -- Now we have hi_mem : i.Mem ((2 * f0)⁻¹)
  -- Use this to prove the fourth membership (v1.Mem ...)
  have hv1_mem_raw : (o.mul (o.transC1 a g) i).Mem ((fieldOps Kv).mul ((fieldOps Kv).transC1 a (Sext.ofPoly ((fRev kk).map σ))) ((2 * f0)⁻¹)) :=
    (rel_ballOpsF hk).mul h_rel_transC1_field hi_mem
  have hv1_mem : (o.mul b (o.mul (o.transC1 a g) i)).Mem (bK kk * (f1 * ((2 * f0)⁻¹))) := by
    -- First combine b with hv1_mem_raw
    have h_mul_b_v1raw : (o.mul b (o.mul (o.transC1 a g) i)).Mem ((fieldOps Kv).mul (bK kk) ((fieldOps Kv).mul ((fieldOps Kv).transC1 a (Sext.ofPoly ((fRev kk).map σ))) ((2 * f0)⁻¹))) :=
      (rel_ballOpsF hk).mul hb hv1_mem_raw
    -- Now rewrite the RHS to the desired form
    rw [h_field_transC1] at h_mul_b_v1raw
    simpa [fieldOps, f0, f1, mul_comm, mul_left_comm, mul_assoc, mul_inv_rev] using h_mul_b_v1raw
  -- Now the 4 memberships
  have h_mem_u0 : (o.ofInt (a * a)).Mem (aK kk ^ 2) := by
    have hmem := Ball.mem_ofInt hk (a * a)
    simpa [o, aK, a, ballOpsF, ballOps, sq] using hmem
  have h_mem_u1 : (o.ofInt (-(2 * a))).Mem (-(2 * aK kk)) := by
    have hmem := Ball.mem_ofInt hk (-(2 * a))
    simpa [o, aK, a, ballOpsF, ballOps] using hmem
  have h_mem_v1 : (o.mul b (o.mul (o.transC1 a g) i)).Mem ((baseKv kk).toSetup.v0.coeff 1) := by
    rcases v0_coeff_baseKv kk with ⟨hv0_0, hv0_1⟩
    rw [hv0_1]
    simpa [f0, f1, div_eq_mul_inv] using hv1_mem
  have h_mem_v0 : (o.sub b (o.mul (o.ofInt a) (o.mul b (o.mul (o.transC1 a g) i)))).Mem
      ((baseKv kk).toSetup.v0.coeff 0 - aK kk * (baseKv kk).toSetup.v0.coeff 1) := by
    rcases v0_coeff_baseKv kk with ⟨hv0_0, hv0_1⟩
    rw [hv0_0, hv0_1]
    -- Goal: (o.sub b ...).Mem (bK kk - aK kk * (bK kk * (f1 / (2 * f0))))
    have h_ofInt_a : (o.ofInt a).Mem (aK kk) := by
      have h := (rel_ballOpsF hk).ofInt a
      simpa [aK, a, fieldOps] using h
    -- Use hv1_mem which has the right type
    have h_mul_a_v1 : (o.mul (o.ofInt a) (o.mul b (o.mul (o.transC1 a g) i))).Mem (aK kk * (bK kk * (f1 * ((2 * f0)⁻¹)))) :=
      (rel_ballOpsF hk).mul h_ofInt_a hv1_mem
    have h_sub : (o.sub b (o.mul (o.ofInt a) (o.mul b (o.mul (o.transC1 a g) i)))).Mem
        ((fieldOps Kv).sub (bK kk) (aK kk * (bK kk * (f1 * ((2 * f0)⁻¹))))) :=
      (rel_ballOpsF hk).sub hb h_mul_a_v1
    simpa [f0, f1, div_eq_mul_inv, fieldOps, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h_sub
  exact ⟨h_mem_u0, h_mem_u1, h_mem_v0, h_mem_v1⟩

theorem mem_AmatBall {k : Ctx} (hk : k.Ok) (kk : Fin 2) {g : Sext Ball}
    (hg : Sext.Rel (fun x b => b.Mem x) (Sext.ofPoly ((fRev kk).map σ)) g) {b : Ball}
    (hb : b.Mem (bK kk)) {A : Mat2 Ball} (h : AmatBall k kk g b = some A) :
    A.a00.Mem (Amat kk 0 0) ∧ A.a01.Mem (Amat kk 0 1) ∧ A.a10.Mem (Amat kk 1 0) ∧
      A.a11.Mem (Amat kk 1 1) := by
  -- Expand the AmatBall definition in h
  simp only [AmatBall, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨i, hi, bi, hbi, rfl⟩ := h
  let fo := fieldOps Kv
  let bo := ballOpsF k
  let a : ℤ := (kk : ℕ)
  have h_rel := rel_ballOpsF hk
  have h_natDegree : ((fRev kk).map σ).natDegree ≤ 6 := by
    have hgood := (goodSextic_fRev_Kv kk)
    have hdeg := hgood.natDegree_eq
    omega
  have h_transC0 : fo.transC0 a (Sext.ofPoly ((fRev kk).map σ)) = (ConcreteKv.fK kk).coeff 0 := by
    rw [fieldOps_transC0 a h_natDegree, ConcreteKv.fK]
    simp [aK, a]
  have h_transC1 : fo.transC1 a (Sext.ofPoly ((fRev kk).map σ)) = (ConcreteKv.fK kk).coeff 1 := by
    rw [fieldOps_transC1 a h_natDegree, ConcreteKv.fK]
    simp [aK, a]
  -- Get membership for i: i.Mem (2 * f0)⁻¹
  have hi_mem : i.Mem (((2 : Kv) * (ConcreteKv.fK kk).coeff 0)⁻¹) := by
    have h_inv_arg : (bo.mul (bo.ofInt 2) (bo.transC0 a g)).Mem
        (fo.mul (fo.ofInt 2) (fo.transC0 a (Sext.ofPoly ((fRev kk).map σ)))) := by
      have h_ofInt : (bo.ofInt (2 : ℤ)).Mem (fo.ofInt (2 : ℤ)) := h_rel.ofInt 2
      have h_transC0' : (bo.transC0 a g).Mem (fo.transC0 a (Sext.ofPoly ((fRev kk).map σ))) :=
        h_rel.transC0 a hg
      exact h_rel.mul h_ofInt h_transC0'
    obtain ⟨y, hy, hiy⟩ := h_rel.inv h_inv_arg hi
    have hy_eq : y = (fo.mul (fo.ofInt 2) (fo.transC0 a (Sext.ofPoly ((fRev kk).map σ))))⁻¹ :=
      (fieldOps_inv_eq_some hy).2
    rw [h_transC0] at hy_eq
    have h_simp : fo.mul (fo.ofInt 2) ((ConcreteKv.fK kk).coeff 0) = (2 : Kv) * (ConcreteKv.fK kk).coeff 0 := by
      simp [fo, fieldOps]
    rw [h_simp] at hy_eq
    rw [hy_eq] at hiy
    exact hiy
  -- Get membership for bi: bi.Mem (bK kk)⁻¹
  have hbi_mem : bi.Mem ((bK kk)⁻¹) := by
    obtain ⟨y, hy, hiy⟩ := h_rel.inv hb hbi
    have hy_eq : y = (bK kk)⁻¹ := (fieldOps_inv_eq_some hy).2
    rw [hy_eq] at hiy
    exact hiy
  -- Now prove the four entries
  have h_ofInt_a : (bo.ofInt a).Mem (aK kk) := by
    have := h_rel.ofInt a
    -- this : (bo.ofInt a).Mem (fo.ofInt a)
    -- and fo.ofInt a = (a : Kv) = ((kk : ℕ) : Kv) = aK kk
    simpa [aK, a, fo, fieldOps] using this
  have h_a00 : (bo.mul bi (bo.ofInt a)).Mem (Amat kk 0 0) := by
    have h_mul := h_rel.mul hbi_mem h_ofInt_a
    convert h_mul using 1
    simp [Amat, Matrix.smul_apply, smul_eq_mul, fieldOps]
  have h_a10 : bi.Mem (Amat kk 1 0) := by
    convert hbi_mem using 1
    simp [Amat, Matrix.smul_apply, smul_eq_mul, fieldOps]
  have hg1_mem : (bo.neg (bo.mul (bo.transC1 a g) i)).Mem (g1K kk) := by
    have h_mul_arg : (bo.mul (bo.transC1 a g) i).Mem
        (fo.mul (fo.transC1 a (Sext.ofPoly ((fRev kk).map σ))) (((2 : Kv) * (ConcreteKv.fK kk).coeff 0)⁻¹)) := by
      have h_transC1' : (bo.transC1 a g).Mem (fo.transC1 a (Sext.ofPoly ((fRev kk).map σ))) :=
        h_rel.transC1 a hg
      exact h_rel.mul h_transC1' hi_mem
    have h_neg_arg : (bo.neg (bo.mul (bo.transC1 a g) i)).Mem
        (fo.neg (fo.mul (fo.transC1 a (Sext.ofPoly ((fRev kk).map σ))) (((2 : Kv) * (ConcreteKv.fK kk).coeff 0)⁻¹))) :=
      h_rel.neg h_mul_arg
    have h_simp : fo.neg (fo.mul (fo.transC1 a (Sext.ofPoly ((fRev kk).map σ))) (((2 : Kv) * (ConcreteKv.fK kk).coeff 0)⁻¹)) = g1K kk := by
      rw [h_transC1]
      simp [g1K, fo, fieldOps, div_eq_mul_inv]
    rw [h_simp] at h_neg_arg
    exact h_neg_arg
  have h_a11 : (bo.mul bi (bo.neg (bo.mul (bo.transC1 a g) i))).Mem (Amat kk 1 1) := by
    have h_mul := h_rel.mul hbi_mem hg1_mem
    convert h_mul using 1
    simp [Amat, Matrix.smul_apply, smul_eq_mul, fieldOps]
  have h_a01 : (bo.mul bi (bo.add (bo.ofInt 1) (bo.mul (bo.ofInt a) (bo.neg (bo.mul (bo.transC1 a g) i))))).Mem (Amat kk 0 1) := by
    have h_mul_a_g1 : (bo.mul (bo.ofInt a) (bo.neg (bo.mul (bo.transC1 a g) i))).Mem (aK kk * g1K kk) :=
      h_rel.mul h_ofInt_a hg1_mem
    have h_ofInt_one : (bo.ofInt (1 : ℤ)).Mem (fo.ofInt (1 : ℤ)) := h_rel.ofInt 1
    have h_add : (bo.add (bo.ofInt 1) (bo.mul (bo.ofInt a) (bo.neg (bo.mul (bo.transC1 a g) i)))).Mem
        (fo.add (fo.ofInt 1) (aK kk * g1K kk)) :=
      h_rel.add h_ofInt_one h_mul_a_g1
    have h_simp_add : fo.add (fo.ofInt 1) (aK kk * g1K kk) = (1 : Kv) + aK kk * g1K kk := by
      simp [fo, fieldOps]
    rw [h_simp_add] at h_add
    have h_mul := h_rel.mul hbi_mem h_add
    convert h_mul using 1
    simp [Amat, Matrix.smul_apply, smul_eq_mul, fieldOps]
  exact ⟨h_a00, h_a01, h_a10, h_a11⟩

end FurioLombardo.Discharge.M4Box
