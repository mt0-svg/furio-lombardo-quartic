import Mathlib
import FurioLombardo.Discharge.KvArith.Ball
import FurioLombardo.Discharge.KvArith.Ops
import FurioLombardo.Discharge.KvArith.Comp.BallOps

/-!
# Balls as a carrier of straight line programs: soundness (lane lean-kv-arith, D1)

`rel_ballOps`: `Ops.Rel (fieldOps Kv) (ballOps k) (fun x b => b.Mem x)`. For any program with a `_rel`
lemma, a successful ball run gives the exact run (all its inverses certified nonzero) inside the output
balls.
-/

namespace FurioLombardo.Discharge.KvArith

open FurioLombardo.Discharge.M4Cert

/-- **Soundness of ball arithmetic.** -/
theorem rel_ballOps {k : Ctx} (hk : k.Ok) :
    Ops.Rel (fieldOps Kv) (ballOps k) (fun x b => b.Mem x) where
  add hx hy := Ball.mem_add hk hx hy
  sub hx hy := Ball.mem_sub hk hx hy
  neg hx := Ball.mem_neg hk hx
  mul hx hy := Ball.mem_mul hk hx hy
  inv {x a b} hx hb := by
    simp only [ballOps, Option.map_eq_some_iff] at hb
    obtain ⟨c, hc, rfl⟩ := hb
    obtain ⟨hx0, hcx⟩ := Ball.mem_inv hk (Ball.mem_norm hk hx) hc
    exact ⟨x⁻¹, by simp [fieldOps, hx0], Ball.mem_norm hk hcx⟩
  ofInt z := Ball.mem_ofInt hk z

/-- Soundness of the carrier with recomputed valuation bounds. -/
theorem rel_ballOpsF {k : Ctx} (hk : k.Ok) :
    Ops.Rel (fieldOps Kv) (ballOpsF k) (fun x b => b.Mem x) where
  add hx hy := Ball.mem_fresh hk (Ball.mem_add hk hx hy)
  sub hx hy := (rel_ballOps hk).sub hx hy
  neg hx := (rel_ballOps hk).neg hx
  mul hx hy := (rel_ballOps hk).mul hx hy
  inv hx hb := (rel_ballOps hk).inv hx hb
  ofInt z := (rel_ballOps hk).ofInt z

end FurioLombardo.Discharge.KvArith
