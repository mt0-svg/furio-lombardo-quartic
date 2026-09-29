import FurioLombardo.Discharge.KvArith.Comp.Ball
import FurioLombardo.Discharge.KvArith.Comp.Ops

/-!
# Balls as a carrier of straight line programs: the computational part (lane lean-kv-arith, D1)

Products and inverses normalized. Soundness: `rel_ballOps` in `KvArith/BallOps.lean`.
-/

namespace FurioLombardo.Discharge.KvArith

/-- The ball carrier. -/
def ballOps (k : Ctx) : Ops Ball where
  add := Ball.add k
  sub := Ball.sub k
  neg := Ball.neg k
  mul := Ball.mul k
  inv b := (Ball.inv k (b.norm k)).map (Ball.norm k)
  ofInt := Ball.ofInt k

/-- The ball carrier with the valuation bound recomputed after each sum. Long chains with cancellation
in sums (the Cantor steps of the D_i values) need it: with `min v_a v_b` the stale bounds enter the
product radii and the chain loses up to four times more precision
(code/local-group/di_values_ball_run.sh). -/
def ballOpsF (k : Ctx) : Ops Ball :=
  { ballOps k with add := fun a b => (Ball.add k a b).fresh k }

end FurioLombardo.Discharge.KvArith
