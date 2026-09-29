import FurioLombardo.Discharge.SelmerBasis.PlaceV
import FurioLombardo.Discharge.SelmerBasis.GlobalGens
import FurioLombardo.Discharge.SelmerBasis.Count.AtV
import FurioLombardo.M4.Instances

/-!
# The place `v`: the frozen statements of the SelmerBasisK21 side at `M4Cert.σ : K21 →+* Kv`

The local points are lane SelmerSpan's `Dpt k`, and `Wv k` is the closure of their images.

* `imageIn_v`: the image of `μ` at `v` lies in `Wv k` (the count `countBound_v` with the
  independence `indepImage_v`);
* the rows `Cv k` and the columns `βK k` of the local condition and of the relation at `v`, whose proofs
  `coordCond_v`, `relAtV_v` are in VCoord.lean.

Data: `CvRows` are the rows `C_w` of stage 6 of code/selmer-local-conditions/selmer_rows_twist<k>_v.out, `βRows` the
columns `β_j` of code/selmer-global-bound/selmer_space_new_generators.out, both as bitsets (bit `s` is entry `s`), written
by code/selmer-local-conditions/v_rows.gp (output v_rows.out). The row space of `Cv k` is the
annihilator of the preimage of `V_w` in `F₂^82`, which does not depend on the local models, so
the certificates of the local models reach it through `coordCond_of_mul`.
-/

namespace FurioLombardo.Discharge.SelmerBasis.V

open Polynomial FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M4Cert
  FurioLombardo.Discharge.M3a.Bruin FurioLombardo.Discharge.SelmerSpan

attribute [local instance] goodSextic_fRev_Kv

/-! ## Data -/

def CvRows : Fin 2 → List ℕ :=
  ![[231086072, 157242549476611944611840, 4736401684692044883173841, 300163474012362799841280, 426773026472650970894167, 1684614457164951254463057, 3964877274784592916640337, 4142638120786108140774699, 2078087342222964436226944, 4227398798420264565598647, 231633819778531824633184],
    [231086072, 157242549476611944611840, 4736401684692044883173841, 300163474012362799841280, 234241404213988825632599, 1282086253292684095917911, 3767397277148151806557446, 703847503909726918699644, 1543104180139820525313820, 3803586474371443994519264, 231633819778531824633184]]
def βRows : Fin 2 → List ℕ :=
  ![[54710522175814725372674, 4231240379912958951886085, 41028887034094182989826, 3038671772707104017875044],
    [36269600134224647555526, 315801059612755868260358, 604462946474000753659200, 1868997883962868445216768]]

/-- The rows at `v`. -/
def Cv (k : Fin 2) : Matrix (Fin 11) (Fin 82) (ZMod 2) :=
  Matrix.of fun i s => bitv 82 ((CvRows k).getD i 0) s

/-- The four columns `β_j` of the Selmer basis. -/
def βK (k : Fin 2) : Fin 4 → Fin 82 → ℕ := fun j s => if ((βRows k).getD j 0).testBit s then 1 else 0

/-- Lane M4's matrix `SB` of the twist `k`. -/
def SBv (k : Fin 2) : Matrix (Fin 7) (Fin 4) ℤ :=
  if k = 0 then FurioLombardo.M4.T0.data.SB else FurioLombardo.M4.T1.data.SB

/-! ## The points and the local image -/

/-- The local points `Dpt k`. -/
noncomputable abbrev Dv (k : Fin 2) : Fin 7 → Jac ((fRev k).map σ) := fun i => Additive.toMul (Dpt k i)

/-- The subgroup spanned by the images of the points. -/
noncomputable abbrev Wv (k : Fin 2) : Subgroup (H ((fRev k).map σ)) :=
  Subgroup.closure (Set.range fun i => muJ ((fRev k).map σ) (Dv k i))

/-- **`ImageIn` at `v`.** -/
theorem imageIn_v (k : Fin 2) : ImageIn ((fRev k).map σ) (Wv k) :=
  imageIn_closure_of_count_indep _ (Dv k) (Count.countBound_v k) (indepImage_v k)

end FurioLombardo.Discharge.SelmerBasis.V
