import Mathlib
import FurioLombardo.M4.Twist
import FurioLombardo.M4.Checks
import FurioLombardo.M4.Sigma

/-!
# Lane M4 for the twists δ0 and δ1

The kernel checked data of `FurioLombardo.M4.Data`/`Checks` packaged as `TwistData`/`TwistChecks`, and the
resulting per twist theorems `T0.twist_local`, `T1.twist_local`. Injectivity of `σ_v` on the Selmer group (the global
input `hloc` comes from it) is `T0.sigma_injective`, `T1.sigma_injective` in `FurioLombardo.M4.Sigma`.
-/

namespace FurioLombardo.M4

namespace T0

/-- The certificate data of the twist δ0 as a `TwistData`. -/
def data : TwistData where
  qD := qD
  lD := lD
  qa := qa
  qb := qb
  la := la
  lb := lb
  H := H
  G := G
  C := C
  Cp := Cp
  U := U
  Ui := Ui
  UG := UG
  Jab := Jab
  Del := Del
  dl := dl
  r := r
  sigE := sigE
  sigA := sigA
  sigB := sigB
  W := W
  SB := SB
  excluded := excluded
  constant := constant
  tails := tails

/-- The finite checks of the twist δ0 (all by `decide +kernel` in `FurioLombardo.M4.Checks`). -/
theorem checks : TwistChecks data where
  cover := cover
  hHG := hHG
  hC := hC
  hCp := hCp
  hGl := hGl
  hUG := hUG
  hid := hid
  hGcol := hGcol
  hDel := hDel
  hdl := hdl
  hJab := hJab
  hr := hr
  hsig := hsig
  hsigq := hsigq
  hqD := hqD
  centres := centres
  centresMem := centresMem
  tailsOK := tailsOK
  tailsVM := tailsVM
  hWc := hWc

/-- **M4 for the twist δ0.** Every global point `x` lies over a known point: its disc and parameter are those of
one of the known lifts listed in `T0.tails`. The inputs at `v` are the named hypotheses of
`FurioLombardo.M4.Hypotheses`, with the analytic input in antiderivative form. -/
theorem twist_local {A B Dk : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B)
    (lam : B →+ (Fin 6 → ℤ_[2])) (T : A) (Dpt : Fin 7 → B)
    (S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])) (φ : Dk → A) (xa xb : Dk)
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) (Twist : ℕ → ℤ_[2] → Prop) (disc : Dk → ℕ) (par : Dk → ℤ_[2])
    (hLam : HLam lam Dpt) (hBD : HBallD data (fun i => lam (Dpt i)))
    (hBP : HBallPhi data (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hSat : HSat (Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i))) S (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hCe : HCentre data lamD) (hAC : HAntiConst data lamD) (hAT : HAntiTail data lamD)
    (hKn : HKnown data S lamD) (hEx : HExcl data Twist) (hDi : HDisc ι lam S φ xa disc par lamD Twist)
    (hloc : HLocInj ι) (hker : HKer ι lam T) (hSel : HSelLoc ι Dpt data) (x : Dk) :
    ∃ t ∈ tails, t.disc = disc x ∧ par x = (t.Xi : ℤ_[2]) :=
  twist_local_anti ι lam T Dpt checks S φ xa xb lamD Twist disc par hLam hBD hBP hSat hCe hAC hAT hKn hEx hDi
    hloc hker hSel x

end T0

namespace T1

/-- The certificate data of the twist δ1 as a `TwistData`. -/
def data : TwistData where
  qD := qD
  lD := lD
  qa := qa
  qb := qb
  la := la
  lb := lb
  H := H
  G := G
  C := C
  Cp := Cp
  U := U
  Ui := Ui
  UG := UG
  Jab := Jab
  Del := Del
  dl := dl
  r := r
  sigE := sigE
  sigA := sigA
  sigB := sigB
  W := W
  SB := SB
  excluded := excluded
  constant := constant
  tails := tails

/-- The finite checks of the twist δ1 (all by `decide +kernel` in `FurioLombardo.M4.Checks`). -/
theorem checks : TwistChecks data where
  cover := cover
  hHG := hHG
  hC := hC
  hCp := hCp
  hGl := hGl
  hUG := hUG
  hid := hid
  hGcol := hGcol
  hDel := hDel
  hdl := hdl
  hJab := hJab
  hr := hr
  hsig := hsig
  hsigq := hsigq
  hqD := hqD
  centres := centres
  centresMem := centresMem
  tailsOK := tailsOK
  tailsVM := tailsVM
  hWc := hWc

/-- **M4 for the twist δ1.** Every global point `x` lies over a known point: its disc and parameter are those of
one of the known lifts listed in `T1.tails`. The inputs at `v` are the named hypotheses of
`FurioLombardo.M4.Hypotheses`, with the analytic input in antiderivative form. -/
theorem twist_local {A B Dk : Type*} [AddCommGroup A] [AddCommGroup B] (ι : A →+ B)
    (lam : B →+ (Fin 6 → ℤ_[2])) (T : A) (Dpt : Fin 7 → B)
    (S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])) (φ : Dk → A) (xa xb : Dk)
    (lamD : ℕ → ℤ_[2] → Fin 6 → ℤ_[2]) (Twist : ℕ → ℤ_[2] → Prop) (disc : Dk → ℕ) (par : Dk → ℤ_[2])
    (hLam : HLam lam Dpt) (hBD : HBallD data (fun i => lam (Dpt i)))
    (hBP : HBallPhi data (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hSat : HSat (Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i))) S (lam (ι (φ xa))) (lam (ι (φ xb))))
    (hCe : HCentre data lamD) (hAC : HAntiConst data lamD) (hAT : HAntiTail data lamD)
    (hKn : HKnown data S lamD) (hEx : HExcl data Twist) (hDi : HDisc ι lam S φ xa disc par lamD Twist)
    (hloc : HLocInj ι) (hker : HKer ι lam T) (hSel : HSelLoc ι Dpt data) (x : Dk) :
    ∃ t ∈ tails, t.disc = disc x ∧ par x = (t.Xi : ℤ_[2]) :=
  twist_local_anti ι lam T Dpt checks S φ xa xb lamD Twist disc par hLam hBD hBP hSat hCe hAC hAT hKn hEx hDi
    hloc hker hSel x

end T1

end FurioLombardo.M4
