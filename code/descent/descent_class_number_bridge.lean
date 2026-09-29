import FurioLombardo.M1.DescentM3a
import FurioLombardo.M2.Main
/-! Sanity check that M2 discharges the hypothesis of M1 (`M2.clK21TwoTorsionTrivial` has the type
`M1.ClK21TwoTorsionTrivial`). Run from lean/ after building FurioLombardo.M2.Main:
`lake env lean ../code/descent/descent_class_number_bridge.lean`. -/
theorem m1_descent_of_zimmert (hZ : FurioLombardo.M2.ZimmertBoundK21) :
    FurioLombardo.M3a.Descent FurioLombardo.M1.K21 (FurioLombardo.Discharge.M3a.Bruin.Mmat 0)
      (FurioLombardo.Discharge.M3a.Bruin.Mmat 1) (FurioLombardo.Discharge.M3a.Bruin.Mmat 2)
      FurioLombardo.Discharge.M3a.Bruin.δ0 FurioLombardo.Discharge.M3a.Bruin.δ1 :=
  FurioLombardo.M1.descent_Mmat (FurioLombardo.M2.clK21TwoTorsionTrivial hZ)
#print axioms m1_descent_of_zimmert
