/- wgen_axioms.lean: `#print axioms` of the generic w-layer, PlaceWGen.lean.
   Run from lean/:
     lake env lean ../code/selmer-local-conditions/wgen_axioms.lean \
       > ../code/selmer-local-conditions/wgen_axioms.out 2>&1 -/
import FurioLombardo.Discharge.SelmerBasis.PlaceWGen

open FurioLombardo.Discharge.SelmerBasis

#print axioms qaLift
#print axioms qaLift_algebraMap
#print axioms qaLift_omega
#print axioms isSquare_of_sub_sq_lt
#print axioms isSquare_of_eisen_cert
#print axioms exists_sqrt_near
#print axioms prod_eq_evTab
#print axioms evTab_trunc
#print axioms norm_evTab_le_one
