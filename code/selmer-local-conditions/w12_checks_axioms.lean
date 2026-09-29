import FurioLombardo.Discharge.SelmerBasis.W2CheckE
import FurioLombardo.Discharge.SelmerBasis.W2CheckK
import FurioLombardo.Discharge.SelmerBasis.W2CheckL
import FurioLombardo.Discharge.SelmerBasis.W2CheckN1
import FurioLombardo.Discharge.SelmerBasis.W2CheckN2
import FurioLombardo.Discharge.SelmerBasis.W2CheckK0
import FurioLombardo.Discharge.SelmerBasis.W2CheckK1

-- Axioms of the kernel checks of the w2 data (code/selmer-local-conditions/kernel_checks_w12.sh); run from lean/:
-- lake env lean ../code/selmer-local-conditions/w12_checks_axioms.lean
open FurioLombardo.Discharge.SelmerBasis.W2

#print axioms ck_E
#print axioms ck_SR
#print axioms ck_SU
#print axioms ck_K
#print axioms ck_L
#print axioms ck_N1
#print axioms ck_N2
#print axioms K0.ck_pt
#print axioms K0.ck_M1
#print axioms K0.ck_M2
#print axioms K0.ck_M3
#print axioms K1.ck_pt
#print axioms K1.ck_M1
#print axioms K1.ck_M2
#print axioms K1.ck_M3
