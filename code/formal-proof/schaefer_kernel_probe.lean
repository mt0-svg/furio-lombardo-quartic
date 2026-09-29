import FurioLombardo.Discharge.SelmerBasis.SchaeferCertDefs
open FurioLombardo.Discharge.SelmerBasis.Cert
-- kernel time probe: the largest Bezout identity (twist 1, i = 1) and the composition check
#eval (bez2Check 1 1 768, bez2Check 1 1 1024, compCheck 1 1024, yzCheck 1 1 1024, bez1Check 1 768, revCheck 1 1 768, eCheck 1 768, piCheck 256)
set_option maxHeartbeats 0 in
theorem probe_bez2 : bez2Check 1 1 1024 = true := by decide +kernel
