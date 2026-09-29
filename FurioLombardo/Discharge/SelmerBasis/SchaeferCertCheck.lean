import FurioLombardo.Discharge.SelmerBasis.SchaeferCertDefs

/-!
# Kernel checks of the certificates of the global Schaefer lemma

One `decide +kernel` per identity of SchaeferCertDefs.lean (code/selmer-global-bound/schaefer_certs.gp,
precisions from code/formal-proof/schaefer_kernel_probe.out), plus the list lengths used by the glue.
-/

namespace FurioLombardo.Discharge.SelmerBasis.Cert

open FurioLombardo.M1.Kron

theorem pi_ok : piCheck 256 = true := by decide +kernel

theorem comp_ok_0 : compCheck 0 1024 = true := by decide +kernel

theorem bez1_ok_0 : bez1Check 0 768 = true := by decide +kernel

theorem e_ok_0 : eCheck 0 768 = true := by decide +kernel

theorem rev_ok_0_0 : revCheck 0 0 768 = true := by decide +kernel

theorem bez2_ok_0_0 : bez2Check 0 0 1024 = true := by decide +kernel

theorem yz_ok_0_0 : yzCheck 0 0 1024 = true := by decide +kernel

theorem rev_ok_0_1 : revCheck 0 1 768 = true := by decide +kernel

theorem bez2_ok_0_1 : bez2Check 0 1 1024 = true := by decide +kernel

theorem yz_ok_0_1 : yzCheck 0 1 1024 = true := by decide +kernel

theorem rev_ok_0_2 : revCheck 0 2 768 = true := by decide +kernel

theorem bez2_ok_0_2 : bez2Check 0 2 1024 = true := by decide +kernel

theorem yz_ok_0_2 : yzCheck 0 2 1024 = true := by decide +kernel

theorem comp_ok_1 : compCheck 1 1024 = true := by decide +kernel

theorem bez1_ok_1 : bez1Check 1 768 = true := by decide +kernel

theorem e_ok_1 : eCheck 1 768 = true := by decide +kernel

theorem rev_ok_1_0 : revCheck 1 0 768 = true := by decide +kernel

theorem bez2_ok_1_0 : bez2Check 1 0 1024 = true := by decide +kernel

theorem yz_ok_1_0 : yzCheck 1 0 1024 = true := by decide +kernel

theorem rev_ok_1_1 : revCheck 1 1 768 = true := by decide +kernel

theorem bez2_ok_1_1 : bez2Check 1 1 1024 = true := by decide +kernel

theorem yz_ok_1_1 : yzCheck 1 1 1024 = true := by decide +kernel

theorem rev_ok_1_2 : revCheck 1 2 768 = true := by decide +kernel

theorem bez2_ok_1_2 : bez2Check 1 2 1024 = true := by decide +kernel

theorem yz_ok_1_2 : yzCheck 1 2 1024 = true := by decide +kernel

theorem FL_length (k : Fin 2) : (FL k).length = 7 := by fin_cases k <;> decide +kernel

theorem F2L_length (k : Fin 2) (i : Fin 3) : (F2L k i).length = 7 := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem compP_FL_length (k : Fin 2) (i : Fin 3) :
    (compP (FL k) [.int i, .int 1]).length = 7 := by
  fin_cases k <;> fin_cases i <;> decide +kernel

theorem m1N_eq (k : Fin 2) : m1N k = 4 := by fin_cases k <;> rfl

end FurioLombardo.Discharge.SelmerBasis.Cert
