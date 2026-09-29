/-
Kernel probe of the w3 certificate checks, at the real sizes of
Discharge/SelmerBasis/W3Data*.lean (data from sb_10_w3.gp, output sb_10_w3.out).
Run from lean/ (one thread, so each profiler line is one declaration):
  /usr/bin/time -v lake env lean -DmaxSynthPendingDepth=3 \
    -Dprofiler=true -Dprofiler.threshold=100 ../code/selmer-basis/sb_11_kernel_probe.lean > ../code/selmer-basis/sb_11_kernel_probe.out 2>&1
-/
import FurioLombardo.Discharge.SelmerBasis.W3Data
import FurioLombardo.Discharge.SelmerBasis.W3DataK0
import FurioLombardo.Discharge.SelmerBasis.PlaceWElem

namespace FurioLombardo.Discharge.SelmerBasis.W3Probe

open FurioLombardo.M1 FurioLombardo.Discharge.SelmerBasis FurioLombardo.Discharge.SelmerBasis.Tower
  FurioLombardo.Discharge.SelmerBasis.W3

theorem pE : W3.E.ok = true := by decide +kernel

theorem pM : W3.M.ok W3.E = true := by decide +kernel

theorem pS : W3.S.ok W3.E W3.M = true := by decide +kernel

theorem pK1 : certOK W3.E W3.cK_1.n0 (kapX W3.E 1) (.int 0) W3.cK_1 = true := by decide +kernel

theorem pL0 : certOK W3.E W3.cL_0.n0 (X0L W3.M (ofL SUnitData.gL_0)) (X1L W3.M (ofL SUnitData.gL_0))
    W3.cL_0 = true := by decide +kernel

theorem pN0 : certOK W3.E W3.cN1_0.n0 (X0N W3.E W3.M W3.S (ofN SUnitData.gN_0) true)
    (X1N W3.E W3.M W3.S (ofN SUnitData.gN_0) true) W3.cN1_0 = true := by decide +kernel

theorem pD0 : W3.K0.pt_0.okD W3.E = true := by decide +kernel

theorem pZ0 : W3.K0.pt_0.okZ W3.E (gW 0) = true := by decide +kernel

theorem pT0 : W3.K0.pt_0.okT = true := by decide +kernel

theorem pM1 : certOK W3.E W3.K0.cM1_0.n0 (X0L W3.M (ofL W3.K0.pt_0.tL)) (X1L W3.M (ofL W3.K0.pt_0.tL))
    W3.K0.cM1_0 = true := by decide +kernel

theorem pM2 : certOK W3.E W3.K0.cM2_0.n0 (X0N W3.E W3.M W3.S (ofN W3.K0.pt_0.tN) true)
    (X1N W3.E W3.M W3.S (ofN W3.K0.pt_0.tN) true) W3.K0.cM2_0 = true := by decide +kernel

end FurioLombardo.Discharge.SelmerBasis.W3Probe
