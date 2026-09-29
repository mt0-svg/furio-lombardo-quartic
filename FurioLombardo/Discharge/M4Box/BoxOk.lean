import Mathlib
import FurioLombardo.Discharge.M4Box.BoxRun
import FurioLombardo.Discharge.M4Box.DInput

/-!
# The per box statements from a box check (lane lean-m4box, D9)

The data files `BoxData/K<k>B<i>.lean` hold, for the box `i` of twist `k` (the constant boxes of
`T<k>.constant`, then the tails of `T<k>.tails`), a spec `B` and one kernel check
`(boxRun (B.ctx dCtx n) g E A B).any (constOK ...) = true` (or `tailOK`), with the twist balls of
DCertData. `constCert_of_ok` and `tailCert_of_ok` turn such a check into `ConstCert`, `TailCert`: the
balls enclose the twist constants (`mem_FvBall` ... `mem_AmatBall`), and `Option.any_eq_true` gives
the run and the check of `constCert_of_run`, `tailCert_of_run`.
-/

open FurioLombardo.M1 FurioLombardo.M3a FurioLombardo.M3a.Genus2
open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv FurioLombardo.Discharge.KvArith

namespace FurioLombardo.Discharge.M4Box

theorem constCert_of_ok (kk : Fin 2) {c : FurioLombardo.M4.CBox} (B : BoxSpec) (n : ℕ)
    (he : B.e ∈ branchTable kk) (hed : B.e.disc = c.disc) (hec : B.e.c = c.c) (hes : B.e.s = c.s)
    (hkk : B.kk = kk) (hBd : B.d = c.disc) (hBc : B.c = (c.c : ℤ)) (hBs : B.s = c.s)
    (hd : IsDisc c.disc) (hY : (2 : ℤ) ^ B.N ∣ G1 B.d B.c B.Y0)
    {F g : Sext Ball} {b : Ball} {E : Mum Ball} {A : Mat2 Ball} {sB : N3} {eB : ℕ}
    (hF : FvBall dCtx (kk : ℕ) = some F) (hg : gBall dCtx F = some g)
    (hb : bKBall dCtx kk g sB eB = some b) (hE : E0Ball dCtx kk g b = some E)
    (hA : AmatBall dCtx kk g b = some A) {D : ℕ}
    (hD2 : 3 * (c.vM / 3 + c.s) + M0 kk + 3 ≤ 2 * D)
    (hok : (boxRun (B.ctx dCtx n) g E A B).any
      (constOK (B.ctx dCtx n) b (IntModelKv.aa kk) (M0 kk) D (3 * (c.vM / 3 + c.s))) = true) :
    ConstCert kk (IntModelKv.admM0 kk) c := by
  obtain ⟨out, hrun, hok'⟩ := (Option.any_eq_true _ _).mp hok
  have hgm := mem_gBall dCtx_ok kk (mem_FvBall dCtx_ok hF) hg
  have hbm := mem_bKBall dCtx_ok kk hgm hb
  exact constCert_of_run kk he hed hec hes dCtx_ok n hkk hBd hBc hBs rfl hd hY hgm
    (mem_E0Ball dCtx_ok kk hgm hbm hE) (mem_AmatBall dCtx_ok kk hgm hbm hA) hbm hrun hD2 hok'

theorem tailCert_of_ok (kk : Fin 2) {t : FurioLombardo.M4.TBox} (B : BoxSpec) (n : ℕ)
    (he : B.e ∈ branchTable kk) (hed : B.e.disc = t.disc) (hec : B.e.c = t.c) (hes : B.e.s = t.s)
    (hkk : B.kk = kk) (hBd : B.d = t.disc) (hBc : B.c = t.Xi) (hBs : B.s = t.s)
    (hd : IsDisc t.disc) (hY : (2 : ℤ) ^ B.N ∣ G1 B.d B.c B.Y0)
    {F g : Sext Ball} {b : Ball} {E : Mum Ball} {A : Mat2 Ball} {sB : N3} {eB : ℕ}
    (hF : FvBall dCtx (kk : ℕ) = some F) (hg : gBall dCtx F = some g)
    (hb : bKBall dCtx kk g sB eB = some b) (hE : E0Ball dCtx kk g b = some E)
    (hA : AmatBall dCtx kk g b = some A) {D a1 aS : ℕ}
    (h1 : M0 kk + 4 ≤ 3 * t.s + min a1 (3 * t.s + aS)) (h2 : 3 * (t.vM / 3) ≤ 3 * t.s0 + aS)
    (h3 : 3 * (t.vM / 3) + M0 kk + 3 ≤ 3 * t.s0 + 2 * min a1 (3 * t.s + aS))
    (hok : (boxRun (B.ctx dCtx n) g E A B).any
      (tailOK (B.ctx dCtx n) b A (IntModelKv.aa kk) (M0 kk) D a1 aS t.q t.g) = true) :
    TailCert kk (IntModelKv.admM0 kk) t := by
  obtain ⟨out, hrun, hok'⟩ := (Option.any_eq_true _ _).mp hok
  have hgm := mem_gBall dCtx_ok kk (mem_FvBall dCtx_ok hF) hg
  have hbm := mem_bKBall dCtx_ok kk hgm hb
  exact tailCert_of_run kk he hed hec hes dCtx_ok n hkk hBd hBc hBs rfl hd hY hgm
    (mem_E0Ball dCtx_ok kk hgm hbm hE) (mem_AmatBall dCtx_ok kk hgm hbm hA) hbm hrun h1 h2 h3 hok'

end FurioLombardo.Discharge.M4Box
