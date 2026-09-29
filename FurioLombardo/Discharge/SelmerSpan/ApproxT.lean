import FurioLombardo.Discharge.M3a.LocalRes
import FurioLombardo.Discharge.SelmerSpan.Mumford

/-!
# Residue arithmetic for the local divisors (lane SelmerSpan)

Integer triples `T3` modulo `2^P` (lane M4Cert's `Approx`, `mulZ`, `modT`) with a reduction after
every operation (`addT`, `subT`, `mulT`), and the residues of the quantities of `Mumford.lean`:
the remainder `divR1, divR0` of a sextic modulo `X² + p X + r` (`approx_divR1`, `approx_divR0`),
the targets `Z0² - p Z1 Z0 + r Z1²` (`approx_nTT`) and `2 Z0 - p Z1 + 2 n` (`approx_aTT`) of the two
square roots.
-/

namespace FurioLombardo.Discharge.SelmerSpan

open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.M3a.Bruin

/-- Sum modulo `2^P`. -/
def addT (P : ℕ) (a b : T3) : T3 := modT (a + b) P

/-- Difference modulo `2^P`. -/
def subT (P : ℕ) (a b : T3) : T3 := modT (a - b) P

/-- Product modulo `2^P`. -/
def mulT (P : ℕ) (a b : T3) : T3 := modT (mulZ a b) P

/-- An integer as a triple. -/
def cT (c : ℤ) : T3 := (c, 0, 0)

variable {x y : Kv} {a b : T3} {P : ℕ}

theorem approx_addT (hx : Approx x a P) (hy : Approx y b P) : Approx (x + y) (addT P a b) P :=
  (hx.add hy).reduce

theorem approx_subT (hx : Approx x a P) (hy : Approx y b P) : Approx (x - y) (subT P a b) P :=
  (approx_sub hx hy).reduce

theorem approx_mulT (hx : Approx x a P) (hy : Approx y b P) : Approx (x * y) (mulT P a b) P :=
  (hx.mul hy).reduce

theorem approx_cT (c : ℤ) (P : ℕ) : Approx (c : Kv) (cT c) P := by
  rw [← evZ_const]; exact approx_evZ _ _

theorem approx_two (P : ℕ) : Approx (2 : Kv) (cT 2) P := by
  have h := approx_cT 2 P
  simpa using h

/-! ## The remainder modulo `X² + p X + r` -/

/-- `divW` on triples. -/
def divWT (P : ℕ) (p r g2 g3 g4 g5 g6 : T3) : T3 × T3 × T3 × T3 × T3 :=
  let w4 := g6
  let w3 := subT P g5 (mulT P p w4)
  let w2 := subT P (subT P g4 (mulT P p w3)) (mulT P r w4)
  let w1 := subT P (subT P g3 (mulT P p w2)) (mulT P r w3)
  let w0 := subT P (subT P g2 (mulT P p w1)) (mulT P r w2)
  (w4, w3, w2, w1, w0)

/-- `divR1` on triples. -/
def divR1T (P : ℕ) (p r g1 g2 g3 g4 g5 g6 : T3) : T3 :=
  let w := divWT P p r g2 g3 g4 g5 g6
  subT P (subT P g1 (mulT P p w.2.2.2.2)) (mulT P r w.2.2.2.1)

/-- `divR0` on triples. -/
def divR0T (P : ℕ) (p r g0 g2 g3 g4 g5 g6 : T3) : T3 :=
  let w := divWT P p r g2 g3 g4 g5 g6
  subT P g0 (mulT P r w.2.2.2.2)

section Div

variable {p r g0 g1 g2 g3 g4 g5 g6 : Kv} {tp tr t0 t1 t2 t3 t4 t5 t6 : T3}

theorem approx_divW (hp : Approx p tp P) (hr : Approx r tr P) (h2 : Approx g2 t2 P)
    (h3 : Approx g3 t3 P) (h4 : Approx g4 t4 P) (h5 : Approx g5 t5 P) (h6 : Approx g6 t6 P) :
    Approx (divW p r g0 g1 g2 g3 g4 g5 g6).2.2.2.2 (divWT P tp tr t2 t3 t4 t5 t6).2.2.2.2 P ∧
      Approx (divW p r g0 g1 g2 g3 g4 g5 g6).2.2.2.1 (divWT P tp tr t2 t3 t4 t5 t6).2.2.2.1 P := by
  have hw3 := approx_subT h5 (approx_mulT hp h6)
  have hw2 := approx_subT (approx_subT h4 (approx_mulT hp hw3)) (approx_mulT hr h6)
  have hw1 := approx_subT (approx_subT h3 (approx_mulT hp hw2)) (approx_mulT hr hw3)
  have hw0 := approx_subT (approx_subT h2 (approx_mulT hp hw1)) (approx_mulT hr hw2)
  exact ⟨hw0, hw1⟩

theorem approx_divR1 (hp : Approx p tp P) (hr : Approx r tr P) (h1 : Approx g1 t1 P)
    (h2 : Approx g2 t2 P) (h3 : Approx g3 t3 P) (h4 : Approx g4 t4 P) (h5 : Approx g5 t5 P)
    (h6 : Approx g6 t6 P) :
    Approx (divR1 p r g0 g1 g2 g3 g4 g5 g6) (divR1T P tp tr t1 t2 t3 t4 t5 t6) P := by
  obtain ⟨hw0, hw1⟩ := approx_divW (g0 := g0) (g1 := g1) hp hr h2 h3 h4 h5 h6
  exact approx_subT (approx_subT h1 (approx_mulT hp hw0)) (approx_mulT hr hw1)

theorem approx_divR0 (hp : Approx p tp P) (hr : Approx r tr P) (h0 : Approx g0 t0 P)
    (h2 : Approx g2 t2 P) (h3 : Approx g3 t3 P) (h4 : Approx g4 t4 P) (h5 : Approx g5 t5 P)
    (h6 : Approx g6 t6 P) :
    Approx (divR0 p r g0 g1 g2 g3 g4 g5 g6) (divR0T P tp tr t0 t2 t3 t4 t5 t6) P := by
  obtain ⟨hw0, -⟩ := approx_divW (g0 := g0) (g1 := g1) hp hr h2 h3 h4 h5 h6
  exact approx_subT h0 (approx_mulT hr hw0)

end Div

/-! ## The targets of the two square roots -/

/-- `Z0² - p Z1 Z0 + r Z1²` on triples. -/
def nTT (P : ℕ) (p r Z1 Z0 : T3) : T3 :=
  addT P (subT P (mulT P Z0 Z0) (mulT P (mulT P p Z1) Z0)) (mulT P r (mulT P Z1 Z1))

/-- `2 Z0 - p Z1 + 2 n` on triples. -/
def aTT (P : ℕ) (p Z1 Z0 n : T3) : T3 :=
  addT P (subT P (mulT P (cT 2) Z0) (mulT P p Z1)) (mulT P (cT 2) n)

theorem approx_nTT {p r Z1 Z0 : Kv} {tp tr t1 t0 : T3} (hp : Approx p tp P) (hr : Approx r tr P)
    (h1 : Approx Z1 t1 P) (h0 : Approx Z0 t0 P) :
    Approx (Z0 ^ 2 - p * Z1 * Z0 + r * Z1 ^ 2) (nTT P tp tr t1 t0) P := by
  have h := approx_addT (approx_subT (approx_mulT h0 h0) (approx_mulT (approx_mulT hp h1) h0))
    (approx_mulT hr (approx_mulT h1 h1))
  unfold nTT
  convert h using 2 <;> ring

theorem approx_aTT {p Z1 Z0 n : Kv} {tp t1 t0 tn : T3} (hp : Approx p tp P) (h1 : Approx Z1 t1 P)
    (h0 : Approx Z0 t0 P) (hn : Approx n tn P) :
    Approx (2 * Z0 - p * Z1 + 2 * n) (aTT P tp t1 t0 tn) P :=
  approx_addT (approx_subT (approx_mulT (approx_two P) h0) (approx_mulT hp h1))
    (approx_mulT (approx_two P) hn)

end FurioLombardo.Discharge.SelmerSpan
