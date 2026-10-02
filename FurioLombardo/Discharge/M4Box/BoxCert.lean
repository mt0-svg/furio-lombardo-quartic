import Mathlib
import FurioLombardo.Discharge.M4Box.Weak
import FurioLombardo.Discharge.M4Box.LogBound
import FurioLombardo.Discharge.M4Box.Coord
import FurioLombardo.Discharge.M4Box.Amat

/-!
# The box inputs from per box chart bounds (lane lean-m4box, D8)

For the twist `k`, lane lean-m4log's logarithm `lam k` and branch `lamD k` (M4Log/Defs.lean), the two
weak box fields of `M4RestKvW` follow from one statement per box about the arc of the box read in
R7's chart:

* `ArcChart k h e X X0 P`: lifts `x`, `x0` on the branch of the table entry `e` over the disc points
  of parameters `X`, `X0`, and a chart point `z` with `ψ z = φ_v(x) - φ_v(x0)` whose chart
  coordinates `t = pv^M0 z` satisfy `P`;
* `ConstCert k h c`: for the constant box `c`, its table entry, a depth `D` with the two inequalities
  of the log bound, and for every `Y ∈ ℤ_[2]` the arc from `c.c` to `c.c + 2^s Y` with
  `‖tᵢ‖ ≤ ‖pv‖^D` and `‖(Amat t)ᵢ‖ ≤ ‖pv‖^(3(vM/3 + s))`;
* `TailCert k h b`: for the tail box `b`, its table entry, fixed `c0`, `c1` with
  `‖2 (Amat c1)ᵢ - (t.g)ᵢ‖ ≤ ‖pv‖^(3q)`, and for every `Y` the arc from `Xi` to `Xi + h`,
  `h = 2^s Y`, with `t = c0 + h c1 + h² S`, `S` and `Amat S` bounded, and three inequalities.

`hConstLip_of_cert` and `hTailQuad_of_cert` derive `HConstLip D (lamD k)` and `HTailQuad D (lamD k)`
from these, with `AdmM0 k`, `LamInt k` and the integrality of `Amat k` (`norm_Amat_le_one`). On a tail, `c0 = 0` follows
from the case `Y = 0` (one lift per branch, `ψ` injective), and `g` is the coordinate vector of
`2 Amat c1`, the same for every point of the box, as `HTailQuad` requires.
-/

open FurioLombardo.Discharge.M4Cert FurioLombardo.Discharge.R7 FurioLombardo.Discharge.M4Log
open FurioLombardo.Discharge.R7.ConcreteKv FurioLombardo.M4
open scoped Matrix

namespace FurioLombardo.Discharge.M4Box

/-! ## The per box statements (frozen interface with the certificates) -/

/-- The arc of the branch `e` from `X0` to `X` read in the chart: lifts `x`, `x0` on the branch over
`pKv e.disc X`, `pKv e.disc X0`, and a chart point `z` of `φ_v(x) - φ_v(x0)` whose chart coordinates
satisfy `P`. -/
def ArcChart (k : Fin 2) (h : AdmM0 k) (e : BranchBox) (X X0 : ℤ_[2]) (P : (Fin 2 → Kv) → Prop) :
    Prop :=
  ∃ x x0 : DPtKv k, x.p = pKv e.disc X ∧ BranchOK e x ∧ x0.p = pKv e.disc X0 ∧ BranchOK e x0 ∧
    ∃ z : (fgl k h).Points,
      chart k h z = Additive.ofMul (phiV k x) - Additive.ofMul (phiV k x0) ∧ P (tK k h z)

/-- **The per box statement of a constant box** `c`: its entry of the branch table, a depth `D`
(`M0 + 4 ≤ D`, `need + M0 + 3 ≤ 2D`, `need = 3(vM/3 + s)`), and for every `Y` the arc from `c.c` to
`c.c + 2^s Y` with `‖tᵢ‖ ≤ ‖pv‖^D` and `‖(Amat t)ᵢ‖ ≤ ‖pv‖^need`. -/
def ConstCert (k : Fin 2) (h : AdmM0 k) (c : CBox) : Prop :=
  ∃ e ∈ branchTable k, e.disc = c.disc ∧ e.c = c.c ∧ e.s = c.s ∧
    ∃ D : ℕ, M0 k + 4 ≤ D ∧ 3 * (c.vM / 3 + c.s) + M0 k + 3 ≤ 2 * D ∧
      ∀ Y : ℤ_[2], ArcChart k h e ((c.c : ℤ_[2]) + 2 ^ c.s * Y) c.c
        (fun t => (∀ i, ‖t i‖ ≤ ‖pv‖ ^ D) ∧
          ∀ i, ‖(Amat k *ᵥ t) i‖ ≤ ‖pv‖ ^ (3 * (c.vM / 3 + c.s)))

/-- **The per box statement of a tail box** `b`: its entry of the branch table, fixed `c0`, `c1`
(`‖c1ᵢ‖ ≤ ‖pv‖^a1`, `2 Amat c1` in the ball of radius `‖pv‖^(3q)` around `b.g`), and for every `Y`
the arc from `Xi` to `Xi + h`, `h = 2^s Y`, with `t = c0 + h c1 + h² S`, `‖Sᵢ‖ ≤ ‖pv‖^aS`,
`‖(Amat S)ᵢ‖ ≤ ‖pv‖^NS`; with `d1 = min a1 (3s + aS)`: `M0 + 4 ≤ 3s + d1`,
`3(vM/3) ≤ 3 s0 + NS` and `3(vM/3) + M0 + 3 ≤ 3 s0 + 2 d1`. -/
def TailCert (k : Fin 2) (h : AdmM0 k) (b : TBox) : Prop :=
  ∃ e ∈ branchTable k, e.disc = b.disc ∧ e.c = b.c ∧ e.s = b.s ∧
    ∃ (c0 c1 : Fin 2 → Kv) (a1 aS NS : ℕ),
      M0 k + 4 ≤ 3 * b.s + min a1 (3 * b.s + aS) ∧
      3 * (b.vM / 3) ≤ 3 * b.s0 + NS ∧
      3 * (b.vM / 3) + M0 k + 3 ≤ 3 * b.s0 + 2 * min a1 (3 * b.s + aS) ∧
      (∀ i, ‖c1 i‖ ≤ ‖pv‖ ^ a1) ∧
      (∀ i, ‖2 * (Amat k *ᵥ c1) i - toKv2 (icast b.g) i‖ ≤ ‖pv‖ ^ (3 * b.q)) ∧
      ∀ Y : ℤ_[2], ArcChart k h e ((b.Xi : ℤ_[2]) + 2 ^ b.s * Y) b.Xi
        (fun t => ∃ S : Fin 2 → Kv,
          t = c0 + toKv (2 ^ b.s * Y) • c1 + toKv (2 ^ b.s * Y) ^ 2 • S ∧
          (∀ i, ‖S i‖ ≤ ‖pv‖ ^ aS) ∧ ∀ i, ‖(Amat k *ᵥ S) i‖ ≤ ‖pv‖ ^ NS)

/-! ## Leaves -/

/-- The difference of two values of `lamPt` is the logarithm of the difference of the classes. -/
theorem lamPt_sub (k : Fin 2) (x x0 : DPtKv k) :
    lamPt k x - lamPt k x0 = lam k (Additive.ofMul (phiV k x) - Additive.ofMul (phiV k x0)) := by
  rw [lamPt, lamPt, ← map_sub]
  congr 1
  abel

/-- Ultrametric bound of a sum by the two bounds. -/
theorem norm_add_le_pow {x y : Kv} {a b n : ℕ} (hx : ‖x‖ ≤ ‖pv‖ ^ a) (hy : ‖y‖ ≤ ‖pv‖ ^ b)
    (ha : n ≤ a) (hb : n ≤ b) : ‖x + y‖ ≤ ‖pv‖ ^ n := by
  have h0 := norm_pv_pos.le
  have h1 := norm_pv_lt_one.le
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (hx.trans (pow_le_pow_of_le_one h0 h1 ha)) (hy.trans (pow_le_pow_of_le_one h0 h1 hb)))

/-- The chart coordinates on a tail: `‖h c + h² S‖ ≤ ‖pv‖^(v + min a1 (s + aS))` when
`‖h‖ = ‖pv‖^v`, `s ≤ v`, `‖c‖ ≤ ‖pv‖^a1`, `‖S‖ ≤ ‖pv‖^aS`. -/
theorem norm_tail_le {hh c S : Kv} {v s a1 aS : ℕ} (hh_n : ‖hh‖ = ‖pv‖ ^ v) (hvs : s ≤ v)
    (hc : ‖c‖ ≤ ‖pv‖ ^ a1) (hS : ‖S‖ ≤ ‖pv‖ ^ aS) :
    ‖hh * c + hh ^ 2 * S‖ ≤ ‖pv‖ ^ (v + min a1 (s + aS)) := by
  have h0 := norm_pv_pos.le
  have h1 := norm_pv_lt_one.le
  have hc' : ‖hh * c‖ ≤ ‖pv‖ ^ (v + a1) := by
    rw [norm_mul, hh_n, pow_add]
    exact mul_le_mul_of_nonneg_left hc (pow_nonneg h0 _)
  have hS' : ‖hh ^ 2 * S‖ ≤ ‖pv‖ ^ (v + v + aS) := by
    rw [norm_mul, norm_pow, hh_n, ← pow_mul, pow_add, mul_two]
    exact mul_le_mul_of_nonneg_left hS (pow_nonneg h0 _)
  exact norm_add_le_pow hc' hS' (by omega) (by omega)

/-- The tail parameter: `Xi + 2^s0 (2^j u) = Xi + 2^s (2^(j - (s - s0)) u)`. -/
theorem tail_param (X u : ℤ_[2]) {s0 s j : ℕ} (hs : s0 ≤ s) (hj : s - s0 ≤ j) :
    X + 2 ^ s0 * (2 ^ j * u) = X + 2 ^ s * (2 ^ (j - (s - s0)) * u) := by
  have e : s0 + j = s + (j - (s - s0)) := by omega
  rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, e]

/-- On a tail box, the parameter `Xi + 2^s Y` lies in the box `{c + 2^s y}`. -/
theorem inBox_tail {b : TBox} (hmod : (b.c : ℤ) % 2 ^ b.s = b.Xi % 2 ^ b.s) (Y : ℤ_[2]) :
    InBox ((b.Xi : ℤ_[2]) + 2 ^ b.s * Y) b.c b.s := by
  have hdvd : (2 : ℤ) ^ b.s ∣ b.Xi - (b.c : ℤ) := Int.ModEq.dvd hmod
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨(m : ℤ_[2]) + Y, ?_⟩
  have hX : (b.Xi : ℤ_[2]) = ((b.c : ℤ) : ℤ_[2]) + ((2 ^ b.s * m : ℤ) : ℤ_[2]) := by
    rw [← hm]
    push_cast
    ring
  rw [hX]
  push_cast
  ring

/-- The zero chart point has zero chart coordinates. -/
theorem tK_zero (k : Fin 2) (h : AdmM0 k) : tK k h 0 = 0 := by
  funext i
  rw [tK_apply]
  simp

/-! ## The constant boxes -/

/-- **`HConstLip` from the per box statements.** Lemma 7.3 of the paper. -/
theorem hConstLip_of_cert {k : Fin 2} {D : TwistData} (h : AdmM0 k) (hI : LamInt k)
    (hc : ∀ c ∈ D.constant, ConstCert k h c) : HConstLip D (lamD k) := by
  have hA := norm_Amat_le_one k
  intro c hcm Y
  obtain ⟨e, he, hd, hcc, hs, D', hD1, hD2, harc⟩ := hc c hcm
  obtain ⟨x, x0, hx, hbx, hx0, hbx0, z, hz, ht, hAt⟩ := harc Y
  have hb1 : boxAt k c.disc ((c.c : ℤ_[2]) + 2 ^ c.s * Y) = some e :=
    boxAt_eq_of_mem he hd ⟨Y, by rw [hcc, hs]⟩
  have hb0 : boxAt k c.disc (c.c : ℤ_[2]) = some e :=
    boxAt_eq_of_mem he hd ⟨0, by rw [hcc, mul_zero, add_zero]⟩
  rw [lamD_eq hb1 x (by rw [hx, hd]) hbx, lamD_eq hb0 x0 (by rw [hx0, hd]) hbx0, lamPt_sub, ← hz]
  apply dvdV_of_norm_toKv2_le
  intro i
  rw [lam_toKv2 k hI]
  have h1 := norm_lamK_chart_sub_le k h hA z hD1 ht i
  have e1 : lamK k (chart k h z) i =
      (lamK k (chart k h z) i - (Amat k *ᵥ tK k h z) i) + (Amat k *ᵥ tK k h z) i := by ring
  rw [e1]
  exact norm_add_le_pow h1 (hAt i) (by omega) le_rfl

/-! ## The tail boxes -/

/-- **`HTailQuad` from the per box statements.** Lemma 7.5 of the paper. -/
theorem hTailQuad_of_cert {k : Fin 2} {D : TwistData} (hD : TwistChecks D) (h : AdmM0 k)
    (hI : LamInt k) (ht : ∀ b ∈ D.tails, TailCert k h b) : HTailQuad D (lamD k) := by
  have hA := norm_Amat_le_one k
  intro b hbm
  obtain ⟨-, -, -, -, hs01, hs0s, -, hmod⟩ := hD.tailsOK b hbm
  obtain ⟨e, he, hd, hcc, hs, c0, c1, a1, aS, NS, hT1, hT2, hT3, hc1, hg, harc⟩ := ht b hbm
  have hbox : ∀ Y : ℤ_[2], boxAt k b.disc ((b.Xi : ℤ_[2]) + 2 ^ b.s * Y) = some e := fun Y =>
    boxAt_eq_of_mem he hd (by rw [hcc, hs]; exact inBox_tail hmod Y)
  have hbox0 : boxAt k b.disc (b.Xi : ℤ_[2]) = some e := by
    simpa using hbox 0
  -- the constant term vanishes: the arc at `Y = 0` is the zero chart point
  have hc0 : c0 = 0 := by
    obtain ⟨x, x0, hx, hbx, hx0, hbx0, z, hz, S, htS, -, -⟩ := harc 0
    have hxx : x = x0 := branch_unique (by rw [hx, hx0, mul_zero, add_zero]) hbx hbx0
    rw [hxx, sub_self] at hz
    have hz0 : z = 0 :=
      (baseKv k).toSetup.psi_injective (hF k) h (hz.trans (map_zero (chart k h)).symm)
    rw [hz0, tK_zero, mul_zero, map_zero, zero_smul, zero_pow two_ne_zero, zero_smul, add_zero,
      add_zero] at htS
    exact htS.symm
  -- the vector `g`: coordinates of `2 Amat c1`
  have hint : ∀ i, ‖(2 : Kv) * (Amat k *ᵥ c1) i‖ ≤ 1 := fun i => by
    have e1 : (2 : Kv) * (Amat k *ᵥ c1) i =
        ((2 : Kv) * (Amat k *ᵥ c1) i - toKv2 (icast b.g) i) + toKv2 (icast b.g) i := by ring
    rw [e1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (norm_toKv2_le_one _ i))
    exact (hg i).trans (pow_le_one₀ norm_pv_pos.le norm_pv_lt_one.le)
  obtain ⟨g, hgG⟩ := exists_toKv2_eq hint
  refine ⟨g, ?_, ?_⟩
  · apply dvdV_of_norm_toKv2_le
    intro i
    rw [map_sub, Pi.sub_apply, hgG]
    exact hg i
  intro j u hj hu
  set m := j - (b.s - b.s0) with hm
  rw [tail_param _ _ hs0s hj]
  obtain ⟨x, x0, hx, hbx, hx0, hbx0, z, hz, S, htS, hS, hAS⟩ := harc (2 ^ m * u)
  rw [lamD_eq (hbox _) x (by rw [hx, hd]) hbx, lamD_eq hbox0 x0 (by rw [hx0, hd]) hbx0, lamPt_sub,
    ← hz]
  have hpar : (2 : ℤ_[2]) ^ b.s * (2 ^ m * u) = 2 ^ (b.s0 + j) * u := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hpar, hc0, zero_add] at htS
  set hh := toKv (2 ^ (b.s0 + j) * u) with hhh
  have hnh : ‖hh‖ = ‖pv‖ ^ (3 * (b.s0 + j)) := norm_toKv_two_pow_mul hu _
  -- the chart coordinates
  have ht : ∀ i, ‖tK k h z i‖ ≤ ‖pv‖ ^ (3 * (b.s0 + j) + min a1 (3 * b.s + aS)) := fun i => by
    rw [htS, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    exact norm_tail_le hnh (by omega) (hc1 i) (hS i)
  have hDt : M0 k + 4 ≤ 3 * (b.s0 + j) + min a1 (3 * b.s + aS) := by omega
  -- the linear term
  have hlin : toKv2 (((2 : ℤ_[2]) ^ j * u) • ((2 : ℤ_[2]) ^ (b.s0 - 1) • g)) =
      hh • (Amat k *ᵥ c1) := by
    rw [toKv2_smul, toKv2_smul, hgG]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    have e2 : (2 : ℤ_[2]) ^ (b.s0 + j) * u = 2 ^ j * u * (2 ^ (b.s0 - 1) * 2) := by
      have : b.s0 + j = (b.s0 - 1) + 1 + j := by omega
      rw [this]
      ring
    rw [hhh, e2]
    simp only [map_mul, map_pow, map_ofNat]
    ring
  apply dvdV_of_norm_toKv2_le
  intro i
  rw [map_sub, lam_toKv2 k hI, hlin]
  have h1 := norm_lamK_chart_sub_le k h hA z hDt ht i
  have hAt : (Amat k *ᵥ tK k h z) i = hh * (Amat k *ᵥ c1) i + hh ^ 2 * (Amat k *ᵥ S) i := by
    rw [htS, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    rfl
  have e3 : (lamK k (chart k h z) - hh • (Amat k *ᵥ c1)) i =
      (lamK k (chart k h z) i - (Amat k *ᵥ tK k h z) i) + hh ^ 2 * (Amat k *ᵥ S) i := by
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hAt]
    ring
  rw [e3]
  have h2 : ‖hh ^ 2 * (Amat k *ᵥ S) i‖ ≤ ‖pv‖ ^ (3 * (b.s0 + j) * 2 + NS) := by
    rw [norm_mul, norm_pow, hnh, ← pow_mul, pow_add]
    exact mul_le_mul_of_nonneg_left (hAS i) (pow_nonneg norm_pv_pos.le _)
  exact norm_add_le_pow h1 h2 (by omega) (by omega)

end FurioLombardo.Discharge.M4Box
