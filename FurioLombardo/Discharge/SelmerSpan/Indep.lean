import FurioLombardo.Discharge.SelmerSpan.Chars
import FurioLombardo.Discharge.SelmerSpan.ApproxN
import FurioLombardo.Discharge.SelmerSpan.IData

/-!
# Independence of the local images `μ_v(D_1), ..., μ_v(D_7)` (lane SelmerSpan)

**`indep_Dpt k`**: for the twist `k`, if `∏ μ_v(D_i)^(c_i) = 1` in `H g = L^× / K_v^× (L^×)²`
(`g = (fRev k)^σ`, `L = K_v[T]/(g)`), then every `c_i` is even. This is the independence conjunct of
lane M3a's `TwistInputsKv` for the points `Dpt k i` of Dpt.lean.

Proof. Reduce the `c_i` modulo 2 to bits `b_i`; the relation says `∏ U_i(T)^(b_i) = c w²` with
`c ∈ K_v^×` (`sqClass`). The characters `ψ1, ψ2, ψ3` of Chars.lean take square values there
(`chars_sq`), also after scaling each factor by a square `4^(-b)` (`isSquare_prod_sq_mul`). For every
nonzero bit vector a certificate shows that one of the three products is not a square
(`comboOK`, one `decide +kernel` over the `2 × 127` vectors):

* level 1: the product of the `ψ1` in `K_v` fails lane M3a's `SqTest` (searched in the kernel);
* level 2: the product of the `ψ2` in `N` has a non-square certificate `NCertOK` (data `lev2D`);
* level 3: for the product `z` of the `ψ3` in `M`, `n² = N_{M/N}(z)` with `n = ⟨s/2, y/s⟩`,
  `m² = x² - δ' y²`, `s² = 2 (x + m)` (two Hensel roots) and `s² (Tr z ± 2 n)` are not squares in `N`
  (`L3OK`, `not_isSquare_L3`; data `lev3D`).

The residues of the factors are computed from the exact `p_i, r_i` of Dpt.lean and the atoms of `q`,
`h` modulo `2^48` (`facOK`, `atomOK`, residues of `σ` modulo `2^58` from Sigma.lean) and compared with
the literals of IData.lean (generator code/local-group/local_divisors_indep_certs.gp).
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M4Cert
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin

namespace FurioLombardo.Discharge.SelmerSpan

/-! ## Generic certificates -/

/-- Reduction of a pair of triples. -/
def modN (P : ℕ) (t : T3 × T3) : T3 × T3 := (modT t.1 P, modT t.2 P)

/-- Reduction of a pair of pairs of triples. -/
def modM (P : ℕ) (t : (T3 × T3) × (T3 × T3)) : (T3 × T3) × (T3 × T3) := (modN P t.1, modN P t.2)

theorem ApproxN.of_modN_eq {δ : Kv} {u : QuadraticAlgebra Kv δ 0} {t t' : T3 × T3} {P : ℕ}
    (h : ApproxN u t P) (he : modN P t = modN P t') : ApproxN u t' P := by
  simp only [modN, Prod.mk.injEq] at he
  exact ⟨h.1.of_modT_eq he.1, h.2.of_modT_eq he.2⟩

theorem ApproxM.of_modM_eq {δ : Kv} {P0 P1 : QuadraticAlgebra Kv δ 0}
    {u : QuadraticAlgebra (QuadraticAlgebra Kv δ 0) (-P0) (-P1)} {t t' : (T3 × T3) × (T3 × T3)} {P : ℕ}
    (h : ApproxM u t P) (he : modM P t = modM P t') : ApproxM u t' P := by
  simp only [modM, Prod.mk.injEq] at he
  exact ⟨h.1.of_modN_eq he.1, h.2.of_modN_eq he.2⟩

theorem inv_four_pow (b : ℕ) : ((2 : Kv) ^ (2 * b))⁻¹ = ((2 ^ b)⁻¹) ^ 2 := by
  rw [pow_mul', inv_pow]

theorem not_isSquare_lev1 {x : Fin 7 → Kv} {t : ℕ → T3} {P : ℕ} (hx : ∀ i : Fin 7, Approx (x i) (t i) P)
    (bs : List Bool) {i j : ℕ} (h : SqTest (prod7T P bs t) i j 0 P) :
    ¬ IsSquare (∏ i : Fin 7, x i ^ bexp (bs.getD i false)) := by
  rintro ⟨r, hr⟩
  exact not_sq_of_sqTest (approx_prod7T hx bs) h r (by rw [hr]; ring)

theorem not_isSquare_lev2 {δ : Kv} {x : Fin 7 → QuadraticAlgebra Kv δ 0} {t : ℕ → T3 × T3} {dl : T3}
    {P : ℕ} (hd : Approx δ dl P) (hx : ∀ i : Fin 7, ApproxN (x i) (t i) P) (bs : List Bool) {c : NCert}
    (h : NCertOK P dl (prod7NT P dl bs t) c) : ¬ IsSquare (∏ i : Fin 7, x i ^ bexp (bs.getD i false)) :=
  not_isSquare_of_NCertOK hd (approx_prod7NT hd hx bs) h

/-- The level 3 certificate for `z ∈ M = N(x0)` with residue `t` modulo `2^P`: `z' = 4^(-bz) z` has
residue `zt`, `N(z') = x + y ω'` residue `Nz`; `bm` (a Hensel start for `m² = x² - δ' y²`, at `2^M`),
`bsq` (for `s² = 2 (x + m)`, at `2^Pm`), `s ≠ 0`, and the non-square certificates of
`4^(-bE±) (2 (x + m) Tr z' ± 2 s (x + m + y ω'))` at `2^(Ps - 2 bE±)`. -/
def L3OK (P : ℕ) (dl : T3) (t0 t1 : T3 × T3) (t : (T3 × T3) × (T3 × T3)) (bz : ℕ) (bm : T3) (sm : ℕ)
    (bsq : T3) (ss bEp : ℕ) (cp : NCert) (bEm : ℕ) (cm : NCert) : Prop :=
  let M := P - 2 * bz
  let zt := scM P bz t
  let Nz := normMT M dl t0 t1 zt
  let Pm := M - (sm + 2)
  let xm := addT Pm Nz.1 bm
  let Ps := Pm - (ss + 2)
  let A1 := scNT Ps (mulT Ps (cT 2) xm) (trMT Ps dl t1 zt)
  let A2 := scNT Ps (mulT Ps (cT 2) bsq) (xm, Nz.2)
  ScMOK P bz t ∧ modT (mulZ bm bm) M = modT (normNT M dl Nz) M ∧ LowOK bm sm ∧ 2 * sm + 4 ≤ M ∧
    modT (mulZ bsq bsq) Pm = modT (mulT Pm (cT 2) xm) Pm ∧ LowOK bsq ss ∧ 2 * ss + 4 ≤ Pm ∧
    modT bsq Ps ≠ modT (0, 0, 0) Ps ∧
    ScNOK Ps bEp (addNT Ps A1 A2) ∧ NCertOK (Ps - 2 * bEp) dl (scN Ps bEp (addNT Ps A1 A2)) cp ∧
    ScNOK Ps bEm (subNT Ps A1 A2) ∧ NCertOK (Ps - 2 * bEm) dl (scN Ps bEm (subNT Ps A1 A2)) cm

instance (P : ℕ) (dl : T3) (t0 t1 : T3 × T3) (t : (T3 × T3) × (T3 × T3)) (bz : ℕ) (bm : T3) (sm : ℕ)
    (bsq : T3) (ss bEp : ℕ) (cp : NCert) (bEm : ℕ) (cm : NCert) :
    Decidable (L3OK P dl t0 t1 t bz bm sm bsq ss bEp cp bEm cm) := by
  dsimp only [L3OK]; infer_instance

/-- **Level 3**: a non-square of `M` from `L3OK`. -/
theorem not_isSquare_L3 {δ : Kv} (hδ : ¬ IsSquare δ) {P0 P1 : QuadraticAlgebra Kv δ 0}
    {z : QuadraticAlgebra (QuadraticAlgebra Kv δ 0) (-P0) (-P1)} {dl : T3} {t0 t1 : T3 × T3}
    {t : (T3 × T3) × (T3 × T3)} {P bz : ℕ} {bm : T3} {sm : ℕ} {bsq : T3} {ss bEp : ℕ} {cp : NCert}
    {bEm : ℕ} {cm : NCert} (hd : Approx δ dl P) (h0 : ApproxN P0 t0 P) (h1 : ApproxN P1 t1 P)
    (hz : ApproxM z t P) (h : L3OK P dl t0 t1 t bz bm sm bsq ss bEp cp bEm cm) : ¬ IsSquare z := by
  dsimp only [L3OK] at h
  obtain ⟨hsc, hbm, hlm, hsm, hbs, hls, hss, hs0, hEp, hcp, hEm, hcm⟩ := h
  set M := P - 2 * bz with hM
  set zt := scM P bz t with hzt
  set Nz := normMT M dl t0 t1 zt with hNz
  set Pm := M - (sm + 2) with hPm
  set xm := addT Pm Nz.1 bm with hxm
  set Ps := Pm - (ss + 2) with hPs
  set A1 := scNT Ps (mulT Ps (cT 2) xm) (trMT Ps dl t1 zt) with hA1
  set A2 := scNT Ps (mulT Ps (cT 2) bsq) (xm, Nz.2) with hA2
  have hMP : M ≤ P := Nat.sub_le _ _
  have hPmM : Pm ≤ M := Nat.sub_le _ _
  have hPsPm : Ps ≤ Pm := Nat.sub_le _ _
  set ιN := algebraMap Kv (QuadraticAlgebra Kv δ 0) with hιN
  set ιM := algebraMap (QuadraticAlgebra Kv δ 0) (QuadraticAlgebra (QuadraticAlgebra Kv δ 0) (-P0) (-P1))
    with hιM
  -- the scaled element `z' = 4^(-bz) z`
  have hz' : ApproxM (ιM (ιN ((2 ^ (2 * bz) : Kv)⁻¹)) * z) zt M := approx_scM hz hsc
  intro hsq
  have hsq' : IsSquare (ιM (ιN ((2 ^ (2 * bz) : Kv)⁻¹)) * z) := by
    rw [inv_four_pow, map_pow, map_pow]
    exact (IsSquare.sq _).mul hsq
  -- `N(z') = x + y ω'`
  have hdM : Approx δ dl M := hd.mono hMP
  have hN := approx_normMT hdM (h0.mono hMP) (h1.mono hMP) hz'
  set Nv := QuadraticAlgebra.norm (ιM (ιN ((2 ^ (2 * bz) : Kv)⁻¹)) * z) with hNv
  have hNN := approx_normNT hdM hN
  obtain ⟨m, hm2, hmA⟩ := exists_sqrt hNN hbm hlm hsm
  have hxmA : Approx (Nv.re + m) xm Pm := approx_addT (hN.1.mono hPmM) hmA
  have h2x : Approx (2 * (Nv.re + m)) (mulT Pm (cT 2) xm) Pm := approx_mulT (approx_two Pm) hxmA
  obtain ⟨s, hs2, hsA⟩ := exists_sqrt h2x hbs hls hss
  have hsne : s ≠ 0 := ne_zero_of_approx hsA hs0
  have hm' : m ^ 2 = Nv.re ^ 2 - δ * Nv.im ^ 2 := by
    rw [hm2, QuadraticAlgebra.norm_def]; ring
  have hn : (⟨s / 2, Nv.im / s⟩ : QuadraticAlgebra Kv δ 0) ^ 2 = Nv :=
    qa0_sq_mk two_ne_zero_Kv hm' hs2 hsne
  -- the two values `s² (Tr z' ± 2 n)`
  have hdS : Approx δ dl Ps := hd.mono (hPsPm.trans (hPmM.trans hMP))
  have htr := approx_trMT hdS (h1.mono (hPsPm.trans (hPmM.trans hMP))) (hz'.mono (hPsPm.trans hPmM))
  have hx2 : Approx (2 * (Nv.re + m)) (mulT Ps (cT 2) xm) Ps :=
    approx_mulT (approx_two Ps) (hxmA.mono hPsPm)
  have hs2A : Approx (2 * s) (mulT Ps (cT 2) bsq) Ps := approx_mulT (approx_two Ps) hsA
  have hA1a := approx_scNT hx2 htr
  have hA2a := approx_scNT hs2A (approx_mkN (δ := δ) (hxmA.mono hPsPm) (hN.2.mono (hPsPm.trans hPmM)))
  have hfac : ∀ (b : ℕ) (E w : QuadraticAlgebra Kv δ 0), E = ιN (s ^ 2) * (w * w) →
      IsSquare (ιN ((2 ^ (2 * b) : Kv)⁻¹) * E) := by
    intro b E w hE
    rw [hE, inv_four_pow, map_pow, map_pow]
    exact (IsSquare.sq _).mul ((IsSquare.sq _).mul ⟨w, rfl⟩)
  refine qa_not_isSquare_of_trace_dom (fun u v h => qa0_mul_eq_zero hδ h) _ ⟨s / 2, Nv.im / s⟩ hn ?_ ?_
    hsq'
  · rintro ⟨w, hw⟩
    have key := qa0_scale_add (y := Nv.im) two_ne_zero_Kv hs2 hsne
      (QuadraticAlgebra.trace (ιM (ιN ((2 ^ (2 * bz) : Kv)⁻¹)) * z))
    have hE := approx_scN (approx_addNT hA1a hA2a) hEp
    refine not_isSquare_of_NCertOK (hdS.mono (Nat.sub_le _ _)) hE hcp (hfac bEp _ w ?_)
    rw [← key, hw]
  · rintro ⟨w, hw⟩
    have key := qa0_scale_sub (y := Nv.im) two_ne_zero_Kv hs2 hsne
      (QuadraticAlgebra.trace (ιM (ιN ((2 ^ (2 * bz) : Kv)⁻¹)) * z))
    have hE := approx_scN (approx_subNT hA1a hA2a) hEm
    refine not_isSquare_of_NCertOK (hdS.mono (Nat.sub_le _ _)) hE hcm (hfac bEm _ w ?_)
    rw [← key, hw]

theorem pow_eq_bexp {G : Type*} [Group G] {x : G} (hx : x ^ 2 = 1) (c : ℤ) :
    x ^ c = x ^ bexp (decide (c % 2 = 1)) := by
  have h1 : x ^ c = x ^ (c % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv c 2]
    rw [zpow_add, zpow_mul, zpow_two, ← pow_two, hx, one_zpow, mul_one]
  rw [h1]
  rcases Int.emod_two_eq_zero_or_one c with h | h <;> rw [h] <;> simp [bexp]

theorem mul_algebraMap_re_im {R : Type*} [CommRing R] {a b : R} (z : QuadraticAlgebra R a b) (n : R) :
    (z * algebraMap R _ n).re = z.re * n ∧ (z * algebraMap R _ n).im = z.im * n := by
  constructor <;> simp [QuadraticAlgebra.algebraMap_eq]

theorem approx_algSubN {δ : Kv} {r : Kv} {tr : T3} {Q : QuadraticAlgebra Kv δ 0} {tQ : T3 × T3} {P : ℕ}
    (hr : Approx r tr P) (hQ : ApproxN Q tQ P) :
    ApproxN (algebraMap Kv _ r - Q) (subT P tr tQ.1, subT P (0, 0, 0) tQ.2) P := by
  constructor
  · have e : (algebraMap Kv (QuadraticAlgebra Kv δ 0) r - Q).re = r - Q.re := by
      simp [QuadraticAlgebra.algebraMap_eq]
    rw [e]; exact approx_subT hr hQ.1
  · have e : (algebraMap Kv (QuadraticAlgebra Kv δ 0) r - Q).im = 0 - Q.im := by
      simp [QuadraticAlgebra.algebraMap_eq]
    rw [e]; exact approx_subT (approx_zero P) hQ.2

/-! ## Data -/

def qLi (k j : ℕ) : List ℤ := (qData.getD k []).getD j []
def atJ (k j : ℕ) : ℕ := ((atJO.getD k []).getD j (0, 1, 1)).1
def atO (k j : ℕ) : ℕ := ((atJO.getD k []).getD j (0, 1, 1)).2.1
def atOI (k j : ℕ) : ℤ := ((atJO.getD k []).getD j (0, 1, 1)).2.2
/-- Residue of the atom `j` (`h1, q0, a0, a1, 2 b0, 2 b1`) with numerator list `l`. -/
def tAt (k j : ℕ) (l : List ℤ) : T3 := sQres1 l (atJ k j) (atOI k j) PI
def tH1 (k : ℕ) : T3 := tAt k 0 (qLi k 1)
def tQ0 (k : ℕ) : T3 := tAt k 1 (qLi k 0)
def mbHalf (k : ℕ) : ℕ := mbDen.getD k 1 / 2
def dlL (k : ℕ) : T3 := dlD.getD k (0, 0, 0)
def P0L (k : ℕ) : T3 × T3 := P0D.getD k ((0, 0, 0), (0, 0, 0))
def P1L (k : ℕ) : T3 × T3 := P1D.getD k ((0, 0, 0), (0, 0, 0))
def F1 (k i : ℕ) : T3 := (F1D.getD k []).getD i (0, 0, 0)
def F2 (k i : ℕ) : T3 × T3 := (F2D.getD k []).getD i ((0, 0, 0), (0, 0, 0))
def F3 (k i : ℕ) : (T3 × T3) × (T3 × T3) :=
  (F3D.getD k []).getD i (((0, 0, 0), (0, 0, 0)), ((0, 0, 0), (0, 0, 0)))
def sb1 (k i : ℕ) : ℕ := ((scalD.getD k []).getD i (0, 0, 0)).1
def sb2 (k i : ℕ) : ℕ := ((scalD.getD k []).getD i (0, 0, 0)).2.1
def sb3 (k i : ℕ) : ℕ := ((scalD.getD k []).getD i (0, 0, 0)).2.2
def pc1 (k : ℕ) : ℕ := (pcD.getD k (0, 0, 0)).1
def pc2 (k : ℕ) : ℕ := (pcD.getD k (0, 0, 0)).2.1
def pc3 (k : ℕ) : ℕ := (pcD.getD k (0, 0, 0)).2.2
def prP (k i : ℕ) : ℤ := ((prOI.getD k []).getD i (1, 1)).1
def prR (k i : ℕ) : ℤ := ((prOI.getD k []).getD i (1, 1)).2

/-- The atoms: exact denominators, residues, `δ' = h1² - q0`, `P0`, `P1` against the literals. -/
def AtomOK (k : ℕ) : Prop :=
  SQok1 (qLi k 1) (2 * qDenN k) (atJ k 0) (atO k 0) (atOI k 0) PI ∧
  SQok1 (qLi k 0) (qDenN k) (atJ k 1) (atO k 1) (atOI k 1) PI ∧
  SQok1 (abL k 0) (maDen.getD k 1) (atJ k 2) (atO k 2) (atOI k 2) PI ∧
  SQok1 (abL k 1) (maDen.getD k 1) (atJ k 3) (atO k 3) (atOI k 3) PI ∧
  SQok1 (abL k 2) (mbHalf k) (atJ k 4) (atO k 4) (atOI k 4) PI ∧
  SQok1 (abL k 3) (mbHalf k) (atJ k 5) (atO k 5) (atOI k 5) PI ∧
  mbDen.getD k 1 = 2 * mbHalf k ∧
  subT PI (mulT PI (tH1 k) (tH1 k)) (tQ0 k) = dlL k ∧
  (modT (tAt k 2 (abL k 0)) PI, modT (tAt k 4 (abL k 2)) PI) = P0L k ∧
  (modT (tAt k 3 (abL k 1)) PI, modT (tAt k 5 (abL k 3)) PI) = P1L k ∧
  pc1 k ≤ PI ∧ pc2 k ≤ PI ∧ pc3 k ≤ PI

instance (k : ℕ) : Decidable (AtomOK k) := by unfold AtomOK; infer_instance

/-- Residue of `p_i`. -/
def tp1 (k i : ℕ) : T3 := sQres1 (pLi k i) (pJ k i) (prP k i) PI
/-- Residue of `r_i`. -/
def tr1 (k i : ℕ) : T3 := sQres1 (rLi k i) (rJ k i) (prR k i) PI

/-- Residue of `U_i(τ) = (h1² + δ' - p h1 + r) + (p - 2 h1) ω'`. -/
def uTau (k i : ℕ) : T3 × T3 :=
  (addT PI (subT PI (addT PI (mulT PI (tH1 k) (tH1 k)) (dlL k)) (mulT PI (tp1 k i) (tH1 k))) (tr1 k i),
   subT PI (tp1 k i) (mulT PI (cT 2) (tH1 k)))

/-- Residue of `U_i(x0) = (r - P0) + (p - P1) x0`. -/
def uX0 (k i : ℕ) : (T3 × T3) × (T3 × T3) :=
  ((subT PI (tr1 k i) (P0L k).1, subT PI (0, 0, 0) (P0L k).2),
   (subT PI (tp1 k i) (P1L k).1, subT PI (0, 0, 0) (P1L k).2))

def ps1T (k i : ℕ) : T3 := normNT PI (dlL k) (uTau k i)
def ps2T (k i : ℕ) : T3 × T3 := normMT PI (dlL k) (P0L k) (P1L k) (uX0 k i)
def ps3T (k i : ℕ) : (T3 × T3) × (T3 × T3) :=
  (mulNT PI (dlL k) (uX0 k i).1 (uTau k i), mulNT PI (dlL k) (uX0 k i).2 (uTau k i))

/-- The factor `i`: `p_i`, `r_i`, and the scaled character values against the literals. -/
def FacOK (k i : ℕ) : Prop :=
  SQok1 (pLi k i) (pMi k i) (pJ k i) (pO k i) (prP k i) PI ∧
  SQok1 (rLi k i) (rMi k i) (rJ k i) (rO k i) (prR k i) PI ∧
  ScOK PI (sb1 k i) (ps1T k i) ∧ pc1 k + 2 * sb1 k i ≤ PI ∧
    modT (scT PI (sb1 k i) (ps1T k i)) (pc1 k) = modT (F1 k i) (pc1 k) ∧
  ScNOK PI (sb2 k i) (ps2T k i) ∧ pc2 k + 2 * sb2 k i ≤ PI ∧
    modN (pc2 k) (scN PI (sb2 k i) (ps2T k i)) = modN (pc2 k) (F2 k i) ∧
  ScMOK PI (sb3 k i) (ps3T k i) ∧ pc3 k + 2 * sb3 k i ≤ PI ∧
    modM (pc3 k) (scM PI (sb3 k i) (ps3T k i)) = modM (pc3 k) (F3 k i)

instance (k i : ℕ) : Decidable (FacOK k i) := by unfold FacOK; infer_instance

/-- Level 1: the kernel searches the square test. -/
def lev1B (k : ℕ) (bs : List Bool) : Bool :=
  (List.range 3).any fun i => (List.range 12).any fun j =>
    decide (SqTest (prod7T (pc1 k) bs (F1 k)) i j 0 (pc1 k))

/-- Level 2: the certificate `lev2D`. -/
def lev2B (k : ℕ) (bs : List Bool) : Bool :=
  match (lev2D.getD k []).lookup bs with
  | some c => decide (NCertOK (pc2 k) (dlL k) (prod7NT (pc2 k) (dlL k) bs (F2 k)) c)
  | none => false

/-- Level 3: the certificate `lev3D`. -/
def lev3B (k : ℕ) (bs : List Bool) : Bool :=
  match (lev3D.getD k []).lookup bs with
  | some (bz, bm, sm, bsq, ss, bEp, cp, bEm, cm) =>
      decide (L3OK (pc3 k) (dlL k) (P0L k) (P1L k) (prod7MT (pc3 k) (dlL k) (P0L k) (P1L k) bs (F3 k))
        bz bm sm bsq ss bEp cp bEm cm)
  | none => false

def comboB (k : ℕ) (bs : List Bool) : Bool := lev1B k bs || lev2B k bs || lev3B k bs

/-! ## The kernel checks -/

theorem atomOK : ∀ k : Fin 2, AtomOK k := by decide +kernel

theorem facOK : ∀ k : Fin 2, ∀ i : Fin 7, FacOK k i := by decide +kernel

theorem comboOK : ∀ k : Fin 2, ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    [b0, b1, b2, b3, b4, b5, b6] = [false, false, false, false, false, false, false] ∨
      comboB k [b0, b1, b2, b3, b4, b5, b6] = true := by
  decide +kernel

/-! ## Residues of the atoms and of the character values -/

theorem approx_h1 (k : Fin 2) : Approx (h1v k) (tH1 k) PI := by
  have h := approx_σ_atom1 (atomOK k).1
  have e : h1v k = σ (((2 * qDenN k : ℕ) : K21)⁻¹ * zkE (qLi k 1)) := by
    rw [h1v, ← ev_q1Q, q1Q, QE.ev_atom, qLi]
    simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul, Nat.cast_ofNat, map_ofNat]
    ring
  rw [e]; exact h

theorem approx_q0 (k : Fin 2) : Approx (q0v k) (tQ0 k) PI := by
  have h := approx_σ_atom1 (atomOK k).2.1
  have e : q0v k = σ (((qDenN k : ℕ) : K21)⁻¹ * zkE (qLi k 0)) := by
    rw [q0v, ← ev_q0Q, q0Q, QE.ev_atom, qLi]
  rw [e]; exact h

theorem approx_a0 (k : Fin 2) : Approx (σ (a0 k)) (tAt k 2 (abL k 0)) PI :=
  approx_σ_atom1 (atomOK k).2.2.1

theorem approx_a1 (k : Fin 2) : Approx (σ (a1 k)) (tAt k 3 (abL k 1)) PI :=
  approx_σ_atom1 (atomOK k).2.2.2.1

theorem two_mul_σ_half (k : Fin 2) (l : List ℤ) :
    2 * σ (((mbDen.getD k 1 : ℕ) : K21)⁻¹ * zkE l) = σ (((mbHalf k : ℕ) : K21)⁻¹ * zkE l) := by
  rw [(atomOK k).2.2.2.2.2.2.1]
  simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul, Nat.cast_ofNat, map_ofNat]
  rw [mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ two_ne_zero_Kv, one_mul]

theorem approx_B0 (k : Fin 2) : Approx (2 * σ (b0 k)) (tAt k 4 (abL k 2)) PI := by
  have h := approx_σ_atom1 (atomOK k).2.2.2.2.1
  rw [b0, b0Q, QE.ev_atom, two_mul_σ_half]; exact h

theorem approx_B1 (k : Fin 2) : Approx (2 * σ (b1 k)) (tAt k 5 (abL k 3)) PI := by
  have h := approx_σ_atom1 (atomOK k).2.2.2.2.2.1
  rw [b1, b1Q, QE.ev_atom, two_mul_σ_half]; exact h

theorem approx_dl (k : Fin 2) : Approx (dlv k) (dlL k) PI := by
  have h := approx_subT (approx_mulT (approx_h1 k) (approx_h1 k)) (approx_q0 k)
  rw [(atomOK k).2.2.2.2.2.2.2.1] at h
  rw [dlv, sq]; exact h

theorem approx_P0 (k : Fin 2) : ApproxN (P0N k) (P0L k) PI := by
  rw [← (atomOK k).2.2.2.2.2.2.2.2.1]
  exact ⟨(approx_a0 k).reduce, (approx_B0 k).reduce⟩

theorem approx_P1 (k : Fin 2) : ApproxN (P1N k) (P1L k) PI := by
  rw [← (atomOK k).2.2.2.2.2.2.2.2.2.1]
  exact ⟨(approx_a1 k).reduce, (approx_B1 k).reduce⟩

theorem approx_p1 (k : Fin 2) (i : Fin 7) : Approx (σ (pG k i)) (tp1 k i) PI :=
  approx_σ_atom1 (facOK k i).1

theorem approx_r1 (k : Fin 2) (i : Fin 7) : Approx (σ (rG k i)) (tr1 k i) PI :=
  approx_σ_atom1 (facOK k i).2.1

theorem approx_uTau (k : Fin 2) (i : Fin 7) :
    ApproxN (evN k (AdjoinRoot.mk _ (Uv k i))) (uTau k i) PI := by
  rw [Uv, evN_mk]
  exact approx_mkN (approx_addT (approx_subT (approx_addT (approx_mulT (approx_h1 k) (approx_h1 k))
    (approx_dl k)) (approx_mulT (approx_p1 k i) (approx_h1 k))) (approx_r1 k i))
    (approx_subT (approx_p1 k i) (approx_mulT (approx_two PI) (approx_h1 k)))

theorem approx_uX0 (k : Fin 2) (i : Fin 7) :
    ApproxM (evM k (AdjoinRoot.mk _ (Uv k i))) (uX0 k i) PI := by
  rw [Uv, evM_mk]
  exact ⟨approx_algSubN (approx_r1 k i) (approx_P0 k), approx_algSubN (approx_p1 k i) (approx_P1 k)⟩

theorem approx_ψ1 (k : Fin 2) (i : Fin 7) :
    Approx (ψ1 k (AdjoinRoot.mk _ (Uv k i))) (ps1T k i) PI :=
  approx_normNT (approx_dl k) (approx_uTau k i)

theorem approx_ψ2 (k : Fin 2) (i : Fin 7) :
    ApproxN (ψ2 k (AdjoinRoot.mk _ (Uv k i))) (ps2T k i) PI :=
  approx_normMT (approx_dl k) (approx_P0 k) (approx_P1 k) (approx_uX0 k i)

theorem approx_ψ3 (k : Fin 2) (i : Fin 7) :
    ApproxM (ψ3 k (AdjoinRoot.mk _ (Uv k i))) (ps3T k i) PI := by
  rw [ψ3_apply]
  obtain ⟨hre, him⟩ := mul_algebraMap_re_im (evM k (AdjoinRoot.mk _ (Uv k i)))
    (evN k (AdjoinRoot.mk _ (Uv k i)))
  refine ⟨?_, ?_⟩
  · rw [hre]; exact approx_mulNT (approx_dl k) (approx_uX0 k i).1 (approx_uTau k i)
  · rw [him]; exact approx_mulNT (approx_dl k) (approx_uX0 k i).2 (approx_uTau k i)

/-- The scaled values `4^(-b) ψ_j(U_i(T))`. -/
noncomputable def x1 (k : Fin 2) (i : Fin 7) : Kv :=
  ((2 ^ sb1 k i : Kv)⁻¹) ^ 2 * ψ1 k (AdjoinRoot.mk _ (Uv k i))

noncomputable def x2 (k : Fin 2) (i : Fin 7) : NF k :=
  (algebraMap Kv (NF k) ((2 ^ sb2 k i : Kv)⁻¹)) ^ 2 * ψ2 k (AdjoinRoot.mk _ (Uv k i))

noncomputable def x3 (k : Fin 2) (i : Fin 7) : MF k :=
  (algebraMap (NF k) (MF k) (algebraMap Kv (NF k) ((2 ^ sb3 k i : Kv)⁻¹))) ^ 2 *
    ψ3 k (AdjoinRoot.mk _ (Uv k i))

theorem approx_x1 (k : Fin 2) (i : Fin 7) : Approx (x1 k i) (F1 k i) (pc1 k) := by
  obtain ⟨-, -, hs, hle, he, -⟩ := facOK k i
  have h := approx_scT (approx_ψ1 k i) hs
  have h' := (h.mono (by omega : pc1 k ≤ PI - 2 * sb1 k i)).of_modT_eq he
  rw [div_four_pow_eq, mul_comm] at h'
  exact h'

theorem approx_x2 (k : Fin 2) (i : Fin 7) : ApproxN (x2 k i) (F2 k i) (pc2 k) := by
  obtain ⟨-, -, -, -, -, hs, hle, he, -⟩ := facOK k i
  have h := approx_scN (approx_ψ2 k i) hs
  have h' := (h.mono (by omega : pc2 k ≤ PI - 2 * sb2 k i)).of_modN_eq he
  rw [x2, ← map_pow, ← inv_four_pow]
  exact h'

theorem approx_x3 (k : Fin 2) (i : Fin 7) : ApproxM (x3 k i) (F3 k i) (pc3 k) := by
  obtain ⟨-, -, -, -, -, -, -, -, hs, hle, he⟩ := facOK k i
  have h := approx_scM (approx_ψ3 k i) hs
  have h' := (h.mono (by omega : pc3 k ≤ PI - 2 * sb3 k i)).of_modM_eq he
  rw [x3, ← map_pow, ← map_pow, ← inv_four_pow]
  exact h'

/-- **For a nonzero bit vector one of the three scaled products is not a square.** -/
theorem not_all_sq (k : Fin 2) (bs : List Bool) (h : comboB k bs = true) :
    ¬ (IsSquare (∏ i : Fin 7, x1 k i ^ bexp (bs.getD i false)) ∧
      IsSquare (∏ i : Fin 7, x2 k i ^ bexp (bs.getD i false)) ∧
      IsSquare (∏ i : Fin 7, x3 k i ^ bexp (bs.getD i false))) := by
  rintro ⟨s1, s2, s3⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hp2, hp3⟩ := atomOK k
  simp only [comboB, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · simp only [lev1B, List.any_eq_true, List.mem_range, decide_eq_true_eq] at h
    obtain ⟨i, -, j, -, hij⟩ := h
    exact not_isSquare_lev1 (approx_x1 k) bs hij s1
  · unfold lev2B at h
    split at h
    · exact not_isSquare_lev2 ((approx_dl k).mono hp2) (approx_x2 k) bs (of_decide_eq_true h) s2
    · exact absurd h Bool.false_ne_true
  · unfold lev3B at h
    split at h
    · have hd := (approx_dl k).mono hp3
      have h0 := (approx_P0 k).mono hp3
      have h1 := (approx_P1 k).mono hp3
      exact not_isSquare_L3 (dlv_not_isSquare k) hd h0 h1 (approx_prod7MT hd h0 h1 (approx_x3 k) bs)
        (of_decide_eq_true h) s3
    · exact absurd h Bool.false_ne_true

attribute [local instance] goodSextic_fRev_Kv

/-- A relation in `sqClass` makes the three scaled products squares. -/
theorem sq_of_mem (k : Fin 2) (e : Fin 7 → ℕ)
    (hmem : ∏ i, (isUnit_U k i).unit ^ e i ∈ sqClass ((fRev k).map σ)) :
    IsSquare (∏ i, x1 k i ^ e i) ∧ IsSquare (∏ i, x2 k i ^ e i) ∧ IsSquare (∏ i, x3 k i ^ e i) := by
  rw [sqClass, Subgroup.mem_sup] at hmem
  obtain ⟨y, ⟨c0, rfl⟩, z, ⟨w, rfl⟩, hyz⟩ := hmem
  have hval : algebraMap Kv (AdjoinRoot ((fRev k).map σ)) (c0 : Kv) * (w : AdjoinRoot _) ^ 2 =
      ∏ i, AdjoinRoot.mk _ (Uv k i) ^ e i := by
    have h := congrArg Units.val hyz
    simpa [Units.coe_prod, IsUnit.unit_spec] using h
  obtain ⟨s1, s2, s3⟩ := chars_sq k c0 w
  rw [hval, map_prod] at s1 s2 s3
  simp only [map_pow] at s1 s2 s3
  exact ⟨isSquare_prod_sq_mul Finset.univ (fun i => ψ1 k (AdjoinRoot.mk _ (Uv k i)))
      (fun i => (2 ^ sb1 k i : Kv)⁻¹) e s1,
    isSquare_prod_sq_mul Finset.univ (fun i => ψ2 k (AdjoinRoot.mk _ (Uv k i)))
      (fun i => algebraMap Kv (NF k) ((2 ^ sb2 k i : Kv)⁻¹)) e s2,
    isSquare_prod_sq_mul Finset.univ (fun i => ψ3 k (AdjoinRoot.mk _ (Uv k i)))
      (fun i => algebraMap (NF k) (MF k) (algebraMap Kv (NF k) ((2 ^ sb3 k i : Kv)⁻¹))) e s3⟩

/-- **(K2), independence**: the local images of `D_1, ..., D_7` are independent in `H g`.
Lemma 6.3 of the paper. -/
theorem indep_Dpt (k : Fin 2) : ∀ c : Fin 7 → ℤ,
    ∏ i, muJ ((fRev k).map σ) (Additive.toMul (Dpt k i)) ^ c i = 1 → ∀ i, (2 : ℤ) ∣ c i := by
  intro c hc
  have hpow : ∀ i, muJ ((fRev k).map σ) (Additive.toMul (Dpt k i)) ^ c i =
      QuotientGroup.mk ((isUnit_U k i).unit ^ bexp (decide (c i % 2 = 1))) := by
    intro i
    rw [muJ_Dpt, pow_eq_bexp (H_sq_eq_one _ _) (c i), QuotientGroup.mk_pow]
  rw [Finset.prod_congr rfl fun i _ => hpow i, ← QuotientGroup.mk_prod,
    QuotientGroup.eq_one_iff] at hc
  obtain ⟨s1, s2, s3⟩ := sq_of_mem k _ hc
  have hbs : ∀ i : Fin 7, [decide (c 0 % 2 = 1), decide (c 1 % 2 = 1), decide (c 2 % 2 = 1),
      decide (c 3 % 2 = 1), decide (c 4 % 2 = 1), decide (c 5 % 2 = 1), decide (c 6 % 2 = 1)].getD i
      false = decide (c i % 2 = 1) := by
    intro i; fin_cases i <;> rfl
  rcases comboOK k (decide (c 0 % 2 = 1)) (decide (c 1 % 2 = 1)) (decide (c 2 % 2 = 1))
    (decide (c 3 % 2 = 1)) (decide (c 4 % 2 = 1)) (decide (c 5 % 2 = 1)) (decide (c 6 % 2 = 1))
    with h0 | h0
  · intro i
    have hb : decide (c i % 2 = 1) = false := by
      rw [← hbs i, h0]; fin_cases i <;> rfl
    have : c i % 2 = 0 := by
      have := Int.emod_two_eq_zero_or_one (c i)
      simp only [decide_eq_false_iff_not] at hb
      omega
    exact Int.dvd_of_emod_eq_zero this
  · exfalso
    apply not_all_sq k _ h0
    simp only [hbs]
    exact ⟨s1, s2, s3⟩

end FurioLombardo.Discharge.SelmerSpan
