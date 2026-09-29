import FurioLombardo.Discharge.SelmerBasis.PlaceWGen
import FurioLombardo.Discharge.SelmerBasis.LocalLemmas
import FurioLombardo.M1.ZK

/-!
# Square certificates at an Eisenstein component, from integer data (lane selmer-basis w-places)

A place of `K21` is a ring hom `σ : K21 →+* Kw` into a complete ultrametric field with a uniformizer
`π = σ(al)` (`WPlace`). An Eisenstein component is `F = QF Kw (σ A) (σ B)` with `A = al (1 + al cA)` and
`B = al bB` (`EisData`, checked in the kernel by `EisData.ok`), `Y = QF.mk 0 1` its uniformizer. The
standard basis of `Fˣ / Fˣ²` is `bF`: `Y`, the units `1 + π^j Y` (`j < 2e`, depth `2j + 1`) and `5`.

`certOK_isSquare`: a passing `certOK` (two coordinate identities in `K21`, one `checkK` each, on the
coordinates of `Y^n` from the table `Ypow` and of `π^d` from `alPow`) makes `x · ∏ bF^a` a square for
every `x` within `‖π‖^n0` of the exact element `toF X0 X1`. The product `∏_{j ∈ S} (1 + π^j Y)` is
expanded by the dynamic program of PlaceWGen.lean and truncated at `π^D`; the truncation and the
distance from `x` are bounded inside the proof (`isSquare_of_eisen_cert`).

Data format: code/selmer-local-conditions/local_certs_w6.gp (function `w3cert`).
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis

open FurioLombardo.M1 FurioLombardo.M1.Kron

/-! ## Integer data and kernel checks -/

/-- A square certificate: bits `a` of the basis product, `m = 2 mh + ep`, `S'' = u0 + s1 Y` with
`u0 = 1 + al c0`, remainders `R0`, `R1` at `al^n0`, `al^n1`, and the `checkK` precision. -/
structure WCert where
  a : ℕ
  mh : ℕ
  ep : ℕ
  u0 : List ℤ
  c0 : List ℤ
  s1 : List ℤ
  n0 : ℕ
  n1 : ℕ
  R0 : List ℤ
  R1 : List ℤ
  prec : ℕ
  deriving Inhabited

/-- An Eisenstein component: `e = e(w/2)`, uniformizer `al`, `A = al (1 + al cA)`, `B = al bB`,
the tables `alPow d = al^d` and `Ypow n = Y^n` (coordinates on `1, Y`), the precision of the checks. -/
structure EisData where
  e : ℕ
  al : List ℤ
  A : List ℤ
  B : List ℤ
  cA : List ℤ
  bB : List ℤ
  alPow : List (List ℤ)
  Ypow : List (List ℤ × List ℤ)
  prec : ℕ
  deriving Inhabited

namespace EisData

variable (E : EisData)

/-- `al^d`. -/
def alP (d : ℕ) : List ℤ := E.alPow.getD d []

/-- `Y^n`. -/
def Yp (n : ℕ) : List ℤ × List ℤ := E.Ypow.getD n ([], [])

/-- The kernel checks of the data. -/
def ok : Bool :=
  checkK E.prec (.sub (.lin E.A) (.mul (.lin E.al) (.add (.int 1) (.mul (.lin E.al) (.lin E.cA))))) &&
  checkK E.prec (.sub (.lin E.B) (.mul (.lin E.al) (.lin E.bB))) &&
  checkK E.prec (.sub (.lin (E.alP 0)) (.int 1)) &&
  allLt (fun d => checkK E.prec (.sub (.lin (E.alP (d + 1))) (.mul (.lin (E.alP d)) (.lin E.al))))
    (E.alPow.length - 1) &&
  checkK E.prec (.sub (.lin (E.Yp 0).1) (.int 1)) && checkK E.prec (.lin (E.Yp 0).2) &&
  allLt (fun n => checkK E.prec (.sub (.lin (E.Yp (n + 1)).1) (.mul (.lin E.A) (.lin (E.Yp n).2))) &&
    checkK E.prec (.sub (.lin (E.Yp (n + 1)).2)
      (.add (.lin (E.Yp n).1) (.mul (.lin E.B) (.lin (E.Yp n).2))))) (E.Ypow.length - 1)

variable {E}

theorem ok_A (h : E.ok = true) : zkE E.A = zkE E.al * (1 + zkE E.al * zkE E.cA) := by
  simp only [ok, Bool.and_eq_true] at h
  simpa using evK_eq_of_check _ _ _ h.1.1.1.1.1.1

theorem ok_B (h : E.ok = true) : zkE E.B = zkE E.al * zkE E.bB := by
  simp only [ok, Bool.and_eq_true] at h
  simpa using evK_eq_of_check _ _ _ h.1.1.1.1.1.2

theorem ok_alP (h : E.ok = true) : ∀ d, d < E.alPow.length → zkE (E.alP d) = zkE E.al ^ d := by
  simp only [ok, Bool.and_eq_true] at h
  have h0 : zkE (E.alP 0) = 1 := by simpa using evK_eq_of_check _ _ _ h.1.1.1.1.2
  have hs := (allLt_iff _ _).mp h.1.1.1.2
  intro d hd
  induction d with
  | zero => simpa using h0
  | succ d ih =>
    have e := evK_eq_of_check _ _ _ (hs d (by omega))
    simp only [evK_lin, evK_mul] at e
    rw [e, ih (by omega), pow_succ]

theorem ok_Yp0 (h : E.ok = true) : zkE (E.Yp 0).1 = 1 ∧ zkE (E.Yp 0).2 = 0 := by
  simp only [ok, Bool.and_eq_true] at h
  exact ⟨by simpa using evK_eq_of_check _ _ _ h.1.1.2, by simpa using evK_eq_zero_of_check _ _ h.1.2⟩

theorem ok_YpS (h : E.ok = true) : ∀ n, n + 1 < E.Ypow.length →
    zkE (E.Yp (n + 1)).1 = zkE E.A * zkE (E.Yp n).2 ∧
      zkE (E.Yp (n + 1)).2 = zkE (E.Yp n).1 + zkE E.B * zkE (E.Yp n).2 := by
  simp only [ok, Bool.and_eq_true] at h
  intro n hn
  have hs := ((allLt_iff _ _).mp h.2) n (by omega)
  simp only [Bool.and_eq_true] at hs
  exact ⟨by simpa using evK_eq_of_check _ _ _ hs.1, by simpa using evK_eq_of_check _ _ _ hs.2⟩

end EisData

/-- The odd depths `2j + 1` of the basis product with bits `a` (bit `j + 1` for `1 + π^j Y`). -/
def selJ (e a : ℕ) : List ℕ := (List.range (2 * e)).filter fun j => a.testBit (j + 1)

/-- The rows of the truncated expansion of `∏_{j ∈ selJ} (1 + π^j Y)`, as zk lists. -/
def eRows (E : EisData) (D a : ℕ) : List (List ℤ) :=
  (truncT D (dpTab (selJ E.e a))).map fun r => combo r E.alPow

/-- Coordinate `i` of `Σ s_p Y^(n_p)`. -/
def lcE (E : EisData) (i : ℕ) (L : List (KE × ℕ)) : KE :=
  KE.sum (L.map fun p => .mul p.1 (.lin (if i = 0 then (E.Yp p.2).1 else (E.Yp p.2).2)))

/-- The terms of `f5 (X0 + X1 Y) Y^(a0 + n) Σ_k r_k Y^k`. -/
def lhsAux (f5 X0 X1 : KE) (a0 : ℕ) : ℕ → List (List ℤ) → List (KE × ℕ)
  | _, [] => []
  | n, r :: rs => (.mul f5 (.mul (.lin r) X0), n + a0) :: (.mul f5 (.mul (.lin r) X1), n + a0 + 1) ::
      lhsAux f5 X0 X1 a0 (n + 1) rs

/-- The terms of `X ∏ bF^a`, truncated. -/
def lhsL (E : EisData) (D : ℕ) (X0 X1 : KE) (a : ℕ) : List (KE × ℕ) :=
  lhsAux (.int (if a.testBit (2 * E.e + 1) then 5 else 1)) X0 X1 (if a.testBit 0 then 1 else 0) 0
    (eRows E D a)

/-- The terms of `al^(2 mh) Y^(2 ep) S''² + al^n0 R0 + al^n1 R1 Y`. -/
def rhsL (E : EisData) (c : WCert) : List (KE × ℕ) :=
  [(.mul (.lin (E.alP (2 * c.mh))) (.mul (.lin c.u0) (.lin c.u0)), 2 * c.ep),
    (.mul (.lin (E.alP (2 * c.mh))) (.mul (.int 2) (.mul (.lin c.u0) (.lin c.s1))), 2 * c.ep + 1),
    (.mul (.lin (E.alP (2 * c.mh))) (.mul (.lin c.s1) (.lin c.s1)), 2 * c.ep + 2),
    (.mul (.lin (E.alP c.n0)) (.lin c.R0), 0), (.mul (.lin (E.alP c.n1)) (.lin c.R1), 1)]

/-- **The certificate check** of `x = toF X0 X1` with truncation at `al^D`. -/
def certOK (E : EisData) (D : ℕ) (X0 X1 : KE) (c : WCert) : Bool :=
  decide (2 * c.mh + c.ep + 2 * E.e < c.n0) && decide (2 * c.mh + c.ep + 2 * E.e ≤ c.n1) &&
  decide (c.n0 ≤ D) && decide (D ≤ E.alPow.length) && decide (2 * c.mh < E.alPow.length) &&
  decide (c.n0 < E.alPow.length) && decide (c.n1 < E.alPow.length) &&
  decide (2 * c.ep + 2 < E.Ypow.length) && decide ((eRows E D c.a).length + 1 < E.Ypow.length) &&
  checkK c.prec (.sub (.lin c.u0) (.add (.int 1) (.mul (.lin E.al) (.lin c.c0)))) &&
  checkK c.prec (.sub (lcE E 0 (lhsL E D X0 X1 c.a)) (lcE E 0 (rhsL E c))) &&
  checkK c.prec (.sub (lcE E 1 (lhsL E D X0 X1 c.a)) (lcE E 1 (rhsL E c)))

/-! ## List lemmas -/

theorem dot_addL {R : Type*} [CommRing R] : ∀ (l m : List ℤ) (V : List R),
    dot (addL l m) V = dot l V + dot m V := by
  intro l m V
  induction' l with a l' ih generalizing m V
  · simp [addL, dot]
  · induction' m with b m' ih' generalizing V
    · simp [addL, dot]
    · cases V with
      | nil => simp [dot]
      | cons v vs =>
        simp [addL, dot, ih m' vs]
        ring

theorem dot_smulL {R : Type*} [CommRing R] (c : ℤ) : ∀ (l : List ℤ) (V : List R),
    dot (smulL c l) V = c * dot l V := by
  intro l V
  induction' l with a l' ih generalizing V
  · simp [smulL, dot]
  · cases V
    · simp [smulL, dot]
    · rename_i v V'
      simp [smulL, dot]
      have h := ih V'
      unfold smulL at h
      rw [h]
      ring

theorem dot_replicate_zero {R : Type*} [CommRing R] : ∀ (r : List ℤ) (n : ℕ),
    dot r (List.replicate n (0 : R)) = 0 := by
  intro r n
  induction r generalizing n with
  | nil => simp [dot]
  | cons c a ih =>
    cases n with
    | zero => simp [dot]
    | succ n =>
      simp only [dot, List.replicate_succ, mul_zero]
      rw [ih n]
      simp

theorem dot_combo {R : Type*} [CommRing R] : ∀ (r : List ℤ) (Ws : List (List ℤ)) (V : List R),
    dot (combo r Ws) V = dot r (Ws.map fun W => dot W V) := by
  intro r Ws V
  induction r generalizing Ws V with
  | nil =>
    simp [combo, dot]
  | cons c a ih =>
    cases Ws with
    | nil =>
      simp [combo, dot]
    | cons W Ws' =>
      cases V with
      | nil =>
        simp only [combo, dot, List.map_cons]
        simp [dot]
        rw [dot_replicate_zero a Ws'.length]
      | cons v V' =>
        simp only [combo, dot, List.map_cons]
        rw [dot_addL, dot_smulL, ih]

theorem zkE_combo (r : List ℤ) (Ws : List (List ℤ)) : zkE (combo r Ws) = dot r (Ws.map zkE) := by
  rw [zkE_eq_dot, dot_combo]
  congr 1
  simp only [List.map_inj_left]
  intro W _
  rw [zkE_eq_dot]

/-- `dot r V = x^k Σ r_d x^d` when `V_d = x^(k + d)` on the length of `r`. -/
theorem dot_eq_evRow {R : Type*} [CommRing R] (x : R) : ∀ (r : List ℤ) (V : List R) (k : ℕ),
    r.length ≤ V.length → (∀ d < r.length, V.getD d 0 = x ^ (k + d)) → dot r V = x ^ k * evRow x r := by
  intro r V k hlen hV
  induction r generalizing V k with
  | nil =>
      simp [dot, evRow]
  | cons c rs ih =>
      match V with
      | [] =>
          simp at hlen
      | v :: vs =>
          simp [dot, evRow]
          have hv : v = x ^ k := by
            have h0 := hV 0 (by simp)
            simpa using h0
          have hlen' : rs.length ≤ vs.length := by
            simpa using hlen
          have hV' : ∀ d < rs.length, vs.getD d 0 = x ^ ((k + 1) + d) := by
            intro d hd
            have hd' : d + 1 < (c :: rs).length := by
              have hlen_r : (c :: rs).length = rs.length + 1 := by simp
              rw [hlen_r]
              omega
            have h := hV (d + 1) hd'
            simpa [add_comm, add_left_comm, add_assoc] using h
          rw [hv, ih vs (k + 1) hlen' hV']
          ring

theorem map_evRow {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (t : R) :
    ∀ r : List ℤ, φ (evRow t r) = evRow (φ t) r := by
  intro r
  induction r with
  | nil => simp [evRow]
  | cons c r ih => simp [evRow, ih]

theorem length_addT (a b : List (List ℤ)) : (addT a b).length = max a.length b.length := by
  induction' a with r a ih generalizing b
  · simp [addT]
  · cases b with
    | nil => simp [addT]
    | cons r' b' =>
      simp [addT, ih, Nat.succ_max_succ]

theorem length_dpStep (j : ℕ) (c : List (List ℤ)) : (dpStep j c).length = c.length + 1 := by
  simp [dpStep, length_addT, List.length_map]

theorem length_dpTab (S : List ℕ) : (dpTab S).length = S.length + 1 := by
  induction' S with j S ih
  · simp [dpTab]
  · dsimp [dpTab] at ih ⊢
    simp [length_dpStep, ih]

theorem length_truncT_row (D : ℕ) (c : List (List ℤ)) : ∀ r ∈ truncT D c, r.length ≤ D := by
  intro r hr
  simp only [truncT, List.mem_map] at hr
  obtain ⟨r', _, rfl⟩ := hr
  exact List.length_take_le _ _

/-- A product over `Fin n` with bit exponents is the product over the selected indices. -/
theorem prod_fin_bits {M : Type*} [CommMonoid M] (g : ℕ → M) (b : ℕ → Bool) : ∀ n : ℕ,
    ∏ j : Fin n, g j ^ (if b j then 1 else 0) = (((List.range n).filter b).map g).prod := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      simp_rw [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      rw [List.range_succ, List.filter_append, List.map_append, List.prod_append]
      have h_last_list : ((List.filter b [n]).map g).prod = if b n then g n else 1 := by
        cases hb : b n
        · simp [hb]
        · simp [hb]
      rw [h_last_list]
      by_cases hb : b n
      · simp [hb]
      · simp [hb]

/-! ## Norms of kernel expressions -/

section Norm

variable {Kw : Type*} [NontriviallyNormedField Kw] [IsUltrametricDist Kw]

/-- Every `evK e` is integral when every `zkE a` is. -/
theorem norm_evK_le_one (σ : K21 →+* Kw) (hint : ∀ a : List ℤ, ‖σ (zkE a)‖ ≤ 1) :
    ∀ e : KE, ‖σ (evK e)‖ ≤ 1
  | .lin a => by simpa using hint a
  | .int m => by
    rw [evK_int, map_intCast]; exact IsUltrametricDist.norm_intCast_le_one Kw m
  | .add e f => by
    rw [evK_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (norm_evK_le_one σ hint e) (norm_evK_le_one σ hint f))
  | .sub e f => by
    rw [evK_sub, map_sub, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_evK_le_one σ hint e) ?_)
    rw [norm_neg]; exact norm_evK_le_one σ hint f
  | .mul e f => by
    rw [evK_mul, map_mul, norm_mul]
    calc ‖σ (evK e)‖ * ‖σ (evK f)‖ ≤ 1 * 1 :=
          mul_le_mul (norm_evK_le_one σ hint e) (norm_evK_le_one σ hint f) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- `‖x - y‖ < ‖y‖` gives `‖x^j - y^j‖ < ‖y‖^j` for `j ≥ 1`. -/
theorem norm_pow_sub_pow_lt {F : Type*} [NormedField F] [IsUltrametricDist F] {x y : F}
    (h : ‖x - y‖ < ‖y‖) {j : ℕ} (hj : 0 < j) : ‖x ^ j - y ^ j‖ < ‖y‖ ^ j := by
  have hy_pos : 0 < ‖y‖ := by
    have h' : 0 ≤ ‖x - y‖ := norm_nonneg _
    linarith
  have hy_nonneg : 0 ≤ ‖y‖ := le_of_lt hy_pos
  have hna : IsNonarchimedean (‖·‖ : F → ℝ) := IsUltrametricDist.isNonarchimedean_norm
  have hx_le_y : ‖x‖ ≤ ‖y‖ := by
    have hmax := IsUltrametricDist.norm_add_le_max (x - y) y
    rw [sub_add_cancel] at hmax
    have hmax' : max ‖x - y‖ ‖y‖ = ‖y‖ := max_eq_right (le_of_lt h)
    rw [hmax'] at hmax
    exact hmax
  have hsum_nonempty : (Finset.range j).Nonempty := by
    rw [Finset.nonempty_range_iff]
    exact Nat.ne_of_gt hj
  have h_factor : (∑ i ∈ Finset.range j, x ^ i * y ^ (j - 1 - i)) * (x - y) = x ^ j - y ^ j :=
    geom_sum₂_mul x y j
  have h_norm_factor : ‖x ^ j - y ^ j‖ = ‖∑ i ∈ Finset.range j, x ^ i * y ^ (j - 1 - i)‖ * ‖x - y‖ := by
    rw [← h_factor, norm_mul]
  have h_pow_le : ∀ (a b : ℝ), 0 ≤ a → a ≤ b → ∀ (n : ℕ), a ^ n ≤ b ^ n := by
    intro a b ha hab n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ]
      have hb' : 0 ≤ b ^ n := pow_nonneg (ha.trans hab) n
      exact mul_le_mul ih hab ha hb'
  have h_sum_le : ‖∑ i ∈ Finset.range j, x ^ i * y ^ (j - 1 - i)‖ ≤ ‖y‖ ^ (j - 1) := by
    refine le_trans (hna.apply_sum_le_sup hsum_nonempty) ?_
    refine (Finset.sup'_le_iff _ _).mpr fun i hi => ?_
    rw [norm_mul, norm_pow, norm_pow]
    have hi_range : i < j := Finset.mem_range.1 hi
    have hx_pow_le : ‖x‖ ^ i ≤ ‖y‖ ^ i := h_pow_le _ _ (norm_nonneg _) hx_le_y i
    refine le_trans (mul_le_mul_of_nonneg_right hx_pow_le (pow_nonneg hy_nonneg _)) ?_
    have h_eq : ‖y‖ ^ i * ‖y‖ ^ (j - 1 - i) = ‖y‖ ^ (j - 1) := by
      rw [← pow_add]
      congr 1
      rw [Nat.add_sub_cancel' (Nat.le_sub_one_of_lt hi_range)]
    rw [h_eq]
  calc
    ‖x ^ j - y ^ j‖ = ‖∑ i ∈ Finset.range j, x ^ i * y ^ (j - 1 - i)‖ * ‖x - y‖ := h_norm_factor
    _ ≤ ‖y‖ ^ (j - 1) * ‖x - y‖ := mul_le_mul_of_nonneg_right h_sum_le (norm_nonneg _)
    _ < ‖y‖ ^ (j - 1) * ‖y‖ := mul_lt_mul_of_pos_left h (pow_pos hy_pos (j - 1))
    _ = ‖y‖ ^ j := by rw [← pow_succ, Nat.sub_add_cancel hj]

end Norm

/-! ## Generic leaves (quadratic fields, bit products, the depth of `1 + t^j Y`) -/

/-- `x + y Y` in `QF`. -/
theorem qf_mk_eq {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)] (x y : K) :
    QF.mk K A B x y = algebraMap K (QF K A B) x + algebraMap K (QF K A B) y * QF.mk K A B 0 1 := by
  have h : (QuadraticAlgebra.mk x y : QuadraticAlgebra K A B) = (algebraMap K (QuadraticAlgebra K A B)) x + (algebraMap K (QuadraticAlgebra K A B)) y * (QuadraticAlgebra.mk 0 1) := by
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.algebraMap_eq]
  dsimp [QF, QF.mk]
  exact h

/-- `Y² = A + B Y` in `QF`. -/
theorem qf_Y_sq {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)] :
    QF.mk K A B 0 1 ^ 2 = algebraMap K (QF K A B) A + algebraMap K (QF K A B) B * QF.mk K A B 0 1 := by
  show (QuadraticAlgebra.mk (0 : K) (1 : K) : QuadraticAlgebra K A B)^2 =
    (algebraMap K (QuadraticAlgebra K A B)) A +
    (algebraMap K (QuadraticAlgebra K A B)) B *
    (QuadraticAlgebra.mk (0 : K) (1 : K) : QuadraticAlgebra K A B)
  calc
    (QuadraticAlgebra.mk (0 : K) (1 : K) : QuadraticAlgebra K A B)^2 =
        (QuadraticAlgebra.mk A B : QuadraticAlgebra K A B) := by
      rw [pow_two]
      simp [QuadraticAlgebra.mk_mul_mk]
    _ = (QuadraticAlgebra.mk A 0 : QuadraticAlgebra K A B) +
        (QuadraticAlgebra.mk (0 : K) B : QuadraticAlgebra K A B) := by
      ext <;> simp
    _ = (algebraMap K (QuadraticAlgebra K A B)) A +
        (algebraMap K (QuadraticAlgebra K A B)) B *
        (QuadraticAlgebra.mk (0 : K) (1 : K) : QuadraticAlgebra K A B) := by
      simp [QuadraticAlgebra.algebraMap_eq, QuadraticAlgebra.mk_mul_mk]

/-- The powers of `Y` from the recurrence of their coordinates. -/
theorem qf_pow_of_rec {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {A B : K} [Fact (∀ r : K, r ^ 2 ≠ A + B * r)] (u v : ℕ → K) (h0 : u 0 = 1) (h0' : v 0 = 0)
    (N : ℕ) (hs : ∀ n, n + 1 < N → u (n + 1) = A * v n ∧ v (n + 1) = u n + B * v n) :
    ∀ n, n < N → QF.mk K A B (u n) (v n) = QF.mk K A B 0 1 ^ n := by
  intro n hn
  induction' n with k ih
  · -- n = 0
    rw [h0, h0', pow_zero]
    rfl
  · -- n = k+1
    have hk : k < N := Nat.lt_of_succ_lt hn
    rcases hs k hn with ⟨hu, hv⟩
    rw [pow_succ, ← ih hk, hu, hv]
    have h_mul : QF.mk K A B (u k) (v k) * QF.mk K A B 0 1 =
                (QuadraticAlgebra.mk (u k) (v k)) * (QuadraticAlgebra.mk 0 1) := rfl
    rw [h_mul]
    dsimp [QF, QF.mk] at *
    apply QuadraticAlgebra.ext
    · simp
    · simp

theorem pbb_prod_fin_eq_list_prod {M : Type*} [CommMonoid M] (n : ℕ) (g : ℕ → M) (a : ℕ) :
    (∏ i : Fin n, (if a.testBit ((i : ℕ) + 1) then g (i : ℕ) else 1)) =
    (((List.range n).filter fun j => a.testBit (j + 1)).map g).prod := by
  induction' n with n ih
  · simp
  · rw [Fin.prod_univ_castSucc]
    have h_prod : (∏ i : Fin n, (if a.testBit ((Fin.castSucc i : ℕ) + 1) then g (Fin.castSucc i : ℕ) else 1)) =
        (∏ i : Fin n, (if a.testBit ((i : ℕ) + 1) then g (i : ℕ) else 1)) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      simp
    rw [h_prod]
    rw [ih]
    rw [List.range_succ, List.filter_append, List.map_append, List.prod_append]
    by_cases h : a.testBit (n + 1)
    · simp [h]
    · simp [h]

/-- The basis product with bits `a`: `y` at bit `0`, `g j` at bit `j + 1` (`j < n`), `f` at bit `n + 1`. -/
theorem prod_bits_basis {M : Type*} [CommMonoid M] (n : ℕ) (y f : M) (g : ℕ → M) (a : ℕ) :
    ∏ i : Fin (n + 2), (if (i : ℕ) = 0 then y else if (i : ℕ) = n + 1 then f else g ((i : ℕ) - 1)) ^
        (bitv (n + 2) a i).val =
      y ^ (if a.testBit 0 then 1 else 0) *
        (((List.range n).filter fun j => a.testBit (j + 1)).map g).prod *
          f ^ (if a.testBit (n + 1) then 1 else 0) := by
  -- Simplify the bitv exponent
  have hbitv_val (i : Fin (n+2)) : (bitv (n+2) a i).val = if a.testBit (i : ℕ) then (1 : ℕ) else 0 := by
    unfold bitv; split <;> decide
  simp_rw [hbitv_val]
  -- Split at i=0
  rw [Fin.prod_univ_succ]
  -- Simplify the i=0 factor
  have h0 : (if ((0 : Fin (n+2)) : ℕ) = 0 then y else if ((0 : Fin (n+2)) : ℕ) = n + 1 then f else g (((0 : Fin (n+2)) : ℕ) - 1)) ^ (if a.testBit ((0 : Fin (n+2)) : ℕ) then (1 : ℕ) else 0) = y ^ (if a.testBit 0 then 1 else 0) := by
    simp
  rw [h0]
  -- Split inner at i=n+1
  rw [Fin.prod_univ_castSucc]
  -- Simplify the last factor (i = Fin.succ (Fin.last n) = n+1)
  have hlast : (if ((Fin.succ (Fin.last n) : Fin (n+2)) : ℕ) = 0 then y else if ((Fin.succ (Fin.last n) : Fin (n+2)) : ℕ) = n + 1 then f else g (((Fin.succ (Fin.last n) : Fin (n+2)) : ℕ) - 1)) ^ (if a.testBit ((Fin.succ (Fin.last n) : Fin (n+2)) : ℕ) then (1 : ℕ) else 0) = f ^ (if a.testBit (n+1) then 1 else 0) := by
    simp
  rw [hlast]
  -- Simplify the middle product
  have hmid_base (i : Fin n) : (if ((Fin.succ (Fin.castSucc i) : Fin (n+2)) : ℕ) = 0 then y else if ((Fin.succ (Fin.castSucc i) : Fin (n+2)) : ℕ) = n + 1 then f else g (((Fin.succ (Fin.castSucc i) : Fin (n+2)) : ℕ) - 1)) = g (i : ℕ) := by
    have hval : ((Fin.succ (Fin.castSucc i) : Fin (n+2)) : ℕ) = (i : ℕ) + 1 := by simp
    have hne0' : (i : ℕ) + 1 ≠ 0 := by omega
    have hnen1' : (i : ℕ) + 1 ≠ n + 1 := by
      have hi : (i : ℕ) < n := i.2
      omega
    rw [hval]
    rw [if_neg hne0', if_neg hnen1']
    simp
  have hmid_exp (i : Fin n) : (if a.testBit ((Fin.succ (Fin.castSucc i) : Fin (n+2)) : ℕ) then (1 : ℕ) else 0) = (if a.testBit ((i : ℕ) + 1) then 1 else 0) := by
    simp
  have hmid_prod : (∏ i : Fin n, (if ((Fin.succ (Fin.castSucc i) : Fin (n+2)) : ℕ) = 0 then y else if ((Fin.succ (Fin.castSucc i) : Fin (n+2)) : ℕ) = n + 1 then f else g (((Fin.succ (Fin.castSucc i) : Fin (n+2)) : ℕ) - 1)) ^ (if a.testBit ((Fin.succ (Fin.castSucc i) : Fin (n+2)) : ℕ) then (1 : ℕ) else 0)) = (∏ i : Fin n, g (i : ℕ) ^ (if a.testBit ((i : ℕ) + 1) then (1 : ℕ) else 0)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hmid_base i, hmid_exp i]
  rw [hmid_prod]
  -- Simplify x^(if P then 1 else 0) = (if P then x else 1)
  have h_pow (b : M) (p : Prop) [Decidable p] : b ^ (if p then (1 : ℕ) else 0) = (if p then b else 1) := by
    split <;> simp
  simp_rw [h_pow]
  -- Now: y^(bit0) * (∏ i : Fin n, (if a.testBit ((i : ℕ) + 1) then g (i : ℕ) else 1)) * f^(bit(n+1)) = y^(bit0) * (((List.range n).filter fun j => a.testBit (j+1)).map g).prod * f^(bit(n+1))
  rw [pbb_prod_fin_eq_list_prod n g a]
  rw [mul_assoc]

/-- A family placed at the components of a product (index `i + n j` for element `i` at component `j`):
component `j` of a bit product is the bit product of the slice of bits `n j, ..., n j + n - 1`. -/
theorem prod_mulSingle_bits {M : Type*} [CommGroup M] {m n : ℕ} (g : Fin n → M) (A : ℕ) (j : Fin m) :
    (∏ l : Fin (m * n), (Pi.mulSingle (finProdFinEquiv.symm l).1 (g (finProdFinEquiv.symm l).2) :
        Fin m → M) ^ (bitv (m * n) A l).val) j =
      ∏ i : Fin n, g i ^ (bitv n (A >>> (n * (j : ℕ))) i).val := by
  simp
  simp only [Pi.mulSingle_apply]
  set f := (fun (x : Fin (m * n)) => (if j = x.divNat then g x.modNat else 1) ^ (bitv (m * n) A x).val) with hf
  set g' := (fun (p : Fin m × Fin n) => (if j = p.1 then g p.2 else 1) ^ (bitv (m * n) A (finProdFinEquiv p)).val) with hg'
  have h_eq : ∀ x : Fin (m * n), f x = g' (finProdFinEquiv.symm x) := by
    intro x
    dsimp [f, g']
    rw [finProdFinEquiv_symm_apply]
    have hx : finProdFinEquiv (x.divNat, x.modNat) = x := by
      rw [← finProdFinEquiv_symm_apply x, Equiv.apply_symm_apply]
    simp [hx]
  rw [Fintype.prod_equiv finProdFinEquiv.symm f g' h_eq]
  rw [Fintype.prod_prod_type]
  have h_g'_ne : ∀ (a : Fin m), a ≠ j → ∀ (b : Fin n), g' (a, b) = 1 := by
    intro a ha_ne b
    dsimp [g']
    by_cases h_eq_ab : j = a
    · exfalso; exact ha_ne h_eq_ab.symm
    · simp [h_eq_ab]
  have h_g'_j : ∀ (b : Fin n), g' (j, b) = g b ^ (bitv n (A >>> (n * (j : ℕ))) b).val := by
    intro b
    dsimp [g']
    simp
    congr 1
    simp [bitv, finProdFinEquiv, Nat.testBit_shiftRight, add_comm]
    rfl
  rw [Finset.prod_eq_single j (fun a _ ha_ne => ?_) (fun hj => ?_)]
  · simp [h_g'_j]
  · simp [h_g'_ne a ha_ne]
  · exfalso; exact hj (Finset.mem_univ j)

/-- **The depth of `1 + t^j Y`**: with `‖t‖ = ‖Y‖²` and `‖Y² - t‖ < ‖t‖`, the unit `1 + t^j Y` has the
datum of the standard unit `1 + Y^(2j+1)` at a component with residue field `𝔽₂`. -/
theorem dfact_odd_near {F : Type*} [NormedField F] [IsUltrametricDist F] (E N : ℕ) {Y t : F}
    (hY0 : Y ≠ 0) (hY1 : ‖Y‖ < 1) (htY : ‖t‖ = ‖Y‖ ^ 2) (ht : ‖Y ^ 2 - t‖ < ‖t‖) (j : ℕ) :
    DFact ⟨E, 1, 1, N⟩ Y ![1] (1 + t ^ j * Y) 1 0 (.odd (2 * j + 1) 1) := by
  have hYpos : 0 < ‖Y‖ := norm_pos_iff.mpr hY0
  have hnormYsq : ‖Y ^ 2‖ = ‖Y‖ ^ 2 := by
    simpa [pow_two] using norm_mul Y Y
  have hnormYsq_eq_t : ‖Y ^ 2‖ = ‖t‖ := by
    have hle : ‖Y ^ 2‖ ≤ ‖t‖ := by
      calc
        ‖Y ^ 2‖ = ‖(Y ^ 2 - t) + t‖ := by ring_nf
        _ ≤ max ‖Y ^ 2 - t‖ ‖t‖ := IsUltrametricDist.norm_add_le_max _ _
        _ = ‖t‖ := max_eq_right (by linarith)
    have hge : ‖t‖ ≤ ‖Y ^ 2‖ := by
      by_contra! hlt
      have hmax : max ‖t - Y ^ 2‖ ‖Y ^ 2‖ < ‖t‖ := by
        refine max_lt ?_ hlt
        -- ht: ‖Y^2 - t‖ < ‖t‖, need ‖t - Y^2‖ < ‖t‖
        have : ‖t - Y ^ 2‖ = ‖Y ^ 2 - t‖ := by rw [← norm_neg, neg_sub]
        rw [this]
        exact ht
      have hle' : ‖t‖ ≤ max ‖t - Y ^ 2‖ ‖Y ^ 2‖ := by
        calc
          ‖t‖ = ‖(t - Y ^ 2) + Y ^ 2‖ := by ring_nf
          _ ≤ max ‖t - Y ^ 2‖ ‖Y ^ 2‖ := IsUltrametricDist.norm_add_le_max _ _
      linarith
    exact le_antisymm hle hge
  have hnorm_tjY : ‖t ^ j * Y‖ = ‖Y‖ ^ (2 * j + 1) := by
    calc
      ‖t ^ j * Y‖ = ‖t ^ j‖ * ‖Y‖ := norm_mul _ _
      _ = ‖t‖ ^ j * ‖Y‖ := by rw [norm_pow]
      _ = (‖Y‖ ^ 2) ^ j * ‖Y‖ := by rw [htY]
      _ = ‖Y‖ ^ (2 * j) * ‖Y‖ := by rw [pow_mul]
      _ = ‖Y‖ ^ (2 * j + 1) := by rw [pow_succ', mul_comm]
  have hlt_one : ‖t ^ j * Y‖ < 1 := by
    rw [hnorm_tjY]
    refine pow_lt_one₀ (norm_nonneg _) hY1 (by omega)
  have hne : ‖(1 : F)‖ ≠ ‖t ^ j * Y‖ := by
    rw [norm_one]
    exact (ne_of_lt hlt_one).symm
  have hfirst : ‖(1 : F) + t ^ j * Y‖ = ‖Y‖ ^ (0 : ℤ) := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, hnorm_tjY]
    exact max_eq_left (by linarith)
  have hlift : liftW ![1] (1 : ℕ) = (1 : F) := by
    simp [liftW, bitv, ZMod.val_one]
  have hsecond : ‖(1 + t ^ j * Y) / (1 : F) ^ 2 - 1 - Y ^ (2 * j + 1) * liftW ![1] (1 : ℕ)‖ < ‖Y‖ ^ (2 * j + 1) := by
    rw [hlift]
    simp [div_one, one_pow]
    have h_eq : t ^ j * Y - Y ^ (2 * j + 1) = Y * (t ^ j - (Y ^ 2) ^ j) := by
      ring
    rw [h_eq, norm_mul]
    rcases eq_or_ne j 0 with rfl | hj
    · -- j = 0: t^0 * Y - Y^1 = 0, goal is 0 < ‖Y‖^1
      simpa using hYpos
    · -- j ≥ 1
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj
      have h_factor : t ^ j - (Y ^ 2) ^ j = (t - Y ^ 2) * (∑ i ∈ Finset.range j, t ^ i * (Y ^ 2) ^ (j - 1 - i)) := by
        have := geom_sum₂_mul t (Y ^ 2) j
        rw [mul_comm] at this
        rw [← this, mul_comm]
      rw [h_factor, norm_mul]
      -- Goal: ‖Y‖ * (‖t - Y ^ 2‖ * ‖∑ i, t ^ i * (Y ^ 2) ^ (j - 1 - i)‖) < ‖Y‖ ^ (2 * j + 1)
      have hsum_bound : ‖∑ i ∈ Finset.range j, t ^ i * (Y ^ 2) ^ (j - 1 - i)‖ ≤ ‖t‖ ^ (j - 1) := by
        have h_nonempty : (Finset.range j).Nonempty := by
          rwa [Finset.nonempty_range_iff]
        have h_each (i : ℕ) (hi : i ∈ Finset.range j) : ‖t ^ i * (Y ^ 2) ^ (j - 1 - i)‖ ≤ ‖t‖ ^ (j - 1) := by
          have hi' : i < j := Finset.mem_range.1 hi
          have h_eq : ‖t ^ i * (Y ^ 2) ^ (j - 1 - i)‖ = ‖t‖ ^ (j - 1) := by
            calc
              ‖t ^ i * (Y ^ 2) ^ (j - 1 - i)‖ = ‖t ^ i‖ * ‖(Y ^ 2) ^ (j - 1 - i)‖ := norm_mul _ _
              _ = ‖t‖ ^ i * ‖Y ^ 2‖ ^ (j - 1 - i) := by simp [norm_pow]
              _ = ‖t‖ ^ i * ‖t‖ ^ (j - 1 - i) := by rw [hnormYsq_eq_t]
              _ = ‖t‖ ^ (i + (j - 1 - i)) := by rw [pow_add]
              _ = ‖t‖ ^ (j - 1) := by
                rw [Nat.add_sub_cancel' (Nat.le_sub_one_of_lt hi')]
          exact h_eq.le
        -- Now use the ultrametric sum bound
        refine le_trans (h_nonempty.norm_sum_le_sup'_norm _) ?_
        apply Finset.sup'_le h_nonempty
        intro i hi
        exact h_each i hi
      have h_norm_tsub : ‖t - Y ^ 2‖ < ‖t‖ := by
        -- ‖t - Y^2‖ = ‖-(Y^2 - t)‖ = ‖Y^2 - t‖
        have : ‖t - Y ^ 2‖ = ‖Y ^ 2 - t‖ := by rw [← norm_neg, neg_sub]
        rw [this]
        exact ht
      -- Now combine: ‖Y‖ * (‖t - Y^2‖ * ‖∑ ...‖) < ‖Y‖ * (‖t‖ * ‖t‖^(j-1))
      -- = ‖Y‖ * ‖t‖^j = ‖Y‖ * (‖Y‖^2)^j = ‖Y‖^(2j+1)
      have h_nonneg_Y : 0 ≤ ‖Y‖ := norm_nonneg _
      have h_nonneg_t_pow : 0 ≤ ‖t‖ ^ (j - 1) := pow_nonneg (norm_nonneg _) _
      have h_mul_nonneg : 0 ≤ ‖Y‖ * ‖t‖ ^ (j - 1) := mul_nonneg h_nonneg_Y h_nonneg_t_pow
      have h_first : ‖Y‖ * (‖t - Y ^ 2‖ * ‖∑ i ∈ Finset.range j, t ^ i * (Y ^ 2) ^ (j - 1 - i)‖) ≤
          ‖Y‖ * (‖t - Y ^ 2‖ * ‖t‖ ^ (j - 1)) := by
        gcongr
      have ht_pos : 0 < ‖t‖ := by
        rw [htY]
        exact pow_pos hYpos 2
      have ht_pow_pos : 0 < ‖t‖ ^ (j - 1) := pow_pos ht_pos _
      have h_inner : ‖t - Y ^ 2‖ * ‖t‖ ^ (j - 1) < ‖t‖ * ‖t‖ ^ (j - 1) :=
        mul_lt_mul_of_pos_right h_norm_tsub ht_pow_pos
      have h_second : ‖Y‖ * (‖t - Y ^ 2‖ * ‖t‖ ^ (j - 1)) < ‖Y‖ * (‖t‖ * ‖t‖ ^ (j - 1)) :=
        mul_lt_mul_of_pos_left h_inner hYpos
      have h_third : ‖Y‖ * (‖t‖ * ‖t‖ ^ (j - 1)) = ‖Y‖ * (‖t‖ ^ j) := by
        rw [← pow_succ', Nat.sub_add_cancel hjpos]
      calc
        ‖Y‖ * (‖t - Y ^ 2‖ * ‖∑ i ∈ Finset.range j, t ^ i * (Y ^ 2) ^ (j - 1 - i)‖)
            ≤ ‖Y‖ * (‖t - Y ^ 2‖ * ‖t‖ ^ (j - 1)) := h_first
        _ < ‖Y‖ * (‖t‖ * ‖t‖ ^ (j - 1)) := h_second
        _ = ‖Y‖ * (‖t‖ ^ j) := h_third
        _ = ‖Y‖ * (‖Y‖ ^ 2) ^ j := by rw [htY]
        _ = ‖Y‖ * ‖Y‖ ^ (2 * j) := by rw [← pow_mul, mul_comm 2 j]
        _ = ‖Y‖ ^ (2 * j + 1) := by rw [pow_succ', mul_comm]
  exact And.intro hfirst hsecond

/-! ## The place and the component -/

section Place

variable {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw]

/-- The facts about a place `σ` used by the certificates. -/
structure WPlace (σ : K21 →+* Kw) (E : EisData) : Prop where
  int : ∀ a : List ℤ, ‖σ (zkE a)‖ ≤ 1
  unif : NormUnif (σ (zkE E.al))
  two : ‖(2 : Kw)‖ = ‖σ (zkE E.al)‖ ^ E.e
  res : ∀ y : Kw, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1
  ok : E.ok = true

variable {σ : K21 →+* Kw} {E : EisData}

theorem WPlace.norm_A (hW : WPlace σ E) : ‖σ (zkE E.A)‖ = ‖σ (zkE E.al)‖ := by
  rw [EisData.ok_A hW.ok, map_mul, norm_mul]
  have h1 : ‖σ (zkE E.al * zkE E.cA)‖ < 1 := by
    rw [map_mul, norm_mul]
    calc ‖σ (zkE E.al)‖ * ‖σ (zkE E.cA)‖ ≤ ‖σ (zkE E.al)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hW.int _) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hW.unif.norm_lt_one
  have h2 : ‖σ (1 + zkE E.al * zkE E.cA)‖ = 1 := by
    rw [map_add, map_one, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_one]; exact h1.ne'), norm_one, max_eq_left h1.le]
  rw [h2, mul_one]

theorem WPlace.norm_B_le (hW : WPlace σ E) : ‖σ (zkE E.B)‖ ≤ ‖σ (zkE E.al)‖ := by
  rw [EisData.ok_B hW.ok, map_mul, norm_mul]
  calc ‖σ (zkE E.al)‖ * ‖σ (zkE E.bB)‖ ≤ ‖σ (zkE E.al)‖ * 1 :=
        mul_le_mul_of_nonneg_left (hW.int _) (norm_nonneg _)
    _ = _ := mul_one _

theorem WPlace.norm_B (hW : WPlace σ E) : ‖σ (zkE E.B)‖ < 1 :=
  lt_of_le_of_lt hW.norm_B_le hW.unif.norm_lt_one

theorem WPlace.noRoot (hW : WPlace σ E) : ∀ r : Kw, r ^ 2 ≠ σ (zkE E.A) + σ (zkE E.B) * r :=
  no_root_eisen hW.unif hW.norm_A hW.norm_B

variable (σ E)

/-- The component field. -/
abbrev CF [Fact (∀ r : Kw, r ^ 2 ≠ σ (zkE E.A) + σ (zkE E.B) * r)] : Type _ :=
  QF Kw (σ (zkE E.A)) (σ (zkE E.B))

variable [Fact (∀ r : Kw, r ^ 2 ≠ σ (zkE E.A) + σ (zkE E.B) * r)]

/-- The uniformizer `Y` of the component. -/
noncomputable def cY : CF σ E := QF.mk Kw _ _ 0 1

/-- `σ u + σ v Y`. -/
noncomputable def toF (u v : K21) : CF σ E := QF.mk Kw _ _ (σ u) (σ v)

/-- `π` in the component. -/
noncomputable def tC : CF σ E := algebraMap Kw (CF σ E) (σ (zkE E.al))

/-- The standard basis: `Y`, `1 + π^(i-1) Y` for `1 ≤ i ≤ 2e`, `5`. -/
noncomputable def bF (i : ℕ) : CF σ E :=
  if i = 0 then cY σ E else if i = 2 * E.e + 1 then 5 else 1 + tC σ E ^ (i - 1) * cY σ E

/-- The basis product with bits `a`. -/
noncomputable def Ba (a : ℕ) : CF σ E :=
  ∏ i : Fin (2 * E.e + 2), bF σ E i ^ (bitv (2 * E.e + 2) a i).val

variable {σ E}

theorem toF_eq (u v : K21) :
    toF σ E u v = algebraMap Kw (CF σ E) (σ u) + algebraMap Kw (CF σ E) (σ v) * cY σ E :=
  qf_mk_eq _ _

theorem cY_sq : cY σ E ^ 2 = algebraMap Kw (CF σ E) (σ (zkE E.A)) +
    algebraMap Kw (CF σ E) (σ (zkE E.B)) * cY σ E :=
  qf_Y_sq

theorem toF_add (u v u' v' : K21) : toF σ E (u + u') (v + v') = toF σ E u v + toF σ E u' v' := by
  rw [toF_eq, toF_eq, toF_eq, map_add, map_add, map_add, map_add]; ring

theorem toF_smul (s u v : K21) :
    toF σ E (s * u) (s * v) = algebraMap Kw (CF σ E) (σ s) * toF σ E u v := by
  rw [toF_eq, toF_eq, map_mul, map_mul, map_mul, map_mul]; ring

theorem toF_Yp (hW : WPlace σ E) : ∀ n, n < E.Ypow.length →
    toF σ E (zkE (E.Yp n).1) (zkE (E.Yp n).2) = cY σ E ^ n := by
  have h0 := EisData.ok_Yp0 hW.ok
  refine qf_pow_of_rec (fun n => σ (zkE (E.Yp n).1)) (fun n => σ (zkE (E.Yp n).2))
    (by simp [h0.1]) (by simp [h0.2]) _ fun n hn => ?_
  have h := EisData.ok_YpS hW.ok n hn
  exact ⟨by simp only [h.1, map_mul], by simp only [h.2, map_add, map_mul]⟩

theorem algebraMap_alP (hW : WPlace σ E) {d : ℕ} (hd : d < E.alPow.length) :
    algebraMap Kw (CF σ E) (σ (zkE (E.alP d))) = tC σ E ^ d := by
  rw [EisData.ok_alP hW.ok d hd, map_pow, map_pow]; rfl

/-! ## The sum of a list of terms -/

theorem evK_lcE (i : ℕ) (L : List (KE × ℕ)) : evK (lcE E i L) =
    (L.map fun p => evK p.1 * zkE (if i = 0 then (E.Yp p.2).1 else (E.Yp p.2).2)).sum := by
  rw [lcE, evK_sum, List.map_map]
  rfl

theorem evK_lcE0 (L : List (KE × ℕ)) :
    evK (lcE E 0 L) = (L.map fun p => evK p.1 * zkE (E.Yp p.2).1).sum := by
  rw [evK_lcE]; rfl

theorem evK_lcE1 (L : List (KE × ℕ)) :
    evK (lcE E 1 L) = (L.map fun p => evK p.1 * zkE (E.Yp p.2).2).sum := by
  rw [evK_lcE]; rfl

/-- **The value of a list of terms** `Σ s_p Y^(n_p)` from its two coordinates. -/
theorem toF_lcE (hW : WPlace σ E) (L : List (KE × ℕ)) (hL : ∀ p ∈ L, p.2 < E.Ypow.length) :
    toF σ E (evK (lcE E 0 L)) (evK (lcE E 1 L)) =
      (L.map fun p => algebraMap Kw (CF σ E) (σ (evK p.1)) * cY σ E ^ p.2).sum := by
  rw [evK_lcE0, evK_lcE1]
  induction L with
  | nil => simp [toF_eq]
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [toF_add, ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)), toF_smul,
      toF_Yp hW _ (hL p List.mem_cons_self)]

/-- The Horner value `Σ_k σ(r_k) Y^k` of a list of zk rows. -/
noncomputable def rowsVal (rs : List (List ℤ)) : CF σ E :=
  rs.foldr (fun r acc => algebraMap Kw (CF σ E) (σ (zkE r)) + cY σ E * acc) 0

theorem sum_lhsAux (f5 X0 X1 : KE) (a0 : ℕ) : ∀ (n : ℕ) (rs : List (List ℤ)),
    ((lhsAux f5 X0 X1 a0 n rs).map fun p => algebraMap Kw (CF σ E) (σ (evK p.1)) * cY σ E ^ p.2).sum =
      algebraMap Kw (CF σ E) (σ (evK f5)) * toF σ E (evK X0) (evK X1) * cY σ E ^ (n + a0) *
        rowsVal (σ := σ) (E := E) rs
  | n, [] => by simp [lhsAux, rowsVal]
  | n, r :: rs => by
    simp only [lhsAux, List.map_cons, List.sum_cons, sum_lhsAux f5 X0 X1 a0 (n + 1) rs]
    simp only [rowsVal, List.foldr_cons, evK_mul, evK_lin, map_mul, toF_eq]
    ring

theorem algebraMap_combo (hW : WPlace σ E) {r : List ℤ} (hr : r.length ≤ E.alPow.length) :
    algebraMap Kw (CF σ E) (σ (zkE (combo r E.alPow))) = evRow (tC σ E) r := by
  have h : zkE (combo r E.alPow) = evRow (zkE E.al) r := by
    rw [zkE_combo, dot_eq_evRow (zkE E.al) r _ 0 (by simpa using hr), pow_zero, one_mul]
    intro d hd
    have hd' : d < E.alPow.length := lt_of_lt_of_le hd hr
    rw [zero_add, ← EisData.ok_alP hW.ok d hd', EisData.alP, List.getD_eq_getElem _ _ (by simpa using hd'),
      List.getD_eq_getElem _ _ hd', List.getElem_map]
  rw [h, ← RingHom.comp_apply, map_evRow]
  rfl

theorem rowsVal_eRows (hW : WPlace σ E) {D a : ℕ} (hD : D ≤ E.alPow.length) :
    rowsVal (σ := σ) (E := E) (eRows E D a) = evTab (tC σ E) (cY σ E) (truncT D (dpTab (selJ E.e a))) := by
  have hlen := length_truncT_row D (dpTab (selJ E.e a))
  rw [eRows]
  generalize truncT D (dpTab (selJ E.e a)) = c at hlen ⊢
  induction c with
  | nil => simp [rowsVal, evTab]
  | cons r c ih =>
    rw [List.map_cons, rowsVal, List.foldr_cons, ← rowsVal, ih (fun q hq => hlen q (List.mem_cons_of_mem _ hq)),
      algebraMap_combo hW ((hlen r List.mem_cons_self).trans hD), evTab]

theorem Ba_eq (a : ℕ) : Ba σ E a = cY σ E ^ (if a.testBit 0 then 1 else 0) *
    (((selJ E.e a).map fun j => 1 + tC σ E ^ j * cY σ E).prod) *
      (5 : CF σ E) ^ (if a.testBit (2 * E.e + 1) then 1 else 0) := by
  rw [Ba, selJ, ← prod_bits_basis (2 * E.e) (cY σ E) 5 (fun j => 1 + tC σ E ^ j * cY σ E) a]
  rfl

theorem lhsAux_idx (f5 X0 X1 : KE) (a0 : ℕ) : ∀ (n : ℕ) (rs : List (List ℤ)),
    ∀ p ∈ lhsAux f5 X0 X1 a0 n rs, p.2 ≤ n + rs.length + a0
  | n, [] => by simp [lhsAux]
  | n, r :: rs => by
    intro p hp
    simp only [lhsAux, List.mem_cons] at hp
    rcases hp with rfl | rfl | hp
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · have := lhsAux_idx f5 X0 X1 a0 (n + 1) rs p hp
      simp only [List.length_cons]; omega

theorem norm_cY_lt_one (hW : WPlace σ E) : ‖cY σ E‖ < 1 :=
  qfE_Y_lt_one hW.unif hW.norm_A hW.norm_B

theorem norm_tC (_hW : WPlace σ E) : ‖tC σ E‖ = ‖σ (zkE E.al)‖ := QF.norm_algebraMap _ _ _ _

theorem norm_toF_le_one (hW : WPlace σ E) (u v : KE) : ‖toF σ E (evK u) (evK v)‖ ≤ 1 := by
  rw [toF, qfE_norm hW.unif hW.norm_A hW.norm_B]
  refine max_le (norm_evK_le_one σ hW.int u) ?_
  calc ‖σ (evK v)‖ * ‖cY σ E‖ ≤ 1 * 1 :=
        mul_le_mul (norm_evK_le_one σ hW.int v) (norm_cY_lt_one hW).le (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem norm_Ba_le_one (hW : WPlace σ E) (a : ℕ) : ‖Ba σ E a‖ ≤ 1 := by
  have hY := (norm_cY_lt_one hW).le
  have ht : ‖tC σ E‖ ≤ 1 := by rw [norm_tC hW]; exact hW.unif.norm_lt_one.le
  rw [Ba_eq, prod_eq_evTab, norm_mul, norm_mul, norm_pow, norm_pow]
  have h5 : ‖(5 : CF σ E)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one (CF σ E) 5
    simpa using this
  have h1 : ‖cY σ E‖ ^ (if a.testBit 0 then 1 else 0) ≤ 1 := pow_le_one₀ (norm_nonneg _) hY
  have h2 := norm_evTab_le_one ht hY (dpTab (selJ E.e a))
  have h3 : ‖(5 : CF σ E)‖ ^ (if a.testBit (2 * E.e + 1) then 1 else 0) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) h5
  have := mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (by positivity) (by norm_num)
  simpa using this

/-- **Square certificate at an Eisenstein component.** A passing `certOK E D X0 X1 c` makes
`x · ∏ bF^a` a square for every `x` within `‖π‖^n0` of `toF X0 X1`. -/
theorem certOK_isSquare [ProperSpace Kw] (hW : WPlace σ E) {D : ℕ} {X0 X1 : KE} {c : WCert}
    (hc : certOK E D X0 X1 c = true) (x : CF σ E)
    (hx : ‖x - toF σ E (evK X0) (evK X1)‖ ≤ ‖σ (zkE E.al)‖ ^ c.n0) :
    IsSquare (x * Ba σ E c.a) := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hn0, hn1⟩, hD⟩, hDl⟩, hmh⟩, hn0l⟩, hn1l⟩, hep⟩, hrows⟩, hu0⟩, h0⟩, h1⟩ := hc
  have hu0' : zkE c.u0 = 1 + zkE E.al * zkE c.c0 := by simpa using evK_eq_of_check _ _ _ hu0
  have hπ1 := hW.unif.norm_lt_one
  have hπ0 : 0 ≤ ‖σ (zkE E.al)‖ := norm_nonneg _
  set X := toF σ E (evK X0) (evK X1) with hXdef
  set T := dpTab (selJ E.e c.a) with hT
  set a0 := if c.a.testBit 0 then 1 else 0 with ha0
  set f5 : ℤ := if c.a.testBit (2 * E.e + 1) then 5 else 1 with hf5
  -- the identity of the check
  have hLl : ∀ p ∈ lhsL E D X0 X1 c.a, p.2 < E.Ypow.length := by
    intro p hp
    have h := lhsAux_idx _ X0 X1 _ 0 _ p hp
    have ha1 : (if c.a.testBit 0 then 1 else 0) ≤ 1 := by split_ifs <;> omega
    omega
  have hLr : ∀ p ∈ rhsL E c, p.2 < E.Ypow.length := by
    intro p hp
    simp only [rhsL, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
  have hid := (toF_lcE hW _ hLl).symm.trans
    ((congrArg₂ (toF σ E) (evK_eq_of_check _ _ _ h0) (evK_eq_of_check _ _ _ h1)).trans (toF_lcE hW _ hLr))
  rw [lhsL, sum_lhsAux, rowsVal_eRows hW hDl, zero_add] at hid
  -- the value of the basis product
  have hf5v : (5 : CF σ E) ^ (if c.a.testBit (2 * E.e + 1) then 1 else 0) =
      algebraMap Kw (CF σ E) (σ (evK (.int f5))) := by
    rw [evK_int, map_intCast, map_intCast, hf5]; split_ifs <;> norm_num
  have hBa : Ba σ E c.a = algebraMap Kw (CF σ E) (σ (evK (.int f5))) * cY σ E ^ a0 *
      (evTab (tC σ E) (cY σ E) (truncT D T) + tC σ E ^ D * evTab (tC σ E) (cY σ E) (restT D T)) := by
    rw [Ba_eq, prod_eq_evTab, ← hT, evTab_trunc (tC σ E) (cY σ E) D T, hf5v]; ring
  -- the remainder
  set t := (x - X) * Ba σ E c.a + algebraMap Kw (CF σ E) (σ (evK (.int f5))) * X * cY σ E ^ a0 *
    (tC σ E ^ D * evTab (tC σ E) (cY σ E) (restT D T)) with htdef
  have hxB : x * Ba σ E c.a = (algebraMap Kw (CF σ E) (σ (zkE E.al)) ^ c.mh * cY σ E ^ c.ep *
      QF.mk Kw _ _ (1 + σ (zkE E.al) * σ (zkE c.c0)) (σ (zkE c.s1))) ^ 2 +
      algebraMap Kw (CF σ E) (σ (zkE E.al) ^ c.n0 * σ (zkE c.R0)) +
      algebraMap Kw (CF σ E) (σ (zkE E.al) ^ c.n1 * σ (zkE c.R1)) * cY σ E + t := by
    have e1 : x * Ba σ E c.a = t + algebraMap Kw (CF σ E) (σ (evK (.int f5))) * X * cY σ E ^ a0 *
        evTab (tC σ E) (cY σ E) (truncT D T) := by
      rw [htdef, hBa]; ring
    rw [e1, hid]
    simp only [rhsL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, evK_mul, evK_add,
      evK_int, evK_lin, map_mul, map_add, map_one, Int.cast_one, Int.cast_ofNat, hu0']
    have hmk : QF.mk Kw (σ (zkE E.A)) (σ (zkE E.B)) (1 + σ (zkE E.al) * σ (zkE c.c0)) (σ (zkE c.s1)) =
        algebraMap Kw (CF σ E) (1 + σ (zkE E.al) * σ (zkE c.c0)) +
          algebraMap Kw (CF σ E) (σ (zkE c.s1)) * cY σ E := qf_mk_eq _ _
    rw [algebraMap_alP hW hmh, algebraMap_alP hW hn0l, algebraMap_alP hW hn1l, hmk]
    simp only [map_add, map_one, map_mul, map_pow, map_ofNat, tC]
    ring
  -- the bound on the remainder
  have hX1 := norm_toF_le_one hW X0 X1
  have hY1 := (norm_cY_lt_one hW).le
  have hf51 : ‖algebraMap Kw (CF σ E) (σ (evK (.int f5)))‖ ≤ 1 := by
    rw [QF.norm_algebraMap]; exact norm_evK_le_one σ hW.int _
  have hDn : ‖σ (zkE E.al)‖ ^ D ≤ ‖σ (zkE E.al)‖ ^ c.n0 := pow_le_pow_of_le_one hπ0 hπ1.le hD
  have ht : ‖t‖ ≤ ‖σ (zkE E.al)‖ ^ c.n0 := by
    rw [htdef]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖x - X‖ * ‖Ba σ E c.a‖ ≤ ‖σ (zkE E.al)‖ ^ c.n0 * 1 :=
            mul_le_mul hx (norm_Ba_le_one hW _) (norm_nonneg _) (pow_nonneg hπ0 _)
        _ = _ := mul_one _
    · have hr : ‖evTab (tC σ E) (cY σ E) (restT D T)‖ ≤ 1 :=
        norm_evTab_le_one (by rw [norm_tC hW]; exact hπ1.le) hY1 _
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_tC hW]
      calc _ ≤ 1 * 1 * 1 * (‖σ (zkE E.al)‖ ^ D * 1) := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) hY1
        _ ≤ ‖σ (zkE E.al)‖ ^ c.n0 := by simpa using hDn
  exact isSquare_of_eisen_cert hW.unif hW.norm_A hW.norm_B hW.two (hW.int _) (hW.int _) (hW.int _)
    (hW.int _) hn0 hn1 ht hxB

end Place

end FurioLombardo.Discharge.SelmerBasis
