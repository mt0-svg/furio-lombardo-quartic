import FurioLombardo.Discharge.SelmerBasis.W2UnramDefs

/-!
# The place w2: one-level square certificates and the models of `L42`, `N84` (lane selmer-w2)

At w2 (`e = 12`, residue field `𝔽₂`) the three components of `K_w2[T]/(fRev k)` are the unramified
quadratic extension `F = QF Kw (-1) 1 = Kw(ζ)`, `ζ² = ζ - 1`. The place data are a
`WPlace σ E` whose Eisenstein part is never used: only `E.e`, `E.al` and the table `E.alPow` of powers
of `al` enter here.

* `BaQ σ E a`: the basis product `∏ bU^(bit i of a)` of `Fˣ / Fˣ²` (26 bits), `BaQ_eq` its integer
  expansion `π^(a₀) evZL π ζ (dpU (facU e a))` (PlaceUCert.lean).
* `certOKU1`: three `checkK` identities: the unit coordinate `1 + al c0`, and the two coordinates of
  `X · π^(a₀) · Σ_{k < n} p_k π^k = π^(2 mh) (u + s ζ)² + al^n (R0 + R1 ζ)`, the `π`-polynomial summed
  first (`polyE`). `certOKU1_isSquare`: a passing check makes `x · BaQ a` a square for every `x` within
  `‖al‖^n` of `toU1 σ X0 X1 = σ X0 + σ X1 ζ`.
* `RhoData`: `3 r0² + ε = al^n R`, `r0 = al^j (1 + al d)`, gives `ρ ∈ Kw` with `3 ρ² = -σ ε` near `r0`
  (`exists_rho`), and `iL2 : L42 →+* F`, `ω ↦ (2 ζ - 1) ρ`.
* `SqrtU`: `s0 = s00 + s01 ζ` with `s0² - Z0 = al^n (R0 + R1 ζ)`, `Z0 = (2 ea - 2 eb r0) + 4 eb r0 ζ` the
  approximation of `iL2 (4 eN)`, gives `sU` with `sU² = iL2 (4 eN)` (`exists_sU`) and
  `iN2 b : N84 →+* F`, `ω_N ↦ ± sU / 2`.
* `X0L2`, `X1L2`, `X0N2`, `X1N2`: the `KE` coordinates approximating `iL2 (evL t)` and `iN2 b (evN t)`.

Data format and generator: code/selmer-local-conditions/.
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis.W2U

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis FurioLombardo.Discharge.SelmerBasis.Tower

/-! ## Generic facts -/

theorem norm_three_eq_one {K : Type*} [NormedField K] [IsUltrametricDist K] (h2 : ‖(2 : K)‖ < 1) :
    ‖(3 : K)‖ = 1 := by
  have h_eq : (3 : K) = (1 : K) + (2 : K) := by norm_num
  rw [h_eq]
  have h_ne : ‖(1 : K)‖ ≠ ‖(2 : K)‖ := by
    rw [norm_one]
    exact h2.ne.symm
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne, norm_one]
  exact max_eq_left h2.le

section Place

variable {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw]
  {σ : K21 →+* Kw} {E : EisData} [Fact (∀ r : Kw, r ^ 2 ≠ -1 + 1 * r)]

variable (Kw) in
/-- `ζ`, `ζ² = ζ - 1`. -/
noncomputable def cZ1 : QF Kw (-1) 1 := QF.mk Kw (-1) 1 0 1

variable (σ) in
/-- The element `σ X0 + σ X1 ζ`. -/
noncomputable def toU1 (X0 X1 : KE) : QF Kw (-1) 1 := QF.mk Kw (-1) 1 (σ (evK X0)) (σ (evK X1))

variable (σ E) in
/-- The basis product `∏ bU^(bit i of a)` of `F`. -/
noncomputable def BaQ (a : ℕ) : QF Kw (-1) 1 :=
  ∏ i : Fin (2 * E.e + 2), bU (A := (-1 : Kw)) (B := 1) (σ (zkE E.al)) E.e i ^ (bitv (2 * E.e + 2) a i).val

theorem cZ1_mul_cZ1 : cZ1 Kw * cZ1 Kw = cZ1 Kw - 1 := by
  simpa [cZ1, QF, QF.mk] using (by
    have h : (⟨0, 1⟩ : QuadraticAlgebra Kw (-1) 1) * (⟨0, 1⟩ : QuadraticAlgebra Kw (-1) 1) =
      (⟨0, 1⟩ : QuadraticAlgebra Kw (-1) 1) - 1 := by
      apply QuadraticAlgebra.ext
      · simp [QuadraticAlgebra.re_one]
      · simp [QuadraticAlgebra.im_one]
    exact h)

theorem qf_mk_eq_cZ1 (x y : Kw) :
    QF.mk Kw (-1) 1 x y = algebraMap Kw (QF Kw (-1) 1) x + algebraMap Kw (QF Kw (-1) 1) y * cZ1 Kw :=
  qf_mk_eq x y

theorem norm_mk1 (hres : ∀ y : Kw, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (x y : Kw) :
    ‖QF.mk Kw (-1) 1 x y‖ = max ‖x‖ ‖y‖ :=
  qfU_norm hres (by simp) (by simp) x y

theorem BaQ_mod (a : ℕ) : BaQ σ E (a % 2 ^ (2 * E.e + 2)) = BaQ σ E a := by
  simp only [BaQ, bitv_mod_two_pow]

theorem BaQ_zero : BaQ σ E 0 = 1 := prod_bitv_zero _ _

/-- The basis product from the integer expansion. -/
theorem BaQ_eq (a : ℕ) : BaQ σ E a =
    algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ bit0U a *
      evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) (dpU (facU E.e a)) := by
  set π := algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) with hπ
  set ζ := cZ1 Kw with hζ
  have hζsq : ζ * ζ = ζ - 1 := cZ1_mul_cZ1
  let g : ℕ → QF Kw (-1) 1 := λ j => 1 + π ^ (2 * (j / 2) + 1) * (if j % 2 = 0 then 1 else ζ)
  have hg_simp : ∀ j, g j = 1 + π ^ (2 * (j / 2) + 1) * (if j % 2 = 0 then (1 : QF Kw (-1) 1) else ζ) := by
    intro j; rfl
  have hBaQ : BaQ σ E a = ∏ i : Fin (2 * E.e + 2),
      (if (i : ℕ) = 0 then π else if (i : ℕ) = 2 * E.e + 1 then 1 + 4 * ζ else g ((i : ℕ) - 1)) ^
        (bitv (2 * E.e + 2) a i).val := by
    unfold BaQ bU
    apply Finset.prod_congr rfl
    intro i hi
    have h_cZ1_eq : cZ1 Kw = QF.mk Kw (-1) 1 0 1 := rfl
    have h_ζ_eq : ζ = QF.mk Kw (-1) 1 0 1 := hζ.symm.trans h_cZ1_eq
    by_cases hi0 : (i : ℕ) = 0
    · simp [hi0, hπ]
    · by_cases hi_last : (i : ℕ) = 2 * E.e + 1
      · simp [hi_last, h_ζ_eq]
      · by_cases h_even : ((i : ℕ) - 1) % 2 = 0
        · simp [hi0, hi_last, h_even, jU, lU, hπ, h_ζ_eq, g]
        · simp [hi0, hi_last, h_even, jU, lU, hπ, h_ζ_eq, g]
  have hprod := prod_bits_basis (2 * E.e) π (1 + 4 * ζ) g a
  have hfacU_map : ((facU E.e a).map (λ ⟨t, ⟨u, v⟩⟩ => 1 + π ^ t * (((u : ℤ) : QF Kw (-1) 1) + ((v : ℤ) : QF Kw (-1) 1) * ζ))).prod =
      (((List.range (2 * E.e)).filter fun j => a.testBit (j + 1)).map g).prod *
        (if a.testBit (2 * E.e + 1) then 1 + 4 * ζ else 1) := by
    unfold facU
    rw [List.map_append, List.prod_append]
    congr 1
    · have h_map_eq : ((List.range (2 * E.e)).filter fun j => a.testBit (j + 1)).map
          ((λ ⟨t, ⟨u, v⟩⟩ => 1 + π ^ t * (((u : ℤ) : QF Kw (-1) 1) + ((v : ℤ) : QF Kw (-1) 1) * ζ)) ∘
            (fun j => (2 * (j / 2) + 1, if j % 2 = 0 then ((1 : ℤ), (0 : ℤ)) else (0, 1)))) =
        ((List.range (2 * E.e)).filter fun j => a.testBit (j + 1)).map g := by
        refine List.map_congr_left (λ j hj => ?_)
        simp [g, Function.comp]
        by_cases hj_even : j % 2 = 0
        · simp [hj_even]
        · simp [hj_even]
      simpa [List.map_map, Function.comp] using congrArg List.prod h_map_eq
    · by_cases hbit : a.testBit (2 * E.e + 1)
      · simp [hbit, hζ, cZ1]
      · simp [hbit]
  have hRHS : π ^ bit0U a * evZL π ζ (dpU (facU E.e a)) =
      π ^ (if a.testBit 0 then 1 else 0) *
        (((List.range (2 * E.e)).filter fun j => a.testBit (j + 1)).map g).prod *
          (1 + 4 * ζ) ^ (if a.testBit (2 * E.e + 1) then 1 else 0) := by
    calc
      π ^ bit0U a * evZL π ζ (dpU (facU E.e a)) =
          π ^ (if a.testBit 0 then 1 else 0) * evZL π ζ (dpU (facU E.e a)) := by
        simp [bit0U]
      _ = π ^ (if a.testBit 0 then 1 else 0) *
          ((facU E.e a).map (λ ⟨t, ⟨u, v⟩⟩ => 1 + π ^ t * (((u : ℤ) : QF Kw (-1) 1) + ((v : ℤ) : QF Kw (-1) 1) * ζ))).prod := by
        have htemp := evZL_dpU (R := QF Kw (-1) 1) (y := π) (z := ζ) hζsq (facU E.e a)
        rw [htemp]
      _ = π ^ (if a.testBit 0 then 1 else 0) *
          ((((List.range (2 * E.e)).filter fun j => a.testBit (j + 1)).map g).prod *
            (if a.testBit (2 * E.e + 1) then 1 + 4 * ζ else 1)) := by
        rw [hfacU_map]
      _ = π ^ (if a.testBit 0 then 1 else 0) *
          (((List.range (2 * E.e)).filter fun j => a.testBit (j + 1)).map g).prod *
            (if a.testBit (2 * E.e + 1) then 1 + 4 * ζ else 1) := by ring
      _ = π ^ (if a.testBit 0 then 1 else 0) *
          (((List.range (2 * E.e)).filter fun j => a.testBit (j + 1)).map g).prod *
            (1 + 4 * ζ) ^ (if a.testBit (2 * E.e + 1) then 1 else 0) := by
        by_cases hbit : a.testBit (2 * E.e + 1)
        · simp [hbit]
        · simp [hbit]
  calc
    BaQ σ E a = ∏ i : Fin (2 * E.e + 2),
        (if (i : ℕ) = 0 then π else if (i : ℕ) = 2 * E.e + 1 then 1 + 4 * ζ else g ((i : ℕ) - 1)) ^
          (bitv (2 * E.e + 2) a i).val := hBaQ
    _ = π ^ (if a.testBit 0 then 1 else 0) *
        (((List.range (2 * E.e)).filter fun j => a.testBit (j + 1)).map g).prod *
          (1 + 4 * ζ) ^ (if a.testBit (2 * E.e + 1) then 1 else 0) := by
      simpa using hprod
    _ = π ^ bit0U a * evZL π ζ (dpU (facU E.e a)) := by symm; exact hRHS

lemma prod_norm_le_one {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, f i ≤ 1) (hf_nonneg : ∀ i ∈ s, 0 ≤ f i) : ∏ i ∈ s, f i ≤ 1 := by
  induction' s using Finset.induction with i s his IH
  · simp
  · have hi : f i ≤ 1 := hf i (Finset.mem_insert_self i s)
    have hprod : ∏ j ∈ s, f j ≤ 1 := IH (fun j hj => hf j (Finset.mem_insert_of_mem hj)) (fun j hj => hf_nonneg j (Finset.mem_insert_of_mem hj))
    have hprod_nonneg : 0 ≤ ∏ j ∈ s, f j := Finset.prod_nonneg fun j hj => hf_nonneg j (Finset.mem_insert_of_mem hj)
    have h_mul : f i * ∏ j ∈ s, f j ≤ 1 * 1 := mul_le_mul hi hprod hprod_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    simpa [Finset.prod_insert his, mul_one] using h_mul

theorem norm_BaQ_le_one_aux_bU_norm_le_one {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw] {σ : K21 →+* Kw} {E : EisData} [Fact (∀ r : Kw, r ^ 2 ≠ -1 + 1 * r)] (hπ : NormUnif (σ (zkE E.al))) (hres : ∀ y : Kw, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (i : ℕ) : ‖bU (A := (-1 : Kw)) (B := 1) (σ (zkE E.al)) E.e i‖ ≤ 1 := by
  unfold bU
  split
  · -- i = 0
    rw [QF.norm_algebraMap (K := Kw) (a := (-1 : Kw)) (b := 1)]
    exact hπ.norm_lt_one.le
  · split
    · -- i = 2 * E.e + 1
      have hnorm_mk : ‖QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw)‖ = 1 := by
        rw [norm_mk1 hres (0 : Kw) (1 : Kw)]
        simp [norm_zero, norm_one]
      have hnorm_4 : ‖(4 : QF Kw (-1) 1)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one (QF Kw (-1) 1) 4
      have hnorm_prod : ‖(4 : QF Kw (-1) 1) * QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw)‖ ≤ 1 := by
        calc
          ‖(4 : QF Kw (-1) 1) * QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw)‖ ≤ ‖(4 : QF Kw (-1) 1)‖ * ‖QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw)‖ := norm_mul_le _ _
          _ ≤ 1 * 1 := mul_le_mul hnorm_4 hnorm_mk.le (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      calc
        ‖1 + (4 : QF Kw (-1) 1) * QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw)‖ ≤ max ‖(1 : QF Kw (-1) 1)‖ ‖(4 : QF Kw (-1) 1) * QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ max 1 1 := by
          refine max_le_max ?_ hnorm_prod
          rw [norm_one]
        _ = 1 := by simp
    · -- other case
      have hnorm_w : ‖(if lU i = 0 then (1 : QF Kw (-1) 1) else QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw))‖ ≤ 1 := by
        split
        · rw [norm_one]
        · rw [norm_mk1 hres (0 : Kw) (1 : Kw)]
          simp [norm_zero, norm_one]
      have hnorm_pow : ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ (2 * jU i + 1)‖ ≤ 1 := by
        rw [norm_pow]
        have hπ_norm : ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))‖ ≤ 1 := by
          rw [QF.norm_algebraMap (K := Kw) (a := (-1 : Kw)) (b := 1)]
          exact hπ.norm_lt_one.le
        exact pow_le_one₀ (norm_nonneg _) hπ_norm
      have hnorm_prod : ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ (2 * jU i + 1) * (if lU i = 0 then (1 : QF Kw (-1) 1) else QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw))‖ ≤ 1 := by
        calc
          ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ (2 * jU i + 1) * (if lU i = 0 then (1 : QF Kw (-1) 1) else QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw))‖ ≤
            ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ (2 * jU i + 1)‖ * ‖(if lU i = 0 then (1 : QF Kw (-1) 1) else QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw))‖ := norm_mul_le _ _
          _ ≤ 1 * 1 := mul_le_mul hnorm_pow hnorm_w (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      calc
        ‖1 + algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ (2 * jU i + 1) * (if lU i = 0 then (1 : QF Kw (-1) 1) else QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw))‖ ≤
          max ‖(1 : QF Kw (-1) 1)‖ ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ (2 * jU i + 1) * (if lU i = 0 then (1 : QF Kw (-1) 1) else QF.mk Kw (-1) 1 (0 : Kw) (1 : Kw))‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ max 1 1 := by
          refine max_le_max ?_ hnorm_prod
          rw [norm_one]
        _ = 1 := by simp


theorem norm_BaQ_le_one (hπ : NormUnif (σ (zkE E.al))) (h2 : ‖(2 : Kw)‖ = ‖σ (zkE E.al)‖ ^ E.e)
    (hres : ∀ y : Kw, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (a : ℕ) : ‖BaQ σ E a‖ ≤ 1 := by
  unfold BaQ
  rw [norm_prod]
  refine prod_norm_le_one (Finset.univ : Finset (Fin (2 * E.e + 2))) (fun i => ‖bU (A := (-1 : Kw)) (B := 1) (σ (zkE E.al)) E.e i ^ (bitv (2 * E.e + 2) a i).val‖) ?_ ?_
  · intro i hi
    rw [norm_pow]
    have hbU : ‖bU (A := (-1 : Kw)) (B := 1) (σ (zkE E.al)) E.e i‖ ≤ 1 :=
      norm_BaQ_le_one_aux_bU_norm_le_one hπ hres (i : ℕ)
    have h_nonneg : 0 ≤ ‖bU (A := (-1 : Kw)) (B := 1) (σ (zkE E.al)) E.e i‖ := norm_nonneg _
    exact pow_le_one₀ h_nonneg hbU
  · intro i hi
    exact norm_nonneg _

/-- The value of a `polyE` pair. -/
theorem polyE_eval (halP : ∀ d, d < E.alPow.length → zkE (E.alP d) = zkE E.al ^ d) (a0 : ℕ) :
    ∀ (n : ℕ) (P : List (ℤ × ℤ)), n + P.length + a0 ≤ E.alPow.length →
      QF.mk Kw (-1) 1 (σ (evK (polyE E Prod.fst a0 n P))) (σ (evK (polyE E Prod.snd a0 n P))) =
        algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ (n + a0) *
          evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) P := by
  intro n P hlen
  induction' P with p P ih generalizing n
  · -- base case: P = []
    simp [polyE, evZL, qf_mk_eq_cZ1]
  · -- inductive case: p :: P
    rcases p with ⟨p1, p2⟩
    -- hlen : n + ((p1, p2) :: P).length + a0 ≤ E.alPow.length
    have hlen_simp : n + P.length + 1 + a0 ≤ E.alPow.length := by
      have : ((p1, p2) :: P).length = P.length + 1 := rfl
      omega
    have hlen_succ : (n + 1) + P.length + a0 ≤ E.alPow.length := by omega
    have h_lt_n_a0 : n + a0 < E.alPow.length := by
      have : 1 ≤ P.length + 1 := by omega
      omega
    have h_halP_n := halP (n + a0) h_lt_n_a0
    set φ := algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) with hφ
    set ζ := cZ1 Kw with hζ
    have h_qf_mk (x y : Kw) : QF.mk Kw (-1) 1 x y = algebraMap Kw (QF Kw (-1) 1) x + algebraMap Kw (QF Kw (-1) 1) y * ζ := by
      rw [qf_mk_eq_cZ1, hζ]
    -- rewrite LHS using h_qf_mk
    rw [h_qf_mk (σ (evK (polyE E Prod.fst a0 n ((p1, p2) :: P)))) (σ (evK (polyE E Prod.snd a0 n ((p1, p2) :: P))))]
    -- expand polyE
    have h_polyE_fst : polyE E Prod.fst a0 n ((p1, p2) :: P) = .add (.mul (.int p1) (.lin (E.alP (n + a0)))) (polyE E Prod.fst a0 (n + 1) P) := by
      simp [polyE]
    have h_polyE_snd : polyE E Prod.snd a0 n ((p1, p2) :: P) = .add (.mul (.int p2) (.lin (E.alP (n + a0)))) (polyE E Prod.snd a0 (n + 1) P) := by
      simp [polyE]
    rw [h_polyE_fst, h_polyE_snd]
    -- push σ and evK through the operations
    simp [evK_add, evK_mul, evK_int, evK_lin, map_add, map_mul, map_pow, h_halP_n]
    -- Now the goal is:
    -- (p1 : QF) * φ ^ (n + a0) + algebraMap (σ (evK X'))
    -- + ((p2 : QF) * φ ^ (n + a0) + algebraMap (σ (evK Y'))) * ζ
    -- = φ ^ (n + a0) * evZL φ ζ ((p1, p2) :: P)
    -- where X' = polyE E Prod.fst a0 (n + 1) P, Y' = polyE E Prod.snd a0 (n + 1) P
    --
    -- Let A = algebraMap (σ (evK X')), B = algebraMap (σ (evK Y'))
    -- Then the goal is: (p1:QF)*φ^(n+a0) + A + ((p2:QF)*φ^(n+a0) + B)*ζ = φ^(n+a0) * evZL φ ζ ((p1,p2)::P)
    --
    -- Expand RHS: evZL φ ζ ((p1,p2)::P) = ((p1:QF) + (p2:QF)*ζ) + φ * evZL φ ζ P
    rw [evZL]
    -- Goal: (p1:QF)*φ^(n+a0) + A + ((p2:QF)*φ^(n+a0) + B)*ζ = φ^(n+a0) * (((p1:QF) + (p2:QF)*ζ) + φ * evZL φ ζ P)
    --
    -- Expand RHS: φ^(n+a0) * ((p1:QF) + (p2:QF)*ζ) + φ^(n+a0) * φ * evZL φ ζ P
    -- = φ^(n+a0) * ((p1:QF) + (p2:QF)*ζ) + φ^((n+1)+a0) * evZL φ ζ P
    --
    -- Expand LHS: (p1:QF)*φ^(n+a0) + A + (p2:QF)*φ^(n+a0)*ζ + B*ζ
    -- = φ^(n+a0) * ((p1:QF) + (p2:QF)*ζ) + (A + B*ζ)
    --
    -- Now A + B*ζ = algebraMap (σ (evK X')) + algebraMap (σ (evK Y')) * ζ
    -- = QF.mk Kw (-1) 1 (σ (evK X')) (σ (evK Y'))  (by h_qf_mk)
    -- = φ ^ ((n+1)+a0) * evZL φ ζ P  (by IH)
    --
    -- So both sides equal φ^(n+a0) * ((p1:QF) + (p2:QF)*ζ) + φ^((n+1)+a0) * evZL φ ζ P
    --
    -- Let's do this algebraically:
    calc
      (p1 : QF Kw (-1) 1) * φ ^ (n + a0) + algebraMap Kw (QF Kw (-1) 1) (σ (evK (polyE E Prod.fst a0 (n + 1) P)))
        + ((p2 : QF Kw (-1) 1) * φ ^ (n + a0) + algebraMap Kw (QF Kw (-1) 1) (σ (evK (polyE E Prod.snd a0 (n + 1) P)))) * ζ
          = φ ^ (n + a0) * ((p1 : QF Kw (-1) 1) + (p2 : QF Kw (-1) 1) * ζ)
            + (algebraMap Kw (QF Kw (-1) 1) (σ (evK (polyE E Prod.fst a0 (n + 1) P)))
              + algebraMap Kw (QF Kw (-1) 1) (σ (evK (polyE E Prod.snd a0 (n + 1) P))) * ζ) := by
        ring
      _ = φ ^ (n + a0) * ((p1 : QF Kw (-1) 1) + (p2 : QF Kw (-1) 1) * ζ)
            + (QF.mk Kw (-1) 1 (σ (evK (polyE E Prod.fst a0 (n + 1) P))) (σ (evK (polyE E Prod.snd a0 (n + 1) P)))) := by
        rw [← h_qf_mk]
      _ = φ ^ (n + a0) * ((p1 : QF Kw (-1) 1) + (p2 : QF Kw (-1) 1) * ζ)
            + (φ ^ ((n + 1) + a0) * evZL φ ζ P) := by
        rw [ih (n + 1) hlen_succ]
      _ = φ ^ (n + a0) * (((p1 : QF Kw (-1) 1) + (p2 : QF Kw (-1) 1) * ζ) + φ * evZL φ ζ P) := by
        ring

/-- The value of the left side. -/
theorem lhs1_eval (X0 X1 P1 P2 : KE) :
    QF.mk Kw (-1) 1 (σ (evK (lhs1 X0 X1 P1 P2).1)) (σ (evK (lhs1 X0 X1 P1 P2).2)) =
      toU1 σ X0 X1 * QF.mk Kw (-1) 1 (σ (evK P1)) (σ (evK P2)) := by
  dsimp [lhs1, toU1]
  simp only [qf_mk_eq_cZ1, evK_add, evK_sub, evK_mul, map_add, map_sub, map_mul]
  have h := cZ1_mul_cZ1 (Kw := Kw)
  linear_combination (-algebraMap Kw (QF Kw (-1) 1) (σ (evK X1)) * algebraMap Kw (QF Kw (-1) 1) (σ (evK P2))) * h

/-- The value of the right side. -/
theorem rhs1_eval (halP : ∀ d, d < E.alPow.length → zkE (E.alP d) = zkE E.al ^ d) (c : UCert1)
    (hn : c.n < E.alPow.length) (hm : 2 * c.mh < E.alPow.length) :
    QF.mk Kw (-1) 1 (σ (evK (rhs1 E c).1)) (σ (evK (rhs1 E c).2)) =
      (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ c.mh *
          QF.mk Kw (-1) 1 (σ (zkE c.u)) (σ (zkE c.s))) ^ 2 +
        algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al) ^ c.n * σ (zkE c.R0)) +
        algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al) ^ c.n * σ (zkE c.R1)) * QF.mk Kw (-1) 1 0 1 := by
  dsimp only [rhs1]
  simp only [qf_mk_eq_cZ1, evK_add, evK_sub, evK_mul, evK_lin, evK_int, halP _ hn, halP _ hm, map_add,
    map_sub, map_mul, map_pow, map_intCast, map_zero, map_one, zero_add, one_mul]
  have h := cZ1_mul_cZ1 (Kw := Kw)
  linear_combination (-(algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ (2 * c.mh) *
    algebraMap Kw (QF Kw (-1) 1) (σ (zkE c.s)) ^ 2)) * h

theorem norm_toU1_le_one (hint : ∀ a : List ℤ, ‖σ (zkE a)‖ ≤ 1)
    (hres : ∀ y : Kw, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (X0 X1 : KE) : ‖toU1 σ X0 X1‖ ≤ 1 := by
  unfold toU1
  rw [norm_mk1 hres]
  apply max_le
  · exact norm_evK_le_one σ hint X0
  · exact norm_evK_le_one σ hint X1

/-- The unit coordinate. -/
theorem norm_unit_one (hint : ∀ a : List ℤ, ‖σ (zkE a)‖ ≤ 1) (hπ : ‖σ (zkE E.al)‖ < 1)
    {a c0 : List ℤ} (h : zkE a = 1 + zkE E.al * zkE c0) : ‖σ (zkE a)‖ = 1 := by
  rw [h]
  have hx_lt_one : ‖σ (zkE E.al) * σ (zkE c0)‖ < 1 := by
    calc
      ‖σ (zkE E.al) * σ (zkE c0)‖ = ‖σ (zkE E.al)‖ * ‖σ (zkE c0)‖ := norm_mul _ _
      _ ≤ ‖σ (zkE E.al)‖ * 1 := mul_le_mul_of_nonneg_left (hint c0) (norm_nonneg _)
      _ = ‖σ (zkE E.al)‖ := mul_one _
      _ < 1 := hπ
  have hx_norm_ne_one : ‖(1 : Kw)‖ ≠ ‖σ (zkE E.al) * σ (zkE c0)‖ := by
    rw [norm_one]
    exact (ne_of_lt hx_lt_one).symm
  calc
    ‖σ (1 + zkE E.al * zkE c0)‖ = ‖σ 1 + σ (zkE E.al) * σ (zkE c0)‖ := by simp
    _ = ‖(1 : Kw) + σ (zkE E.al) * σ (zkE c0)‖ := by simp
    _ = max ‖(1 : Kw)‖ ‖σ (zkE E.al) * σ (zkE c0)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hx_norm_ne_one
    _ = max (1 : ℝ) ‖σ (zkE E.al) * σ (zkE c0)‖ := by simp
    _ = (1 : ℝ) := max_eq_left (by linarith)
    _ = 1 := rfl

/-- The remainder: `‖(x - X) BaQ + X π^a0 π^n evZL(tail) ‖ ≤ ‖π‖^n`. -/
theorem norm_rem1_le (hπ : NormUnif (σ (zkE E.al))) (h2 : ‖(2 : Kw)‖ = ‖σ (zkE E.al)‖ ^ E.e)
    (hint : ∀ a : List ℤ, ‖σ (zkE a)‖ ≤ 1) (hres : ∀ y : Kw, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1)
    {X0 X1 : KE} {n : ℕ} (x : QF Kw (-1) 1) (hx : ‖x - toU1 σ X0 X1‖ ≤ ‖σ (zkE E.al)‖ ^ n)
    (a a0 : ℕ) (P : List (ℤ × ℤ)) :
    ‖(x - toU1 σ X0 X1) * BaQ σ E a +
        toU1 σ X0 X1 * algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ a0 *
          (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ n *
            evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) P)‖ ≤
      ‖σ (zkE E.al)‖ ^ n := by
  have hnonneg_sigma : 0 ≤ ‖σ (zkE E.al)‖ := norm_nonneg _
  have hnonneg_sigma_pow (k : ℕ) : 0 ≤ ‖σ (zkE E.al)‖ ^ k := pow_nonneg hnonneg_sigma k
  have hsigma_le_one : ‖σ (zkE E.al)‖ ≤ 1 := hπ.norm_lt_one.le
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  refine max_le ?_ ?_
  · -- ‖(x - toU1 σ X0 X1) * BaQ σ E a‖ ≤ ‖σ (zkE E.al)‖ ^ n
    calc
      ‖(x - toU1 σ X0 X1) * BaQ σ E a‖ ≤ ‖x - toU1 σ X0 X1‖ * ‖BaQ σ E a‖ := norm_mul_le _ _
      _ ≤ (‖σ (zkE E.al)‖ ^ n) * 1 :=
        mul_le_mul hx (norm_BaQ_le_one hπ h2 hres a) (norm_nonneg _) (hnonneg_sigma_pow n)
      _ = ‖σ (zkE E.al)‖ ^ n := by simp
  · -- ‖toU1 σ X0 X1 * algebraMap ... ^ a0 * (algebraMap ... ^ n * evZL ... (cZ1 Kw) P)‖ ≤ ‖σ (zkE E.al)‖ ^ n
    have htoU1 : ‖toU1 σ X0 X1‖ ≤ 1 := norm_toU1_le_one hint hres X0 X1
    have halg_pow_a0_le_one : ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ a0‖ ≤ 1 := by
      rw [norm_pow, QF.norm_algebraMap]
      exact pow_le_one₀ (n := a0) hnonneg_sigma hsigma_le_one
    have hcZ1_le_one : ‖cZ1 Kw‖ ≤ 1 := by
      have h := norm_mk1 hres 0 1
      have h' : ‖cZ1 Kw‖ = 1 := by
        simpa [cZ1] using h
      exact h'.le
    have halv_n_le : ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ n‖ ≤ ‖σ (zkE E.al)‖ ^ n := by
      rw [norm_pow, QF.norm_algebraMap]
    have hevZL_le_one : ‖evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) P‖ ≤ 1 :=
      norm_evZL_le_one (by rw [QF.norm_algebraMap]; exact hint E.al) hcZ1_le_one P
    have hthird : ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ n *
        evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) P‖ ≤ ‖σ (zkE E.al)‖ ^ n * 1 := by
      calc
        ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ n *
            evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) P‖
            ≤ ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ n‖ *
                ‖evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) P‖ :=
          norm_mul_le _ _
        _ ≤ (‖σ (zkE E.al)‖ ^ n) * 1 :=
          mul_le_mul halv_n_le hevZL_le_one (norm_nonneg _) (hnonneg_sigma_pow n)
    calc
      ‖toU1 σ X0 X1 * algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ a0 *
          (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ n *
            evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) P)‖
          ≤ ‖toU1 σ X0 X1 * algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ a0‖ *
              ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ n *
                evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) P‖ :=
        norm_mul_le _ _
      _ ≤ (‖toU1 σ X0 X1‖ * ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ a0‖) *
              ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ n *
                evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) P‖ := by
        refine mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖toU1 σ X0 X1‖ * (‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ a0‖ *
              ‖algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ n *
                evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) P‖) := by ring
      _ ≤ 1 * (1 * (‖σ (zkE E.al)‖ ^ n * 1)) := by
        refine mul_le_mul htoU1 ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
        refine mul_le_mul halg_pow_a0_le_one hthird (norm_nonneg _) (by norm_num)
      _ = ‖σ (zkE E.al)‖ ^ n := by simp

/-- **Square certificate at `F`.** -/
theorem certOKU1_isSquare [ProperSpace Kw] (hW : WPlace σ E) {X0 X1 : KE} {c : UCert1}
    (hc : certOKU1 E X0 X1 c = true) (x : QF Kw (-1) 1)
    (hx : ‖x - toU1 σ X0 X1‖ ≤ ‖σ (zkE E.al)‖ ^ c.n) :
    IsSquare (x * BaQ σ E c.a) := by
  simp only [certOKU1, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hn, hnl⟩, hu⟩, h1⟩, h2⟩ := hc
  have halP := EisData.ok_alP hW.ok
  have ha01 : bit0U c.a ≤ 1 := by unfold bit0U; split_ifs <;> omega
  have hlen : (trU E c.a c.n).length ≤ c.n := List.length_take_le _ _
  have e1 := congrArg σ (evK_eq_of_check _ _ _ h1)
  have e2 := congrArg σ (evK_eq_of_check _ _ _ h2)
  have hid := congrArg₂ (QF.mk Kw (-1) 1) e1 e2
  rw [lhs1_eval, polyE_eval halP (bit0U c.a) 0 (trU E c.a c.n) (by omega),
    rhs1_eval halP c hnl (by omega), zero_add] at hid
  have hBa : BaQ σ E c.a = algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ bit0U c.a *
      (evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) (trU E c.a c.n) +
        algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al)) ^ c.n *
          evZL (algebraMap Kw (QF Kw (-1) 1) (σ (zkE E.al))) (cZ1 Kw) ((dpU (facU E.e c.a)).drop c.n)) := by
    rw [BaQ_eq, trU, ← evZL_take_drop]
  have ht := norm_rem1_le hW.unif hW.two hW.int hW.res x hx c.a (bit0U c.a) ((dpU (facU E.e c.a)).drop c.n)
  have hunit : ‖σ (zkE c.u)‖ = 1 ∨ ‖σ (zkE c.s)‖ = 1 := by
    have e := evK_eq_of_check _ _ _ hu
    simp only [evK_lin, evK_add, evK_mul, evK_int, Int.cast_one] at e
    cases hub : c.ub
    · rw [hub] at e
      exact Or.inl (norm_unit_one hW.int hW.unif.norm_lt_one (by simpa using e))
    · rw [hub] at e
      exact Or.inr (norm_unit_one hW.int hW.unif.norm_lt_one (by simpa using e))
  refine isSquare_of_unram_cert (K := Kw) (A := -1) (B := 1) (π := σ (zkE E.al))
    (r0 := σ (zkE c.R0)) (r1 := σ (zkE c.R1)) hW.unif hW.res
    (by simp) (by simp) hW.two (hW.int _) (hW.int _) hunit (hW.int _) (hW.int _) (by omega) (by omega) ht ?_
  rw [hBa]
  linear_combination hid

/-! ## `L42 →+* F` -/

lemma exists_rho_aux_norm_three_eq_one {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw] {σ : K21 →+* Kw} {E : EisData} [Fact (∀ r : Kw, r ^ 2 ≠ -1 + 1 * r)] (hW : WPlace σ E) : ‖(3 : Kw)‖ = 1 := by
  have h_norm2_le_one : ‖(2 : Kw)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one Kw 2
  have h_res := hW.res (2 : Kw) h_norm2_le_one
  have h_norm_sub_le_max : ∀ x y : Kw, ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
    intro x y
    calc
      ‖x - y‖ = ‖x + (-y)‖ := by rw [sub_eq_add_neg]
      _ ≤ max ‖x‖ ‖-y‖ := IsUltrametricDist.norm_add_le_max _ _
      _ = max ‖x‖ ‖y‖ := by simp
  rcases h_res with (h_lt | h_lt')
  · -- h_lt : ‖(2 : Kw)‖ < 1
    have h_le : ‖(3 : Kw)‖ ≤ 1 := by
      calc
        ‖(3 : Kw)‖ = ‖(1 : Kw) + (2 : Kw)‖ := by norm_num
        _ ≤ max ‖(1 : Kw)‖ ‖(2 : Kw)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ = max 1 ‖(2 : Kw)‖ := by simp
        _ = 1 := by
          rw [max_eq_left (by linarith)]
    have h_ge : 1 ≤ ‖(3 : Kw)‖ := by
      have h_sub : ‖(3 : Kw) - (2 : Kw)‖ ≤ max ‖(3 : Kw)‖ ‖(2 : Kw)‖ := h_norm_sub_le_max _ _
      have : ‖(3 : Kw) - (2 : Kw)‖ = 1 := by
        have : (3 : Kw) - (2 : Kw) = (1 : Kw) := by norm_num
        simp [this]
      rw [this] at h_sub
      by_contra! h_lt3
      have h_max_lt_one : max ‖(3 : Kw)‖ ‖(2 : Kw)‖ < 1 := by
        rw [max_lt_iff]
        exact ⟨h_lt3, h_lt⟩
      linarith
    linarith
  · -- h_lt' : ‖(2 : Kw) - 1‖ < 1
    have : ‖(2 : Kw) - 1‖ = 1 := by
      have : (2 : Kw) - 1 = (1 : Kw) := by norm_num
      simp [this]
    rw [this] at h_lt'
    linarith

lemma exists_rho_aux_norm_three_ne_zero {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw] {σ : K21 →+* Kw} {E : EisData} [Fact (∀ r : Kw, r ^ 2 ≠ -1 + 1 * r)] (hW : WPlace σ E) : (3 : Kw) ≠ 0 := by
  have h_norm3 : ‖(3 : Kw)‖ = 1 := exists_rho_aux_norm_three_eq_one hW
  intro hzero
  rw [hzero, norm_zero] at h_norm3
  linarith

lemma exists_rho_aux_norm_div_three_le_one {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw] {σ : K21 →+* Kw} {E : EisData} [Fact (∀ r : Kw, r ^ 2 ≠ -1 + 1 * r)] (hW : WPlace σ E) (x : Kw) (hx : ‖x‖ ≤ 1) : ‖x / (3 : Kw)‖ ≤ 1 := by
  rw [norm_div]
  have h_norm3 : ‖(3 : Kw)‖ = 1 := exists_rho_aux_norm_three_eq_one hW
  rw [h_norm3, div_one]
  exact hx


/-- `ρ` with `3 ρ² = -σ ε` near `r0`. -/
theorem exists_rho (hW : WPlace σ E) {S : RhoData} (hS : S.ok E = true) :
    ∃ ρ : Kw, 3 * ρ ^ 2 = -σ epsK ∧ ‖ρ - σ (evK (S.r0 E))‖ ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := by
  -- Unpack hS
  have hS_unpacked : S.n < E.alPow.length ∧ S.j < E.alPow.length ∧ 2 * E.e + 2 * S.j < S.n ∧
    checkK S.prec (.sub (.add (.mul (.int 3) (.mul (S.r0 E) (S.r0 E))) (.lin epsL))
      (.mul (.lin (E.alP S.n)) (.lin S.R))) = true := by
    have h := hS
    simp only [RhoData.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨hn, hj⟩, h_ineq⟩, h_check⟩
    exact ⟨hn, hj, h_ineq, h_check⟩
  rcases hS_unpacked with ⟨hn, hj, h_ineq, h_check⟩
  -- Key identity from the check
  have h_evK_eq : evK (.add (.mul (.int 3) (.mul (S.r0 E) (S.r0 E))) (.lin epsL)) =
      evK (.mul (.lin (E.alP S.n)) (.lin S.R)) :=
    evK_eq_of_check S.prec _ _ h_check
  -- Expand both sides using evK lemmas to get an identity in K21
  have h_id_K21 : (3 : K21) * (((zkE E.al) ^ S.j * ((1 : K21) + zkE E.al * zkE S.d)) ^ 2) + epsK =
      (zkE E.al) ^ S.n * zkE S.R := by
    have h_left : evK (.add (.mul (.int 3) (.mul (S.r0 E) (S.r0 E))) (.lin epsL)) =
        (3 : K21) * (evK (S.r0 E)) ^ 2 + epsK := by
      simp [evK_add, evK_mul, evK_int, evK_lin, epsK_eq, pow_two]
    have h_right : evK (.mul (.lin (E.alP S.n)) (.lin S.R)) = zkE (E.alP S.n) * zkE S.R := by
      simp [evK_mul, evK_lin]
    have h_r0 : evK (S.r0 E) = zkE (E.alP S.j) * ((1 : K21) + zkE E.al * zkE S.d) := by
      simp [RhoData.r0, evK_mul, evK_add, evK_int, evK_lin]
    have h_alP_eq : ∀ d, d < E.alPow.length → zkE (E.alP d) = (zkE E.al) ^ d :=
      FurioLombardo.Discharge.SelmerBasis.EisData.ok_alP hW.ok
    rw [h_left, h_right] at h_evK_eq
    rw [h_r0] at h_evK_eq
    rw [h_alP_eq S.j hj, h_alP_eq S.n hn] at h_evK_eq
    exact h_evK_eq
  -- Apply σ to the identity in K21 to get an identity in Kw
  set π := σ (zkE E.al) with hπ_def
  set δ := σ (zkE S.d) with hδ_def
  have h_id_Kw : (3 : Kw) * ((π ^ S.j * ((1 : Kw) + π * δ)) ^ 2) + σ epsK = π ^ S.n * σ (zkE S.R) := by
    have h := congrArg σ h_id_K21
    -- Manually expand using ring homomorphism properties
    simp [RingHom.map_add, RingHom.map_mul, RingHom.map_pow, RingHom.map_one, epsK_eq] at h
    -- Now h: σ 3 * (σ (zkE E.al) ^ S.j * (1 + σ (zkE E.al) * σ (zkE S.d))) ^ 2 + σ (zkE epsL) = ...
    -- Need to replace σ 3 with (3 : Kw) and σ (zkE epsL) with σ epsK
    have h3 : σ (3 : K21) = (3 : Kw) := map_natCast σ 3
    rw [h3, ← epsK_eq] at h
    simpa [hπ_def, hδ_def] using h
  -- Now apply exists_sqrt_of_cert
  have hπ0 : π ≠ 0 := hW.unif.ne_zero
  have hπ1 : ‖π‖ < 1 := hW.unif.norm_lt_one
  have h2 : ‖(2 : Kw)‖ = ‖π‖ ^ E.e := hW.two
  have hz : ‖(-σ epsK) / (3 : Kw)‖ ≤ 1 := by
    rw [norm_div, norm_neg]
    have h_norm3 : ‖(3 : Kw)‖ = 1 := exists_rho_aux_norm_three_eq_one hW
    rw [h_norm3, div_one, epsK_eq]
    exact hW.int epsL
  have hδ : ‖δ‖ ≤ 1 := by
    rw [hδ_def]
    exact hW.int S.d
  have hρ : ‖σ (zkE S.R) / (3 : Kw)‖ ≤ 1 :=
    exists_rho_aux_norm_div_three_le_one hW (σ (zkE S.R)) (hW.int S.R)
  have hM : 2 * E.e + 2 * S.j < S.n := h_ineq
  have h3_ne_zero : (3 : Kw) ≠ 0 :=
    exists_rho_aux_norm_three_ne_zero hW
  have hc : (π ^ S.j * ((1 : Kw) + π * δ)) ^ 2 - ((-σ epsK) / (3 : Kw)) = π ^ S.n * (σ (zkE S.R) / (3 : Kw)) := by
    calc
      (π ^ S.j * ((1 : Kw) + π * δ)) ^ 2 - ((-σ epsK) / (3 : Kw))
          = ((π ^ S.j * ((1 : Kw) + π * δ)) ^ 2 * (3 : Kw) - (-σ epsK)) / (3 : Kw) := by
        field_simp [h3_ne_zero]
      _ = ((π ^ S.j * ((1 : Kw) + π * δ)) ^ 2 * (3 : Kw) + σ epsK) / (3 : Kw) := by ring
      _ = ((3 : Kw) * (π ^ S.j * ((1 : Kw) + π * δ)) ^ 2 + σ epsK) / (3 : Kw) := by ring
      _ = (π ^ S.n * σ (zkE S.R)) / (3 : Kw) := by rw [h_id_Kw]
      _ = π ^ S.n * (σ (zkE S.R) / (3 : Kw)) := by ring
  -- Get the square root
  obtain ⟨s, hs_sq, hs_norm⟩ := exists_sqrt_of_cert hπ0 hπ1 h2 hz hδ hρ hM hc
  -- Now s satisfies s^2 = -σ epsK / 3, so 3 * s^2 = -σ epsK
  have h_goal1 : 3 * s ^ 2 = -σ epsK := by
    rw [hs_sq]
    field_simp [h3_ne_zero]
  -- Need to show ‖s - σ (evK (S.r0 E))‖ ≤ ‖π‖ ^ (S.n - E.e - S.j)
  have h_goal2 : ‖s - σ (evK (S.r0 E))‖ ≤ ‖π‖ ^ (S.n - E.e - S.j) := by
    -- First show σ (evK (S.r0 E)) = π ^ S.j * (1 + π * δ)
    have h_evK_r0 : σ (evK (S.r0 E)) = π ^ S.j * ((1 : Kw) + π * δ) := by
      calc
        σ (evK (S.r0 E)) = σ (zkE (E.alP S.j) * ((1 : K21) + zkE E.al * zkE S.d)) := by
          simp [RhoData.r0, evK_mul, evK_add, evK_int, evK_lin]
        _ = σ (zkE (E.alP S.j)) * σ ((1 : K21) + zkE E.al * zkE S.d) := by rw [RingHom.map_mul]
        _ = σ (zkE (E.alP S.j)) * (σ (1 : K21) + σ (zkE E.al) * σ (zkE S.d)) := by
          simp [RingHom.map_add, RingHom.map_mul]
        _ = σ ((zkE E.al) ^ S.j) * ((1 : Kw) + π * δ) := by
          simp [hπ_def, hδ_def, FurioLombardo.Discharge.SelmerBasis.EisData.ok_alP hW.ok S.j hj]
        _ = π ^ S.j * ((1 : Kw) + π * δ) := by rw [RingHom.map_pow]
    rw [h_evK_r0]
    exact hs_norm
  exact ⟨s, h_goal1, h_goal2⟩

variable (σ E) in
noncomputable def rho (hW : WPlace σ E) {S : RhoData} (hS : S.ok E = true) : Kw :=
  (exists_rho hW hS).choose

theorem rho_sq (hW : WPlace σ E) {S : RhoData} (hS : S.ok E = true) :
    3 * rho σ E hW hS ^ 2 = -σ epsK :=
  (exists_rho hW hS).choose_spec.1

theorem rho_near (hW : WPlace σ E) {S : RhoData} (hS : S.ok E = true) :
    ‖rho σ E hW hS - σ (evK (S.r0 E))‖ ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) :=
  (exists_rho hW hS).choose_spec.2

variable (Kw) in
/-- The image `(2 ζ - 1) ρ` of `ω`. -/
noncomputable def omU (ρ : Kw) : QF Kw (-1) 1 := (2 * cZ1 Kw - 1) * algebraMap Kw (QF Kw (-1) 1) ρ

theorem omU_sq_aux_sqzeta {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw] [Fact (∀ r : Kw, r ^ 2 ≠ -1 + 1 * r)] :
    (2 * cZ1 Kw - 1) ^ 2 = (-3 : QF Kw (-1) 1) := by
  calc
    (2 * cZ1 Kw - 1) ^ 2 = 4 * (cZ1 Kw) ^ 2 - 4 * cZ1 Kw + 1 := by ring
    _ = 4 * (cZ1 Kw - 1) - 4 * cZ1 Kw + 1 := by
      rw [pow_two, cZ1_mul_cZ1 (Kw := Kw)]
    _ = -3 := by ring


theorem omU_sq {ρ : Kw} (h : 3 * ρ ^ 2 = -σ epsK) :
    omU Kw ρ * omU Kw ρ = ((algebraMap Kw (QF Kw (-1) 1)).comp σ) epsK +
      ((algebraMap Kw (QF Kw (-1) 1)).comp σ) 0 * omU Kw ρ := by
  have h_sq : omU Kw ρ * omU Kw ρ = (-3 : QF Kw (-1) 1) * ((algebraMap Kw (QF Kw (-1) 1)) ρ) ^ 2 := by
    dsimp [omU]
    calc
      ((2 * cZ1 Kw - 1) * algebraMap Kw (QF Kw (-1) 1) ρ) * ((2 * cZ1 Kw - 1) * algebraMap Kw (QF Kw (-1) 1) ρ)
          = (2 * cZ1 Kw - 1) ^ 2 * (algebraMap Kw (QF Kw (-1) 1) ρ) ^ 2 := by ring
      _ = (-3 : QF Kw (-1) 1) * (algebraMap Kw (QF Kw (-1) 1) ρ) ^ 2 := by rw [omU_sq_aux_sqzeta]
  have h_map : (3 : QF Kw (-1) 1) * ((algebraMap Kw (QF Kw (-1) 1)) ρ) ^ 2 = -(algebraMap Kw (QF Kw (-1) 1)) (σ epsK) := by
    have := congrArg (algebraMap Kw (QF Kw (-1) 1)) h
    simpa [map_mul, map_pow, map_neg, map_ofNat] using this
  calc
    omU Kw ρ * omU Kw ρ = (-3 : QF Kw (-1) 1) * ((algebraMap Kw (QF Kw (-1) 1)) ρ) ^ 2 := h_sq
    _ = -((3 : QF Kw (-1) 1) * ((algebraMap Kw (QF Kw (-1) 1)) ρ) ^ 2) := by ring
    _ = -(-(algebraMap Kw (QF Kw (-1) 1)) (σ epsK)) := by rw [h_map]
    _ = algebraMap Kw (QF Kw (-1) 1) (σ epsK) := by ring
    _ = ((algebraMap Kw (QF Kw (-1) 1)).comp σ) epsK := rfl
    _ = ((algebraMap Kw (QF Kw (-1) 1)).comp σ) epsK + 0 := by ring
    _ = ((algebraMap Kw (QF Kw (-1) 1)).comp σ) epsK + ((algebraMap Kw (QF Kw (-1) 1)).comp σ) 0 * omU Kw ρ := by
      simp

variable (σ E) in
/-- **`L42 →+* F`**, `ω ↦ (2 ζ - 1) ρ`. -/
noncomputable def iL2 (hW : WPlace σ E) {S : RhoData} (hS : S.ok E = true) : L42 →+* QF Kw (-1) 1 :=
  qaLift ((algebraMap Kw (QF Kw (-1) 1)).comp σ) (omU Kw (rho σ E hW hS)) (omU_sq (rho_sq hW hS))

theorem iL2_apply (hW : WPlace σ E) {S : RhoData} (hS : S.ok E = true) (z : L42) :
    iL2 σ E hW hS z = algebraMap Kw (QF Kw (-1) 1) (σ z.re) +
      algebraMap Kw (QF Kw (-1) 1) (σ z.im) * omU Kw (rho σ E hW hS) := by
  rw [iL2, qaLift_apply]; rfl

theorem iL2_algebraMap (hW : WPlace σ E) {S : RhoData} (hS : S.ok E = true) (x : K21) :
    iL2 σ E hW hS (algebraMap K21 L42 x) = algebraMap Kw (QF Kw (-1) 1) (σ x) := by
  rw [iL2, qaLift_algebraMap]; rfl

theorem iL2_comp_algebraMap (hW : WPlace σ E) {S : RhoData} (hS : S.ok E = true) :
    (iL2 σ E hW hS).comp (algebraMap K21 L42) = (algebraMap Kw (QF Kw (-1) 1)).comp σ :=
  RingHom.ext fun x => iL2_algebraMap hW hS x

private theorem norm_omU_approx_aux1 (ρ r a b : Kw) :
    (algebraMap Kw (QF Kw (-1) 1) a + algebraMap Kw (QF Kw (-1) 1) b * omU Kw ρ) -
      QF.mk Kw (-1) 1 (a - b * r) (2 * (b * r)) =
      algebraMap Kw (QF Kw (-1) 1) (b * (ρ - r)) * (2 * cZ1 Kw - 1) := by
  set A := algebraMap Kw (QF Kw (-1) 1)
  have hA2 : A 2 = (2 : QF Kw (-1) 1) := by
    calc
      A 2 = A (1 + 1) := by norm_num
      _ = A 1 + A 1 := by rw [RingHom.map_add]
      _ = 1 + 1 := by rw [RingHom.map_one]
      _ = (2 : QF Kw (-1) 1) := by norm_num
  unfold omU
  simp only [map_mul, map_sub, qf_mk_eq_cZ1]
  rw [hA2]
  ring

private theorem norm_omU_approx_aux2 (hres : ∀ y : Kw, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) :
    ‖2 * cZ1 Kw - 1‖ ≤ 1 := by
  have h_eq : 2 * cZ1 Kw - 1 = QF.mk Kw (-1) 1 (-1) 2 := by
    rw [qf_mk_eq_cZ1 (-1) 2]
    have h2 : algebraMap Kw (QF Kw (-1) 1) 2 = (2 : QF Kw (-1) 1) := by
      calc
        algebraMap Kw (QF Kw (-1) 1) 2 = algebraMap Kw (QF Kw (-1) 1) (1 + 1) := by norm_num
        _ = algebraMap Kw (QF Kw (-1) 1) 1 + algebraMap Kw (QF Kw (-1) 1) 1 := by rw [RingHom.map_add]
        _ = 1 + 1 := by rw [RingHom.map_one]
        _ = (2 : QF Kw (-1) 1) := by norm_num
    calc
      2 * cZ1 Kw - 1 = (-1) + 2 * cZ1 Kw := by ring
      _ = algebraMap Kw (QF Kw (-1) 1) (-1) + algebraMap Kw (QF Kw (-1) 1) 2 * cZ1 Kw := by
        simp [RingHom.map_neg, RingHom.map_one, h2]
  rw [h_eq]
  rw [norm_mk1 hres (-1) 2]
  have h_norm_neg_one : ‖(-1 : Kw)‖ = 1 := by
    rw [norm_neg, norm_one]
  rw [h_norm_neg_one]
  have h_norm_two_le_one : ‖(2 : Kw)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one (R := Kw) (n := 2)
  rw [max_le_iff]
  exact ⟨le_refl 1, h_norm_two_le_one⟩



/-- The approximation of `alg a + alg b (2 ζ - 1) ρ` with `ρ ≈ r`. -/
theorem norm_omU_approx (hres : ∀ y : Kw, ‖y‖ ≤ 1 → ‖y‖ < 1 ∨ ‖y - 1‖ < 1) (ρ r a b : Kw) :
    ‖(algebraMap Kw (QF Kw (-1) 1) a + algebraMap Kw (QF Kw (-1) 1) b * omU Kw ρ) -
        QF.mk Kw (-1) 1 (a - b * r) (2 * (b * r))‖ ≤ ‖b‖ * ‖ρ - r‖ := by
  rw [norm_omU_approx_aux1 ρ r a b]
  rw [norm_mul]
  rw [QF.norm_algebraMap]
  rw [norm_mul]
  have h_nonneg : 0 ≤ ‖b‖ * ‖ρ - r‖ := by positivity
  exact mul_le_of_le_one_right h_nonneg (norm_omU_approx_aux2 hres)

theorem iL2_four_eN (hW : WPlace σ E) {S : RhoData} (hS : S.ok E = true) :
    iL2 σ E hW hS (4 * eN) = algebraMap Kw (QF Kw (-1) 1) (σ (2 * zkE eaL)) +
      algebraMap Kw (QF Kw (-1) 1) (σ (2 * zkE ebL)) * omU Kw (rho σ E hW hS) := by
  rw [← Tower.evL_e4LC, iL2_apply]
  have hre : (evL e4LC).re = 2 * zkE eaL := by
    simp [e4LC, evL, evK_mul, evK_int, evK_lin]
  have him : (evL e4LC).im = 2 * zkE ebL := by
    simp [e4LC, evL, evK_mul, evK_int, evK_lin]
  rw [hre, him]

/-- The approximate square root has norm `‖π‖^j`. -/
theorem norm_s0U (hW : WPlace σ E) {SR : RhoData} {S : SqrtU} (hS : S.ok E SR = true) :
    ‖toU1 σ (.lin S.s00) (.lin S.s01)‖ = ‖σ (zkE E.al)‖ ^ S.j := by
  unfold SqrtU.ok at hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hS
  have hnS : S.n < E.alPow.length := hS.1.1.1.1.1.1.1
  have hjS : S.j < E.alPow.length := hS.1.1.1.1.1.1.2
  have h2S : 2 * E.e + 2 * S.j < S.n := hS.1.1.1.1.1.2
  have hjSR : S.n + SR.j ≤ SR.n := hS.1.1.1.1.2
  have hS00 : checkK S.prec (.sub (.lin S.s00) (.mul (.lin (E.alP S.j)) (.add (.int 1) (.mul (.lin E.al) (.lin S.d0))))) = true := hS.1.1.1.2
  have hS01 : checkK S.prec (.sub (.lin S.s01) (.mul (.lin (E.alP S.j)) (.lin S.d1))) = true := hS.1.1.2
  have hj_lt : S.j < E.alPow.length := by simpa using hjS
  have h_alP := EisData.ok_alP hW.ok S.j hj_lt
  have h_s00_eq : zkE S.s00 = zkE E.al ^ S.j * (1 + zkE E.al * zkE S.d0) := by
    have h := evK_eq_of_check S.prec (.lin S.s00) (.mul (.lin (E.alP S.j)) (.add (.int 1) (.mul (.lin E.al) (.lin S.d0)))) hS00
    have hRHS : evK (.mul (.lin (E.alP S.j)) (.add (.int 1) (.mul (.lin E.al) (.lin S.d0)))) = zkE (E.alP S.j) * (1 + zkE E.al * zkE S.d0) := by
      simp only [evK_mul, evK_lin, evK_add, evK_int, Int.cast_one]
    simpa [evK_lin, hRHS, h_alP] using h
  have h_s01_eq : zkE S.s01 = zkE E.al ^ S.j * zkE S.d1 := by
    have h := evK_eq_of_check S.prec (.lin S.s01) (.mul (.lin (E.alP S.j)) (.lin S.d1)) hS01
    have hRHS : evK (.mul (.lin (E.alP S.j)) (.lin S.d1)) = zkE (E.alP S.j) * zkE S.d1 := by
      simp only [evK_mul, evK_lin, evK_add, evK_int, Int.cast_one]
    simpa [evK_lin, hRHS, h_alP] using h
  rw [toU1, evK_lin S.s00, evK_lin S.s01, h_s00_eq, h_s01_eq]
  rw [norm_mk1 hW.res]
  have h_norm_s00 : ‖σ (zkE E.al ^ S.j * (1 + zkE E.al * zkE S.d0))‖ = ‖σ (zkE E.al)‖ ^ S.j := by
    calc
      ‖σ (zkE E.al ^ S.j * (1 + zkE E.al * zkE S.d0))‖
          = ‖σ (zkE E.al ^ S.j) * σ (1 + zkE E.al * zkE S.d0)‖ := by
        simp [map_mul]
      _ = ‖σ (zkE E.al ^ S.j)‖ * ‖σ (1 + zkE E.al * zkE S.d0)‖ := by
        rw [norm_mul]
      _ = ‖σ (zkE E.al) ^ S.j‖ * ‖σ (1 + zkE E.al * zkE S.d0)‖ := by
        simp [map_pow]
      _ = ‖σ (zkE E.al)‖ ^ S.j * ‖σ (1 + zkE E.al * zkE S.d0)‖ := by
        simp [norm_pow]
      _ = ‖σ (zkE E.al)‖ ^ S.j * 1 := by
        have h_norm_unit : ‖σ (1 + zkE E.al * zkE S.d0)‖ = 1 := by
          have h_add : σ (1 + zkE E.al * zkE S.d0) = (1 : Kw) + σ (zkE E.al * zkE S.d0) := by
            simp [map_add, map_mul]
          rw [h_add]
          have h_norm_lt : ‖σ (zkE E.al * zkE S.d0)‖ < 1 := by
            calc
              ‖σ (zkE E.al * zkE S.d0)‖ = ‖σ (zkE E.al) * σ (zkE S.d0)‖ := by simp [map_mul]
              _ = ‖σ (zkE E.al)‖ * ‖σ (zkE S.d0)‖ := by rw [norm_mul]
              _ < 1 := by
                have hπ_lt_one : ‖σ (zkE E.al)‖ < 1 := hW.unif.norm_lt_one
                have hδ_le_one : ‖σ (zkE S.d0)‖ ≤ 1 := hW.int S.d0
                have h_nonneg : 0 ≤ ‖σ (zkE E.al)‖ := norm_nonneg _
                have hδ_nonneg : 0 ≤ ‖σ (zkE S.d0)‖ := norm_nonneg _
                nlinarith
          have h_ne : ‖(1 : Kw)‖ ≠ ‖σ (zkE E.al * zkE S.d0)‖ := by
            rw [norm_one]
            exact (ne_of_lt h_norm_lt).symm
          rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h_ne, norm_one, max_eq_left]
          exact le_of_lt h_norm_lt
        rw [h_norm_unit]
      _ = ‖σ (zkE E.al)‖ ^ S.j := by simp
  have h_norm_s01 : ‖σ (zkE E.al ^ S.j * zkE S.d1)‖ ≤ ‖σ (zkE E.al)‖ ^ S.j := by
    calc
      ‖σ (zkE E.al ^ S.j * zkE S.d1)‖ = ‖σ (zkE E.al ^ S.j) * σ (zkE S.d1)‖ := by simp [map_mul]
      _ = ‖σ (zkE E.al ^ S.j)‖ * ‖σ (zkE S.d1)‖ := by rw [norm_mul]
      _ = ‖σ (zkE E.al) ^ S.j‖ * ‖σ (zkE S.d1)‖ := by simp [map_pow]
      _ = ‖σ (zkE E.al)‖ ^ S.j * ‖σ (zkE S.d1)‖ := by simp [norm_pow]
      _ ≤ ‖σ (zkE E.al)‖ ^ S.j * 1 := by
        have h_nonneg : 0 ≤ ‖σ (zkE E.al)‖ ^ S.j := by
          apply pow_nonneg (norm_nonneg _) _
        nlinarith [hW.int S.d1]
      _ = ‖σ (zkE E.al)‖ ^ S.j := by simp
  rw [h_norm_s00]
  exact max_eq_left h_norm_s01

/-- `s0² - iL2 (4 eN)` is small. -/
theorem norm_s0U_sq_sub (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true) {S : SqrtU}
    (hS : S.ok E SR = true) :
    ‖toU1 σ (.lin S.s00) (.lin S.s01) ^ 2 - iL2 σ E hW hSR (4 * eN)‖ ≤ ‖σ (zkE E.al)‖ ^ S.n := by
  have hS' := hS
  simp only [SqrtU.ok, Bool.and_eq_true, decide_eq_true_eq] at hS'
  obtain ⟨⟨⟨⟨⟨⟨⟨hnl, -⟩, -⟩, hnj⟩, -⟩, -⟩, c3⟩, c4⟩ := hS'
  have hSR' := hSR
  simp only [RhoData.ok, Bool.and_eq_true, decide_eq_true_eq] at hSR'
  have hR : 2 * E.e + 2 * SR.j < SR.n := hSR'.1.2
  have halP := EisData.ok_alP hW.ok
  have e3 := congrArg (fun x => algebraMap Kw (QF Kw (-1) 1) (σ x)) (evK_eq_of_check _ _ _ c3)
  have e4 := congrArg (fun x => algebraMap Kw (QF Kw (-1) 1) (σ x)) (evK_eq_of_check _ _ _ c4)
  simp only [evK_sub, evK_add, evK_mul, evK_lin, evK_int, halP _ hnl, map_sub, map_add, map_mul,
    map_pow, map_intCast, Int.cast_ofNat, map_ofNat] at e3 e4
  have hkey : toU1 σ (.lin S.s00) (.lin S.s01) ^ 2 - iL2 σ E hW hSR (4 * eN) =
      QF.mk Kw (-1) 1 (σ (zkE E.al) ^ S.n * σ (zkE S.R0)) (σ (zkE E.al) ^ S.n * σ (zkE S.R1)) +
      algebraMap Kw (QF Kw (-1) 1) (2 * σ (zkE ebL) * (rho σ E hW hSR - σ (evK (SR.r0 E)))) *
        -(2 * cZ1 Kw - 1) := by
    rw [iL2_four_eN, toU1, omU]
    simp only [qf_mk_eq_cZ1, evK_lin, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg]
    have h := cZ1_mul_cZ1 (Kw := Kw)
    linear_combination e3 + cZ1 Kw * e4 + algebraMap Kw (QF Kw (-1) 1) (σ (zkE S.s01)) ^ 2 * h
  rw [hkey]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mk1 hW.res]
    refine max_le ?_ ?_ <;> rw [norm_mul, norm_pow] <;>
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hW.int _)
  · rw [norm_mul, norm_neg, QF.norm_algebraMap]
    refine (mul_le_of_le_one_right (norm_nonneg _) (norm_omU_approx_aux2 hW.res)).trans ?_
    rw [norm_mul, norm_mul, hW.two]
    have hρ := rho_near hW hSR
    calc ‖σ (zkE E.al)‖ ^ E.e * ‖σ (zkE ebL)‖ * ‖rho σ E hW hSR - σ (evK (SR.r0 E))‖
        ≤ ‖σ (zkE E.al)‖ ^ E.e * 1 * ‖σ (zkE E.al)‖ ^ (SR.n - E.e - SR.j) := by
          gcongr
          exact hW.int _
      _ = ‖σ (zkE E.al)‖ ^ (SR.n - SR.j) := by
          rw [mul_one, ← pow_add]; congr 1; omega
      _ ≤ ‖σ (zkE E.al)‖ ^ S.n :=
          pow_le_pow_of_le_one (norm_nonneg _) hW.unif.norm_lt_one.le (by omega)

/-- The product approximation in an ultrametric field. -/
theorem norm_approx_prod {F : Type*} [NormedField F] [IsUltrametricDist F] {a A x X s s0 c : F} {B : ℝ}
    (hB : B ≤ 1) (ha : ‖a - A‖ ≤ B) (hx : ‖x - X‖ ≤ B) (hs : ‖s - s0‖ ≤ B) (hX : ‖X‖ ≤ 1)
    (hs0 : ‖s0‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ‖(a + c * (x * s)) - (A + c * (X * s0))‖ ≤ B := by
  have hB_nonneg : 0 ≤ B := by
    have h := norm_nonneg (a - A)
    linarith
  have hs_norm : ‖s‖ ≤ 1 := by
    have h_eq : s = s0 + (s - s0) := by ring
    rw [h_eq]
    have h_ultra := IsUltrametricDist.norm_add_le_max s0 (s - s0)
    refine le_trans h_ultra ?_
    have h_max : max ‖s0‖ ‖s - s0‖ ≤ 1 :=
      max_le hs0 (le_trans hs hB)
    exact h_max
  have h_eq : (a + c * (x * s)) - (A + c * (X * s0)) = (a - A) + c * ((x - X) * s + X * (s - s0)) := by
    ring
  rw [h_eq]
  have h_ultra1 := IsUltrametricDist.norm_add_le_max (a - A) (c * ((x - X) * s + X * (s - s0)))
  refine le_trans h_ultra1 ?_
  have h_max2 : max ‖a - A‖ ‖c * ((x - X) * s + X * (s - s0))‖ ≤ B := by
    refine max_le ha ?_
    rw [norm_mul]
    have h_inner : ‖(x - X) * s + X * (s - s0)‖ ≤ B := by
      have h_ultra2 := IsUltrametricDist.norm_add_le_max ((x - X) * s) (X * (s - s0))
      refine le_trans h_ultra2 ?_
      have h_max3 : max ‖(x - X) * s‖ ‖X * (s - s0)‖ ≤ B := by
        refine max_le ?_ ?_
        · rw [norm_mul]
          calc
            ‖x - X‖ * ‖s‖ ≤ B * ‖s‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
            _ ≤ B * 1 := mul_le_mul_of_nonneg_left hs_norm hB_nonneg
            _ = B := mul_one _
        · rw [norm_mul]
          calc
            ‖X‖ * ‖s - s0‖ ≤ 1 * ‖s - s0‖ := mul_le_mul_of_nonneg_right hX (norm_nonneg _)
            _ ≤ 1 * B := mul_le_mul_of_nonneg_left hs (by linarith)
            _ = B := one_mul _
      exact h_max3
    calc
      ‖c‖ * ‖(x - X) * s + X * (s - s0)‖ ≤ 1 * ‖(x - X) * s + X * (s - s0)‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 1 * B := mul_le_mul_of_nonneg_left h_inner (by linarith)
      _ = B := one_mul _
  exact h_max2

theorem norm_iL2_evL_sub (hW : WPlace σ E) {S : RhoData} (hS : S.ok E = true) (t : LC) :
    ‖iL2 σ E hW hS (evL t) - toU1 σ (X0L2 E S t) (X1L2 E S t)‖ ≤
      ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := by
  have h_apply := iL2_apply hW hS (evL t)
  rw [h_apply]
  have h_evL_re : (evL t).re = evK t.1 := rfl
  have h_evL_im : (evL t).im = evK t.2 := rfl
  rw [h_evL_re, h_evL_im]
  unfold toU1 X0L2 X1L2
  simp only [evK_sub, evK_mul, evK_int, map_sub, map_mul]
  have h_approx := norm_omU_approx hW.res (rho σ E hW hS) (σ (evK (S.r0 E))) (σ (evK t.1)) (σ (evK t.2))
  have h_le_one : ‖σ (evK t.2)‖ ≤ 1 := norm_evK_le_one σ hW.int t.2
  have h_rho_near : ‖rho σ E hW hS - σ (evK (S.r0 E))‖ ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := rho_near hW hS
  have h_nonneg : 0 ≤ ‖σ (evK t.2)‖ := norm_nonneg _
  have h_pow_nonneg : 0 ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := by
    apply pow_nonneg (norm_nonneg _) _
  have h_bound : ‖σ (evK t.2)‖ * ‖rho σ E hW hS - σ (evK (S.r0 E))‖ ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := by
    calc
      ‖σ (evK t.2)‖ * ‖rho σ E hW hS - σ (evK (S.r0 E))‖ ≤
          ‖σ (evK t.2)‖ * ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) :=
        mul_le_mul_of_nonneg_left h_rho_near h_nonneg
      _ ≤ 1 * ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) :=
        mul_le_mul_of_nonneg_right h_le_one h_pow_nonneg
      _ = ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := by simp
  have hgoal := le_trans h_approx h_bound
  -- hgoal has `2 * ...` but goal has `σ 2 * ...`; we rewrite `σ 2` to `2` in the goal
  have h_sigma2 : σ (2 : K21) = (2 : Kw) := by
    simpa using map_natCast σ 2
  simpa [h_sigma2] using hgoal

/-! ## `N84 →+* F` -/

theorem exists_sU [ProperSpace Kw] (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true) {S : SqrtU}
    (hS : S.ok E SR = true) :
    ∃ s : QF Kw (-1) 1, s ^ 2 = iL2 σ E hW hSR (4 * eN) ∧
      ‖s - toU1 σ (.lin S.s00) (.lin S.s01)‖ ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := by
  have hS' := hS
  simp only [SqrtU.ok, Bool.and_eq_true, decide_eq_true_eq] at hS'
  have hn : 2 * E.e + 2 * S.j < S.n := hS'.1.1.1.1.1.2
  have hπ0 : 0 < ‖σ (zkE E.al)‖ := norm_pos_iff.mpr hW.unif.ne_zero
  have hπ1 : ‖σ (zkE E.al)‖ < 1 := hW.unif.norm_lt_one
  have hs0 : ‖toU1 σ (.lin S.s00) (.lin S.s01)‖ = ‖σ (zkE E.al)‖ ^ S.j := norm_s0U hW hS
  have hsq := norm_s0U_sq_sub hW hSR hS
  have h2 : ‖(2 : QF Kw (-1) 1)‖ = ‖σ (zkE E.al)‖ ^ E.e := by
    rw [show (2 : QF Kw (-1) 1) = algebraMap Kw (QF Kw (-1) 1) 2 from (map_ofNat _ 2).symm,
      QF.norm_algebraMap, hW.two]
  have h2s0 : ‖2 * toU1 σ (.lin S.s00) (.lin S.s01)‖ = ‖σ (zkE E.al)‖ ^ (E.e + S.j) := by
    rw [norm_mul, h2, hs0, pow_add]
  have hs0le : ‖toU1 σ (.lin S.s00) (.lin S.s01)‖ ≤ 1 := by
    rw [hs0]; exact pow_le_one₀ hπ0.le hπ1.le
  have hz : ‖iL2 σ E hW hSR (4 * eN)‖ ≤ 1 := by
    have e : iL2 σ E hW hSR (4 * eN) = toU1 σ (.lin S.s00) (.lin S.s01) ^ 2 -
        (toU1 σ (.lin S.s00) (.lin S.s01) ^ 2 - iL2 σ E hW hSR (4 * eN)) := by ring
    rw [e, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hs0le
    · rw [norm_neg]; exact hsq.trans (pow_le_one₀ hπ0.le hπ1.le)
  have hlt : ‖toU1 σ (.lin S.s00) (.lin S.s01) ^ 2 - iL2 σ E hW hSR (4 * eN)‖ <
      ‖2 * toU1 σ (.lin S.s00) (.lin S.s01)‖ ^ 2 := by
    rw [h2s0, ← pow_mul]
    exact hsq.trans_lt (pow_lt_pow_right_of_lt_one₀ hπ0 hπ1 (by omega))
  obtain ⟨s, hs, hsn⟩ := exists_sqrt_near hz hs0le hlt
  refine ⟨s, hs, hsn.trans ?_⟩
  rw [h2s0, div_le_iff₀ (pow_pos hπ0 _), ← pow_add,
    show S.n - E.e - S.j + (E.e + S.j) = S.n by omega]
  exact hsq

variable (σ E) in
noncomputable def sU [ProperSpace Kw] (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true)
    {S : SqrtU} (hS : S.ok E SR = true) : QF Kw (-1) 1 :=
  (exists_sU hW hSR hS).choose

theorem sU_sq [ProperSpace Kw] (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true) {S : SqrtU}
    (hS : S.ok E SR = true) : sU σ E hW hSR hS ^ 2 = iL2 σ E hW hSR (4 * eN) :=
  (exists_sU hW hSR hS).choose_spec.1

theorem sU_near [ProperSpace Kw] (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true) {S : SqrtU}
    (hS : S.ok E SR = true) :
    ‖sU σ E hW hSR hS - toU1 σ (.lin S.s00) (.lin S.s01)‖ ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) :=
  (exists_sU hW hSR hS).choose_spec.2

theorem half_sq_of_sq {F : Type*} [Field F] {z s : F} (h2 : (2 : F) ≠ 0) (h : s ^ 2 = 4 * z)
    (b : Bool) :
    ((if b then 1 else -1) * s / 2) * ((if b then 1 else -1) * s / 2) = z + 0 * ((if b then 1 else -1) * s / 2) := by
  simp
  field_simp [h2]
  cases b <;> simp <;> linear_combination h

theorem two_ne_zero_U1 (hW : WPlace σ E) : (2 : QF Kw (-1) 1) ≠ 0 := by
  have h2Kw : (2 : Kw) ≠ 0 := by
    intro hzero
    have hnorm0 : ‖(2 : Kw)‖ = 0 := by simp [hzero]
    have hnorm_eq : ‖(2 : Kw)‖ = ‖σ (zkE E.al)‖ ^ E.e := hW.two
    rw [hnorm0] at hnorm_eq
    have hnorm_pow_zero : ‖σ (zkE E.al)‖ ^ E.e = 0 := by
      symm; exact hnorm_eq
    have hnorm_zero : ‖σ (zkE E.al)‖ = 0 := by
      contrapose! hnorm_pow_zero
      exact pow_ne_zero E.e hnorm_pow_zero
    have hzero' : σ (zkE E.al) = 0 := norm_eq_zero.mp hnorm_zero
    exact hW.unif.ne_zero hzero'
  exact (map_ne_zero (algebraMap Kw (QF Kw (-1) 1))).mpr h2Kw

theorem half_sU_sq [ProperSpace Kw] (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true) {S : SqrtU}
    (hS : S.ok E SR = true) (b : Bool) :
    ((if b then 1 else -1) * sU σ E hW hSR hS / 2) * ((if b then 1 else -1) * sU σ E hW hSR hS / 2) =
      iL2 σ E hW hSR eN + iL2 σ E hW hSR 0 * ((if b then 1 else -1) * sU σ E hW hSR hS / 2) := by
  rw [map_zero]
  exact half_sq_of_sq (two_ne_zero_U1 hW) (by rw [sU_sq, map_mul, map_ofNat]) b

variable (σ E) in
/-- **`N84 →+* F`**, `ω_N ↦ ± sU / 2` (`b = true`: `+`). -/
noncomputable def iN2 [ProperSpace Kw] (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true)
    {S : SqrtU} (hS : S.ok E SR = true) (b : Bool) : N84 →+* QF Kw (-1) 1 :=
  qaLift (iL2 σ E hW hSR) ((if b then 1 else -1) * sU σ E hW hSR hS / 2) (half_sU_sq hW hSR hS b)

theorem iN2_apply [ProperSpace Kw] (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true) {S : SqrtU}
    (hS : S.ok E SR = true) (b : Bool) (z : N84) :
    iN2 σ E hW hSR hS b z =
      iL2 σ E hW hSR z.re + iL2 σ E hW hSR z.im * ((if b then 1 else -1) * sU σ E hW hSR hS / 2) :=
  rfl

theorem iN2_algebraMap [ProperSpace Kw] (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true)
    {S : SqrtU} (hS : S.ok E SR = true) (b : Bool) (x : K21) :
    iN2 σ E hW hSR hS b (algebraMap K21 N84 x) = algebraMap Kw (QF Kw (-1) 1) (σ x) := by
  rw [Tower.algebraMap_N84, iN2_apply]
  simp only [map_zero, zero_mul, add_zero]
  exact iL2_algebraMap hW hSR x

theorem iN2_comp_algebraMap [ProperSpace Kw] (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true)
    {S : SqrtU} (hS : S.ok E SR = true) (b : Bool) :
    (iN2 σ E hW hSR hS b).comp (algebraMap K21 N84) = (algebraMap Kw (QF Kw (-1) 1)).comp σ :=
  RingHom.ext fun x => iN2_algebraMap hW hSR hS b x

theorem toU1_XN2 (SR : RhoData) (S : SqrtU) (t : NC) (b : Bool) :
    toU1 σ (X0N2 E SR S t b) (X1N2 E SR S t b) =
      toU1 σ (X0L2 E SR t.1) (X1L2 E SR t.1) + (if b then 1 else -1) *
        (toU1 σ (X0L2 E SR t.2) (X1L2 E SR t.2) * toU1 σ (.lin S.s00) (.lin S.s01)) := by
  have h := cZ1_mul_cZ1 (Kw := Kw)
  cases b
  · simp only [toU1, X0N2, X1N2, qf_mk_eq_cZ1, evK_add, evK_sub, evK_mul, evK_lin, evK_int, map_add,
      map_sub, map_mul, Bool.false_eq_true, ite_false, Int.cast_one, Int.cast_neg,
      map_one, map_neg]
    linear_combination (algebraMap Kw (QF Kw (-1) 1) (σ (evK (X1L2 E SR t.2))) *
      algebraMap Kw (QF Kw (-1) 1) (σ (zkE S.s01))) * h
  · simp only [toU1, X0N2, X1N2, qf_mk_eq_cZ1, evK_add, evK_sub, evK_mul, evK_lin, evK_int, map_add,
      map_sub, map_mul, ite_true, Int.cast_one, map_one]
    linear_combination (-(algebraMap Kw (QF Kw (-1) 1) (σ (evK (X1L2 E SR t.2))) *
      algebraMap Kw (QF Kw (-1) 1) (σ (zkE S.s01)))) * h

theorem iN2_evN [ProperSpace Kw] (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true) {S : SqrtU}
    (hS : S.ok E SR = true) (b : Bool) (t : NC) :
    iN2 σ E hW hSR hS b (evN t) = iL2 σ E hW hSR (evL t.1) + (if b then 1 else -1) *
      (iL2 σ E hW hSR (evL t.2) * sU σ E hW hSR hS) := by
  simp [iN2, qaLift, evN, evL]
  have h2 : (2 : QF Kw (-1) 1) ≠ 0 := two_ne_zero_U1 hW
  field_simp [h2]
  have h_smul : { re := 2 * evK t.2.1, im := 2 * evK t.2.2 } = (2 : L42) * { re := evK t.2.1, im := evK t.2.2 } := by
    ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      show QuadraticAlgebra.re (2 : L42) = (2 : K21) by rfl,
      show QuadraticAlgebra.im (2 : L42) = (0 : K21) by rfl]
  have h_eq : (iL2 σ E hW hSR) { re := 2 * evK t.2.1, im := 2 * evK t.2.2 } =
      (2 : QF Kw (-1) 1) * (iL2 σ E hW hSR) { re := evK t.2.1, im := evK t.2.2 } := by
    rw [h_smul, map_mul]
    have h2 : (iL2 σ E hW hSR) (2 : L42) = (2 : QF Kw (-1) 1) := by
      simpa using map_natCast (iL2 σ E hW hSR) 2
    rw [h2]
  simp [h_eq, mul_comm, mul_left_comm]

theorem norm_iN2_evN_sub [ProperSpace Kw] (hW : WPlace σ E) {SR : RhoData} (hSR : SR.ok E = true)
    {S : SqrtU} (hS : S.ok E SR = true) (b : Bool) (t : NC) :
    ‖iN2 σ E hW hSR hS b (evN t) - toU1 σ (X0N2 E SR S t b) (X1N2 E SR S t b)‖ ≤
      ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) := by
  have hS' := hS
  simp only [SqrtU.ok, Bool.and_eq_true, decide_eq_true_eq] at hS'
  have hjn : S.n + SR.j ≤ SR.n := hS'.1.1.1.1.2
  have hπ1 : ‖σ (zkE E.al)‖ ≤ 1 := hW.unif.norm_lt_one.le
  have hmono : ‖σ (zkE E.al)‖ ^ (SR.n - E.e - SR.j) ≤ ‖σ (zkE E.al)‖ ^ (S.n - E.e - S.j) :=
    pow_le_pow_of_le_one (norm_nonneg _) hπ1 (by omega)
  rw [iN2_evN, toU1_XN2]
  refine norm_approx_prod (pow_le_one₀ (norm_nonneg _) hπ1)
    ((norm_iL2_evL_sub hW hSR t.1).trans hmono) ((norm_iL2_evL_sub hW hSR t.2).trans hmono)
    (sU_near hW hSR hS) (norm_toU1_le_one hW.int hW.res _ _)
    ((norm_s0U hW hS).le.trans (pow_le_one₀ (norm_nonneg _) hπ1)) ?_
  cases b <;> simp

end Place

end FurioLombardo.Discharge.SelmerBasis.W2U
