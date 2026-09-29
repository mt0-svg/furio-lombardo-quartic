import FurioLombardo.Discharge.SelmerBasis.PlaceWElem

/-!
# Rows over three components and the standard basis at a w-place

* over `G = Fin 3 → Fˣ`, the basis `bG` (`bF i` at component `c`, position `n c + i`),
  `isSquare_mul_rows` (from one square certificate per component to a square in `G`) and
  `indep_rows` (independence in `G` from independence at one component);
* at a component `CF σ E`, the unit data of the standard basis `bF` (`dfact_bF`), their echelon
  (`echelonOK_std`) and the independence of `bF` modulo squares (`bF_indep`).
-/

set_option linter.unusedSectionVars false

namespace FurioLombardo.Discharge.SelmerBasis

open Polynomial FurioLombardo.M1 FurioLombardo.M1.Kron FurioLombardo.Discharge.M3a
  FurioLombardo.Discharge.M3b FurioLombardo.Discharge.SelmerBasis.Tower

/-! ## Rows over three components -/

section Rows

variable {F : Type*} [Field F] (n : ℕ) (bF : ℕ → F) (hb : ∀ i, bF i ≠ 0)

/-- The basis of `G = Fin 3 → Fˣ`: `bF i` at component `c`, position `n c + i`. -/
noncomputable def bG : Fin (3 * n) → Fin 3 → Fˣ := fun l =>
  Pi.mulSingle (finProdFinEquiv.symm l).1 (Units.mk0 (bF (finProdFinEquiv.symm l).2) (hb _))

variable {n bF hb}

/-- **Squares in `G` from squares at the components.** If `x c · ∏_i bF i ^ (bit (n c + i) of A)`
is a square in `F` for each component `c`, then `x · ∏ bG ^ bits A` is a square in `G`. -/
theorem isSquare_mul_rows (x : Fin 3 → Fˣ) (A : ℕ)
    (h : ∀ c : Fin 3, IsSquare ((x c : F) * ∏ i : Fin n, bF i ^ (bitv n (A >>> (n * (c : ℕ))) i).val)) :
    IsSquare (x * ∏ l : Fin (3 * n), bG n bF hb l ^ (bitv (3 * n) A l).val) := by
  let P := ∏ l : Fin (3 * n), bG n bF hb l ^ (bitv (3 * n) A l).val
  have hP_val : ∀ c : Fin 3, ((P c : Fˣ) : F) = ∏ i : Fin n, bF i ^ (bitv n (A >>> (n * (c : ℕ))) i).val := by
    intro c
    have hprod := prod_mulSingle_bits (g := λ i : Fin n => Units.mk0 (bF i) (hb i)) (A := A) (j := c)
    have htemp : ((P c : Fˣ) : F) = (∏ i : Fin n, (Units.mk0 (bF i) (hb i)) ^ (bitv n (A >>> (n * (c : ℕ))) i).val : F) := by
      simpa [bG, P] using congrArg (λ (u : Fˣ) => (u : F)) hprod
    simpa [Units.val_pow_eq_pow_val, Units.val_mk0] using htemp
  have h_sq_comp : ∀ c : Fin 3, IsSquare ((x * P) c) := by
    intro c
    have h_val : (((x * P) c : Fˣ) : F) = (x c : F) * ∏ i : Fin n, bF i ^ (bitv n (A >>> (n * (c : ℕ))) i).val := by
      simp [Pi.mul_apply, hP_val c]
    have h_sq_F : IsSquare (((x * P) c : Fˣ) : F) := by
      rw [h_val]
      exact h c
    exact isSquare_units_of_isSquare ((x * P) c) h_sq_F
  have h_exists : ∃ r : Fin 3 → Fˣ, x * P = r * r := by
    have h_choice : ∀ c : Fin 3, ∃ r : Fˣ, (x * P) c = r * r := h_sq_comp
    let r : Fin 3 → Fˣ := λ c => (h_choice c).choose
    refine ⟨r, funext λ c => (h_choice c).choose_spec⟩
  exact h_exists

/-- **Independence in `G` from independence at one component.** -/
theorem indep_rows (h1 : ∀ ε : Fin n → ZMod 2, IsSquare (∏ i : Fin n, bF i ^ (ε i).val) → ε = 0) :
    ∀ ε : Fin (3 * n) → ZMod 2, IsSquare (∏ l, bG n bF hb l ^ (ε l).val) → ε = 0 := by
  intro ε hsq
  rcases hsq with ⟨r, hr⟩
  ext l
  set c := (finProdFinEquiv.symm l).1 with hc
  set i := (finProdFinEquiv.symm l).2 with hi
  have hl : l = finProdFinEquiv (c, i) := by
    calc
      l = finProdFinEquiv (finProdFinEquiv.symm l) := (Equiv.apply_symm_apply finProdFinEquiv l).symm
      _ = finProdFinEquiv (c, i) := by simp [hc, hi]
  have h_prod_reindex : (∏ l : Fin (3 * n), bG n bF hb l ^ (ε l).val) =
      (∏ p : Fin 3 × Fin n, bG n bF hb (finProdFinEquiv p) ^ (ε (finProdFinEquiv p)).val) := by
    have h := Finset.prod_equiv (s := Finset.univ) (t := Finset.univ)
      (f := fun (p : Fin 3 × Fin n) => bG n bF hb (finProdFinEquiv p) ^ (ε (finProdFinEquiv p)).val)
      (g := fun (l : Fin (3 * n)) => bG n bF hb l ^ (ε l).val)
      finProdFinEquiv
      (by intro p; exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
      (by intro p hp; rfl)
    simpa using h.symm
  have h_eval_c := congrArg (fun f : Fin 3 → Fˣ => f c) hr
  simp_rw [h_prod_reindex, Finset.prod_apply] at h_eval_c
  simp_rw [Pi.pow_apply] at h_eval_c
  simp_rw [bG, Pi.mulSingle_apply] at h_eval_c
  simp_rw [Equiv.symm_apply_apply] at h_eval_c
  rw [Fintype.prod_prod_type] at h_eval_c
  have h_others : ∀ c' : Fin 3, c' ≠ c → (∏ i' : Fin n, ((if c = c' then Units.mk0 (bF i') (hb i') else 1)) ^ (ε (finProdFinEquiv (c', i'))).val) = 1 := by
    intro c' hc'
    apply Finset.prod_eq_one
    intro i' hi'
    simp [Ne.symm hc']
  have h_prod_single : (∏ c' : Fin 3, (∏ i' : Fin n, ((if c = c' then Units.mk0 (bF i') (hb i') else 1)) ^ (ε (finProdFinEquiv (c', i'))).val)) =
      (∏ i' : Fin n, Units.mk0 (bF i') (hb i') ^ (ε (finProdFinEquiv (c, i'))).val) := by
    have h_single := Finset.prod_eq_single (s := Finset.univ) (f := fun (c' : Fin 3) => (∏ i' : Fin n, ((if c = c' then Units.mk0 (bF i') (hb i') else 1)) ^ (ε (finProdFinEquiv (c', i'))).val)) c
      (fun c' hc' hne => by
        apply Finset.prod_eq_one
        intro i' hi'
        simp [Ne.symm hne])
      (fun h => by exfalso; exact h (Finset.mem_univ c))
    simpa [show c = c from rfl] using h_single
  rw [h_prod_single] at h_eval_c
  have h_square : IsSquare (∏ i' : Fin n, bF i' ^ (ε (finProdFinEquiv (c, i'))).val) := by
    refine ⟨(r c).val, ?_⟩
    calc
      ∏ i' : Fin n, bF i' ^ (ε (finProdFinEquiv (c, i'))).val =
          ∏ i' : Fin n, ((Units.mk0 (bF i') (hb i')) ^ (ε (finProdFinEquiv (c, i'))).val).val := by
        simp [Units.val_pow_eq_pow_val, Units.val_mk0]
      _ = (∏ i' : Fin n, (Units.mk0 (bF i') (hb i')) ^ (ε (finProdFinEquiv (c, i'))).val).val := by
        simp
      _ = ((r * r) c).val := by rw [h_eval_c]
      _ = ((r c) * (r c)).val := by rw [Pi.mul_apply]
      _ = (r c).val * (r c).val := by simp [Units.val_mul]
  have h_eps_c_zero : (fun i' : Fin n => ε (finProdFinEquiv (c, i'))) = 0 :=
    h1 (fun i' => ε (finProdFinEquiv (c, i'))) h_square
  have h_eps_l_zero : ε (finProdFinEquiv (c, i)) = 0 := by
    simpa using congrFun h_eps_c_zero i
  rw [hl]
  exact h_eps_l_zero

end Rows

/-! ## Bits -/

theorem bitv_mod_two_pow (n a : ℕ) : bitv n (a % 2 ^ n) = bitv n a := by
  funext j
  unfold bitv
  have htest : (a % 2 ^ n).testBit (j : ℕ) = a.testBit (j : ℕ) := by
    rw [Nat.testBit_mod_two_pow a n (j : ℕ)]
    simp [j.is_lt]
  rw [htest]

theorem prod_bitv_zero {M : Type*} [CommMonoid M] (n : ℕ) (g : Fin n → M) :
    ∏ i : Fin n, g i ^ (bitv n 0 i).val = 1 := by
  simp [bitv]

theorem dyGen_ne_zero {F : Type*} [NormedField F] {π : F} (hπ : NormUnif π) (i : ℕ) : dyGen π i ≠ 0 := by
  unfold dyGen
  split
  · exact hπ.ne_zero
  · case isFalse h_ne_zero =>
    intro hzero
    have h_eq : π ^ i = -1 := by
      calc
        π ^ i = (1 + π ^ i) - 1 := by ring
        _ = 0 - 1 := by rw [hzero]
        _ = -1 := by ring
    have h_norm_eq : ‖π‖ ^ i = 1 := by
      calc
        ‖π‖ ^ i = ‖π ^ i‖ := by
          symm; exact norm_pow _ _
        _ = ‖(-1 : F)‖ := by rw [h_eq]
        _ = ‖(1 : F)‖ := by rw [norm_neg]
        _ = 1 := norm_one
    have h_lt : ‖π‖ ^ i < 1 := by
      refine pow_lt_one₀ (norm_nonneg _) hπ.norm_lt_one h_ne_zero
    linarith

/-! ## The echelon of the standard basis

At a component `F = CF σ E` (uniformizer `Y`, `‖2‖ = ‖Y‖ ^ (2e)`, residue field `𝔽₂`), `bF 0 = Y` has
valuation `1`, `bF i = 1 + π^(i-1) Y` (`1 ≤ i ≤ 2e`) has depth `2i - 1` with digit `1`, and
`bF (2e + 1) = 5 = 1 + 4 · 1`. Pivots: the valuation, the depths `2i - 1`, the position `4`. -/

/-- The unit datum of `bF i`. -/
def uStd (e i : ℕ) : UDatum :=
  if i = 0 then .none else if i = 2 * e + 1 then .four 1 else .odd (2 * i - 1) 1

/-- The valuation exponent of `bF i`. -/
def kStd (i : ℕ) : ℤ := if i = 0 then 1 else 0

/-- The pivot of `bF i`. -/
def pivStd (e i : ℕ) : CPos :=
  if i = 0 then .val else if i = 2 * e + 1 then .four else .odd (2 * i - 1) 0

theorem echelonOK_std (e : ℕ) (he : 0 < e) :
    echelonOK (fun i p => admB ⟨2 * e, 1, 1, 0⟩ (uStd e i) p)
      (fun i p => digB ⟨2 * e, 1, 1, 0⟩ (kStd i) (uStd e i) p) (pivStd e) (2 * e + 2) = true := by
  let Q : CShape := ⟨2 * e, 1, 1, 0⟩
  have hQe : 0 < Q.e := by
    dsimp [Q]
    omega
  unfold echelonOK
  rw [allLt_iff]
  intro i hi
  have hi_lt : i < 2 * e + 2 := hi
  dsimp [Q]
  simp only [Bool.and_eq_true]
  have h_adm : admB Q (uStd e i) (pivStd e i) = true := by
    unfold uStd pivStd
    split_ifs with h0 h1
    · -- i = 0
      simp [admB]
    · -- i = 2*e+1
      simp [admB, Q, hQe]
    · -- odd case: i ≠ 0, i ≠ 2*e+1
      simp [admB, Q]
      omega
  have h_dig : digB Q (kStd i) (uStd e i) (pivStd e i) = true := by
    unfold uStd kStd pivStd
    split_ifs with h0 h1
    · -- i = 0
      simp [digB]
    · -- i = 2*e+1
      simp [digB, Q, dotB]
    · -- odd case
      simp [digB]
  have h_inner : allLt (fun i' => decide (i' ≤ i) || (admB Q (uStd e i') (pivStd e i) && !digB Q (kStd i') (uStd e i') (pivStd e i))) (2 * e + 2) = true := by
    rw [allLt_iff]
    intro i' hi'
    have hi'_lt : i' < 2 * e + 2 := hi'
    by_cases hi'_le_i : i' ≤ i
    · -- then decide (i' ≤ i) = true, so the whole thing is true
      simp [hi'_le_i]
    · -- i' > i, so we need adm && !dig
      have hi_lt_i' : i < i' := by omega
      -- analyze pivStd e i based on i
      -- We already know i is not 0 (otherwise hi'_le_i would hold for i'=0) and not 2*e+1 (otherwise i' can't be > i)
      -- But we need to handle all cases
      unfold pivStd
      split_ifs with hi0 hi_last
      · -- i = 0, but then i' > 0, so decide (i' ≤ 0) = false, need adm && !dig
        -- This case shouldn't happen because if i=0, then i' > 0, so hi'_le_i is false, and we need to prove the condition
        -- But wait, if i=0 and i' > 0, then decide (i' ≤ 0) = false, so we need admB Q (uStd e i') .val && !digB Q (kStd i') (uStd e i') .val
        -- admB Q u .val = true, digB Q k u .val = decide (k % 2 = 1)
        -- kStd i' = 0 (since i' ≠ 0), so decide (0 % 2 = 1) = false, !false = true
        -- So the condition holds
        simp [admB, digB, kStd]
        by_cases hi'0 : i' = 0
        · subst hi'0; omega
        · simp [hi'0]
      · -- i = 2*e+1, then i' > 2*e+1, but i' < 2*e+2, so i' = 2*e+1 is impossible since i' > i = 2*e+1
        -- Actually i' < 2*e+2 and i' > 2*e+1 means i' can't exist, contradiction
        omega
      · -- i is odd: pivStd e i = .odd (2*i-1) 0
        -- Now analyze uStd e i' and kStd i'
        unfold uStd kStd
        split_ifs with hi'0 hi'last
        · -- i' = 0
          -- But i' > i ≥ 1, so i' = 0 is impossible
          omega
        · -- i' = 2*e+1
          -- Then uStd e i' = .four 1, kStd i' = 0
          -- pivStd e i = .odd (2*i-1) 0
          -- admB Q (.four 1) (.odd (2*i-1) 0) = (decide ((2*i-1) % 2 = 1) && decide ((2*i-1) < 2*Q.e) && decide (0 < Q.f) && match .four 1 with | .odd t' _ => decide (2*i-1 ≤ t') | .four _ => true | _ => false)
          -- = (true && true && true && true) = true (since .four matches .four branch)
          -- digB Q 0 (.four 1) (.odd (2*i-1) 0) = false (since .odd case, u is .four, so false)
          -- !false = true
          -- So the condition holds
          simp [admB, digB, Q]
          omega
        · -- i' is odd
          -- uStd e i' = .odd (2*i'-1) 1, kStd i' = 0
          -- pivStd e i = .odd (2*i-1) 0
          -- admB Q (.odd (2*i'-1) 1) (.odd (2*i-1) 0) = decide ((2*i-1) % 2 = 1) && decide ((2*i-1) < 2*Q.e) && decide (0 < Q.f) && match .odd (2*i'-1) 1 with | .odd t' _ => decide (2*i-1 ≤ t') | _ => false
          -- = true && true && true && decide (2*i-1 ≤ 2*i'-1)
          -- Since i < i', we have 2*i-1 < 2*i'-1, so decide (2*i-1 ≤ 2*i'-1) = true
          -- digB Q 0 (.odd (2*i'-1) 1) (.odd (2*i-1) 0) = decide (2*i-1 = 2*i'-1) && 1.testBit 0 = decide (2*i-1 = 2*i'-1) && true
          -- Since i < i', 2*i-1 ≠ 2*i'-1, so this is false
          -- !false = true
          -- So the condition holds
          simp [admB, digB, Q]
          omega
  exact ⟨⟨h_adm, h_dig⟩, h_inner⟩

/-! ## The standard basis at a w-place -/

section Basis

variable {Kw : Type*} [NontriviallyNormedField Kw] [CompleteSpace Kw] [IsUltrametricDist Kw]
  {σ : K21 →+* Kw} {E : EisData} [Fact (∀ r : Kw, r ^ 2 ≠ σ (zkE E.A) + σ (zkE E.B) * r)]

theorem Ba_mod (a : ℕ) : Ba σ E (a % 2 ^ (2 * E.e + 2)) = Ba σ E a := by
  simp only [Ba, bitv_mod_two_pow]

theorem Ba_zero : Ba σ E 0 = 1 := prod_bitv_zero _ _

theorem norm_tC_eq (hW : WPlace σ E) : ‖tC σ E‖ = ‖cY σ E‖ ^ 2 := by
  rw [norm_tC hW, ← qfE_norm_Y hW.unif hW.norm_A hW.norm_B]
  rfl

theorem norm_cY_sq_sub_tC (hW : WPlace σ E) : ‖cY σ E ^ 2 - tC σ E‖ < ‖tC σ E‖ := by
  have hal0 : 0 < ‖σ (zkE E.al)‖ := norm_pos_iff.mpr hW.unif.ne_zero
  have hal1 := hW.unif.norm_lt_one
  have hsplit : cY σ E ^ 2 - tC σ E =
      algebraMap Kw (CF σ E) (σ (zkE E.al) * σ (zkE E.al) * σ (zkE E.cA)) +
        algebraMap Kw (CF σ E) (σ (zkE E.B)) * cY σ E := by
    have hAm : algebraMap Kw (CF σ E) (σ (zkE E.A)) = algebraMap Kw (CF σ E) (σ (zkE E.al)) +
        algebraMap Kw (CF σ E) (σ (zkE E.al) * σ (zkE E.al) * σ (zkE E.cA)) := by
      rw [← map_add]
      congr 1
      rw [EisData.ok_A hW.ok, map_mul, map_add, map_one, map_mul]
      ring
    rw [cY_sq, tC, hAm]
    ring
  rw [hsplit, norm_tC hW]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [QF.norm_algebraMap, norm_mul, norm_mul]
    have hcA := hW.int E.cA
    calc ‖σ (zkE E.al)‖ * ‖σ (zkE E.al)‖ * ‖σ (zkE E.cA)‖
        ≤ ‖σ (zkE E.al)‖ * ‖σ (zkE E.al)‖ * 1 :=
          mul_le_mul_of_nonneg_left hcA (by positivity)
      _ < ‖σ (zkE E.al)‖ := by nlinarith
  · rw [norm_mul, QF.norm_algebraMap]
    calc ‖σ (zkE E.B)‖ * ‖cY σ E‖ ≤ ‖σ (zkE E.al)‖ * ‖cY σ E‖ :=
          mul_le_mul_of_nonneg_right hW.norm_B_le (norm_nonneg _)
      _ < ‖σ (zkE E.al)‖ * 1 := mul_lt_mul_of_pos_left (norm_cY_lt_one hW) hal0
      _ = ‖σ (zkE E.al)‖ := mul_one _

theorem dfact_bF (hW : WPlace σ E) (he : 0 < E.e) (i : ℕ) (hi : i < 2 * E.e + 2) :
    DFact ⟨2 * E.e, 1, 1, 0⟩ (cY σ E) ![1] (bF σ E i) 1 (kStd i) (uStd E.e i) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have hb : bF σ E 0 = cY σ E := by simp [bF]
    rw [hb, show kStd 0 = 1 from rfl, show uStd E.e 0 = .none from rfl]
    exact dfact_pi _ _ _
  by_cases h5 : i = 2 * E.e + 1
  · have h2 : ‖(2 : Kw)‖ < 1 := by
      rw [hW.two]; exact pow_lt_one₀ (norm_nonneg _) hW.unif.norm_lt_one he.ne'
    have h20 : 0 < ‖(2 : Kw)‖ := by
      rw [hW.two]; exact pow_pos (norm_pos_iff.mpr hW.unif.ne_zero) _
    have h4n : ‖(4 : CF σ E)‖ = ‖(2 : Kw)‖ * ‖(2 : Kw)‖ := by
      rw [show (4 : CF σ E) = algebraMap Kw (CF σ E) 4 from (map_ofNat _ 4).symm,
        QF.norm_algebraMap, show (4 : Kw) = 2 * 2 by norm_num, norm_mul]
    have h4 : (4 : CF σ E) ≠ 0 := by
      intro h; rw [h, norm_zero] at h4n; nlinarith
    have h41 : ‖(4 : CF σ E)‖ < 1 := by rw [h4n]; nlinarith
    have hl : liftW (![1] : Fin 1 → CF σ E) 1 = 1 := by
      simp only [liftW, Fin.sum_univ_one, Matrix.cons_val_zero, mul_one]
      rw [show (bitv 1 1 0).val = 1 by decide, Nat.cast_one]
    have h := dfact_four_std ⟨2 * E.e, 1, 1, 0⟩ (cY σ E) ![1]
      (by intro l; fin_cases l; simp) h4 h41 1
    rw [hl, show (1 : CF σ E) + 4 * 1 = 5 by norm_num] at h
    have hb : bF σ E i = 5 := by simp [bF, h5]
    have hu : uStd E.e i = .four 1 := by simp [uStd, h5]
    have hk : kStd i = 0 := by simp [kStd, hi0.ne']
    rw [hb, hu, hk]
    exact h
  · have hY0 : cY σ E ≠ 0 := (qfE_normUnif hW.unif hW.norm_A hW.norm_B).ne_zero
    have h := dfact_odd_near (2 * E.e) 0 hY0 (norm_cY_lt_one hW) (norm_tC_eq hW)
      (norm_cY_sq_sub_tC hW) (i - 1)
    have hj : 2 * (i - 1) + 1 = 2 * i - 1 := by omega
    rw [hj] at h
    have hb : bF σ E i = 1 + tC σ E ^ (i - 1) * cY σ E := by simp [bF, hi0.ne', h5]
    have hu : uStd E.e i = .odd (2 * i - 1) 1 := by simp [uStd, hi0.ne', h5]
    have hk : kStd i = 0 := by simp [kStd, hi0.ne']
    rw [hb, hu, hk]
    exact h

/-- **The standard basis is independent modulo squares.** -/
theorem bF_indep (hW : WPlace σ E) (he : 0 < E.e) :
    ∀ ε : Fin (2 * E.e + 2) → ZMod 2,
      IsSquare (∏ i : Fin (2 * E.e + 2), bF σ E i ^ (ε i).val) → ε = 0 := by
  intro ε hε
  set b : Fin (2 * E.e + 2) → (CF σ E)ˣ := fun i => Units.mk0 (bF σ E i) (bF_ne_zero hW i) with hb
  have hsq : IsSquare (∏ i, b i ^ (ε i).val) :=
    isSquare_units_of_isSquare _ (by simpa [hb, Units.coe_prod] using hε)
  have hQ : CompOK ⟨2 * E.e, 1, 1, 0⟩ (cY σ E) ![1] :=
    compOK_F2 (qfE_normUnif hW.unif hW.norm_A hW.norm_B) (by omega)
      (qfE_two hW.unif hW.norm_A hW.norm_B hW.two) (qfE_res hW.unif hW.norm_A hW.norm_B hW.res) 0
  exact sb_indep_of_echelonOK b (fun i p => admB ⟨2 * E.e, 1, 1, 0⟩ (uStd E.e i) p)
    (fun i p => digB ⟨2 * E.e, 1, 1, 0⟩ (kStd i) (uStd E.e i) p) (pivStd E.e)
    (fun p ε' hadm hsq' => comp_test b (MonoidHom.id _) _ hQ (fun _ => 1) (fun i => kStd i)
      (fun i => uStd E.e i) (fun i => dfact_bF hW he i i.isLt) p ε' hadm hsq')
    (echelonOK_std E.e he) ε hsq

end Basis

end FurioLombardo.Discharge.SelmerBasis
