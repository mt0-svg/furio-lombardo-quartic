import FurioLombardo.Discharge.SelmerBasis.LocalGlue

/-!
# From coordinates at a place to `RelAtV`, and generic facts for the place `v`

* `relAtV_of_coords`: when `ev : (K'[T]/(f))ˣ ≃* G` is an isomorphism (the CRT at the place), the
  relation `RelAtV` follows from square certificates of the global classes, of the points and of the
  scalars `κ0` on a family `b` of `G`, and one identity of coordinate vectors over `ZMod 2` per column
  (the difference of the coordinates of `∏ g^β_j` and `∏ μ(D_i)^SB_ij` is a combination of those of
  the scalars). No independence of `b` is needed.
* `coordCond_of_mul`: `CoordCond` passes from `C'` to `M * C'`.
* `irreducible_of_disc`: a monic quadratic whose discriminant is not a square is irreducible.
* `norm_le_one_of_isIntegral`: an integral element over `ℤ` has norm at most `1` in an ultrametric field.
-/

open Polynomial FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.SelmerBasis

section Glue

variable {K' : Type*} [Field K']

/-- **The relation at a place from coordinates.** -/
theorem relAtV_of_coords {K : Type*} [Field K] (φ : K →+* K') (f : K[X]) [GoodSextic (f.map φ)]
    {m r : ℕ} (gu : Fin m → (AdjoinRoot f)ˣ) (D : Fin r → Jac (f.map φ))
    (U : Fin r → (AdjoinRoot (f.map φ))ˣ) (hU : ∀ i, muJ (f.map φ) (D i) = QuotientGroup.mk (U i))
    {G : Type*} [CommGroup G] (ev : (AdjoinRoot (f.map φ))ˣ ≃* G) {nb : ℕ} (b : Fin nb → G)
    {mκ : ℕ} (κ0 : Fin mκ → K'ˣ) (Aκ : Fin mκ → Fin nb → ZMod 2)
    (hAκ : ∀ l, IsSquare (ev (Units.map (algebraMap K' (AdjoinRoot (f.map φ))).toMonoidHom (κ0 l)) *
      ∏ i, b i ^ (Aκ l i).val))
    (Aμ : Fin r → Fin nb → ZMod 2) (hAμ : ∀ i, IsSquare (ev (U i) * ∏ j, b j ^ (Aμ i j).val))
    (Cg : Fin m → Fin nb → ZMod 2)
    (hCg : ∀ s, IsSquare (ev (Units.map (etaleMap φ f).toMonoidHom (gu s)) * ∏ j, b j ^ (Cg s j).val))
    (β : Fin 4 → Fin m → ℕ) (SB : Matrix (Fin r) (Fin 4) ℤ) (c : Fin 4 → Fin mκ → ZMod 2)
    (hcert : ∀ j, ∑ s, ((β j s : ℕ) : ZMod 2) • Cg s + ∑ i, ((SB i j : ℤ) : ZMod 2) • Aμ i =
      ∑ l, c j l • Aκ l) :
    RelAtV φ f (fun s => (QuotientGroup.mk (gu s) : H f)) β D SB := by
  classical
  set e : (AdjoinRoot f)ˣ →* (AdjoinRoot (f.map φ))ˣ := Units.map (etaleMap φ f).toMonoidHom with he
  set T : Subgroup G := (sqClass (f.map φ)).map ev.toMonoidHom with hT
  set π : G →* G ⧸ T := QuotientGroup.mk' T with hπ
  have hπ_ev : ∀ x, π (ev x) = 1 ↔ x ∈ sqClass (f.map φ) := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hT, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply]
  have hπ2 : ∀ q : G ⧸ T, q * q = 1 := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective T q
    obtain ⟨x, rfl⟩ := ev.surjective y
    rw [← map_mul, ← map_mul, hπ_ev]
    exact Subgroup.mem_sup_right ⟨x, by simp [sq]⟩
  have hinv : ∀ q : G ⧸ T, q⁻¹ = q := fun q => inv_eq_of_mul_eq_one_right (hπ2 q)
  have hsqc : ∀ y z : G, IsSquare (y * z) → π y = π z := by
    rintro y z ⟨w, hw⟩
    have h1 : π y * π z = 1 := by rw [← map_mul, hw, map_mul]; exact hπ2 _
    rw [← hinv (π z)]
    exact eq_inv_of_mul_eq_one_left h1
  let Φ : (Fin nb → ZMod 2) → G ⧸ T := fun v => ∏ j, π (b j) ^ (v j).val
  have hΦP : ∀ v, π (∏ j, b j ^ (v j).val) = Φ v := fun v => by simp [Φ, map_prod, map_pow]
  have hpow2 : ∀ (q : G ⧸ T) (n : ℕ), q ^ n = q ^ (n % 2) := fun q n =>
    pow_eq_pow_mod n (by rw [sq]; exact hπ2 q)
  have hnat : ∀ (q : G ⧸ T) (n : ℕ), q ^ ((n : ZMod 2).val) = q ^ n := fun q n => by
    rw [ZMod.val_natCast, ← hpow2]
  have hint : ∀ (q : G ⧸ T) (z : ℤ), q ^ ((z : ZMod 2).val) = q ^ z := fun q z => by
    rw [zpow_eq_zpow_emod z (n := 2) (by rw [zpow_two]; exact hπ2 q), ← zpow_natCast]
    congr 1
    rw [ZMod.val_intCast]
    norm_num
  have hΦadd : ∀ v w, Φ (v + w) = Φ v * Φ w := by
    intro v w
    simp only [Φ, ← Finset.prod_mul_distrib, ← pow_add]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Pi.add_apply, ZMod.val_add, ← hpow2]
  have hΦ0 : Φ 0 = 1 := by simp [Φ]
  have hΦsum : ∀ {n : ℕ} (s : Finset (Fin n)) (F : Fin n → Fin nb → ZMod 2),
      Φ (∑ i ∈ s, F i) = ∏ i ∈ s, Φ (F i) := by
    intro n s F
    induction s using Finset.induction_on with
    | empty => simp [hΦ0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hΦadd, ih]
  have hΦsmul : ∀ (c : ZMod 2) v, Φ (c • v) = Φ v ^ c.val := by
    intro c v
    obtain rfl | rfl : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    · rw [zero_smul, ZMod.val_zero, pow_zero, hΦ0]
    · rw [one_smul, ZMod.val_one, pow_one]
  have hgs : ∀ s, π (ev (e (gu s))) = Φ (Cg s) := fun s => by rw [hsqc _ _ (hCg s), hΦP]
  have hUs : ∀ i, π (ev (U i)) = Φ (Aμ i) := fun i => by rw [hsqc _ _ (hAμ i), hΦP]
  have hκs : ∀ l, Φ (Aκ l) = 1 := fun l => by
    rw [← hΦP, ← hsqc _ _ (hAκ l), hπ_ev]
    exact Subgroup.mem_sup_left ⟨κ0 l, rfl⟩
  intro j
  have hL : Hmap φ f (∏ s, (QuotientGroup.mk (gu s) : H f) ^ β j s) =
      QuotientGroup.mk (∏ s, e (gu s) ^ β j s) := by
    simp [map_prod, map_pow, Hmap, e]
  have hR : ∏ i, muJ (f.map φ) (D i) ^ SB i j =
      QuotientGroup.mk (∏ i, U i ^ SB i j) := by
    simp [hU]
  rw [hL, hR, QuotientGroup.eq, ← hπ_ev]
  simp only [map_mul, map_inv, map_prod, map_pow, map_zpow, hgs, hUs, hinv]
  have h1 : ∏ s, Φ (Cg s) ^ β j s = Φ (∑ s, ((β j s : ℕ) : ZMod 2) • Cg s) := by
    rw [hΦsum]; exact Finset.prod_congr rfl fun s _ => by rw [hΦsmul, hnat]
  have h2 : ∏ i, Φ (Aμ i) ^ SB i j = Φ (∑ i, ((SB i j : ℤ) : ZMod 2) • Aμ i) := by
    rw [hΦsum]; exact Finset.prod_congr rfl fun i _ => by rw [hΦsmul, hint]
  rw [h1, h2, ← hΦadd, hcert j, hΦsum]
  exact Finset.prod_eq_one fun l _ => by rw [hΦsmul, hκs, one_pow]

/-- `CoordCond` for `M * C'` from `CoordCond` for `C'`. -/
theorem coordCond_of_mul {K : Type*} [Field K] (φ : K →+* K') (f : K[X]) {m c c' : ℕ}
    (g : Fin m → H f) (W : Subgroup (H (f.map φ))) (C' : Matrix (Fin c') (Fin m) (ZMod 2))
    (M : Matrix (Fin c) (Fin c') (ZMod 2)) (hC' : CoordCond φ f g W C') :
    CoordCond φ f g W (M * C') := by
  intro a ha
  have h := hC' a ha
  calc
    (M * C').mulVec (fun s => (a s : ZMod 2)) = M.mulVec (C'.mulVec (fun s => (a s : ZMod 2))) := by
      rw [← Matrix.mulVec_mulVec]
    _ = M.mulVec 0 := by rw [h]
    _ = 0 := by simp

end Glue

/-- A monic quadratic whose discriminant is not a square is irreducible. -/
theorem irreducible_of_disc {K : Type*} [Field K] {p : K[X]} (hp : p.Monic) (hdeg : p.natDegree = 2)
    (h2 : (2 : K) ≠ 0) (hd : ¬ IsSquare (p.coeff 1 ^ 2 - 4 * p.coeff 0)) : Irreducible p := by
  have h_deg_range : p.natDegree ∈ Finset.Icc 1 3 := by
    rw [hdeg]
    exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have h_no_root : ∀ x : K, ¬ p.IsRoot x := by
    intro r
    intro hroot
    have heval : p.eval r = 0 := by
      rwa [Polynomial.IsRoot.def] at hroot
    have hp_eq : p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
      rw [hp.as_sum, hdeg]
      simp [Finset.sum_range_succ]
      ring
    rw [hp_eq] at heval
    simp [eval_add, eval_mul, eval_C, eval_X, eval_pow] at heval
    have h_square : IsSquare (p.coeff 1 ^ 2 - 4 * p.coeff 0) := by
      have hcalc : p.coeff 1 ^ 2 - 4 * p.coeff 0 = (2 * r + p.coeff 1) * (2 * r + p.coeff 1) := by
        have hzero : r ^ 2 + p.coeff 1 * r + p.coeff 0 = 0 := heval
        have h4 : 4 * (r ^ 2 + p.coeff 1 * r + p.coeff 0) = 0 := by rw [hzero, mul_zero]
        calc
          p.coeff 1 ^ 2 - 4 * p.coeff 0 = (0 - 4 * p.coeff 0) + p.coeff 1 ^ 2 := by ring
          _ = (4 * (r ^ 2 + p.coeff 1 * r + p.coeff 0) - 4 * p.coeff 0) + p.coeff 1 ^ 2 := by rw [h4]
          _ = 4 * (r ^ 2 + p.coeff 1 * r) + p.coeff 1 ^ 2 := by ring
          _ = 4 * r ^ 2 + 4 * p.coeff 1 * r + p.coeff 1 ^ 2 := by ring
          _ = (2 * r + p.coeff 1) * (2 * r + p.coeff 1) := by ring
      exact ⟨2 * r + p.coeff 1, hcalc⟩
    exact hd h_square
  exact Polynomial.irreducible_of_degree_le_three_of_not_isRoot h_deg_range h_no_root

/-- An element integral over `ℤ` has norm at most `1` in an ultrametric normed field. -/
theorem norm_le_one_of_isIntegral {F : Type*} [NormedField F] [IsUltrametricDist F] {x : F}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  by_contra! h
  -- h : 1 < ‖x‖
  rcases hx with ⟨P, hP_monic, hP⟩
  -- hP : aeval x P = 0
  set n := P.natDegree with hn
  by_cases hn0 : n = 0
  · -- n = 0 case: monic constant polynomial must be 1, but aeval x 1 = 1 ≠ 0
    have hP_eq_one : P = 1 :=
      ((Polynomial.Monic.natDegree_eq_zero hP_monic).mp hn0)
    rw [hP_eq_one] at hP
    simp at hP
  · -- n > 0
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have h_range_nonempty : (Finset.range n).Nonempty := by
      rw [Finset.nonempty_range_iff]
      exact hn0
    -- From monic.as_sum: P = X^n + ∑_{i < n} C(P.coeff i) * X^i
    have hP_as_sum := hP_monic.as_sum
    -- hP_as_sum : P = X ^ P.natDegree + ∑ i ∈ range P.natDegree, C (P.coeff i) * X ^ i
    rw [← hn] at hP_as_sum
    -- Now apply aeval x to both sides
    have h_aeval := congrArg (aeval x) hP_as_sum
    -- aeval is an algebra hom, so aeval x (X^n) = x^n and aeval x (C a * X^i) = a * x^i
    have h_aeval_simp : aeval x P = x ^ n + ∑ i ∈ Finset.range n, (P.coeff i : F) * x ^ i := by
      simpa [map_add, aeval_X_pow, aeval_C, aeval_X, aeval_mul, map_pow, map_sum] using h_aeval
    have h_zero : aeval x P = 0 := by
      rw [aeval_def, hP]
    rw [h_zero] at h_aeval_simp
    -- h_aeval_simp : 0 = x ^ n + ∑ i ∈ range n, (P.coeff i : F) * x ^ i
    -- Rearranged: x^n = -∑ ...
    have h_eq : x ^ n = -∑ i ∈ Finset.range n, (P.coeff i : F) * x ^ i :=
      eq_neg_of_add_eq_zero_left h_aeval_simp.symm
    -- Now we estimate norms
    have h_terms_lt : ∀ i ∈ Finset.range n, ‖(P.coeff i : F) * x ^ i‖ < ‖x‖ ^ n := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hi_lt_n : i < n := hi
      calc
        ‖(P.coeff i : F) * x ^ i‖ = ‖(P.coeff i : F)‖ * ‖x ^ i‖ := norm_mul _ _
        _ = ‖(P.coeff i : F)‖ * ‖x‖ ^ i := by rw [norm_pow]
        _ ≤ 1 * ‖x‖ ^ i := by
          gcongr
          exact IsUltrametricDist.norm_intCast_le_one (R := F) (P.coeff i)
        _ = ‖x‖ ^ i := by simp
        _ < ‖x‖ ^ n := pow_lt_pow_right₀ h hi_lt_n
    -- Now use the ultrametric sum inequality
    have h_sum_lt : ‖∑ i ∈ Finset.range n, (P.coeff i : F) * x ^ i‖ < ‖x‖ ^ n := by
      have h_le := Finset.Nonempty.norm_sum_le_sup'_norm h_range_nonempty
        (fun i => (P.coeff i : F) * x ^ i)
      -- h_le : ‖∑ ...‖ ≤ (range n).sup' h_range_nonempty (fun i => ‖(P.coeff i : F) * x ^ i‖)
      have h_sup_lt : (Finset.range n).sup' h_range_nonempty (fun i => ‖(P.coeff i : F) * x ^ i‖) < ‖x‖ ^ n := by
        rw [Finset.sup'_lt_iff h_range_nonempty]
        exact h_terms_lt
      linarith
    -- But from h_eq, ∑ ... = -x^n, so ‖∑ ...‖ = ‖x^n‖ = ‖x‖^n, contradiction
    have h_sum_eq : ∑ i ∈ Finset.range n, (P.coeff i : F) * x ^ i = -x ^ n := by
      rw [← neg_inj, neg_neg, ← h_eq]
    rw [h_sum_eq] at h_sum_lt
    have h_norm_pow : ‖x ^ n‖ = ‖x‖ ^ n := norm_pow x n
    rw [norm_neg, h_norm_pow] at h_sum_lt
    linarith

end FurioLombardo.Discharge.SelmerBasis
