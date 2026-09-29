import Mathlib
import FurioLombardo.M4.Series

/-!
# The lattice layer: the certificates of log A(k_v), its saturated submodule S, and the characterisation of S + 2^n Λ
-/


open FurioLombardo.M4

variable {V : Type*} [AddCommGroup V] [Module ℤ_[2] V]

theorem FurioLombardo.M4.imv_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (x y : Fin n → ℤ_[2]) : imv A (x + y) = imv A x + imv A y := by
  unfold imv
  rw [Matrix.mulVec_add]

theorem FurioLombardo.M4.imv_icast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (c : Fin n → ℤ) : imv A (icast c) = icast (A.mulVec c) := by
  ext i
  dsimp [imv, icast, Matrix.mulVec, dotProduct]
  push_cast
  rfl

theorem FurioLombardo.M4.imv_mul {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (B : Matrix (Fin n) (Fin p) ℤ) (x : Fin p → ℤ_[2]) :
    imv (A * B) x = imv A (imv B x) := by
  unfold imv
  have h := Matrix.map_mul (f := Int.castRingHom ℤ_[2]) (L := A) (M := B)
  simpa [Matrix.mulVec_mulVec] using congrArg (·.mulVec x) h

theorem FurioLombardo.M4.imv_scalar {n : ℕ} (c : ℤ) (x : Fin n → ℤ_[2]) : imv ((c : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)) x = (c : ℤ_[2]) • x := by
  unfold imv
  have hmap : ((c : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)).map (Int.cast : ℤ → ℤ_[2]) = (c : ℤ_[2]) • (1 : Matrix (Fin n) (Fin n) ℤ_[2]) := by
    calc
      ((c : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)).map (Int.cast : ℤ → ℤ_[2])
          = ((Int.cast : ℤ → ℤ_[2]) c) • ((1 : Matrix (Fin n) (Fin n) ℤ).map (Int.cast : ℤ → ℤ_[2])) := by
        simpa using Matrix.map_smul' (Int.cast : ℤ → ℤ_[2]) (c : ℤ) (1 : Matrix (Fin n) (Fin n) ℤ) Int.cast_mul
      _ = (c : ℤ_[2]) • ((1 : Matrix (Fin n) (Fin n) ℤ).map (Int.cast : ℤ → ℤ_[2])) := by simp
      _ = (c : ℤ_[2]) • (1 : Matrix (Fin n) (Fin n) ℤ_[2]) := by simp
  rw [hmap]
  simp [Matrix.smul_mulVec, Matrix.one_mulVec]

theorem FurioLombardo.M4.imv_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (c : ℤ_[2]) (x : Fin n → ℤ_[2]) : imv A (c • x) = c • imv A x := by
  unfold imv
  exact Matrix.mulVec_smul _ _ _

theorem FurioLombardo.M4.imv_sub {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (x y : Fin n → ℤ_[2]) : imv A (x - y) = imv A x - imv A y := by
  unfold imv
  exact Matrix.mulVec_sub _ _ _

theorem FurioLombardo.M4.inSL_add {Λ S : Submodule ℤ_[2] V} {n : ℕ} {x y : V} (hx : InSL Λ S n x) (hy : InSL Λ S n y) :
    InSL Λ S n (x + y) := by
  rcases hx with ⟨s, hs, l, hl, hx_eq⟩
  rcases hy with ⟨s', hs', l', hl', hy_eq⟩
  refine ⟨s + s', S.add_mem hs hs', l + l', Λ.add_mem hl hl', ?_⟩
  calc
    x + y = (s + (2 : ℤ_[2]) ^ n • l) + (s' + (2 : ℤ_[2]) ^ n • l') := by rw [hx_eq, hy_eq]
    _ = (s + s') + ((2 : ℤ_[2]) ^ n • l + (2 : ℤ_[2]) ^ n • l') := by abel
    _ = (s + s') + (2 : ℤ_[2]) ^ n • (l + l') := by rw [smul_add]

theorem FurioLombardo.M4.inSL_mono {Λ S : Submodule ℤ_[2] V} {n r : ℕ} {x : V} (hnr : n ≤ r) (hx : InSL Λ S r x) : InSL Λ S n x := by
  rcases hx with ⟨s, hs, l, hl, hx⟩
  refine ⟨s, hs, (2 : ℤ_[2]) ^ (r - n) • l, Submodule.smul_mem Λ _ hl, ?_⟩
  calc
    x = s + (2 : ℤ_[2]) ^ r • l := hx
    _ = s + (2 : ℤ_[2]) ^ (n + (r - n)) • l := by rw [Nat.add_sub_cancel' hnr]
    _ = s + ((2 : ℤ_[2]) ^ n * (2 : ℤ_[2]) ^ (r - n)) • l := by rw [pow_add]
    _ = s + (2 : ℤ_[2]) ^ n • ((2 : ℤ_[2]) ^ (r - n) • l) := by rw [mul_smul]

theorem FurioLombardo.M4.inSL_smul {Λ S : Submodule ℤ_[2] V} {n : ℕ} {x : V} (c : ℤ_[2]) (hx : InSL Λ S n x) : InSL Λ S n (c • x) := by
  rcases hx with ⟨s, hs, l, hl, hx_eq⟩
  refine ⟨c • s, S.smul_mem c hs, c • l, Λ.smul_mem c hl, ?_⟩
  rw [hx_eq, smul_add, smul_smul, mul_comm, ← smul_smul]

theorem FurioLombardo.M4.inSL_of_unit_smul {Λ S : Submodule ℤ_[2] V} {n : ℕ} {x : V} {D : ℤ_[2]} (hD : IsUnit D) (hx : InSL Λ S n (D • x)) :
    InSL Λ S n x := by
  rcases hD.exists_right_inv with ⟨e, he⟩
  rcases hx with ⟨s, hs, l, hl, h⟩
  refine ⟨e • s, Submodule.smul_mem _ e hs, e • l, Submodule.smul_mem _ e hl, ?_⟩
  calc
    x = (1 : ℤ_[2]) • x := by simp
    _ = (D * e) • x := by rw [he]
    _ = D • (e • x) := by rw [smul_smul]
    _ = e • (D • x) := by rw [smul_comm D e x]
    _ = e • (s + (2 : ℤ_[2]) ^ n • l) := by rw [h]
    _ = e • s + e • ((2 : ℤ_[2]) ^ n • l) := by rw [smul_add]
    _ = e • s + (e * (2 : ℤ_[2]) ^ n) • l := by rw [smul_smul]
    _ = e • s + ((2 : ℤ_[2]) ^ n * e) • l := by rw [mul_comm]
    _ = e • s + (2 : ℤ_[2]) ^ n • (e • l) := by rw [smul_smul]

theorem FurioLombardo.M4.inSL_of_mem {Λ S : Submodule ℤ_[2] V} {n : ℕ} {x : V} (hx : x ∈ Λ) (c : ℤ_[2]) (hc : (2 : ℤ_[2]) ^ n ∣ c) :
    InSL Λ S n (c • x) := by
  rcases hc with ⟨d, hd⟩
  refine ⟨0, Submodule.zero_mem S, d • x, Submodule.smul_mem Λ d hx, ?_⟩
  calc
    c • x = ((2 : ℤ_[2]) ^ n * d) • x := by rw [hd]
    _ = (2 : ℤ_[2]) ^ n • (d • x) := by rw [mul_smul]
    _ = 0 + (2 : ℤ_[2]) ^ n • (d • x) := by simp

theorem FurioLombardo.M4.inSL_of_mem_S {Λ S : Submodule ℤ_[2] V} {n : ℕ} {x : V} (hx : x ∈ S) : InSL Λ S n x := by
  refine ⟨x, hx, 0, Submodule.zero_mem Λ, ?_⟩
  simp

theorem FurioLombardo.M4.inSL_of_cert {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {a b σ : Fin 6 → ℤ_[2]} (hS : IsSatOf Λ S a b)
    (h4 : ∀ x, DvdV 2 x → x ∈ Λ) (hσ : σ ∈ Λ) (r e : ℕ) (α β : ℤ_[2])
    (hc : DvdV (r + e + 2) ((2 : ℤ_[2]) ^ e • σ - α • a - β • b)) : InSL Λ S r σ := by
  -- From hc, each coordinate is divisible by 2^(r+e+2)
  have hc_coord : ∀ i, ∃ t_i : ℤ_[2], ((2 : ℤ_[2]) ^ e • σ - α • a - β • b) i = (2 : ℤ_[2]) ^ (r + e + 2) * t_i := by
    intro i
    exact (hc i)
  choose t ht using hc_coord
  -- l := 4 • t = 2^2 • t
  set l := (4 : ℤ_[2]) • t with hl_def
  have hl_in_Λ : l ∈ Λ := by
    apply h4 l
    intro i
    have hli : l i = (4 : ℤ_[2]) * t i := by
      simp [hl_def, Pi.smul_apply]
    rw [hli]
    have h4_eq : (2 : ℤ_[2]) ^ 2 = (4 : ℤ_[2]) := by norm_num
    rw [h4_eq]
    exact ⟨t i, by ring⟩
  set s := σ - (2 : ℤ_[2]) ^ r • l with hs_def
  have hs_in_Λ : s ∈ Λ := by
    rw [hs_def]
    apply Submodule.sub_mem Λ hσ
    apply Submodule.smul_mem Λ ((2 : ℤ_[2]) ^ r) hl_in_Λ
  have hs_in_S : s ∈ S := by
    rw [hS s]
    refine ⟨hs_in_Λ, e, ?_⟩
    -- need (2)^e • s ∈ Submodule.span ℤ_[2] {a, b}
    have h_eq : (2 : ℤ_[2]) ^ e • σ - α • a - β • b = (2 : ℤ_[2]) ^ (r + e + 2) • t := by
      ext i
      calc
        ((2 : ℤ_[2]) ^ e • σ - α • a - β • b) i = (2 : ℤ_[2]) ^ (r + e + 2) * t i := ht i
        _ = ((2 : ℤ_[2]) ^ (r + e + 2) • t) i := by simp [Pi.smul_apply]
    have hcalc : (2 : ℤ_[2]) ^ e • s = α • a + β • b := by
      calc
        (2 : ℤ_[2]) ^ e • s = (2 : ℤ_[2]) ^ e • (σ - (2 : ℤ_[2]) ^ r • l) := by rw [hs_def]
        _ = (2 : ℤ_[2]) ^ e • σ - (2 : ℤ_[2]) ^ e • ((2 : ℤ_[2]) ^ r • l) := by rw [smul_sub]
        _ = (2 : ℤ_[2]) ^ e • σ - ((2 : ℤ_[2]) ^ e * (2 : ℤ_[2]) ^ r) • l := by rw [smul_smul]
        _ = (2 : ℤ_[2]) ^ e • σ - (2 : ℤ_[2]) ^ (e + r) • l := by rw [← pow_add (2 : ℤ_[2]) e r]
        _ = (2 : ℤ_[2]) ^ e • σ - (2 : ℤ_[2]) ^ (r + e) • l := by rw [add_comm e r]
        _ = (2 : ℤ_[2]) ^ e • σ - ((2 : ℤ_[2]) ^ (r + e) * (4 : ℤ_[2])) • t := by
          dsimp [l]
          rw [smul_smul]
        _ = (2 : ℤ_[2]) ^ e • σ - (2 : ℤ_[2]) ^ (r + e + 2) • t := by
          have h : ((2 : ℤ_[2]) ^ (r + e) * (4 : ℤ_[2])) = (2 : ℤ_[2]) ^ (r + e + 2) := by ring
          rw [h]
        _ = ((2 : ℤ_[2]) ^ e • σ - α • a - β • b) + (α • a + β • b) - (2 : ℤ_[2]) ^ (r + e + 2) • t := by
          ring
        _ = ((2 : ℤ_[2]) ^ (r + e + 2) • t) + (α • a + β • b) - (2 : ℤ_[2]) ^ (r + e + 2) • t := by rw [h_eq]
        _ = α • a + β • b := by ring
    rw [hcalc]
    have ha : a ∈ Submodule.span ℤ_[2] {a, b} := Submodule.subset_span (by simp)
    have hb : b ∈ Submodule.span ℤ_[2] {a, b} := Submodule.subset_span (by simp)
    have hαa : α • a ∈ Submodule.span ℤ_[2] {a, b} := Submodule.smul_mem _ α ha
    have hβb : β • b ∈ Submodule.span ℤ_[2] {a, b} := Submodule.smul_mem _ β hb
    exact Submodule.add_mem _ hαa hβb
  refine ⟨s, hs_in_S, l, hl_in_Λ, ?_⟩
  dsimp [s, l]
  rw [sub_add_cancel]

theorem FurioLombardo.M4.cramer_two {p a b : Fin 6 → ℤ_[2]} {α β : ℤ_[2]} (m : ℕ)
    (h : (2 : ℤ_[2]) ^ m • p = α • a + β • b) (o : Fin 6) :
    (a 0 * b 1 - a 1 * b 0) * p o = (b 1 * p 0 - b 0 * p 1) * a o + (a 0 * p 1 - a 1 * p 0) * b o := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have ho := congrFun h o
  simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h0 h1 ho
  have h2m : (2 : ℤ_[2]) ^ m ≠ 0 :=
    pow_ne_zero m (by norm_num : (2 : ℤ_[2]) ≠ 0)
  apply mul_left_cancel₀ h2m
  calc
    (2 : ℤ_[2]) ^ m * ((a 0 * b 1 - a 1 * b 0) * p o)
        = (a 0 * b 1 - a 1 * b 0) * ((2 : ℤ_[2]) ^ m * p o) := by ring
    _ = (a 0 * b 1 - a 1 * b 0) * (α * a o + β * b o) := by rw [ho]
    _ = (b 1 * (α * a 0 + β * b 0) - b 0 * (α * a 1 + β * b 1)) * a o
        + (a 0 * (α * a 1 + β * b 1) - a 1 * (α * a 0 + β * b 0)) * b o := by ring
    _ = (b 1 * ((2 : ℤ_[2]) ^ m * p 0) - b 0 * ((2 : ℤ_[2]) ^ m * p 1)) * a o
        + (a 0 * ((2 : ℤ_[2]) ^ m * p 1) - a 1 * ((2 : ℤ_[2]) ^ m * p 0)) * b o := by rw [h0, h1]
    _ = (2 : ℤ_[2]) ^ m * ((b 1 * p 0 - b 0 * p 1) * a o + (a 0 * p 1 - a 1 * p 0) * b o) := by ring

theorem FurioLombardo.M4.dvd_of_cramer {p a b : Fin 6 → ℤ_[2]} {J δ : ℕ} {u : ℤ_[2]} (hu : IsUnit u)
    (hΔ : a 0 * b 1 - a 1 * b 0 = 2 ^ δ * u) (hδ : δ ≤ J + 2)
    (hp0 : (4 : ℤ_[2]) ∣ p 0) (hp1 : (4 : ℤ_[2]) ∣ p 1) (o : Fin 6)
    (ha : (2 : ℤ_[2]) ^ J ∣ a o) (hb : (2 : ℤ_[2]) ^ J ∣ b o)
    (hid : (a 0 * b 1 - a 1 * b 0) * p o = (b 1 * p 0 - b 0 * p 1) * a o + (a 0 * p 1 - a 1 * p 0) * b o) :
    (2 : ℤ_[2]) ^ (J + 2 - δ) ∣ p o := by
  have h_pow_eq : (2 : ℤ_[2]) ^ (J + 2) = (4 : ℤ_[2]) * (2 : ℤ_[2]) ^ J := by
    calc
      (2 : ℤ_[2]) ^ (J + 2) = (2 : ℤ_[2]) ^ J * (2 : ℤ_[2]) ^ 2 := by rw [pow_add]
      _ = (2 : ℤ_[2]) ^ J * (4 : ℤ_[2]) := by norm_num
      _ = (4 : ℤ_[2]) * (2 : ℤ_[2]) ^ J := mul_comm _ _
  have h4 : (4 : ℤ_[2]) ∣ (b 1 * p 0 - b 0 * p 1) := by
    have h1 : (4 : ℤ_[2]) ∣ b 1 * p 0 := hp0.mul_left (b 1)
    have h2 : (4 : ℤ_[2]) ∣ b 0 * p 1 := hp1.mul_left (b 0)
    exact dvd_sub h1 h2
  have h4' : (4 : ℤ_[2]) ∣ (a 0 * p 1 - a 1 * p 0) := by
    have h1 : (4 : ℤ_[2]) ∣ a 0 * p 1 := hp1.mul_left (a 0)
    have h2 : (4 : ℤ_[2]) ∣ a 1 * p 0 := hp0.mul_left (a 1)
    exact dvd_sub h1 h2
  have h_term1 : (2 : ℤ_[2]) ^ (J + 2) ∣ (b 1 * p 0 - b 0 * p 1) * a o := by
    rw [h_pow_eq]
    exact mul_dvd_mul h4 ha
  have h_term2 : (2 : ℤ_[2]) ^ (J + 2) ∣ (a 0 * p 1 - a 1 * p 0) * b o := by
    rw [h_pow_eq]
    exact mul_dvd_mul h4' hb
  have hRHS : (2 : ℤ_[2]) ^ (J + 2) ∣ (b 1 * p 0 - b 0 * p 1) * a o + (a 0 * p 1 - a 1 * p 0) * b o :=
    dvd_add h_term1 h_term2
  rw [← hid, hΔ] at hRHS
  have hRHS' : (2 : ℤ_[2]) ^ (J + 2) ∣ u * ((2 : ℤ_[2]) ^ δ * p o) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hRHS
  have h_cancel_u : (2 : ℤ_[2]) ^ (J + 2) ∣ (2 : ℤ_[2]) ^ δ * p o :=
    ((IsUnit.dvd_mul_left hu).mp hRHS')
  have h_pow_split : (2 : ℤ_[2]) ^ (J + 2) = (2 : ℤ_[2]) ^ δ * (2 : ℤ_[2]) ^ (J + 2 - δ) := by
    calc
      (2 : ℤ_[2]) ^ (J + 2) = (2 : ℤ_[2]) ^ (δ + (J + 2 - δ)) := by
        rw [Nat.add_sub_cancel' hδ]
      _ = (2 : ℤ_[2]) ^ δ * (2 : ℤ_[2]) ^ (J + 2 - δ) := by rw [pow_add]
  rw [h_pow_split] at h_cancel_u
  have h2pow_ne_zero : (2 : ℤ_[2]) ^ δ ≠ 0 := pow_ne_zero δ (by norm_num : (2 : ℤ_[2]) ≠ 0)
  exact (mul_dvd_mul_iff_left h2pow_ne_zero).mp h_cancel_u

theorem FurioLombardo.M4.dvd_Q_of_mem_S {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {a b : Fin 6 → ℤ_[2]} (hS : IsSatOf Λ S a b)
    (UG : Matrix (Fin 6) (Fin 6) ℤ) (h4 : ∀ x ∈ Λ, ∀ j, (4 : ℤ_[2]) ∣ imv UG x j) {J δ : ℕ} {u : ℤ_[2]}
    (hu : IsUnit u) (hΔ : imv UG a 0 * imv UG b 1 - imv UG a 1 * imv UG b 0 = 2 ^ δ * u) (hδ : δ ≤ J + 2)
    (hab : ∀ o : Fin 6, 2 ≤ o.val → (2 : ℤ_[2]) ^ J ∣ imv UG a o ∧ (2 : ℤ_[2]) ^ J ∣ imv UG b o)
    {s : Fin 6 → ℤ_[2]} (hs : s ∈ S) (o : Fin 6) (ho : 2 ≤ o.val) :
    (2 : ℤ_[2]) ^ (J + 2 - δ) ∣ imv UG s o := by
  have hmem := (hS s).mp hs
  rcases hmem with ⟨hsΛ, m, hm⟩
  have hspan := (Submodule.mem_span_pair (R := ℤ_[2])).mp hm
  rcases hspan with ⟨α, β, hspan_eq⟩
  have hspan_imv : α • imv UG a + β • imv UG b = (2 : ℤ_[2]) ^ m • imv UG s := by
    calc
      α • imv UG a + β • imv UG b = imv UG (α • a + β • b) := by
        simp [imv_add, imv_smul]
      _ = imv UG ((2 : ℤ_[2]) ^ m • s) := by rw [hspan_eq]
      _ = (2 : ℤ_[2]) ^ m • imv UG s := by rw [imv_smul]
  have hcramer := cramer_two m (hspan_imv.symm) o
  exact dvd_of_cramer hu hΔ hδ (h4 s hsΛ 0) (h4 s hsΛ 1) o ((hab o ho).1) ((hab o ho).2) hcramer

theorem FurioLombardo.M4.eq_two_pow_mul_unit_of_approx {x : ℤ_[2]} {D : ℤ} {δ q : ℕ} (hD : (2 : ℤ) ^ δ ∣ D) (hD' : ¬ (2 : ℤ) ^ (δ + 1) ∣ D) (hq : δ < q)
    (hx : (2 : ℤ_[2]) ^ q ∣ x - (D : ℤ_[2])) : ∃ u : ℤ_[2], IsUnit u ∧ x = 2 ^ δ * u := by
  obtain ⟨e, rfl⟩ := hD
  have he : ¬ (2 : ℤ) ∣ e := by
    rintro ⟨f, rfl⟩
    exact hD' ⟨f, by ring⟩
  obtain ⟨y, hy⟩ := hx
  obtain ⟨k, rfl⟩ : ∃ k, q = δ + (k + 1) := ⟨q - δ - 1, by omega⟩
  refine ⟨(e : ℤ_[2]) + 2 ^ (k + 1) * y, ?_, ?_⟩
  · by_contra hu
    have hm : (e : ℤ_[2]) + 2 ^ (k + 1) * y ∈ IsLocalRing.maximalIdeal ℤ_[2] := hu
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
    have h2 : (2 : ℤ_[2]) ∣ 2 ^ (k + 1) * y := ⟨2 ^ k * y, by ring⟩
    have he2 : (2 : ℤ_[2]) ∣ (e : ℤ_[2]) := by
      have := dvd_sub hm h2
      simpa using this
    have h1 : ‖(e : ℤ_[2])‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).mpr (by exact_mod_cast he2)
    exact he (by exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd (p := 2) e).mp h1)
  · have : x = ((2 ^ δ * e : ℤ) : ℤ_[2]) + 2 ^ (δ + (k + 1)) * y := by rw [← hy]; ring
    rw [this]; push_cast; ring

theorem FurioLombardo.M4.four_single_mem {Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} (ℓ : Fin 7 → Fin 6 → ℤ_[2])
    (hΛ : Λ = Submodule.span ℤ_[2] (Set.range ℓ)) (l : Fin 7 → Fin 6 → ℤ)
    (hl : ∀ i, DvdV 3 (ℓ i - icast (l i))) (C : Matrix (Fin 6) (Fin 7) ℤ)
    (hC : ∀ k j, (8 : ℤ) ∣ (∑ i, C k i * l i j) - (if j = k then 4 else 0)) (k : Fin 6) :
    ∃ l' ∈ Λ, ∃ e : Fin 6 → ℤ_[2], DvdV 3 e ∧ (4 : ℤ_[2]) • Pi.single k 1 = l' + e := by
  rw [hΛ]
  set l' := ∑ i : Fin 7, (C k i : ℤ_[2]) • ℓ i with hl'
  have hl'_mem : l' ∈ Submodule.span ℤ_[2] (Set.range ℓ) := by
    rw [hl']
    refine Submodule.sum_mem _ ?_
    intro i _
    refine Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ?_
    exact ⟨i, rfl⟩
  set e := (4 : ℤ_[2]) • Pi.single k 1 - l' with he
  have heq : (4 : ℤ_[2]) • Pi.single k 1 = l' + e := by
    dsimp [e]
    abel
  have hDvdV : DvdV 3 e := by
    intro j
    dsimp [e, DvdV]
    simp only [Pi.single_apply]
    simp only [mul_ite, mul_one, mul_zero]
    have hlsum : l' j = ∑ i : Fin 7, (C k i : ℤ_[2]) * ℓ i j := by
      dsimp [l']
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hlsum]
    have h_split : (if j = k then (4 : ℤ_[2]) else 0) - ∑ i : Fin 7, (C k i : ℤ_[2]) * ℓ i j =
      - (∑ i : Fin 7, (C k i : ℤ_[2]) * (ℓ i j - (l i j : ℤ_[2]))) +
      ((if j = k then (4 : ℤ_[2]) else 0) - (∑ i : Fin 7, (C k i : ℤ_[2]) * (l i j : ℤ_[2]))) := by
      have hsum : ∑ i : Fin 7, (C k i : ℤ_[2]) * (ℓ i j - (l i j : ℤ_[2])) =
        (∑ i : Fin 7, (C k i : ℤ_[2]) * ℓ i j) - (∑ i : Fin 7, (C k i : ℤ_[2]) * (l i j : ℤ_[2])) := by
        simp [Finset.sum_sub_distrib, mul_sub]
      rw [hsum]
      ring
    rw [h_split]
    have hterm1 : (2 : ℤ_[2]) ^ 3 ∣ ∑ i : Fin 7, (C k i : ℤ_[2]) * (ℓ i j - (l i j : ℤ_[2])) := by
      refine Finset.dvd_sum ?_
      intro i hi
      have hdvd : (2 : ℤ_[2]) ^ 3 ∣ ℓ i j - (l i j : ℤ_[2]) := by
        have := hl i j
        simpa [DvdV, icast] using this
      exact hdvd.mul_left (C k i : ℤ_[2])
    have hterm2 : (2 : ℤ_[2]) ^ 3 ∣ (if j = k then (4 : ℤ_[2]) else 0) - (∑ i : Fin 7, (C k i : ℤ_[2]) * (l i j : ℤ_[2])) := by
      have hsum_cast : (∑ i : Fin 7, (C k i : ℤ_[2]) * (l i j : ℤ_[2])) = ((∑ i : Fin 7, C k i * l i j : ℤ) : ℤ_[2]) := by
        simp [Int.cast_sum, Int.cast_mul]
      rw [hsum_cast]
      have h_dvd_int : (8 : ℤ) ∣ (∑ i : Fin 7, C k i * l i j) - (if j = k then 4 else 0) := hC k j
      have h_dvd_icast : (8 : ℤ_[2]) ∣ ((∑ i : Fin 7, C k i * l i j : ℤ) - (if j = k then 4 else 0) : ℤ_[2]) := by
        simpa using map_dvd (Int.castRingHom ℤ_[2]) h_dvd_int
      have h_expr : (if j = k then (4 : ℤ_[2]) else 0) - ((∑ i : Fin 7, C k i * l i j : ℤ) : ℤ_[2]) =
        -(((∑ i : Fin 7, C k i * l i j : ℤ) : ℤ_[2]) - (if j = k then (4 : ℤ_[2]) else 0)) := by
        ring
      rw [h_expr]
      have h8 : (8 : ℤ_[2]) = (2 : ℤ_[2]) ^ 3 := by norm_num
      rw [h8] at h_dvd_icast
      exact dvd_neg.mpr h_dvd_icast
    have h_neg : (2 : ℤ_[2]) ^ 3 ∣ - (∑ i : Fin 7, (C k i : ℤ_[2]) * (ℓ i j - (l i j : ℤ_[2]))) :=
      dvd_neg.mpr hterm1
    exact dvd_add h_neg hterm2
  refine ⟨l', hl'_mem, e, hDvdV, heq⟩

theorem FurioLombardo.M4.nakayama_four {Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2])}
    (h : ∀ k : Fin 6, ∃ l ∈ Λ, ∃ e : Fin 6 → ℤ_[2], DvdV 3 e ∧ (4 : ℤ_[2]) • Pi.single k 1 = l + e) :
    ∀ x : Fin 6 → ℤ_[2], DvdV 2 x → x ∈ Λ := by
  classical
  set N' : Submodule ℤ_[2] (Fin 6 → ℤ_[2]) :=
    Submodule.span ℤ_[2] (Set.range fun k : Fin 6 => (4 : ℤ_[2]) • Pi.single k (1 : ℤ_[2])) with hN'
  -- every vector with all coordinates divisible by 4 lies in N'
  have hin : ∀ y : Fin 6 → ℤ_[2], DvdV 2 y → y ∈ N' := by
    intro y hy
    choose t ht using hy
    have e : y = ∑ k, t k • ((4 : ℤ_[2]) • Pi.single k (1 : ℤ_[2])) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp only [ite_true]
      rw [ht j]; norm_num; ring
    rw [e]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hfg : N'.FG := Submodule.fg_span (Set.finite_range _)
  have hI : Ideal.span {(2 : ℤ_[2])} ≤ Ideal.jacobson ⊥ := by
    have h2 : Ideal.span {(2 : ℤ_[2])} = IsLocalRing.maximalIdeal ℤ_[2] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; norm_num
    rw [h2]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥
  have hNN : N' ≤ Λ ⊔ Ideal.span {(2 : ℤ_[2])} • N' := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    obtain ⟨l, hl, e, he, hsum⟩ := h k
    show (4 : ℤ_[2]) • Pi.single k (1 : ℤ_[2]) ∈ Λ ⊔ Ideal.span {(2 : ℤ_[2])} • N'
    rw [hsum]
    apply Submodule.add_mem_sup hl
    choose t ht using he
    have e2 : e = (2 : ℤ_[2]) • (fun j => 4 * t j) := by
      funext j; simp only [Pi.smul_apply, smul_eq_mul]; rw [ht j]; ring
    rw [e2]
    apply Submodule.smul_mem_smul (Ideal.mem_span_singleton_self 2)
    exact hin _ (fun j => ⟨t j, by ring⟩)
  intro x hx
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hfg hI hNN (hin x hx)

theorem FurioLombardo.M4.col_mem {Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} (ℓ : Fin 7 → Fin 6 → ℤ_[2])
    (hΛ : Λ = Submodule.span ℤ_[2] (Set.range ℓ)) (h4 : ∀ x, DvdV 2 x → x ∈ Λ) (l : Fin 7 → Fin 6 → ℤ)
    (hl : ∀ i, DvdV 2 (ℓ i - icast (l i))) (H : Matrix (Fin 6) (Fin 6) ℤ) (Cp : Matrix (Fin 7) (Fin 6) ℤ)
    (hCp : ∀ j k, (4 : ℤ) ∣ H j k - ∑ i, l i j * Cp i k) (k : Fin 6) : icast (fun j => H j k) ∈ Λ := by
  have hsum : (∑ i, (Cp i k : ℤ_[2]) • ℓ i) ∈ Λ := by
    rw [hΛ]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
  have he : DvdV 2 (icast (fun j => H j k) - ∑ i, (Cp i k : ℤ_[2]) • ℓ i) := by
    intro j
    have e : (icast (fun j => H j k) - ∑ i, (Cp i k : ℤ_[2]) • ℓ i) j =
        (((H j k - ∑ i, l i j * Cp i k : ℤ)) : ℤ_[2]) - ∑ i, (Cp i k : ℤ_[2]) * (ℓ i j - icast (l i) j) := by
      simp only [icast, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      simp only [mul_comm]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [e]
    apply dvd_sub
    · have h := map_dvd (Int.castRingHom ℤ_[2]) (hCp j k)
      norm_num at h ⊢
      exact h
    · exact Finset.dvd_sum (fun i _ => Dvd.dvd.mul_left (hl i j) _)
  have := Λ.add_mem hsum (h4 _ he)
  simpa using this

theorem FurioLombardo.M4.mem_of_imv_dvd {Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} (H G : Matrix (Fin 6) (Fin 6) ℤ)
    (hHG : H * G = (4 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ))
    (hcol : ∀ k : Fin 6, icast (fun j => H j k) ∈ Λ) {x : Fin 6 → ℤ_[2]}
    (hx : ∀ j, (4 : ℤ_[2]) ∣ imv G x j) : x ∈ Λ := by
  have h4 : (4 : ℤ_[2]) ≠ 0 := by norm_num
  choose y hy using hx
  have hG : imv G x = (4 : ℤ_[2]) • y := by
    funext j; rw [hy j]; rfl
  have h_eq : (4 : ℤ_[2]) • x = (4 : ℤ_[2]) • imv H y := by
    have e1 : imv ((4 : ℤ) • (1 : Matrix (Fin 6) (Fin 6) ℤ)) x = ((4 : ℤ) : ℤ_[2]) • x := imv_scalar 4 x
    rw [← hHG, imv_mul, hG] at e1
    have e2 : imv H ((4 : ℤ_[2]) • y) = (4 : ℤ_[2]) • imv H y := by
      unfold imv; rw [Matrix.mulVec_smul]
    rw [e2] at e1
    rw [show ((4 : ℤ) : ℤ_[2]) = 4 by norm_num] at e1
    exact e1.symm
  have hxe : x = imv H y := smul_right_injective _ h4 h_eq
  have hsum : imv H y = ∑ k : Fin 6, y k • icast (fun j => H j k) := by
    funext i
    simp [imv, icast, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hxe, hsum]
  exact Submodule.sum_mem Λ (fun k _ => Submodule.smul_mem Λ (y k) (hcol k))

theorem FurioLombardo.M4.mem_isSatOf {Λ S : Submodule ℤ_[2] V} {a b : V} (h : IsSatOf Λ S a b) (ha : a ∈ Λ) (hb : b ∈ Λ) (α β : ℤ_[2]) :
    α • a + β • b ∈ S := by
  apply (h (α • a + β • b)).mpr
  constructor
  · exact Submodule.add_mem Λ (Submodule.smul_mem Λ α ha) (Submodule.smul_mem Λ β hb)
  · refine ⟨0, ?_⟩
    have ha_span : a ∈ Submodule.span ℤ_[2] {a, b} := Submodule.subset_span (by simp)
    have hb_span : b ∈ Submodule.span ℤ_[2] {a, b} := Submodule.subset_span (by simp)
    have hαa : α • a ∈ Submodule.span ℤ_[2] {a, b} := Submodule.smul_mem _ α ha_span
    have hβb : β • b ∈ Submodule.span ℤ_[2] {a, b} := Submodule.smul_mem _ β hb_span
    simpa [pow_zero, one_smul] using Submodule.add_mem _ hαa hβb

theorem FurioLombardo.M4.saturated_of_isSatOf {Λ S : Submodule ℤ_[2] V} {a b : V} (h : IsSatOf Λ S a b) : Saturated Λ S := by
  refine ⟨?_, ?_⟩
  · intro x hxS
    exact ((h x).mp hxS).1
  · intro x hxΛ h2xS
    have h2x := (h ((2 : ℤ_[2]) • x)).mp h2xS
    rcases h2x with ⟨h2xΛ, m, hm⟩
    have hx : (2 : ℤ_[2]) ^ (m + 1) • x ∈ Submodule.span ℤ_[2] {a, b} := by
      rw [pow_succ, mul_smul]
      exact hm
    exact ((h x).mpr ⟨hxΛ, m + 1, hx⟩)

theorem FurioLombardo.M4.inSL_of_Q {Λ S : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {r : ℕ} (H Ut UG : Matrix (Fin 6) (Fin 6) ℤ) (D : ℤ)
    (hD : IsUnit (D : ℤ_[2])) (hid : H * Ut * UG = (4 * D) • (1 : Matrix (Fin 6) (Fin 6) ℤ))
    (hcol : ∀ k : Fin 6, icast (fun j => (H * Ut) j k) ∈ Λ)
    (hsig : ∀ k : Fin 6, k.val < 2 → ∀ n ≤ r, InSL Λ S n (icast (fun j => (H * Ut) j k)))
    (h4 : ∀ x ∈ Λ, ∀ j, (4 : ℤ_[2]) ∣ imv UG x j) {n : ℕ} (hn : n ≤ r) {x : Fin 6 → ℤ_[2]}
    (hx : x ∈ Λ) (hQ : ∀ o : Fin 6, 2 ≤ o.val → (2 : ℤ_[2]) ^ (n + 2) ∣ imv UG x o) : InSL Λ S n x := by
  classical
  choose z hz using fun j => h4 x hx j
  have hzn : ∀ o : Fin 6, 2 ≤ o.val → (2 : ℤ_[2]) ^ n ∣ z o := by
    intro o ho
    have h := hQ o ho
    have e : (2 : ℤ_[2]) ^ (n + 2) = 4 * 2 ^ n := by rw [pow_add]; norm_num; ring
    rw [e, hz o] at h
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ_[2]) ≠ 0)).mp h
  have hzv : imv UG x = (4 : ℤ_[2]) • z := funext fun j => by rw [hz j]; rfl
  have hDx : (D : ℤ_[2]) • x = imv (H * Ut) z := by
    have h1 : imv (H * Ut * UG) x = (((4 * D : ℤ)) : ℤ_[2]) • x := by rw [hid, imv_scalar]
    have hs : imv (H * Ut) ((4 : ℤ_[2]) • z) = (4 : ℤ_[2]) • imv (H * Ut) z := Matrix.mulVec_smul _ _ _
    rw [imv_mul, hzv, hs] at h1
    apply smul_right_injective (Fin 6 → ℤ_[2]) (by norm_num : (4 : ℤ_[2]) ≠ 0)
    simp only
    rw [h1, smul_smul]; push_cast; rfl
  have hsum : imv (H * Ut) z = ∑ k, z k • icast (fun j => (H * Ut) j k) := by
    funext j
    simp [imv, Matrix.mulVec, dotProduct, Finset.sum_apply, icast, mul_comm]
  apply inSL_of_unit_smul hD
  rw [hDx, hsum]
  apply Finset.sum_induction _ (InSL Λ S n) (fun a b ha hb => inSL_add ha hb)
    ⟨0, S.zero_mem, 0, Λ.zero_mem, by simp⟩
  intro k _
  by_cases hk : k.val < 2
  · exact inSL_smul (z k) (hsig k hk n hn)
  · exact inSL_of_mem (hcol k) (z k) (hzn k (by omega))

theorem FurioLombardo.M4.dvd_imv_of_mem_span {Λ : Submodule ℤ_[2] (Fin 6 → ℤ_[2])} {k : ℕ} (ℓ : Fin k → Fin 6 → ℤ_[2])
    (hΛ : Λ = Submodule.span ℤ_[2] (Set.range ℓ)) (G : Matrix (Fin 6) (Fin 6) ℤ) (N : ℕ)
    (hℓ : ∀ i j, (2 : ℤ_[2]) ^ N ∣ imv G (ℓ i) j) {x : Fin 6 → ℤ_[2]} (hx : x ∈ Λ) (j : Fin 6) :
    (2 : ℤ_[2]) ^ N ∣ imv G x j := by
  rw [hΛ] at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, rfl⟩
    exact hℓ i j
  · simp [imv]
  · intro a b ha_mem hb_mem ih_a ih_b
    have h_add : imv G (a + b) j = imv G a j + imv G b j := by
      simp [imv, Matrix.mulVec_add]
    rw [h_add]
    exact dvd_add ih_a ih_b
  · intro r a ha_mem ih_a
    have h_smul : imv G (r • a) j = r * imv G a j := by
      simp [imv, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    rw [h_smul]
    exact (dvd_mul_of_dvd_right ih_a r)
