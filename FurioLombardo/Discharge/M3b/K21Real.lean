import FurioLombardo.Discharge.M3b.K21Defs
import FurioLombardo.Discharge.M3b.DataL
import FurioLombardo.Discharge.M3b.RealCert

/-!
# The real embeddings of `K21` and the signs used by the M3b discharge

`realEmb k` is the real embedding with `θ` in the `k`-th root interval of `f` (roots near -0.8799,
-0.8361, 1.8940 for k = 0, 1, 2); these are all the ring homomorphisms `K21 →+* ℝ`.

Certificate (found by code/selmer-global-bound/real_root_cert.gp, PARI/GP; rechecked here by the
kernel with the Möbius sign certificates of RealCert.lean), all over the denominator `Dr = 2^24`:
* `f < 0` on `(-∞, -4)`, `f > 0` on `(4, ∞)`; breakpoints `-4, -2, -1, -7/8, -27/32, -13/16, -3/4,
  -1/2, 0, 1, 3/2, 7/4, 2, 4`, `f ≠ 0` at each; on every piece between them `f` has a sign, except
  the three pieces `monoR` = `(-1, -7/8)`, `(-27/32, -13/16)`, `(7/4, 2)`, where `f'` has a sign
  (`rootCover`, `ck_mono`). So every real root of `f` lies in one of these pieces, at most one each.
* the root intervals `(rtA k / Dr, rtB k / Dr)`, inside the pieces, where `f` changes sign
  (`ck_bracket`), and on which the elements `ε`, `gO 1`, `gO 3`, `gO 7`, `m` have a certified sign.
-/

namespace FurioLombardo.Discharge.M3b

open FurioLombardo.M1 FurioLombardo.M1.Kron NumberField Polynomial

/-! ## The certificate -/

/-- The common denominator. -/
def Dr : ℕ := 16777216

/-- The first breakpoint, `-4`. -/
def bpLo : ℤ := -67108864

/-- The other breakpoints, `-2, -1, -7/8, -27/32, -13/16, -3/4, -1/2, 0, 1, 3/2, 7/4, 2, 4`. -/
def bpL : List ℤ := [-33554432, -16777216, -14680064, -14155776, -13631488, -12582912, -8388608, 0,
  16777216, 25165824, 29360128, 33554432, 67108864]

/-- The pieces where `f` is monotone: `(-1, -7/8)`, `(-27/32, -13/16)`, `(7/4, 2)`. -/
def monoR : Fin 3 → ℤ × ℤ :=
  ![(-16777216, -14680064), (-14155776, -13631488), (29360128, 33554432)]

/-- Signs of `f'` on the pieces `monoR`. -/
def monoS : Fin 3 → ℤ := ![1, -1, 1]

/-- The root intervals: lower ends. -/
def rtA : Fin 3 → ℤ := ![-14762752, -14028800, 31776570]

/-- The root intervals: upper ends. -/
def rtB : Fin 3 → ℤ := ![-14762496, -14026752, 31776571]

theorem ck_cover : rootCover Dr fL [monoR 0, monoR 1, monoR 2] bpLo bpL = true := by
  decide +kernel

theorem ck_mono : ∀ k : Fin 3,
    signCert (monoS k) [(monoR k).1, (monoR k).2] [(Dr : ℤ), (Dr : ℤ)] (derivL fL) = true := by
  decide +kernel

theorem ck_bracket : ∀ k : Fin 3, bracketL Dr fL (rtA k) (rtB k) = true := by
  decide +kernel

theorem ck_inside : ∀ k : Fin 3, (monoR k).1 ≤ rtA k ∧ rtB k ≤ (monoR k).2 := by
  decide +kernel

/-- Sign certificate of the element with zk coordinates `a` on the root intervals. -/
def elemCert (a : List ℤ) (s : Fin 3 → ℤ) : Prop :=
  ∀ k : Fin 3, signCert (s k) [rtA k, rtB k] [(Dr : ℤ), (Dr : ℤ)] (combo a zkNum) = true

theorem ck_eps : elemCert epsL ![1, 1, 1] := by
  unfold elemCert; decide +kernel

theorem ck_m : elemCert mL ![-1, -1, -1] := by
  unfold elemCert; decide +kernel

theorem ck_g1 : elemCert (gensL.getD 1 []) ![1, -1, -1] := by
  unfold elemCert; decide +kernel

theorem ck_g3 : elemCert (gensL.getD 3 []) ![1, 1, -1] := by
  unfold elemCert; decide +kernel

theorem ck_g7 : elemCert (gensL.getD 7 []) ![-1, 1, 1] := by
  unfold elemCert; decide +kernel

/-! ## The three real roots -/

theorem Dr_pos : 0 < Dr := by decide

theorem exists_rootR (k : Fin 3) :
    ∃ r : ℝ, (rtA k : ℝ) / Dr < r ∧ r < (rtB k : ℝ) / Dr ∧ evalL r fL = 0 :=
  exists_root_of_bracketL Dr_pos (ck_bracket k)

/-- The `k`-th real root of `f`. -/
noncomputable def rootR (k : Fin 3) : ℝ := (exists_rootR k).choose

theorem rootR_spec (k : Fin 3) :
    (rtA k : ℝ) / Dr < rootR k ∧ rootR k < (rtB k : ℝ) / Dr ∧ evalL (rootR k) fL = 0 :=
  (exists_rootR k).choose_spec

theorem eval₂_fQ (r : ℝ) : fQ.eval₂ (algebraMap ℚ ℝ) r = evalL r fL := by
  have h : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := RingHom.ext_int _ _
  rw [fQ, eval₂_map, h, ← ofListL_fL, evalL_ofListL]

theorem rootR_mem (k : Fin 3) :
    rootR k ∈ Set.Icc (((monoR k).1 : ℝ) / Dr) (((monoR k).2 : ℝ) / Dr) := by
  have hD : (0 : ℝ) < Dr := by exact_mod_cast Dr_pos
  obtain ⟨h1, h2⟩ := ck_inside k
  obtain ⟨h3, h4, -⟩ := rootR_spec k
  constructor
  · refine le_trans ?_ h3.le
    exact div_le_div_of_nonneg_right (by exact_mod_cast h1) hD.le
  · refine le_trans h4.le ?_
    exact div_le_div_of_nonneg_right (by exact_mod_cast h2) hD.le

/-- Every real root of `f` is one of the `rootR k`. -/
theorem eq_rootR {x : ℝ} (hx : evalL x fL = 0) : ∃ k, x = rootR k := by
  obtain ⟨p, hp, h1, h2⟩ := rootCover_sound Dr_pos ck_cover hx
  have key : ∀ k, p = monoR k → x = rootR k := by
    intro k hk
    subst hk
    refine injOn_of_signCert Dr_pos (ck_mono k) ⟨h1.le, h2.le⟩ (rootR_mem k) ?_
    simp only
    rw [hx, (rootR_spec k).2.2]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp
  exacts [⟨0, key 0 hp⟩, ⟨1, key 1 hp⟩, ⟨2, key 2 hp⟩]

theorem rootR_lt_01 : rootR 0 < rootR 1 := by
  have h0 := (rootR_spec 0).2.1
  have h1 := (rootR_spec 1).1
  have hD : (0 : ℝ) < Dr := by exact_mod_cast Dr_pos
  have : ((rtB 0 : ℤ) : ℝ) / Dr ≤ ((rtA 1 : ℤ) : ℝ) / Dr :=
    div_le_div_of_nonneg_right (by exact_mod_cast (by decide : rtB 0 ≤ rtA 1)) hD.le
  linarith

theorem rootR_lt_12 : rootR 1 < rootR 2 := by
  have h0 := (rootR_spec 1).2.1
  have h1 := (rootR_spec 2).1
  have hD : (0 : ℝ) < Dr := by exact_mod_cast Dr_pos
  have : ((rtB 1 : ℤ) : ℝ) / Dr ≤ ((rtA 2 : ℤ) : ℝ) / Dr :=
    div_le_div_of_nonneg_right (by exact_mod_cast (by decide : rtB 1 ≤ rtA 2)) hD.le
  linarith

/-! ## The embeddings -/

/-- The three real embeddings of `K21`. -/
noncomputable def realEmb (k : Fin 3) : K21 →+* ℝ :=
  AdjoinRoot.lift (algebraMap ℚ ℝ) (rootR k) (by rw [eval₂_fQ]; exact (rootR_spec k).2.2)

theorem realEmb_θ (k : Fin 3) : realEmb k θ = rootR k := AdjoinRoot.lift_root _

theorem realEmb_zkE (k : Fin 3) (a : List ℤ) :
    realEmb k (zkE a) = (Dz : ℝ)⁻¹ * evalL (rootR k) (combo a zkNum) := by
  show realEmb k (dInv * evalL θ (combo a zkNum)) = _
  rw [map_mul, dInv, map_inv₀, map_natCast, evalL_hom, realEmb_θ]

theorem realEmb_injective : Function.Injective realEmb := by
  intro k k' h
  have e : rootR k = rootR k' := by rw [← realEmb_θ, ← realEmb_θ, h]
  have h01 := rootR_lt_01
  have h12 := rootR_lt_12
  match k, k', e with
  | 0, 0, _ => rfl
  | 1, 1, _ => rfl
  | 2, 2, _ => rfl
  | 0, 1, e => exact absurd e h01.ne
  | 1, 0, e => exact absurd e h01.ne'
  | 1, 2, e => exact absurd e h12.ne
  | 2, 1, e => exact absurd e h12.ne'
  | 0, 2, e => exact absurd e (h01.trans h12).ne
  | 2, 0, e => exact absurd e (h01.trans h12).ne'

theorem exists_eq_realEmb (σ : K21 →+* ℝ) : ∃ k, σ = realEmb k := by
  have hx : evalL (σ θ) fL = 0 := by rw [← evalL_hom, evalL_θ_fL, map_zero]
  obtain ⟨k, hk⟩ := eq_rootR hx
  refine ⟨k, AdjoinRoot.ringHom_ext (Subsingleton.elim _ _) ?_⟩
  change σ θ = realEmb k θ
  rw [realEmb_θ, hk]

/-! ## Signs -/

theorem elem_sign {a : List ℤ} {s : Fin 3 → ℤ} (h : elemCert a s) (k : Fin 3) :
    0 < (s k : ℝ) * realEmb k (zkE a) := by
  rw [realEmb_zkE]
  have h1 := signCert_Ioo Dr_pos (h k) (rootR_spec k).1 (rootR_spec k).2.1
  have hDz : (0 : ℝ) < (Dz : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (by decide : 0 < Dz))
  calc (0 : ℝ) < (Dz : ℝ)⁻¹ * ((s k : ℝ) * evalL (rootR k) (combo a zkNum)) := mul_pos hDz h1
    _ = _ := by ring

theorem neg_iff_of_pos_mul {s : ℤ} {v : ℝ} (hs : s = 1 ∨ s = -1) (h : 0 < (s : ℝ) * v) :
    v < 0 ↔ s = -1 := by
  rcases hs with rfl | rfl
  · simp only [Int.cast_one, one_mul] at h
    constructor
    · intro hv; linarith
    · intro h'; norm_num at h'
  · simp only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_pos] at h
    exact ⟨fun _ => rfl, fun _ => h⟩

theorem realEmb_epsK_pos (k : Fin 3) : 0 < realEmb k epsK := by
  have h := elem_sign ck_eps k
  have hs : ∀ k : Fin 3, (![1, 1, 1] : Fin 3 → ℤ) k = 1 := by decide
  rw [hs k, Int.cast_one, one_mul] at h
  exact h

theorem realEmb_m_neg (k : Fin 3) : realEmb k (zkE mL) < 0 := by
  have h := elem_sign ck_m k
  have hs : ∀ k : Fin 3, (![-1, -1, -1] : Fin 3 → ℤ) k = -1 := by decide
  rw [hs k, Int.cast_neg, Int.cast_one, neg_mul, one_mul, neg_pos] at h
  exact h

theorem realEmb_gO7_neg_iff (k : Fin 3) : realEmb k (gO 7 : K21) < 0 ↔ k = 0 := by
  rw [show (gO 7 : K21) = zkE (gensL.getD 7 []) from rfl,
    neg_iff_of_pos_mul (by revert k; decide) (elem_sign ck_g7 k)]
  revert k; decide

theorem realEmb_gO1_mul_gO3_neg_iff (k : Fin 3) :
    realEmb k ((gO 1 : K21) * (gO 3 : K21)) < 0 ↔ k = 1 := by
  rw [show (gO 1 : K21) = zkE (gensL.getD 1 []) from rfl,
    show (gO 3 : K21) = zkE (gensL.getD 3 []) from rfl, map_mul]
  have h1 := elem_sign ck_g1 k
  have h3 := elem_sign ck_g3 k
  have h : 0 < (((![1, -1, -1] : Fin 3 → ℤ) k * (![1, 1, -1] : Fin 3 → ℤ) k : ℤ) : ℝ) *
      (realEmb k (zkE (gensL.getD 1 [])) * realEmb k (zkE (gensL.getD 3 []))) := by
    have := mul_pos h1 h3
    push_cast
    linarith
  have hs : ∀ k : Fin 3,
      (((![1, -1, -1] : Fin 3 → ℤ) k * (![1, 1, -1] : Fin 3 → ℤ) k = 1 ∨
        (![1, -1, -1] : Fin 3 → ℤ) k * (![1, 1, -1] : Fin 3 → ℤ) k = -1) ∧
      ((![1, -1, -1] : Fin 3 → ℤ) k * (![1, 1, -1] : Fin 3 → ℤ) k = -1 ↔ k = 1)) := by
    decide
  rw [neg_iff_of_pos_mul (hs k).1 h]
  exact (hs k).2

theorem realEmb_gO3_neg_iff (k : Fin 3) : realEmb k (gO 3 : K21) < 0 ↔ k = 2 := by
  rw [show (gO 3 : K21) = zkE (gensL.getD 3 []) from rfl,
    neg_iff_of_pos_mul (by revert k; decide) (elem_sign ck_g3 k)]
  revert k; decide

end FurioLombardo.Discharge.M3b
