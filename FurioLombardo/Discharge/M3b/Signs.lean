import FurioLombardo.Discharge.M3b.RamN
import FurioLombardo.Discharge.M3b.DyadicRho

/-!
# `dyadicL` and `signsN`

* `dyadic_L42`: the dyadic reduction data of `L42 / K21` (`exists_dyadic`, DyadicRho.lean) with
  `δ = ω t`, `δ² = ε t² = d`; `δ ∉ K21` because its `ω`-coordinate is `t ≠ 0` (`t = 0` would give
  `ρ d = 0 ≠ D`).
* `signPattern_N84`: above each real embedding `realEmb k` of `K21` (`ε > 0` there) the two real
  embeddings `ω ↦ ±√ε` of `L42` give values of `e'` with product `m < 0`; the one where `e' < 0`
  defines a real place `w k` of `L42` ramified in `N84` (`mem_ramifiedRealPlaces_of_neg`). At
  `w k` the units `gO 7`, `gO 1 gO 3`, `gO 3` of `K21` take the signs of `realEmb k`, negative
  exactly for `k = 0`, `1`, `2` respectively (K21Real.lean).
-/

namespace FurioLombardo.Discharge.M3b

open FurioLombardo.M1 NumberField QuadraticAlgebra InfinitePlace

/-! ### dyadicL -/

theorem elt_D_ne_zero : FurioLombardo.M3b.DyadicCert.elt FurioLombardo.M3b.DyadicCert.D ≠ 0 := by
  intro h
  have h0 : FurioLombardo.M3b.DyadicCert.elt (0, 0, 0) = 0 := by
    simp [FurioLombardo.M3b.DyadicCert.elt]
  rw [← h0] at h
  have := FurioLombardo.M3b.DyadicCert.elt_injective h
  revert this
  decide

/-- **dyadicL**. -/
theorem dyadic_L42 : FurioLombardo.M3b.DyadicReduction K21 L42 := by
  obtain ⟨v, ρ, d, u, u', hd, hu, hρu, hρd⟩ := exists_dyadic
  refine ⟨v, ρ, (ω : L42) * algebraMap K21 L42 (tO : K21), d, u, u', ?_, ?_, hu, hρu, hρd⟩
  · rw [hd, map_mul, map_pow, mul_pow, sq (ω : L42), omega_mul_omega_zero]
  · intro k hk
    have him := congrArg QuadraticAlgebra.im hk
    simp [QuadraticAlgebra.algebraMap_eq] at him
    have hd0 : d = 0 := by
      apply Subtype.ext
      rw [hd, ← him]
      simp
    rw [hd0, map_zero] at hρd
    exact elt_D_ne_zero hρd.symm

/-! ### signsN -/

/-- `√(ε)` at `realEmb k`. -/
noncomputable def sqrtEps (k : Fin 3) : ℝ := Real.sqrt (realEmb k epsK)

theorem sqrtEps_mul (k : Fin 3) : sqrtEps k * sqrtEps k = realEmb k epsK :=
  Real.mul_self_sqrt (realEmb_epsK_pos k).le

theorem neg_sqrtEps_mul (k : Fin 3) : (-sqrtEps k) * (-sqrtEps k) = realEmb k epsK := by
  rw [neg_mul_neg]; exact sqrtEps_mul k

/-- The two real embeddings of `L42` above `realEmb k`. -/
noncomputable def τp (k : Fin 3) : L42 →+* ℝ := extendHom (realEmb k) (sqrtEps k) (sqrtEps_mul k)

noncomputable def τm (k : Fin 3) : L42 →+* ℝ :=
  extendHom (realEmb k) (-sqrtEps k) (neg_sqrtEps_mul k)

theorem τp_mul_τm (k : Fin 3) : τp k eN * τm k eN < 0 := by
  have h := mul_eq_norm_of_neg (τ₁ := τp k) (τ₂ := τm k)
    (by rw [τp, τm, extendHom_comp_algebraMap, extendHom_comp_algebraMap])
    (by rw [τp, τm, extendHom_omega, extendHom_omega, neg_neg]) eN
  rw [h, norm_eN, τm, extendHom_comp_algebraMap]
  exact realEmb_m_neg k

open scoped Classical in
/-- The real embedding of `L42` above `realEmb k` where `e' < 0`. -/
noncomputable def τN (k : Fin 3) : L42 →+* ℝ := if τp k eN < 0 then τp k else τm k

theorem τN_eN (k : Fin 3) : τN k eN < 0 := by
  unfold τN
  split_ifs with h
  · exact h
  · have h2 := τp_mul_τm k
    rw [not_lt] at h
    by_contra h3
    rw [not_lt] at h3
    exact absurd h2 (not_lt.mpr (mul_nonneg h h3))

theorem τN_comp (k : Fin 3) : (τN k).comp (algebraMap K21 L42) = realEmb k := by
  unfold τN
  split_ifs
  · exact extendHom_comp_algebraMap _ _ _
  · exact extendHom_comp_algebraMap _ _ _

/-- The real place `w k` of `L42`. -/
noncomputable def wN (k : Fin 3) : InfinitePlace L42 :=
  InfinitePlace.mk (Complex.ofRealHom.comp (τN k))

theorem wN_isReal (k : Fin 3) : (wN k).IsReal := isReal_mk_iff.mpr (isReal_ofReal_comp _)

theorem wN_mem (k : Fin 3) : wN k ∈ FurioLombardo.M3b.ramifiedRealPlaces L42 N84 := by
  refine mem_ramifiedRealPlaces_of_neg (a := eN) (wN k) (wN_isReal k) ?_
  have h2 : embedding_of_isReal (wN_isReal k) eN = τN k eN :=
    congrArg (fun f => f eN) (embedding_of_isReal_mk (τN k) (wN_isReal k))
  rw [h2]
  exact τN_eN k

theorem wN_embedding (k : Fin 3) (x : L42) : ((wN k).embedding x).re = τN k x := by
  unfold wN
  rw [embedding_mk_eq_of_isReal (isReal_ofReal_comp _)]
  simp

/-- The units `gO 7`, `gO 1 gO 3`, `gO 3` of `K21`. -/
noncomputable def unitK (i : Fin 3) : (𝓞 K21)ˣ :=
  match i with
  | 0 => Units.mkOfMulEqOne (gO 7) (gIO 7) (gO_mul_gIO 7 (by norm_num))
  | 1 => Units.mkOfMulEqOne (gO 1) (gIO 1) (gO_mul_gIO 1 (by norm_num)) *
      Units.mkOfMulEqOne (gO 3) (gIO 3) (gO_mul_gIO 3 (by norm_num))
  | 2 => Units.mkOfMulEqOne (gO 3) (gIO 3) (gO_mul_gIO 3 (by norm_num))

/-- Their images in `𝓞 L42`. -/
noncomputable def unitL (i : Fin 3) : (𝓞 L42)ˣ :=
  Units.map (algebraMap (𝓞 K21) (𝓞 L42)).toMonoidHom (unitK i)

theorem unitL_coe (i : Fin 3) :
    ((unitL i : 𝓞 L42) : L42) = algebraMap K21 L42 ((unitK i : 𝓞 K21) : K21) := rfl

theorem realEmb_unitK_neg_iff (i k : Fin 3) :
    realEmb k ((unitK i : 𝓞 K21) : K21) < 0 ↔ i = k := by
  fin_cases i
  · simp only [unitK, Units.mkOfMulEqOne]
    rw [realEmb_gO7_neg_iff]; exact eq_comm
  · simp only [unitK, Units.mkOfMulEqOne, Units.val_mul]
    rw [show ((gO 1 * gO 3 : 𝓞 K21) : K21) = (gO 1 : K21) * (gO 3 : K21) from
      map_mul (algebraMap (𝓞 K21) K21) _ _, realEmb_gO1_mul_gO3_neg_iff]
    exact eq_comm
  · simp only [unitK, Units.mkOfMulEqOne]
    rw [realEmb_gO3_neg_iff]; exact eq_comm

/-- **signsN**: the diagonal sign pattern at three real places of `L42` ramified in `N84`. -/
theorem signPattern_N84 : FurioLombardo.M3b.SignPattern L42 N84 3 := by
  refine ⟨wN, unitL, wN_mem, fun i j => ?_⟩
  rw [wN_embedding, unitL_coe, ← RingHom.comp_apply, τN_comp]
  exact realEmb_unitK_neg_iff i j

end FurioLombardo.Discharge.M3b
