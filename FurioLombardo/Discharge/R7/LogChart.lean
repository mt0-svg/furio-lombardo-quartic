import Mathlib
import FurioLombardo.Discharge.R7.KvBall
import FurioLombardo.Discharge.Analytic.ModTwo

/-!
# `LogChartFin` from the logarithmic chart of a formal group law over `OKv` (item R7.6)

For a formal group law `Φ` of dimension 2 over `OKv` and an injective homomorphism
`ψ : Φ.Points →+ B` into an abelian group, the logarithmic chart `log_chart_OKv` gives an additive
bijection `L : B1 Φ c → OKv²` (`c = pv ^ 4`, the scaled logarithm `z = c y ↦ logVal y`). Its
transport `H' := ψ(B1 Φ c)` is then a subgroup of `B` isomorphic to `OKv² ≅ ℤ_[2] ^ 6`
(`coordEquiv`, coordinates in the basis `1, pv, pv²`). Under the hypothesis `HFinIdx` (some
subgroup of finite index lies in `H'`; a theorem for the charts of `SetupKv`,
`FinIdx.hFinIdx_of_setupKv`), `H'` has finite index `m`, and
`lam b := lam1 (m • b)` is defined on all of `B`, injective on `H'`, with image of `H'` containing
`2 ^ a ℤ_[2] ^ 6` where `m = 2 ^ a r`, `r` odd. This is `Analytic.LogChartFin lam`
(`exists_logChartFin_of_chart`), and on `ψ(B1 Φ c)` the map `lam` is `m` times the coordinates of
the scaled logarithm `logVal` itself.

Generic parts: `eq_zero_of_nsmul_eq_zero` (`ℤ_[2] ^ n` is torsion free), `isUnit_natCast_of_odd`,
`exists_addSubgroup_of_bijective` (the image of a submonoid with a bijective additive map to a
group is a subgroup), `exists_logChartFin` (the extension `b ↦ lam1 (m • b)`).
-/

namespace FurioLombardo.Discharge.R7

open FurioLombardo.Vendor.Toolbox.UnitBall FurioLombardo.Vendor.Toolbox.FormalGroup FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman FurioLombardo.Discharge.M4Cert

/-! ### Generic lemmas -/

/-- `ℤ_[2] ^ n` has no torsion. -/
theorem eq_zero_of_nsmul_eq_zero {n : ℕ} {m : ℕ} (hm : m ≠ 0) {x : Fin n → ℤ_[2]}
    (h : m • x = 0) : x = 0 := by
  funext i
  have h_i := congrFun h i
  have h_mul : (m : ℤ_[2]) * x i = 0 := by
    simpa [nsmul_eq_mul] using h_i
  have hm_ne_zero : (m : ℤ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr hm
  exact (mul_eq_zero.mp h_mul).resolve_left hm_ne_zero

/-- An odd natural number is a unit of `ℤ_[2]`. -/
theorem isUnit_natCast_of_odd {r : ℕ} (hr : ¬ 2 ∣ r) : IsUnit (r : ℤ_[2]) :=
  PadicInt.isUnit_iff.mpr <| PadicInt.norm_natCast_eq_one_iff.mpr <|
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hr

/-- The image under an injective `ψ` of a submonoid `S` carrying an additive bijection `L` onto a
group is a subgroup `H`, with an additive bijection `e : H → V` transporting `L`. -/
theorem exists_addSubgroup_of_bijective {M G V : Type*} [AddCommMonoid M] [AddCommGroup G]
    [AddCommGroup V] (S : AddSubmonoid M) (ψ : M →+ G) (hψ : Function.Injective ψ)
    (L : S →+ V) (hL : Function.Bijective L) :
    ∃ (H : AddSubgroup G) (e : H →+ V), Function.Bijective e ∧
      (∀ g ∈ H, ∃ z : S, ψ z = g) ∧ ∀ z : S, ∃ h : ψ z ∈ H, e ⟨ψ z, h⟩ = L z := by
  have hL_inj : Function.Injective L := hL.injective
  have hL_surj : Function.Surjective L := hL.surjective
  have h_neg : ∀ z : S, ∃ z' : S, z + z' = 0 := by
    intro z
    obtain ⟨z', hz'⟩ := hL_surj (-L z)
    refine ⟨z', ?_⟩
    apply hL_inj
    simp [hz']
  let H : AddSubgroup G :=
    { carrier := Set.image ψ (S : Set M)
      zero_mem' := by
        refine ⟨0, S.zero_mem, ?_⟩
        simp
      add_mem' := by
        rintro a b ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
        refine ⟨z + w, S.add_mem hz hw, ?_⟩
        simp
      neg_mem' := by
        rintro a ⟨z, hz, rfl⟩
        obtain ⟨z', hz'⟩ := h_neg ⟨z, hz⟩
        refine ⟨z', z'.2, ?_⟩
        have h_eq : ψ z + ψ (z' : M) = 0 := by
          have h := congrArg (λ (x : S) => ψ (x : M)) hz'
          simpa [map_add, map_zero] using h
        calc
          ψ (z' : M) = (ψ z + ψ (z' : M)) - ψ z := by abel
          _ = 0 - ψ z := by rw [h_eq]
          _ = -ψ z := by simp
    }
  let j : S →+ H :=
    { toFun := λ z => Subtype.mk (ψ z) ⟨z, z.2, rfl⟩
      map_add' := by
        intro x y
        ext
        simp
      map_zero' := by
        ext
        simp
    }
  have hj_inj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply hψ
    have hval := congrArg (λ (t : H) => (t : G)) h
    simpa [j] using hval
  have hj_surj : Function.Surjective j := by
    intro h
    have hmem : (h : G) ∈ (H : Set G) := h.property
    rcases hmem with ⟨z, hz, hz_eq⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    simpa [j] using hz_eq
  have hj_bijective : Function.Bijective j := ⟨hj_inj, hj_surj⟩
  let j_equiv : S ≃+ H := AddEquiv.ofBijective j hj_bijective
  let e : H →+ V := L.comp j_equiv.symm.toAddMonoidHom
  have he_bijective : Function.Bijective e := by
    have h_symm_bijective : Function.Bijective j_equiv.symm :=
      ⟨j_equiv.symm.injective, j_equiv.symm.surjective⟩
    simpa [e] using Function.Bijective.comp hL h_symm_bijective
  have h_forall_g : ∀ g ∈ H, ∃ z : S, ψ z = g := by
    intro g hg
    rcases hg with ⟨z, hz, hz_eq⟩
    exact ⟨⟨z, hz⟩, hz_eq⟩
  have h_forall_z : ∀ z : S, ∃ h : ψ z ∈ H, e ⟨ψ z, h⟩ = L z := by
    intro z
    have hmem : ψ (z : M) ∈ (H : Set G) := by
      refine ⟨z, z.2, rfl⟩
    have h_j_symm : j_equiv.symm ⟨ψ z, hmem⟩ = z := by
      apply j_equiv.injective
      rw [AddEquiv.apply_symm_apply]
      dsimp [j_equiv, j]
      apply Subtype.ext
      rfl
    refine ⟨hmem, ?_⟩
    calc
      e ⟨ψ z, hmem⟩ = (L.comp j_equiv.symm.toAddMonoidHom) ⟨ψ z, hmem⟩ := rfl
      _ = L (j_equiv.symm ⟨ψ z, hmem⟩) := rfl
      _ = L z := by rw [h_j_symm]
  exact ⟨H, e, he_bijective, h_forall_g, h_forall_z⟩

/-- **Extension of a chart from a subgroup of finite index**: for `B1` of finite index `m` and
`lam1 : B1 → ℤ_[2] ^ 6` injective with image containing `2 ^ N ℤ_[2] ^ 6`, the homomorphism
`lam := lam1 (m • ·)` on `B` satisfies `LogChartFin` and equals `m • lam1` on `B1`. -/
theorem exists_logChartFin {B : Type*} [AddCommGroup B] (B1 : AddSubgroup B) [B1.FiniteIndex]
    (lam1 : B1 →+ (Fin 6 → ℤ_[2])) (hinj : Function.Injective lam1) (N : ℕ)
    (hsurj : ∀ v : Fin 6 → ℤ_[2], ∃ b : B1, lam1 b = (2 : ℤ_[2]) ^ N • v) :
    ∃ lam : B →+ (Fin 6 → ℤ_[2]), Analytic.LogChartFin lam ∧
      ∀ b : B1, lam b = B1.index • lam1 b := by
  set m := B1.index
  have hm0 : m ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  let μ : B →+ B1 :=
    { toFun := fun b ↦ ⟨m • b, AddSubgroup.nsmul_index_mem B1 b⟩
      map_zero' := Subtype.ext (smul_zero m)
      map_add' := fun x y ↦ Subtype.ext (smul_add m x y) }
  have hμ : ∀ b : B1, lam1 (μ b) = m • lam1 b := fun b ↦ by
    rw [← map_nsmul]
    rfl
  refine ⟨lam1.comp μ, ⟨B1, inferInstance, fun b hb h0 ↦ ?_, ?_⟩, hμ⟩
  · have h1 : lam1 ⟨b, hb⟩ = 0 := eq_zero_of_nsmul_eq_zero hm0 ((hμ ⟨b, hb⟩).symm.trans h0)
    exact congrArg Subtype.val (hinj (h1.trans (map_zero lam1).symm))
  · obtain ⟨a, r, hr, hmr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 2 (by norm_num)
    obtain ⟨u, hu⟩ := isUnit_natCast_of_odd hr
    refine ⟨N + a, fun v ↦ ?_⟩
    obtain ⟨b, hb⟩ := hsurj ((↑u⁻¹ : ℤ_[2]) • v)
    refine ⟨b, b.2, ?_⟩
    change lam1 (μ b) = _
    rw [hμ, hb, hmr, ← Nat.cast_smul_eq_nsmul ℤ_[2], smul_smul, smul_smul]
    congr 1
    push_cast
    rw [← hu, pow_add]
    calc (2 : ℤ_[2]) ^ a * u * 2 ^ N * ↑u⁻¹ = 2 ^ N * 2 ^ a * (u * ↑u⁻¹) := by ring
      _ = 2 ^ N * 2 ^ a := by rw [Units.mul_inv, mul_one]

/-! ### Coordinates on `OKv` -/

/-- The coordinates of an element of `OKv` in the basis `1, pv, pv²` are `2`-adic integers. -/
theorem norm_equivFun_le_one (x : OKv) (i : Fin 3) : ‖bKv.equivFun (x : Kv) i‖ ≤ 1 := by
  refine (norm_evQ_le_one_iff _).mp ?_ i
  rw [evQ_eq_equivFun, LinearEquiv.symm_apply_apply]
  exact x.2

/-- `OKv ≅ ℤ_[2] ^ 3`: coordinates in the basis `1, pv, pv²` (`norm_evQ_le_one_iff`). -/
noncomputable def okvEquiv : OKv ≃+ (Fin 3 → ℤ_[2]) where
  toFun x i := ⟨bKv.equivFun (x : Kv) i, norm_equivFun_le_one x i⟩
  invFun a := ⟨evQ fun i ↦ (a i : ℚ_[2]), (norm_evQ_le_one_iff _).mpr fun i ↦ (a i).2⟩
  left_inv x := Subtype.ext <| by
    change evQ (fun i ↦ bKv.equivFun (x : Kv) i) = x
    rw [evQ_eq_equivFun, LinearEquiv.symm_apply_apply]
  right_inv a := funext fun i ↦ PadicInt.ext <| by
    change bKv.equivFun (evQ fun i ↦ (a i : ℚ_[2])) i = (a i : ℚ_[2])
    rw [evQ_eq_equivFun, LinearEquiv.apply_symm_apply]
  map_add' x y := funext fun i ↦ PadicInt.ext <| by
    change bKv.equivFun ((x : Kv) + y) i = bKv.equivFun (x : Kv) i + bKv.equivFun (y : Kv) i
    rw [map_add, Pi.add_apply]

@[simp]
theorem coe_okvEquiv_apply (x : OKv) (i : Fin 3) :
    (okvEquiv x i : ℚ_[2]) = bKv.equivFun (x : Kv) i := rfl

/-- `x = a₀ + a₁ pv + a₂ pv²` with `a = okvEquiv x`. -/
theorem evQ_okvEquiv (x : OKv) : evQ (fun i ↦ (okvEquiv x i : ℚ_[2])) = x := by
  change evQ (fun i ↦ bKv.equivFun (x : Kv) i) = x
  rw [evQ_eq_equivFun, LinearEquiv.symm_apply_apply]

/-- `OKv ^ 2 ≅ ℤ_[2] ^ 6`: coordinate `j` of component `i` in slot `finProdFinEquiv (i, j)`. -/
noncomputable def coordEquiv : (Fin 2 → OKv) ≃+ (Fin 6 → ℤ_[2]) :=
  (AddEquiv.piCongrRight fun _ ↦ okvEquiv).trans
    (((LinearEquiv.curry ℤ_[2] ℤ_[2] (Fin 2) (Fin 3)).symm.trans
      (LinearEquiv.funCongrLeft ℤ_[2] ℤ_[2] finProdFinEquiv.symm)).toAddEquiv)

@[simp]
theorem coordEquiv_apply (x : Fin 2 → OKv) (i : Fin 2) (j : Fin 3) :
    coordEquiv x (finProdFinEquiv (i, j)) = okvEquiv (x i) j := by
  simp [coordEquiv, LinearEquiv.funCongrLeft_apply]

/-! ### The chart -/

/-- **The finite index hypothesis**: some subgroup of finite index of `B` lies in the
image of `B1 Φ c` under `ψ`. Proved for the charts of `SetupKv` by `FinIdx.hFinIdx_of_setupKv`
(FinIdx/Assembly.lean). -/
def HFinIdx {B : Type*} [AddCommGroup B] (Φ : FormalGroupLaw OKv (Fin 2)) (ψ : Φ.Points →+ B)
    (c : OKv) : Prop :=
  ∃ H : AddSubgroup B, H.FiniteIndex ∧ ∀ b ∈ H, ∃ z : Φ.Points, z ∈ B1 Φ c ∧ ψ z = b

/-- **`LogChartFin` from the logarithmic chart** (item R7.6). For a formal group law `Φ` of
dimension 2 over `OKv`, an injective `ψ : Φ.Points →+ B` and `HFinIdx` at `c = pv ^ 4`, there is
`lam : B →+ ℤ_[2] ^ 6` with `LogChartFin lam`. Moreover `H' := ψ(B1 Φ c)` is a subgroup of finite
index and, on it, `lam` is `[B : H']` times the coordinates of the scaled logarithm: for `z = c y`
in `B1 Φ c`, `lam (ψ z) = [B : H'] • coordEquiv (logVal Φ (unitBall Kv).subtype c y)`. -/
theorem exists_logChartFin_of_chart {B : Type*} [AddCommGroup B]
    (Φ : FormalGroupLaw OKv (Fin 2)) (ψ : Φ.Points →+ B) (hψ : Function.Injective ψ)
    (hH : HFinIdx Φ ψ (pvO ^ (3 + 1))) :
    ∃ lam : B →+ (Fin 6 → ℤ_[2]), Analytic.LogChartFin lam ∧
      ∃ H' : AddSubgroup B, (H' : Set B) = ψ '' (B1 Φ (pvO ^ (3 + 1)) : Set Φ.Points) ∧
        H'.FiniteIndex ∧
        ∀ z ∈ B1 Φ (pvO ^ (3 + 1)), ∀ y : Fin 2 → OKv,
          (∀ j, (z j : OKv) = pvO ^ (3 + 1) * y j) →
          lam (ψ z) = H'.index • coordEquiv (logVal Φ (unitBall Kv).subtype (pvO ^ (3 + 1)) y) := by
  obtain ⟨L, hLbij, hLval, -⟩ := log_chart_OKv Φ
  obtain ⟨H', e, he, hH'1, hH'2⟩ :=
    exists_addSubgroup_of_bijective (B1 Φ (pvO ^ (3 + 1))) ψ hψ L hLbij
  obtain ⟨H, hHfin, hHsub⟩ := hH
  have hle : H ≤ H' := fun b hb ↦ by
    obtain ⟨z, hz, rfl⟩ := hHsub b hb
    exact (hH'2 ⟨z, hz⟩).1
  have : H'.FiniteIndex := AddSubgroup.finiteIndex_of_le hle
  let lam1 : H' →+ (Fin 6 → ℤ_[2]) := coordEquiv.toAddMonoidHom.comp e
  have hlam1 : Function.Bijective lam1 := coordEquiv.bijective.comp he
  obtain ⟨lam, hlam, hlamB⟩ := exists_logChartFin H' lam1 hlam1.1 0 fun v ↦ by
    obtain ⟨b, hb⟩ := hlam1.2 v
    exact ⟨b, by rw [hb, pow_zero, one_smul]⟩
  refine ⟨lam, hlam, H', ?_, inferInstance, ?_⟩
  · ext b
    constructor
    · intro hb
      obtain ⟨z, rfl⟩ := hH'1 b hb
      exact ⟨z, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact (hH'2 ⟨z, hz⟩).1
  · intro z hz y hzy
    obtain ⟨h, hez⟩ := hH'2 ⟨z, hz⟩
    rw [show ψ z = ((⟨ψ z, h⟩ : H') : B) from rfl, hlamB]
    change H'.index • coordEquiv (e ⟨ψ z, h⟩) = _
    rw [hez, hLval ⟨z, hz⟩ y hzy]

/-! ### Tests -/

example {B : Type*} [AddCommGroup B] (Φ : FormalGroupLaw OKv (Fin 2)) (ψ : Φ.Points →+ B)
    (hψ : Function.Injective ψ) (hH : HFinIdx Φ ψ (pvO ^ (3 + 1))) :
    ∃ lam : B →+ (Fin 6 → ℤ_[2]), FurioLombardo.Discharge.Analytic.LogChartFin lam :=
  (exists_logChartFin_of_chart Φ ψ hψ hH).imp fun _ h ↦ h.1

end FurioLombardo.Discharge.R7
