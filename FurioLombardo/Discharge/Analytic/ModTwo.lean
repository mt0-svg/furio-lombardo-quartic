import Mathlib
import FurioLombardo.Discharge.Analytic.TwoIndex
import FurioLombardo.Discharge.Analytic.LogChart

/-!
# The seven local points generate `A(k_v)` modulo 2

`GenModTwo Dpt` (FurioLombardo.Discharge.Analytic.LogChart) from three facts:

* `LogChartFin lam`: the chart of `LogChart` on a subgroup `B1` of finite index (for the real objects, the points of
  the formal group with coordinates in `4 O_v`, an open subgroup of the compact group `A(k_v)`);
* `B[2]` has at most two elements (lane M3a's `LocalTwoTorsion`, (L1): the 2-power torsion of `A(k_v)` is `{0, T}`);
* `IndepModTwo Dpt`: the `D_i` are independent modulo `2B` (certificate: their `x - T` images are independent).

Then `[B : 2B] = [V : 2V] · #B[2] ≤ 2^7` (`index_twoB_le`, from `index_twoB_eq` and `relIndex_two_eq_index_twoB`), and
seven points independent modulo `2B` generate `B/2B` (`genModTwo_of_indep`). Also `LogChartFin` implies `LogChart`.
-/

namespace FurioLombardo.Discharge.Analytic

open AddSubgroup FurioLombardo.M4

/-- `LogChart` with a subgroup of finite index. -/
def LogChartFin {B : Type*} [AddCommGroup B] (lam : B →+ (Fin 6 → ℤ_[2])) : Prop :=
  ∃ B1 : AddSubgroup B, B1.FiniteIndex ∧ (∀ b ∈ B1, lam b = 0 → b = 0) ∧
    ∃ N : ℕ, ∀ v : Fin 6 → ℤ_[2], ∃ b ∈ B1, lam b = (2 : ℤ_[2]) ^ N • v

/-- The points `Dpt i` are independent modulo `2B`. -/
def IndepModTwo {B : Type*} [AddCommGroup B] (Dpt : Fin 7 → B) : Prop :=
  ∀ c : Fin 7 → ℤ, (∃ b : B, ∑ i, c i • Dpt i = (2 : ℕ) • b) → ∀ i, (2 : ℤ) ∣ c i

section V

/-- Doubling is injective on `V = Fin 6 → ℤ_[2]`. -/
theorem dbl_injective_V : Function.Injective (dbl (Fin 6 → ℤ_[2])) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  funext i
  have h := congrFun hv i
  simp only [dbl, nsmulAddMonoidHom_apply, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at h
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero

/-- `[ℤ_[2] : 2ℤ_[2]] = 2`. -/
theorem index_twoB_Z2 : (twoB ℤ_[2]).index = 2 := by
  have hker : (twoB ℤ_[2]) = (PadicInt.toZMod : ℤ_[2] →+* ZMod 2).toAddMonoidHom.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ← RingHom.mem_ker,
      PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, by simp [nsmul_eq_mul]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, by simp [nsmul_eq_mul]⟩
  rw [hker, index_ker]
  have hs : Function.Surjective (PadicInt.toZMod : ℤ_[2] →+* ZMod 2).toAddMonoidHom :=
    ZMod.ringHom_surjective _
  rw [AddMonoidHom.range_eq_top.mpr hs]
  simp [Nat.card_eq_fintype_card]

/-- `[V : 2V] = 2^6`. -/
theorem index_twoB_V : (twoB (Fin 6 → ℤ_[2])).index = 2 ^ 6 := by
  have h : twoB (Fin 6 → ℤ_[2]) = AddSubgroup.pi Set.univ (fun _ => twoB ℤ_[2]) := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩ i -
      exact ⟨w i, rfl⟩
    · intro hv
      choose w hw using fun i => hv i (Set.mem_univ i)
      exact ⟨w, funext fun i => hw i⟩
  rw [h, index_pi]
  simp [index_twoB_Z2]

/-- `(2^k) V`, as a subgroup. -/
noncomputable def twoPowSub : ℕ → AddSubgroup (Fin 6 → ℤ_[2])
  | 0 => ⊤
  | k + 1 => (twoPowSub k).map (dbl _)

theorem twoPow_smul_mem_twoPowSub (k : ℕ) (v : Fin 6 → ℤ_[2]) : (2 : ℤ_[2]) ^ k • v ∈ twoPowSub k := by
  induction k generalizing v with
  | zero => simp [twoPowSub]
  | succ k ih =>
    refine ⟨(2 : ℤ_[2]) ^ k • v, ih v, ?_⟩
    simp only [dbl, nsmulAddMonoidHom_apply]
    rw [← Nat.cast_smul_eq_nsmul ℤ_[2], smul_smul, pow_succ]
    norm_num [mul_comm]

theorem mem_twoPowSub {k : ℕ} {v : Fin 6 → ℤ_[2]} (h : v ∈ twoPowSub k) : ∃ w, (2 : ℤ_[2]) ^ k • w = v := by
  induction k generalizing v with
  | zero => exact ⟨v, by simp⟩
  | succ k ih =>
    obtain ⟨u, hu, rfl⟩ := h
    obtain ⟨w, rfl⟩ := ih hu
    refine ⟨w, ?_⟩
    simp only [dbl, nsmulAddMonoidHom_apply]
    rw [← Nat.cast_smul_eq_nsmul ℤ_[2], smul_smul, pow_succ]
    norm_num [mul_comm]

theorem index_twoPowSub (k : ℕ) : (twoPowSub k).index = (2 ^ 6) ^ k := by
  induction k with
  | zero => simp [twoPowSub]
  | succ k ih =>
    have hle : (twoPowSub k).map (dbl _) ≤ twoB (Fin 6 → ℤ_[2]) := by
      rintro _ ⟨b, -, rfl⟩
      exact ⟨b, rfl⟩
    have e2 := relIndex_mul_index hle
    have e3 : ((twoPowSub k).map (dbl _)).relIndex (twoB (Fin 6 → ℤ_[2])) = (twoPowSub k).index := by
      show ((twoPowSub k).map (dbl _)).relIndex (dbl (Fin 6 → ℤ_[2])).range = _
      rw [AddMonoidHom.range_eq_map, relIndex_map_map_of_injective _ _ dbl_injective_V, relIndex_top_right]
    rw [e3, ih, index_twoB_V] at e2
    show ((twoPowSub k).map (dbl _)).index = _
    rw [← e2]
    ring

/-- A subgroup of `V` containing `2^N V` has finite index. -/
theorem finiteIndex_of_twoPow {M : AddSubgroup (Fin 6 → ℤ_[2])} {N : ℕ}
    (hM : ∀ v, (2 : ℤ_[2]) ^ N • v ∈ M) : M.FiniteIndex := by
  have hfi : (twoPowSub N).FiniteIndex := by
    rw [finiteIndex_iff, index_twoPowSub]
    positivity
  refine finiteIndex_of_le (H := twoPowSub N) ?_
  intro v hv
  obtain ⟨w, rfl⟩ := mem_twoPowSub hv
  exact hM w

end V

section Count

variable {B : Type*} [AddCommGroup B] {lam : B →+ (Fin 6 → ℤ_[2])}

/-- `LogChartFin` gives `LogChart`: every point has a positive multiple (the index) in `B1`. -/
theorem logChart_of_fin (h : LogChartFin lam) : LogChart lam := by
  obtain ⟨B1, hfi, hinj, hN⟩ := h
  refine ⟨B1, fun b => ⟨B1.index, Nat.pos_of_ne_zero hfi.index_ne_zero, B1.nsmul_index_mem b⟩, hinj, hN⟩

/-- **The index of `2B`**: under `LogChartFin lam`, `[B : 2B] = 2^6 · #B[2]`. -/
theorem index_twoB_of_chart (h : LogChartFin lam) : (twoB B).index = 2 ^ 6 * Nat.card (tors2 B) := by
  obtain ⟨B1, hfi, hinj, N, hN⟩ := h
  have hB1 : B1 ⊓ tors2 B = ⊥ := by
    rw [eq_bot_iff]
    rintro b ⟨hb1, hb2⟩
    apply hinj b hb1
    have h2 : (2 : ℕ) • lam b = 0 := by rw [← map_nsmul]; exact (congrArg lam hb2).trans (map_zero lam)
    exact dbl_injective_V (by simpa [dbl] using h2)
  have hM : ∀ v, (2 : ℤ_[2]) ^ N • v ∈ B1.map lam := by
    intro v
    obtain ⟨b, hb, hbv⟩ := hN v
    exact ⟨b, hb, hbv⟩
  have := finiteIndex_of_twoPow hM
  rw [index_twoB_eq B1 hB1, relIndex_two_map lam B1 hinj,
    relIndex_two_eq_index_twoB dbl_injective_V, index_twoB_V]

/-- If every element of `B[2]` is `0` or `T`, then `#B[2] ≤ 2`. -/
theorem card_tors2_le_two {T : B} (hT : ∀ b : B, (2 : ℕ) • b = 0 → b = 0 ∨ b = T) : Nat.card (tors2 B) ≤ 2 := by
  have hsub : ((tors2 B : AddSubgroup B) : Set B) ⊆ {0, T} := by
    intro b hb
    rcases hT b hb with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc Nat.card (tors2 B) = ((tors2 B : AddSubgroup B) : Set B).ncard := Nat.card_coe_set_eq _
    _ ≤ ({0, T} : Set B).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
      rcases eq_or_ne (0 : B) T with h | h
      · rw [← h, Set.pair_eq_singleton, Set.ncard_singleton]; norm_num
      · rw [Set.ncard_pair h]

/-- **Seven points independent modulo `2B` generate `B/2B` when `[B : 2B] ≤ 2^7`.** -/
theorem genModTwo_of_indep {Dpt : Fin 7 → B} (hind : IndepModTwo Dpt) (hidx : (twoB B).index ≤ 2 ^ 7)
    (hfi : (twoB B).index ≠ 0) : GenModTwo Dpt := by
  have : (twoB B).FiniteIndex := ⟨hfi⟩
  let g : (Fin 7 → ZMod 2) → B ⧸ twoB B :=
    fun ε => QuotientAddGroup.mk (∑ i, ((ε i).val : ℤ) • Dpt i)
  have hginj : Function.Injective g := by
    intro ε ε' he
    have he' := QuotientAddGroup.eq.mp he
    obtain ⟨b, hb⟩ := he'
    have hb0 : (2 : ℕ) • b = -(∑ i, ((ε i).val : ℤ) • Dpt i) + ∑ i, ((ε' i).val : ℤ) • Dpt i := hb
    have hb' : ∑ i, (((ε' i).val : ℤ) - (ε i).val) • Dpt i = (2 : ℕ) • b := by
      rw [hb0]
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    have h2 := hind _ ⟨b, hb'⟩
    funext i
    have hi := h2 i
    have hlt := ZMod.val_lt (ε i)
    have hlt' := ZMod.val_lt (ε' i)
    have : (ε' i).val = (ε i).val := by omega
    exact (ZMod.val_injective 2 this).symm
  have hcard : Nat.card (B ⧸ twoB B) ≤ Nat.card (Fin 7 → ZMod 2) := by
    rw [← index_eq_card]
    simpa [Nat.card_eq_fintype_card] using hidx
  have hbij := hginj.bijective_of_nat_card_le hcard
  intro b
  obtain ⟨ε, hε⟩ := hbij.2 (QuotientAddGroup.mk b)
  have h' := QuotientAddGroup.eq.mp hε
  obtain ⟨c, hc⟩ := h'
  have hc0 : (2 : ℕ) • c = -(∑ i, ((ε i).val : ℤ) • Dpt i) + b := hc
  refine ⟨fun i => ((ε i).val : ℤ), c, ?_⟩
  rw [hc0]
  abel

/-- **GenModTwo from the chart, the 2-torsion and the independence certificate.** -/
theorem genModTwo_of_chart {Dpt : Fin 7 → B} {T : B} (h : LogChartFin lam)
    (hT : ∀ b : B, (2 : ℕ) • b = 0 → b = 0 ∨ b = T) (hind : IndepModTwo Dpt) : GenModTwo Dpt := by
  have hidx := index_twoB_of_chart h
  have hc := card_tors2_le_two hT
  refine genModTwo_of_indep hind ?_ ?_
  · rw [hidx]
    calc 2 ^ 6 * Nat.card (tors2 B) ≤ 2 ^ 6 * 2 := Nat.mul_le_mul_left _ hc
      _ = 2 ^ 7 := by norm_num
  · rw [hidx]
    have hsub : ((tors2 B : AddSubgroup B) : Set B) ⊆ {0, T} := fun b hb => hT b hb
    have : Finite (tors2 B) := ((Set.toFinite ({0, T} : Set B)).subset hsub).to_subtype
    have : 0 < Nat.card (tors2 B) := Nat.card_pos (α := tors2 B)
    positivity

/-- **HLam from the finite index chart, the 2-torsion and the independence certificate.** -/
theorem hLam_of_chartFin {Dpt : Fin 7 → B} {T : B} (h : LogChartFin lam)
    (hT : ∀ b : B, (2 : ℕ) • b = 0 → b = 0 ∨ b = T) (hind : IndepModTwo Dpt) : HLam lam Dpt :=
  hLam_of_chart (logChart_of_fin h) (genModTwo_of_chart h hT hind)

end Count

end FurioLombardo.Discharge.Analytic
