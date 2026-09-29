import Mathlib
import FurioLombardo.M4.Hypotheses
import FurioLombardo.M3a.Hypotheses
import FurioLombardo.Discharge.Analytic.Saturation

/-!
# The logarithm near the origin: kernel, range and the lattice `Λ`

The analytic content of `HLam` (lane M4) and of `LogKernelTorsion`, `LogRange` (lane M3a) is one fact about the
logarithm `lam : A(k_v) → V = O_v²` near the origin, `LogChart lam`: there is a subgroup `B1` of `A(k_v)` such that
every point has a positive multiple in `B1`, `lam` is injective on `B1`, and `lam(B1)` contains `2^N V` for some `N`.
For the real objects, `B1` is the group of points of the formal group of `A` at `v` with coordinates in `4 O_v`; the
logarithm of a formal group law of dimension 2 over `O_v` is a bijection from these points onto `4 O_v²`
(Toolbox, formal group logarithm scaled by `4`), `A(k_v)/B1` is finite, and `lam` differs from the formal logarithm
by an invertible linear map.

Proved here, for any abelian group `B` and any additive `lam : B → V`:

* `kernel_torsion_of_chart`: `LogChart lam` gives `ker lam ⊆ torsion` (lane M3a's `LogKernelTorsion`,
  `logKernelTorsion_of_chart`);
* `rangeSubmodule`: under `LogChart lam` the range of `lam` is a `ℤ_[2]`-submodule of `V`;
* `hLam_of_chart`: `LogChart lam` and `GenModTwo Dpt` (the seven points `D_i` generate `B` modulo `2B`) give
  `HLam lam Dpt` (Nakayama over `ℤ_[2]`), hence lane M3a's `LogRange` for `Λ := span (lam D_i)` (`logRange_of_hLam`).
-/

namespace FurioLombardo.Discharge.Analytic

open FurioLombardo.M4

/-- The logarithm is a chart near the origin: some subgroup `B1` of `B` has a positive multiple of every point,
`lam` is injective on it, and its image contains `2^N V`. -/
def LogChart {B : Type*} [AddCommGroup B] (lam : B →+ (Fin 6 → ℤ_[2])) : Prop :=
  ∃ B1 : AddSubgroup B, (∀ b : B, ∃ n : ℕ, 0 < n ∧ n • b ∈ B1) ∧ (∀ b ∈ B1, lam b = 0 → b = 0) ∧
    ∃ N : ℕ, ∀ v : Fin 6 → ℤ_[2], ∃ b ∈ B1, lam b = (2 : ℤ_[2]) ^ N • v

/-- The points `Dpt i` generate `B` modulo `2B`. -/
def GenModTwo {B : Type*} [AddCommGroup B] (Dpt : Fin 7 → B) : Prop :=
  ∀ b : B, ∃ n : Fin 7 → ℤ, ∃ b' : B, b = ∑ i, n i • Dpt i + (2 : ℕ) • b'

section Chart

variable {B : Type*} [AddCommGroup B] {lam : B →+ (Fin 6 → ℤ_[2])}

/-- Under `LogChart lam`, a point with zero logarithm is torsion. -/
theorem kernel_torsion_of_chart (h : LogChart lam) (b : B) (hb : lam b = 0) : ∃ n : ℕ, 0 < n ∧ n • b = 0 := by
  obtain ⟨B1, hmul, hinj, -⟩ := h
  obtain ⟨n, hn, hnb⟩ := hmul b
  refine ⟨n, hn, hinj _ hnb ?_⟩
  rw [map_nsmul, hb, nsmul_zero]

/-- Under `LogChart lam`, the range of `lam` is stable under multiplication by `ℤ_[2]`: write `c = k + 2^N c'` with
`k` an integer. -/
theorem exists_eq_smul_of_chart (h : LogChart lam) (c : ℤ_[2]) (b : B) : ∃ b' : B, lam b' = c • lam b := by
  obtain ⟨B1, -, -, N, hN⟩ := h
  have hc := PadicInt.appr_spec N c
  rw [Ideal.mem_span_singleton] at hc
  obtain ⟨c', hc'⟩ := hc
  obtain ⟨b1, -, hb1⟩ := hN (c' • lam b)
  refine ⟨(c.appr N) • b + b1, ?_⟩
  have hc2 : c = (c.appr N : ℤ_[2]) + (2 : ℤ_[2]) ^ N * c' := by
    have : ((2 : ℕ) : ℤ_[2]) = 2 := by norm_num
    rw [this] at hc'
    rw [← hc']; ring
  rw [map_add, map_nsmul, hb1, smul_smul, ← Nat.cast_smul_eq_nsmul ℤ_[2], ← add_smul, ← hc2]

/-- Under `LogChart lam`, the range of `lam` as a `ℤ_[2]`-submodule of `V`. -/
def rangeSubmodule (h : LogChart lam) : Submodule ℤ_[2] (Fin 6 → ℤ_[2]) where
  carrier := Set.range lam
  add_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
    exact ⟨b + b', map_add lam b b'⟩
  zero_mem' := ⟨0, map_zero lam⟩
  smul_mem' := by
    rintro c _ ⟨b, rfl⟩
    exact exists_eq_smul_of_chart h c b

theorem mem_rangeSubmodule (h : LogChart lam) (y : Fin 6 → ℤ_[2]) :
    y ∈ rangeSubmodule h ↔ ∃ b : B, lam b = y :=
  Iff.rfl

/-- **HLam from the chart and the generators modulo 2.** If `lam` is a chart near the origin and the `Dpt i` generate
`B` modulo `2B`, the image of `lam` is the `ℤ_[2]`-span of the `lam (Dpt i)` (Nakayama over the local ring
`ℤ_[2]`, the image being finitely generated since `V` is noetherian). -/
theorem hLam_of_chart {Dpt : Fin 7 → B} (h : LogChart lam) (hgen : GenModTwo Dpt) : HLam lam Dpt := by
  set R := rangeSubmodule h with hR
  set N0 := Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i)) with hN0
  have hN0R : N0 ≤ R := by
    rw [hN0, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Dpt i, rfl⟩
  have hRN0 : R ≤ N0 := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal ℤ_[2])
      (IsNoetherian.noetherian R) ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · rintro _ ⟨b, rfl⟩
      obtain ⟨n, b', hb⟩ := hgen b
      rw [hb, map_add, map_sum]
      refine Submodule.add_mem_sup ?_ ?_
      · refine Submodule.sum_mem _ (fun i _ => ?_)
        rw [map_zsmul]
        exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[2]]
        refine Submodule.smul_mem_smul ?_ ⟨b', rfl⟩
        rw [PadicInt.maximalIdeal_eq_span_p]
        exact Ideal.mem_span_singleton_self _
  intro y
  constructor
  · rintro ⟨b, rfl⟩
    exact hRN0 ⟨b, rfl⟩
  · intro hy
    exact hN0R hy

end Chart

/-- **LogKernelTorsion from the chart** (lane M3a, (L2)): on `A(k_v) = Jac f`, a logarithm that is a chart near the
origin kills only torsion points. -/
theorem logKernelTorsion_of_chart {kv : Type*} [Field kv] {f : Polynomial kv} [FurioLombardo.M3a.Genus2.GoodSextic f]
    {lam : Additive (FurioLombardo.M3a.Genus2.Jac f) →+ (Fin 6 → ℤ_[2])} (h : LogChart lam) :
    FurioLombardo.M3a.Route.LogKernelTorsion f lam :=
  kernel_torsion_of_chart h

/-- **LogRange from HLam** (lane M3a): with `Λ := span (lam D_i)`, `HLam` is lane M3a's `LogRange`. -/
theorem logRange_of_hLam {B : Type*} [AddCommGroup B] {lam : B →+ (Fin 6 → ℤ_[2])} {Dpt : Fin 7 → B}
    (h : HLam lam Dpt) :
    FurioLombardo.M3a.Route.LogRange lam (Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i))) :=
  fun l => (h l).symm

/-- The image of `lam` contains `lam (Dpt i)`, so `a = lam b ∈ span (lam D_i)` under `HLam`. -/
theorem mem_span_of_hLam {B : Type*} [AddCommGroup B] {lam : B →+ (Fin 6 → ℤ_[2])} {Dpt : Fin 7 → B}
    (h : HLam lam Dpt) (b : B) : lam b ∈ Submodule.span ℤ_[2] (Set.range fun i => lam (Dpt i)) :=
  (h (lam b)).1 ⟨b, rfl⟩

/-- **HKer from the chart and the local 2-power torsion** ((L1), (L2)): under `LogChart lam`, if the 2-power torsion of
`B` is `{0, ι T}` and `2 T = 0`, a point with zero logarithm is in `2B` or in `ι T + 2B`. -/
theorem hKer_of_chart {A B : Type*} [AddCommGroup A] [AddCommGroup B] {ι : A →+ B} {lam : B →+ (Fin 6 → ℤ_[2])}
    {T : A} (h : LogChart lam) (hL1 : ∀ b : B, (∃ k : ℕ, (2 ^ k : ℕ) • b = 0) → b = 0 ∨ b = ι T)
    (hT2 : (2 : ℕ) • T = 0) : HKer ι lam T := by
  refine ⟨fun b hb => ?_, hT2⟩
  obtain ⟨n, hn, hnb⟩ := kernel_torsion_of_chart h b hb
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  obtain ⟨j, rfl⟩ := hm
  have h2 : (2 ^ a : ℕ) • ((2 * j + 1) • b) = 0 := by rw [smul_smul]; exact hnb
  have hb' : b = (2 * j + 1) • b + (2 : ℕ) • (-(j • b)) := by
    rw [add_nsmul, one_nsmul, smul_neg, smul_smul]
    abel
  rcases hL1 _ ⟨a, h2⟩ with h0 | hT
  · exact ⟨-(j • b), Or.inl (hb'.trans (by rw [h0, zero_add]))⟩
  · exact ⟨-(j • b), Or.inr (hb'.trans (by rw [hT]))⟩

end FurioLombardo.Discharge.Analytic
