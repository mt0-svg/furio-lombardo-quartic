import Mathlib
import FurioLombardo.Vendor.Toolbox.PowerSeries.Bounded
import FurioLombardo.Vendor.Toolbox.PowerSeries.Conv
import FurioLombardo.Vendor.Toolbox.FormalGroup.Resc
import FurioLombardo.Vendor.Toolbox.Polynomial.SubPoly

/-!
# Evaluation of rescaled series with bounded denominators

`bddR σ π l` is the subring of series `G` such that `G(l t)` has bounded denominators, and
`evS hπ l z : bddR σ π l →+* K` is the value of `G(l t)` at `t = z` (`evS_apply`), for `z` a
family in the maximal ideal of a complete local ring `O ⊆ K`. Every convergent series
(`FurioLombardo.Vendor.Toolbox.Conv.conv`) lies in `bddR σ π (π ^ M)` for all large `M` (`eventually_mem_bddR`), and
renamings of variables commute with the evaluation (`evS_rename`).

Origin: written for this formalization (the formal group of the Jacobian at the place above 2,
`FurioLombardo.Discharge.R7`).
-/

open FurioLombardo.Vendor.Toolbox.Conv FurioLombardo.Vendor.Toolbox.FGLResc FurioLombardo.Vendor.Toolbox.SubPoly


namespace FurioLombardo.Vendor.Toolbox.Bounded

open MvPowerSeries

variable {K : Type*} [Field K] {O : Subring K} {σ τ : Type*}

variable (σ) in
/-- The series `G` such that `G(l t)` has bounded denominators. -/
noncomputable def bddR (π : O) (l : K) : Subring (MvPowerSeries σ K) :=
  (bdd O σ π).comap (rescale (fun _ => l))

theorem mem_bddR {π : O} {l : K} {G : MvPowerSeries σ K} :
    G ∈ bddR σ π l ↔ rescale (fun _ => l) G ∈ bdd O σ π := Iff.rfl

theorem C_mem_bddR {π : O} (hπ : (π : K) ≠ 0) (hbd : ∀ x : K, ∃ k : ℕ, (π : K) ^ k * x ∈ O)
    (l a : K) : C a ∈ bddR σ π l := by
  rw [mem_bddR, rescale_C']
  exact C_mem_bdd hπ hbd a

theorem C_mem_intSeries {a : K} (ha : a ∈ O) : (C a : MvPowerSeries σ K) ∈ intSeries O σ := by
  classical
  rw [mem_intSeries]
  intro d
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact O.zero_mem

theorem rescale_X_eq {l : K} (i : σ) :
    rescale (fun _ => l) (X i : MvPowerSeries σ K) = C l * X i := by
  rw [← smul_X_eq_rescale, smul_eq_C_mul]

theorem X_mem_bddR {π : O} {l : K} (hl : l ∈ O) (i : σ) :
    (X i : MvPowerSeries σ K) ∈ bddR σ π l := by
  rw [mem_bddR, rescale_X_eq]
  exact intSeries_le_bdd π (Subring.mul_mem _ (C_mem_intSeries hl) (X_mem_intSeries i))

theorem bddR_mono {π : O} {M M' : ℕ} (h : M ≤ M') :
    bddR σ π ((π : K) ^ M) ≤ bddR σ π ((π : K) ^ M') := by
  intro G hG
  rw [mem_bddR] at hG ⊢
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  have := rescale_mem_bdd (π ^ e) hG
  rw [rescale_rescale] at this
  convert this using 3
  funext _
  simp [pow_add]

theorem mem_bddR_of_data {π : O} {κ N M : ℕ} (hM : κ ≤ M) {G : MvPowerSeries σ K}
    (hG : Data O π κ N G) : G ∈ bddR σ π ((π : K) ^ M) := by
  rw [mem_bddR]
  refine ⟨N, fun d => ?_⟩
  rw [coeff_rescale_const]
  exact (hG.mono hM le_rfl) d

theorem eventually_mem_bddR {π : O} {G : MvPowerSeries σ K} (hG : G ∈ conv O π σ) :
    ∀ᶠ M in Filter.atTop, G ∈ bddR σ π ((π : K) ^ M) := by
  obtain ⟨κ, N, h⟩ := hG
  exact Filter.eventually_atTop.mpr ⟨κ, fun M hM => mem_bddR_of_data hM h⟩

theorem eventually_mem_LR {π : O} {p : Polynomial (MvPowerSeries σ K)} (hp : p ∈ convPoly O π σ) :
    ∀ᶠ M in Filter.atTop, p ∈ LR (bddR σ π ((π : K) ^ M)) := by
  obtain ⟨κ, N, h⟩ := exists_data_poly hp
  exact Filter.eventually_atTop.mpr ⟨κ, fun M hM => mem_LR.mpr fun n => mem_bddR_of_data hM (h n)⟩

/-- A renaming of variables `X s ↦ X (e s)` commutes with a constant rescaling. -/
theorem rescale_rename [Finite σ] (l : K) (e : σ → τ) (g : MvPowerSeries σ K) :
    rescale (fun _ => l) (subst (fun s => (X (e s) : MvPowerSeries τ K)) g) =
      subst (fun s => (X (e s) : MvPowerSeries τ K)) (rescale (fun _ => l) g) := by
  have hb : HasSubst (fun s => (X (e s) : MvPowerSeries τ K)) :=
    hasSubst_of_constantCoeff_zero fun s => by simp
  rw [← rescale_subst' _ hb, subst_rescale' _ hb]
  congr 1
  funext s
  exact (smul_X_eq_rescale l (e s)).symm

theorem rename_mem_bddR [Finite σ] {π : O} {l : K} (e : σ → τ) {g : MvPowerSeries σ K}
    (hg : g ∈ bddR σ π l) :
    subst (fun s => (X (e s) : MvPowerSeries τ K)) g ∈ bddR τ π l := by
  rw [mem_bddR, rescale_rename]
  exact subst_mem_bdd (fun s => X_mem_intSeries (e s)) (fun s => by simp) hg

theorem evB_congr {π : O} (hπ : (π : K) ≠ 0) [IsLocalRing O] [UniformSpace O]
    [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [Finite σ] [IsUniformAddGroup O]
    [CompleteSpace O] [T2Space O] [IsTopologicalRing O] (z : σ → IsLocalRing.maximalIdeal O)
    {G H : bdd O σ π} (h : (G : MvPowerSeries σ K) = H) : evB hπ z G = evB hπ z H := by
  rw [Subtype.ext h]

section Eval

variable [IsLocalRing O] [UniformSpace O] [Fact (IsAdic (IsLocalRing.maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

/-- The value at `l z` of a series of `bddR σ π l`. -/
noncomputable def evS [Finite σ] {π : O} (hπ : (π : K) ≠ 0) (l : K)
    (z : σ → IsLocalRing.maximalIdeal O) : bddR σ π l →+* K :=
  (evB hπ z).comp ((rescale (fun _ => l)).restrict (bddR σ π l) (bdd O σ π) fun _ hx => hx)

theorem evS_apply [Finite σ] {π : O} (hπ : (π : K) ≠ 0) (l : K)
    (z : σ → IsLocalRing.maximalIdeal O) (G : bddR σ π l) :
    evS hπ l z G = evB hπ z ⟨rescale (fun _ => l) G.1, G.2⟩ := rfl

theorem evS_C [Finite σ] {π : O} (hπ : (π : K) ≠ 0) (l : K) (z : σ → IsLocalRing.maximalIdeal O)
    (a : K) (h : C a ∈ bddR σ π l) : evS hπ l z ⟨C a, h⟩ = a := by
  rw [evS_apply]
  have h' : (C a : MvPowerSeries σ K) ∈ bdd O σ π := by
    have := h; rwa [mem_bddR, rescale_C'] at this
  rw [evB_congr hπ z (H := ⟨C a, h'⟩) (rescale_C' _ a), evB_C]

theorem evS_X [Finite σ] {π : O} (hπ : (π : K) ≠ 0) {l : K} (hl : l ∈ O)
    (z : σ → IsLocalRing.maximalIdeal O) (i : σ) (h : (X i : MvPowerSeries σ K) ∈ bddR σ π l) :
    evS hπ l z ⟨X i, h⟩ = l * (z i : K) := by
  rw [evS_apply]
  have hC : (C l : MvPowerSeries σ K) ∈ bdd O σ π := intSeries_le_bdd π (C_mem_intSeries hl)
  have hX : (X i : MvPowerSeries σ K) ∈ bdd O σ π := intSeries_le_bdd π (X_mem_intSeries i)
  rw [evB_congr hπ z (H := ⟨C l, hC⟩ * ⟨X i, hX⟩) (rescale_X_eq i), map_mul, evB_C,
    evB_X]

/-- Evaluation of a renamed series. -/
theorem evS_rename [Finite σ] [Finite τ] {π : O} (hπ : (π : K) ≠ 0) (l : K)
    (p : τ → IsLocalRing.maximalIdeal O) (e : σ → τ) {g : MvPowerSeries σ K}
    (hg : g ∈ bddR σ π l) :
    evS hπ l p ⟨subst (fun s => (X (e s) : MvPowerSeries τ K)) g, rename_mem_bddR e hg⟩ =
      evS hπ l (p ∘ e) ⟨g, hg⟩ := by
  have ha : ∀ s, (X (e s) : MvPowerSeries τ K) ∈ intSeries O τ := fun s => X_mem_intSeries (e s)
  have ha0 : ∀ s, constantCoeff (X (e s) : MvPowerSeries τ K) = 0 := fun s => by simp
  have hg' : rescale (fun _ => l) g ∈ bdd O σ π := hg
  have hs : subst (fun s => (X (e s) : MvPowerSeries τ K)) (rescale (fun _ => l) g) ∈ bdd O τ π :=
    subst_mem_bdd ha ha0 hg'
  have h1 : evS hπ l p ⟨subst (fun s => (X (e s) : MvPowerSeries τ K)) g, rename_mem_bddR e hg⟩ =
      evB hπ p ⟨subst (fun s => (X (e s) : MvPowerSeries τ K)) (rescale (fun _ => l) g), hs⟩ :=
    evB_congr hπ p (rescale_rename l e g)
  rw [h1, evB_subst hπ p ha ha0 hg', evS_apply]
  congr 2
  funext s
  apply Subtype.ext
  simp only [Function.comp_apply]
  rw [(toO_eq_iff (X_mem_intSeries (e s)) (X (e s))).mpr (map_X _ _), evO_X]

end Eval

end FurioLombardo.Vendor.Toolbox.Bounded
