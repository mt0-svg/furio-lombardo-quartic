import Mathlib
import FurioLombardo.Discharge.R7.FGLK
import FurioLombardo.Vendor.Toolbox.FormalGroup.Resc

/-!
# The integral formal group law of the chart (item R7)

For a `Setup K` the addition series `G` converges near 0 (`G_mem`), so `G(π^κ s)` is integral for
some `κ` (`exists_kappa_G`). For `M ≥ 2 κ` (`GoodM M`) the conjugate
`Φ(ŝ) = π^(-M) G(π^M ŝ)` has coefficients in `O` and is a formal group law over `O`
(`fglO`), with `Φ` mapped to `K` equal to `resc (π ^ M) G` (`map_fglO_F`).
-/

open Polynomial
open FurioLombardo.M3a.Genus2
open FurioLombardo.Vendor.Toolbox.G2Formal FurioLombardo.Vendor.Toolbox.Conv FurioLombardo.Vendor.Toolbox.FGLResc

namespace FurioLombardo.Vendor.Toolbox.G2Formal.Setup

variable {K : Type*} [Field K] (S : Setup K)

/-- `G(π^κ s)` is integral. -/
theorem exists_kappa_G : ∃ κ : ℕ, ∀ i d,
    (S.π : K) ^ (κ * d.degree) * MvPowerSeries.coeff d (S.G i) ∈ S.O := by
  have h : ∀ i, ∃ κ : ℕ, Data S.O S.π κ 0 (S.G i) := fun i => by
    obtain ⟨κ, N, hκN⟩ := S.G_mem i
    exact ⟨κ + N, data_int_of_constantCoeff hκN (S.G_const i)⟩
  obtain ⟨κ0, h0⟩ := h 0
  obtain ⟨κ1, h1⟩ := h 1
  refine ⟨max κ0 κ1, fun i d => ?_⟩
  have hi : Data S.O S.π (max κ0 κ1) 0 (S.G i) := by
    fin_cases i
    · exact h0.mono (le_max_left _ _) le_rfl
    · exact h1.mono (le_max_right _ _) le_rfl
  have := hi d
  rwa [pow_zero, one_mul] at this

/-- `M` is admissible: `π^(-M) G(π^M ŝ)` is integral. -/
def GoodM (M : ℕ) : Prop :=
  ∃ κ : ℕ, 2 * κ ≤ M ∧ ∀ i d, (S.π : K) ^ (κ * d.degree) * MvPowerSeries.coeff d (S.G i) ∈ S.O

theorem exists_goodM : ∃ M0, ∀ M, M0 ≤ M → S.GoodM M := by
  obtain ⟨κ, hκ⟩ := S.exists_kappa_G
  exact ⟨2 * κ, fun M hM => ⟨κ, hM, hκ⟩⟩

variable [CharZero K] [GoodSextic S.f]

/-- The conjugate `π^(-M) G(π^M ŝ)` over `K`. -/
noncomputable def fglK (M : ℕ) : FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.FormalGroupLaw K (Fin 2) :=
  fglResc S.fgl (pow_ne_zero M S.hπ0)

theorem fglK_F (M : ℕ) (i : Fin 2) : (S.fglK M).F i = resc ((S.π : K) ^ M) (S.G i) := rfl

theorem fglK_coeff_mem {M : ℕ} (hM : S.GoodM M) (i : Fin 2) (d : Fin 2 ⊕ Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d ((S.fglK M).F i) ∈ S.O := by
  obtain ⟨κ, hκM, hκ⟩ := hM
  rw [fglK_F]
  exact coeff_resc_mem S.O S.π.2 S.hπ0 hκM S.fgl hκ i d

/-- **The integral formal group law of the chart.** -/
noncomputable def fglO {M : ℕ} (hM : S.GoodM M) :
    FurioLombardo.Vendor.Toolbox.Stoll.ChabautyColeman.FormalGroupLaw S.O (Fin 2) :=
  descend S.O (S.fglK M) (S.fglK_coeff_mem hM)

theorem map_fglO_F {M : ℕ} (hM : S.GoodM M) (i : Fin 2) :
    MvPowerSeries.map S.O.subtype ((S.fglO hM).F i) = resc ((S.π : K) ^ M) (S.G i) :=
  map_descend_F S.O _ _ i

end FurioLombardo.Vendor.Toolbox.G2Formal.Setup
