import Mathlib

/-!
# Polynomials with coefficients in a subring, and their images under a homomorphism

For a subring `B` of a commutative ring `A`, `LR B = liftsRing B.subtype` is the subring of `A[X]`
of polynomials with coefficients in `B` (`mem_LR`). A ring homomorphism `Φ : B →+* L` acts on it
coefficientwise, as a ring homomorphism `evR B Φ : LR B →+* L[X]` (`coeff_evR`). Divisibility by
a monic polynomial of `LR B` is kept (`evR_dvd`), because the quotient stays in `LR B`
(`divByMonic_mem_LR`).

Origin: written for this formalization (the formal group of the Jacobian at the place above 2,
`FurioLombardo.Discharge.R7`).
-/

open Polynomial

namespace FurioLombardo.Vendor.Toolbox.SubPoly

variable {A : Type*} [CommRing A] (B : Subring A)

/-- The polynomials with coefficients in `B`. -/
noncomputable abbrev LR : Subring A[X] := liftsRing B.subtype

variable {B}

theorem mem_LR {P : A[X]} : P ∈ LR B ↔ ∀ n, P.coeff n ∈ B := by
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts]
  simp

theorem coeff_mem {P : LR B} (n : ℕ) : (P : A[X]).coeff n ∈ B := mem_LR.mp P.2 n

theorem X_mem_LR : (X : A[X]) ∈ LR B := mem_LR.mpr fun n => by
  rw [coeff_X]; split_ifs <;> simp [B.one_mem, B.zero_mem]

theorem C_mem_LR {c : A} (hc : c ∈ B) : C c ∈ LR B := mem_LR.mpr fun n => by
  rw [coeff_C]; split_ifs <;> simp [hc, B.zero_mem]

theorem divByMonic_mem_LR {m p : A[X]} (hm : m.Monic) (hml : m ∈ LR B) (hpl : p ∈ LR B) :
    p /ₘ m ∈ LR B := by
  rw [← lifts_iff_liftsRing] at hml hpl ⊢
  obtain ⟨m', hm'map, -, hm'⟩ := lifts_and_natDegree_eq_and_monic hml hm
  obtain ⟨p', rfl⟩ := (mem_lifts p).mp hpl
  rw [mem_lifts]
  exact ⟨p' /ₘ m', by rw [map_divByMonic _ hm', hm'map]⟩

variable (B)

/-- `B[X] ≃ LR B`. -/
noncomputable def liftE : B[X] ≃+* LR B :=
  RingEquiv.ofBijective (mapRingHom B.subtype).rangeRestrict
    ⟨fun _ _ h => map_injective _ Subtype.val_injective (congrArg Subtype.val h),
      (mapRingHom B.subtype).rangeRestrict_surjective⟩

theorem map_liftE_symm (P : LR B) : ((liftE B).symm P).map B.subtype = P := by
  have := congrArg Subtype.val ((liftE B).apply_symm_apply P)
  exact this

theorem coeff_liftE_symm (P : LR B) (n : ℕ) :
    ((liftE B).symm P).coeff n = ⟨(P : A[X]).coeff n, coeff_mem n⟩ := by
  apply Subtype.ext
  have := congrArg (fun p => p.coeff n) (map_liftE_symm B P)
  simpa [coeff_map] using this

variable {L : Type*} [CommRing L] (Φ : B →+* L)

/-- Coefficientwise image of a polynomial of `LR B` under `Φ`. -/
noncomputable def evR : LR B →+* L[X] :=
  (mapRingHom Φ).comp (liftE B).symm.toRingHom

theorem coeff_evR (P : LR B) (n : ℕ) :
    (evR B Φ P).coeff n = Φ ⟨(P : A[X]).coeff n, coeff_mem n⟩ := by
  simp only [evR, RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, coeff_map,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, coeff_liftE_symm]

theorem evR_eq {P : LR B} {q : L[X]} (h : ∀ n, Φ ⟨(P : A[X]).coeff n, coeff_mem n⟩ = q.coeff n) :
    evR B Φ P = q := by
  ext n; rw [coeff_evR]; exact h n

theorem evR_X : evR B Φ ⟨X, X_mem_LR⟩ = X := by
  refine evR_eq B Φ fun n => ?_
  simp only [coeff_X]
  split_ifs
  · rw [← map_one Φ]; rfl
  · rw [← map_zero Φ]; rfl

theorem evR_C {c : A} (hc : c ∈ B) : evR B Φ ⟨C c, C_mem_LR hc⟩ = C (Φ ⟨c, hc⟩) := by
  refine evR_eq B Φ fun n => ?_
  simp only [coeff_C]
  split_ifs
  · rfl
  · rw [← map_zero Φ]; rfl

theorem evR_dvd {P Q : A[X]} (hP : P ∈ LR B) (hQ : Q ∈ LR B) (hm : P.Monic) (h : P ∣ Q) :
    evR B Φ ⟨P, hP⟩ ∣ evR B Φ ⟨Q, hQ⟩ := by
  have hq : Q /ₘ P ∈ LR B := divByMonic_mem_LR hm hP hQ
  have e : (⟨Q, hQ⟩ : LR B) = ⟨P, hP⟩ * ⟨Q /ₘ P, hq⟩ := by
    apply Subtype.ext
    have h0 := modByMonic_add_div Q P
    rw [(modByMonic_eq_zero_iff_dvd hm).mpr h, zero_add] at h0
    exact h0.symm
  rw [e, map_mul]
  exact dvd_mul_right _ _

/-- The image of a polynomial with coefficients in the image of a ring homomorphism `A0 → A`
with values in `B`. -/
theorem evR_map {A0 : Type*} [CommRing A0] (g : A0 →+* A) (hg : ∀ x, g x ∈ B) (ψ : A0 →+* L)
    (hψ : ∀ x, Φ ⟨g x, hg x⟩ = ψ x) (p : A0[X]) (hp : p.map g ∈ LR B) :
    evR B Φ ⟨p.map g, hp⟩ = p.map ψ := by
  refine evR_eq B Φ fun n => ?_
  simp only [coeff_map]
  exact hψ _

theorem map_mem_LR {A0 : Type*} [CommRing A0] (g : A0 →+* A) (hg : ∀ x, g x ∈ B) (p : A0[X]) :
    p.map g ∈ LR B := mem_LR.mpr fun n => by rw [coeff_map]; exact hg _

end FurioLombardo.Vendor.Toolbox.SubPoly
