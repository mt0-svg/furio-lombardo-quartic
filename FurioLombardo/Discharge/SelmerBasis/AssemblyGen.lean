import FurioLombardo.Discharge.SelmerBasis.Interfaces
import FurioLombardo.Discharge.SelmerBasis.Echelon

/-!
# Generic lemmas of the assembly of `SelmerBasisK21`

* `coordCond_anti`, `coordCond_range`: `CoordCond` for a subgroup `W` containing the image of `μ` gives
  `CoordCond` for the image itself, so every place can be stated with the image as subgroup (`ImageIn` is
  then trivial).
* `mem_span_of_stacked`: the common zeros of the rows of finitely many matrices lie in a span, from one
  `kerSpanOK` certificate on the stacked rows.
* `exists_decomp_of_mem_span`: membership in the span of `p + nr` bit rows as the decomposition that
  `selmerBasis_of_interfaces` asks for (`hX`).
-/

open Polynomial FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.SelmerBasis

theorem coordCond_anti {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (f : K[X]) {m c : ℕ}
    (g : Fin m → H f) {W1 W2 : Subgroup (H (f.map φ))} (C : Matrix (Fin c) (Fin m) (ZMod 2))
    (h : CoordCond φ f g W2 C) (hle : W1 ≤ W2) : CoordCond φ f g W1 C :=
  fun a ha => h a (hle ha)

theorem coordCond_range {K K' : Type*} [Field K] [Field K'] (φ : K →+* K') (f : K[X])
    [GoodSextic (f.map φ)] {m c : ℕ} (g : Fin m → H f) {W : Subgroup (H (f.map φ))}
    (C : Matrix (Fin c) (Fin m) (ZMod 2)) (h : CoordCond φ f g W C) (hW : ImageIn (f.map φ) W) :
    CoordCond φ f g (muJ (f.map φ)).range C :=
  coordCond_anti φ f g C h (by rintro _ ⟨Q, rfl⟩; exact hW Q)

theorem imageIn_range {K : Type*} [Field K] (f : K[X]) [GoodSextic f] :
    ImageIn f (muJ f).range :=
  fun Q => ⟨Q, rfl⟩

/-- **Stacked rows.** -/
theorem mem_span_of_stacked {ι : Type*} [Fintype ι] {c : ι → ℕ} {n : ℕ}
    (C : ∀ w, Matrix (Fin (c w)) (Fin n) (ZMod 2)) (Rn : ι → ℕ → ℕ)
    (hC : ∀ w (r : Fin (c w)) (s : Fin n), C w r s = bitv n (Rn w r) s) {M : ℕ → ℕ} {m : ℕ}
    (src : ℕ → ι) (row : ℕ → ℕ) (hsrc : ∀ i < m, row i < c (src i) ∧ M i = Rn (src i) (row i))
    {T piv : ℕ → ℕ} {q : ℕ} {W : ℕ → ℕ} {nw : ℕ} {U : ℕ → ℕ}
    (h : kerSpanOK M m n T piv q W nw U = true) (a : Fin n → ZMod 2)
    (ha : ∀ w, (C w).mulVec a = 0) :
    a ∈ Submodule.span (ZMod 2) (Set.range fun l : Fin nw => bitv n (W l)) := by
  apply mem_span_of_kerSpanOK h a
  intro i
  obtain ⟨hr, hMi⟩ := hsrc i i.isLt
  rw [hMi]
  simpa [Matrix.mulVec, dotProduct, ← hC (src i) ⟨row i, hr⟩] using congrFun (ha (src i)) ⟨row i, hr⟩

/-- **The decomposition of `hX`.** -/
theorem exists_decomp_of_mem_span {n p nr : ℕ} (β : Fin p → Fin n → ℕ) (κ : Fin nr → Fin n → ℕ)
    (W : ℕ → ℕ) (hWβ : ∀ (j : Fin p) (s : Fin n), bitv n (W j) s = (β j s : ZMod 2))
    (hWκ : ∀ (t : Fin nr) (s : Fin n), bitv n (W (p + t)) s = (κ t s : ZMod 2)) (a : Fin n → ZMod 2)
    (ha : a ∈ Submodule.span (ZMod 2) (Set.range fun l : Fin (p + nr) => bitv n (W l))) :
    ∃ e : Fin p → ZMod 2, ∃ ε : Fin nr → ZMod 2,
      a = ∑ j, e j • (fun s => (β j s : ZMod 2)) + ∑ t, ε t • (fun s => (κ t s : ZMod 2)) := by
  rcases (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp ha with ⟨c, hc⟩
  have hβ_eq (j : Fin p) : bitv n (W (Fin.castAdd nr j)) = (fun s => (β j s : ZMod 2)) := by
    ext s
    simpa [Fin.val_castAdd] using hWβ j s
  have hκ_eq (t : Fin nr) : bitv n (W (Fin.natAdd p t)) = (fun s => (κ t s : ZMod 2)) := by
    ext s
    simpa [Fin.val_natAdd] using hWκ t s
  refine ⟨fun j => c (Fin.castAdd nr j), fun t => c (Fin.natAdd p t), ?_⟩
  calc
    a = ∑ l : Fin (p + nr), c l • bitv n (W l) := by rw [← hc]
    _ = ∑ j : Fin p, c (Fin.castAdd nr j) • bitv n (W (Fin.castAdd nr j))
        + ∑ t : Fin nr, c (Fin.natAdd p t) • bitv n (W (Fin.natAdd p t)) := by rw [Fin.sum_univ_add]
    _ = ∑ j : Fin p, c (Fin.castAdd nr j) • (fun s => (β j s : ZMod 2))
        + ∑ t : Fin nr, c (Fin.natAdd p t) • (fun s => (κ t s : ZMod 2)) := by
      refine congrArg₂ (· + ·) ?_ ?_
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [hβ_eq j]
      · refine Finset.sum_congr rfl fun t _ => ?_
        rw [hκ_eq t]
    _ = ∑ j, (fun j => c (Fin.castAdd nr j)) j • (fun s => (β j s : ZMod 2))
        + ∑ t, (fun t => c (Fin.natAdd p t)) t • (fun s => (κ t s : ZMod 2)) := rfl

end FurioLombardo.Discharge.SelmerBasis
