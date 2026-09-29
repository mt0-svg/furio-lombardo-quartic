import FurioLombardo.Discharge.SelmerSpan.Dpt
import FurioLombardo.Discharge.SelmerSpan.QuadSq
import FurioLombardo.Discharge.M3a.LocalFacts

/-!
# Three characters of `K_v[T]/(g)` that kill `K_v^× (L^×)²` (lane SelmerSpan)

For the twist `k`, `g = (fRev k)^σ = c q h` over `K_v` (lane M4Cert's completion, `e = 3`). Put
`h1 = σ(q1)/2`, `δ' = h1² - σ(q0)` (`= σ(d)/4`, not a square), `N = K_v(ω')` with `ω'² = δ'`
(`NF k`), `P0 = σ(a0) + 2 σ(b0) ω'`, `P1 = σ(a1) + 2 σ(b1) ω'` and `M = N(x0)` with `x0² = -P0 - P1 x0`
(`MF k`). Then `τ = -h1 + ω'` is a root of `q^σ` and `x0` a root of `h^σ` (`h = A² - d B²`, lane
M3a's `h_eq_normForm`), which gives ring maps `evN : K_v[T]/(g) → N` and `evM : K_v[T]/(g) → M`
and the multiplicative characters

* `ψ1 y = N_{N/K_v}(evN y)`, `ψ2 y = N_{M/N}(evM y)`, `ψ3 y = evM y · evN y`;

each takes square values on `K_v^× (L^×)²` (`chars_sq`). Values at `U = X² + p X + r`:
`evN U = (h1² + δ' - p h1 + r) + (p - 2 h1) ω'` (`evN_mk`), `evM U = (r - P0) + (p - P1) x0` (`evM_mk`).
-/

open Polynomial
open FurioLombardo.M1 FurioLombardo.M3a.Genus2 FurioLombardo.Discharge.M4Cert
  FurioLombardo.Discharge.M3a FurioLombardo.Discharge.M3a.Bruin

namespace FurioLombardo.Discharge.SelmerSpan

/-! ## The fields `N` and `M` -/

/-- `h1 = σ(q1)/2`. -/
noncomputable def h1v (k : Fin 2) : Kv := σ ((q k).coeff 1) / 2

/-- `σ(q0)`. -/
noncomputable def q0v (k : Fin 2) : Kv := σ ((q k).coeff 0)

/-- `δ' = h1² - σ(q0) = σ(d)/4`. -/
noncomputable def dlv (k : Fin 2) : Kv := h1v k ^ 2 - q0v k

theorem σ_q1 (k : Fin 2) : σ ((q k).coeff 1) = 2 * h1v k := by
  rw [h1v]; field_simp [two_ne_zero_Kv]

theorem σ_d (k : Fin 2) : σ (d k) = 4 * dlv k := by
  rw [d, map_sub, map_pow, map_mul, σ_q1, dlv, q0v, map_ofNat]; ring

theorem dlv_not_isSquare (k : Fin 2) : ¬ IsSquare (dlv k) := by
  rintro ⟨r, hr⟩
  exact d_not_isSquare_Kv k ⟨2 * r, by rw [σ_d, hr]; ring⟩

theorem fact_dlv (k : Fin 2) : Fact (¬ IsSquare (dlv k)) := ⟨dlv_not_isSquare k⟩

/-- `N = K_v(ω')`, `ω'² = δ'`. -/
abbrev NF (k : Fin 2) : Type := QuadraticAlgebra Kv (dlv k) 0

/-- `P0 = σ(a0) + 2 σ(b0) ω'`. -/
noncomputable def P0N (k : Fin 2) : NF k := ⟨σ (a0 k), 2 * σ (b0 k)⟩

/-- `P1 = σ(a1) + 2 σ(b1) ω'`. -/
noncomputable def P1N (k : Fin 2) : NF k := ⟨σ (a1 k), 2 * σ (b1 k)⟩

/-- `M = N(x0)`, `x0² = -P0 - P1 x0`. -/
abbrev MF (k : Fin 2) : Type := QuadraticAlgebra (NF k) (-P0N k) (-P1N k)

/-- `K_v → M`. -/
noncomputable def ιM (k : Fin 2) : Kv →+* MF k := (algebraMap (NF k) (MF k)).comp (algebraMap Kv (NF k))

/-! ## The two evaluations -/

theorem q_eval_τ (k : Fin 2) :
    ((q k).map σ).eval₂ (algebraMap Kv (NF k)) (⟨-h1v k, 1⟩ : NF k) = 0 := by
  rw [q_explicit k]
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, map_X, map_C, eval₂_add,
    eval₂_pow, eval₂_mul, eval₂_X, eval₂_C]
  rw [σ_q1]
  exact qa0_tau_root rfl

theorem g_eval_τ (k : Fin 2) :
    ((fRev k).map σ).eval₂ (algebraMap Kv (NF k)) (⟨-h1v k, 1⟩ : NF k) = 0 := by
  rw [fRev_eq_mul, Polynomial.map_mul, Polynomial.map_mul, eval₂_mul, eval₂_mul, q_eval_τ, mul_zero,
    zero_mul]

theorem h_eval_x0 (k : Fin 2) : ((h k).map σ).eval₂ (ιM k) (⟨0, 1⟩ : MF k) = 0 := by
  rw [h_map_eq, eval₂_normForm]
  refine normForm_root_of (ιM k) (w := algebraMap (NF k) (MF k) ⟨0, 2⟩) ?_ ?_
  · rw [← map_mul, ιM, RingHom.comp_apply, σ_d]
    congr 1
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.algebraMap_eq] <;> ring
  · have e0 : ιM k (σ (a0 k)) + ιM k (σ (b0 k)) * algebraMap (NF k) (MF k) ⟨0, 2⟩ =
        algebraMap (NF k) (MF k) (P0N k) := by
      rw [ιM, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, ← map_add]
      congr 1
      apply QuadraticAlgebra.ext <;> simp [P0N, QuadraticAlgebra.algebraMap_eq] <;> ring
    have e1 : ιM k (σ (a1 k)) + ιM k (σ (b1 k)) * algebraMap (NF k) (MF k) ⟨0, 2⟩ =
        algebraMap (NF k) (MF k) (P1N k) := by
      rw [ιM, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, ← map_add]
      congr 1
      apply QuadraticAlgebra.ext <;> simp [P1N, QuadraticAlgebra.algebraMap_eq] <;> ring
    rw [e0, e1]
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.algebraMap_eq]

theorem g_eval_x0 (k : Fin 2) : ((fRev k).map σ).eval₂ (ιM k) (⟨0, 1⟩ : MF k) = 0 := by
  rw [fRev_eq_mul, Polynomial.map_mul, Polynomial.map_mul, eval₂_mul, eval₂_mul, h_eval_x0, mul_zero]

/-- `y ↦ y(τ)`, `τ = -h1 + ω'`. -/
noncomputable def evN (k : Fin 2) : AdjoinRoot ((fRev k).map σ) →+* NF k :=
  AdjoinRoot.lift (algebraMap Kv (NF k)) ⟨-h1v k, 1⟩ (g_eval_τ k)

/-- `y ↦ y(x0)`. -/
noncomputable def evM (k : Fin 2) : AdjoinRoot ((fRev k).map σ) →+* MF k :=
  AdjoinRoot.lift (ιM k) ⟨0, 1⟩ (g_eval_x0 k)

theorem evN_mk (k : Fin 2) (p r : Kv) :
    evN k (AdjoinRoot.mk _ (quad p r)) =
      ⟨h1v k * h1v k + dlv k - p * h1v k + r, p - 2 * h1v k⟩ := by
  rw [evN, AdjoinRoot.lift_mk, quad]
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
  rw [qa0_tau_quad, sq]

theorem evM_mk (k : Fin 2) (p r : Kv) :
    evM k (AdjoinRoot.mk _ (quad p r)) =
      ⟨algebraMap Kv (NF k) r - P0N k, algebraMap Kv (NF k) p - P1N k⟩ := by
  rw [evM, AdjoinRoot.lift_mk, quad]
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, ιM, RingHom.comp_apply]
  exact qa_root_quad (P0N k) (P1N k) _ _

/-! ## The characters -/

/-- `ψ1 y = N_{N/K_v}(y(τ))`. -/
noncomputable def ψ1 (k : Fin 2) : AdjoinRoot ((fRev k).map σ) →* Kv :=
  QuadraticAlgebra.norm.comp (evN k).toMonoidHom

/-- `ψ2 y = N_{M/N}(y(x0))`. -/
noncomputable def ψ2 (k : Fin 2) : AdjoinRoot ((fRev k).map σ) →* NF k :=
  QuadraticAlgebra.norm.comp (evM k).toMonoidHom

/-- `ψ3 y = y(x0) y(τ)` in `M`. -/
noncomputable def ψ3 (k : Fin 2) : AdjoinRoot ((fRev k).map σ) →* MF k :=
  (evM k).toMonoidHom * ((algebraMap (NF k) (MF k)).comp (evN k)).toMonoidHom

theorem ψ1_apply (k : Fin 2) (y : AdjoinRoot ((fRev k).map σ)) :
    ψ1 k y = QuadraticAlgebra.norm (evN k y) := rfl

theorem ψ2_apply (k : Fin 2) (y : AdjoinRoot ((fRev k).map σ)) :
    ψ2 k y = QuadraticAlgebra.norm (evM k y) := rfl

theorem ψ3_apply (k : Fin 2) (y : AdjoinRoot ((fRev k).map σ)) :
    ψ3 k y = evM k y * algebraMap (NF k) (MF k) (evN k y) := rfl

theorem ψ3_sq (k : Fin 2) (c : Kv) (w : AdjoinRoot ((fRev k).map σ)) :
    IsSquare (ψ3 k (algebraMap Kv _ c * w ^ 2)) := by
  rw [map_mul, map_pow]
  refine IsSquare.mul ?_ (IsSquare.sq _)
  refine ⟨ιM k c, ?_⟩
  have h0 : evM k (algebraMap Kv _ c) = ιM k c := AdjoinRoot.lift_of _
  have h1 : evN k (algebraMap Kv _ c) = algebraMap Kv (NF k) c := AdjoinRoot.lift_of _
  rw [ψ3_apply, h0, h1]
  rfl

/-- **The three characters are squares on `K_v^× (L^×)²`.** -/
theorem chars_sq (k : Fin 2) (c : Kv) (w : AdjoinRoot ((fRev k).map σ)) :
    IsSquare (ψ1 k (algebraMap Kv _ c * w ^ 2)) ∧ IsSquare (ψ2 k (algebraMap Kv _ c * w ^ 2)) ∧
      IsSquare (ψ3 k (algebraMap Kv _ c * w ^ 2)) := by
  have hN : evN k (algebraMap Kv _ c * w ^ 2) = algebraMap Kv (NF k) c * evN k w ^ 2 := by
    rw [map_mul, map_pow, AdjoinRoot.algebraMap_eq, evN, AdjoinRoot.lift_of]
  have hM : evM k (algebraMap Kv _ c * w ^ 2) =
      algebraMap (NF k) (MF k) (algebraMap Kv (NF k) c) * evM k w ^ 2 := by
    have h0 : evM k (algebraMap Kv _ c) = ιM k c := AdjoinRoot.lift_of _
    rw [map_mul, map_pow, h0]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [ψ1_apply, hN]; exact qa_isSquare_norm_mul c _
  · rw [ψ2_apply, hM]; exact qa_isSquare_norm_mul _ _
  · exact ψ3_sq k c w

end FurioLombardo.Discharge.SelmerSpan
