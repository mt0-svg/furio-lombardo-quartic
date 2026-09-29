import FurioLombardo.M1.ZK

/-!
# The integral basis spans an order: every `zkE a` is an algebraic integer

The multiplication table `zkTab` (DataField.lean) is checked by the kernel with the Kronecker test:
`w_i * w_j = zkE (zkTab[i][j])` for all `i, j < 21`. With `w_0 = 1`, the ℤ-span `Λ` of the `w_j` is
a subalgebra of K21, finitely generated as a ℤ-module, so all its elements are integral over ℤ
(`IsIntegral.of_mem_of_fg`). Hence `zkO a : 𝓞 K21`.
-/

namespace FurioLombardo.M1

open Polynomial Kron NumberField

/-- The table entry `zkTab[i][j]`. -/
def tabL (i j : ℕ) : List ℤ := (zkTab.getD i []).getD j []

/-- The Kronecker expression `w_i w_j - zkE (zkTab[i][j])`. -/
def tabExpr (i j : ℕ) : KE := .sub (.mul (.lin (unitL i)) (.lin (unitL j))) (.lin (tabL i j))

/-- All 441 table entries pass the Kronecker test at `N = 2 ^ 400`. -/
def tabOK : Bool :=
  (List.range 21).all fun i => (List.range 21).all fun j => checkK 400 (tabExpr i j)

theorem tabOK_true : tabOK = true := by decide +kernel

theorem wK_mul (i j : ℕ) (hi : i < 21) (hj : j < 21) : wK i * wK j = zkE (tabL i j) := by
  have h := List.all_eq_true.mp tabOK_true i (List.mem_range.mpr hi)
  have h' := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  exact evK_eq_of_check 400 _ _ h'

theorem zkNum_zero : zkNum.getD 0 [] = (Dz : ℤ) :: List.replicate 20 0 := by decide +kernel

theorem wK_zero : wK 0 = 1 := by
  rw [wK_eq 0 (by norm_num), zkNum_zero, wv]
  simp [evalL, List.replicate]
  exact dInv_mul

/-- The ℤ-span of the integral basis. -/
noncomputable def Λ : Submodule ℤ K21 := Submodule.span ℤ (Set.range fun i : Fin 21 => wK i)

theorem mul_mem_Λ {x y : K21} (hx : x ∈ Λ) (hy : y ∈ Λ) : x * y ∈ Λ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [wK_mul i j i.isLt j.isLt]
      exact zkE_mem_span _
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact Λ.add_mem ha hb
    | smul n a _ ha => rw [mul_smul_comm]; exact Λ.smul_mem n ha
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact Λ.add_mem ha hb
  | smul n a _ ha => rw [smul_mul_assoc]; exact Λ.smul_mem n ha

theorem one_mem_Λ : (1 : K21) ∈ Λ := by
  rw [← wK_zero]; exact Submodule.subset_span ⟨⟨0, by norm_num⟩, rfl⟩

/-- `Λ` as a subalgebra. -/
noncomputable def ΛAlg : Subalgebra ℤ K21 :=
  Λ.toSubalgebra one_mem_Λ fun _ _ hx hy => mul_mem_Λ hx hy

theorem isIntegral_of_mem_Λ {x : K21} (hx : x ∈ Λ) : IsIntegral ℤ x :=
  IsIntegral.of_mem_of_fg ΛAlg (Submodule.fg_span (Set.finite_range _)) x hx

theorem isIntegral_zkE (a : List ℤ) : IsIntegral ℤ (zkE a) :=
  isIntegral_of_mem_Λ (zkE_mem_span a)

/-- The element of `𝓞 K21` with zk coordinates `a`. -/
noncomputable def zkO (a : List ℤ) : 𝓞 K21 := ⟨zkE a, isIntegral_zkE a⟩

@[simp] theorem coe_zkO (a : List ℤ) : ((zkO a : 𝓞 K21) : K21) = zkE a := rfl

theorem isIntegral_θ : IsIntegral ℤ θ := by
  refine ⟨fZ, fZ_monic, ?_⟩
  have h := evalL_θ_fL
  rw [← evalL_ofListL, ofListL_fL] at h
  convert h using 2
  exact RingHom.ext_int _ _

end FurioLombardo.M1
