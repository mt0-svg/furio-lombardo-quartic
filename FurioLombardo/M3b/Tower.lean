import FurioLombardo.M3b.Characters

/-!
# Lane M3b: `Cl(L)[2] = 0` and `Cl(N)[2] = 0` for a tower of quadratic extensions

`K ⊂ L ⊂ N` number fields with `[L : K] = [N : L] = 2` (in route R: `K = K21`,
`L = K21(√d)`, `N = L(√e)`). The hypotheses, each a named Prop (theorems for
`K21 ⊂ L42 ⊂ N84`: Discharge/M3b and lane M2):

* `ClTwoTrivial K`: `Cl(K)` has no element of order 2 (lane M2 proves `h(K21) = 1`);
* `RamBound K L 2`: at most 2 places of `K` ramify in `L`;
* `NonNormUnit K L`: some unit of `K` is not a norm from `L`;
* `RamBound L N 4`: at most 4 places of `L` ramify in `N`;
* `SignPattern L N 3`: three real places of `L` ramified in `N` and three units of `L` with the
  diagonal sign pattern.

`classGroups_twoTorsion_trivial`: under these, `ClTwoTrivial L` and `ClTwoTrivial N`
(Chevalley's formula twice, `twoTorsion_trivial`).
-/

namespace FurioLombardo.M3b

open NumberField InfinitePlace Module

/-- `Cl(K)` has no element of order 2. -/
def ClTwoTrivial (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ c : ClassGroup (𝓞 K), c ^ 2 = 1 → c = 1

/-- At most `t` places of `K` (finite and real) ramify in `L`. -/
def RamBound (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (t : ℕ) : Prop :=
  ramifiedPlaceCount K L ≤ t

/-- Some unit of `K` is not a norm from `L`. -/
def NonNormUnit (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Prop :=
  ∃ u : (𝓞 K)ˣ, u ∉ normUnits K L

/-- `n` real places `w j` of `K` ramified in `L` and `n` units `u i` of `K` with `u i` negative at
`w j` exactly when `i = j`. -/
def SignPattern (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (n : ℕ) : Prop :=
  ∃ (w : Fin n → InfinitePlace K) (u : Fin n → (𝓞 K)ˣ),
    (∀ j, w j ∈ ramifiedRealPlaces K L) ∧
      ∀ i j, ((w j).embedding ((u i : 𝓞 K) : K)).re < 0 ↔ i = j

variable {K L N : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field N]
  [NumberField N] [Algebra K L] [Algebra L N]

theorem odd_classNumber_of_clTwoTrivial (h : ClTwoTrivial K) : Odd (classNumber K) := by
  have := odd_card_of_sq_eq_one h
  rwa [Nat.card_eq_fintype_card] at this

/-- One step: a quadratic extension with `h_K` odd, `t ≤ k + 1` ramified places and
`[E_K : E_K ∩ N] ≥ 2 ^ k` has `Cl(L)[2] = 0`. -/
theorem clTwoTrivial_of_index (h2 : Module.finrank K L = 2) (hK : ClTwoTrivial K) {k : ℕ}
    (ht : RamBound K L (k + 1)) (hidx : 2 ^ k ≤ (normUnits K L).index) : ClTwoTrivial L := by
  refine twoTorsion_trivial h2 (odd_classNumber_of_clTwoTrivial hK) ?_
  calc 2 ^ ramifiedPlaceCount K L ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) ht
    _ = 2 * 2 ^ k := by ring
    _ ≤ 2 * (normUnits K L).index := by omega

/-- **Class groups of the tower**: these hypotheses give `Cl(L)[2] = 0` and `Cl(N)[2] = 0`. -/
theorem classGroups_twoTorsion_trivial (hKL : Module.finrank K L = 2)
    (hLN : Module.finrank L N = 2) (hK : ClTwoTrivial K) (htL : RamBound K L 2)
    (hnn : NonNormUnit K L) (htN : RamBound L N 4) (hsg : SignPattern L N 3) :
    ClTwoTrivial L ∧ ClTwoTrivial N := by
  obtain ⟨u, hu⟩ := hnn
  have hL : ClTwoTrivial L :=
    clTwoTrivial_of_index hKL hK (k := 1) htL (by simpa using two_le_index_of_not_mem hKL hu)
  obtain ⟨w, v, hw, hv⟩ := hsg
  exact ⟨hL, clTwoTrivial_of_index hLN hL (k := 3) htN (pow_le_index_of_signs hLN w hw v hv)⟩

end FurioLombardo.M3b
