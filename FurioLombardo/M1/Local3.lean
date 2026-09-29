import FurioLombardo.M1.SqCond
import FurioLombardo.M1.Data3

/-!
# The 3-adic step of the sieve: `ℤ/27`, `θ ↦ 17`

`17` is a root of `f` modulo 27 (the degree one prime `(pi3)` above 3, `θ ≡ -1 (mod 3)`), so
`resHom` gives `ψ3 : 𝓞 K21 →+* ZMod 27` with `θ ↦ 17`. Its values on the lattice `zkO a` are
computed by the kernel in integer arithmetic (`res27`), and the data of Data3.lean (residues of
the coefficients of `Q1`, `Q3` and of `G_k` for the survivors `k < 4`) are rechecked.

A primitive integer point `a` has a coordinate prime to 3, so modulo 27 it is `λ P` with `λ` a
unit and `P` in one of the planes `x = 1`, `y = 1`, `z = 1` (coordinates in `[0, 27)`). The kernel
checks every such `P` (`kill27_planes`): either `F(P) ≢ 0 (mod 27)`, or for every `k < 4` one of
`Q1(P) G_k`, `Q3(P) G_k` is not a square modulo 27. `SqCond a (survE k)` makes both squares modulo
27 (`kill3`).
-/

namespace FurioLombardo.M1

open Polynomial NumberField Kron Vendor.NetOfConics

/-! ## Kernel checks, in integer arithmetic -/

/-- The image of `zkO a` in `ℤ/27` (`θ ↦ 17`), as an integer in `[0, 27)`. -/
def res27 (a : List ℤ) : ℤ := (uD27 * evalL (17 : ℤ) (combo a zkNum)) % 27

/-- The residue of the coefficient `m` of `Q_(i+1)` (`i = 0` or `i = 2`). -/
def q27c (i m : ℕ) : ℤ := (q27.getD (i / 2) []).getD m 0

/-- The ternary quadratic form with coefficient list `c` (on x², xy, xz, y², yz, z²). -/
def qz (c : List ℤ) (x y z : ℤ) : ℤ :=
  c.getD 0 0 * x ^ 2 + c.getD 1 0 * (x * y) + c.getD 2 0 * (x * z) + c.getD 3 0 * y ^ 2 +
    c.getD 4 0 * (y * z) + c.getD 5 0 * z ^ 2

/-- `t` is a square modulo 27. -/
def sq27 (t : ℤ) : Bool := (List.range 27).any fun s => ((s : ℤ) * s - t) % 27 == 0

/-- The test at a triple: `F ≢ 0`, or for every `k < 4` one of `Q1 G_k`, `Q3 G_k` is a nonsquare. -/
def kill27 (x y z : ℤ) : Bool :=
  FurioLombardo.F x y z % 27 != 0 ||
    (List.range 4).all fun k => !(sq27 (qz (q27.getD 0 []) x y z * g27.getD k 0) &&
      sq27 (qz (q27.getD 1 []) x y z * g27.getD k 0))

/-- The product of the residues of the generators selected by the survivor `k`. -/
def selProd27 (k : ℕ) : ℤ :=
  ((List.finRange 18).map fun i => if survE k i then res27 (gensL.getD i []) else 1).prod

theorem root27 : evalL (17 : ℤ) fL % 27 = 0 := by decide +kernel

theorem uB27_ok : (uB27 * DB - 1) % 27 = 0 := by decide +kernel

theorem uD27_ok : (uD27 * (Dz : ℤ) - 1) % 27 = 0 := by decide +kernel

theorem q27_ok : ([0, 2] : List ℕ).all (fun i => (List.range 6).all fun m =>
    res27 (qcA i m) == q27c i m) = true := by decide +kernel

theorem g27_ok : (List.range 4).all (fun k => selProd27 k % 27 == g27.getD k 0) = true := by
  decide +kernel

/-- **The plane test** (2187 triples). -/
theorem kill27_planes : (List.range 27).all (fun u => (List.range 27).all fun v =>
    kill27 u v 1 && kill27 1 u v && kill27 u 1 v) = true := by decide +kernel

theorem unit27 : ∀ u : ZMod 27, u.val % 3 ≠ 0 → u * u ^ 17 = 1 := by decide

/-! ## Casts to `ZMod 27` -/

theorem cast27_emod (n : ℤ) : ((n % 27 : ℤ) : ZMod 27) = (n : ZMod 27) := by
  have h := ZMod.intCast_mod n 27
  rwa [Nat.cast_ofNat] at h

theorem cast27_eq_zero (n : ℤ) (h : n % 27 = 0) : (n : ZMod 27) = 0 := by
  rw [← cast27_emod, h, Int.cast_zero]

theorem emod27_of_cast (n : ℤ) (h : (n : ZMod 27) = 0) : n % 27 = 0 := by
  have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd n 27).mp h
  rw [Nat.cast_ofNat] at h'
  exact Int.emod_eq_zero_of_dvd h'

theorem cast27_one (n : ℤ) (h : (n - 1) % 27 = 0) : (n : ZMod 27) = 1 := by
  have h' := cast27_eq_zero _ h
  rw [Int.cast_sub, Int.cast_one] at h'
  exact sub_eq_zero.mp h'

theorem cast27_evalL (l : List ℤ) : evalL (17 : ZMod 27) l = ((evalL (17 : ℤ) l : ℤ) : ZMod 27) := by
  have h := map_evalL (Int.castRingHom (ZMod 27)) (17 : ℤ) l
  simp only [eq_intCast, Int.cast_ofNat] at h
  exact h.symm

/-! ## The residue map `ψ3` -/

theorem aeval_17_fZ : aeval (17 : ZMod 27) fZ = 0 := by
  rw [← ofListL_fL, aeval_ofListL, cast27_evalL]
  exact cast27_eq_zero _ root27

theorem uB27_inv : (uB27 : ZMod 27) * (DB : ZMod 27) = 1 := by
  have h := cast27_one _ uB27_ok
  rwa [Int.cast_mul] at h

theorem uD27_inv : (uD27 : ZMod 27) * ((Dz : ℤ) : ZMod 27) = 1 := by
  have h := cast27_one _ uD27_ok
  rwa [Int.cast_mul] at h

/-- The residue map `𝓞 K21 → ℤ/27`, `θ ↦ 17`. -/
noncomputable def ψ3 : 𝓞 K21 →+* ZMod 27 := resHom (17 : ZMod 27) aeval_17_fZ (uB27 : ZMod 27) uB27_inv

theorem ψ3_θO : ψ3 θO = 17 := resHom_θO _ _ _ _

theorem ψ3_zkO (a : List ℤ) : ψ3 (zkO a) = ((res27 a : ℤ) : ZMod 27) := by
  rw [hom_zkO ψ3 (uD27 : ZMod 27) uD27_inv a, ψ3_θO, res27, cast27_emod, Int.cast_mul, cast27_evalL]

theorem res27_qcA (i : Fin 3) (hi : i = 0 ∨ i = 2) (m : Fin 6) : res27 (qcA i m) = q27c i m := by
  have hi' : (i : ℕ) ∈ ([0, 2] : List ℕ) := by rcases hi with rfl | rfl <;> simp
  exact beq_iff_eq.mp
    (List.all_eq_true.mp (List.all_eq_true.mp q27_ok _ hi') m (List.mem_range.mpr m.isLt))

theorem ψ3_qO (i : Fin 3) (hi : i = 0 ∨ i = 2) (a : Fin 3 → ℤ) :
    ψ3 (qO i a) = qev (fun m => ((q27c i m : ℤ) : ZMod 27)) (fun j => ((a j : ℤ) : ZMod 27)) := by
  rw [qO, map_qev]
  congr 1
  · funext m
    rw [show qC i m = zkO (qcA i m) from rfl, ψ3_zkO, res27_qcA i hi m]
  · funext j
    exact map_intCast ψ3 (a j)

theorem qev_list {R : Type*} [CommRing R] (l : List ℤ) (P : Fin 3 → R) :
    qev (fun m : Fin 6 => ((l.getD m 0 : ℤ) : R)) P =
      (l.getD 0 0 : R) * P 0 ^ 2 + (l.getD 1 0 : R) * (P 0 * P 1) + (l.getD 2 0 : R) * (P 0 * P 2) +
        (l.getD 3 0 : R) * P 1 ^ 2 + (l.getD 4 0 : R) * (P 1 * P 2) + (l.getD 5 0 : R) * P 2 ^ 2 :=
  rfl

/-- `ψ3(Q_(i+1)(a))` at `a ≡ λ P (mod 27)`. -/
theorem ψ3_qO_pt (i : Fin 3) (hi : i = 0 ∨ i = 2) (a : Fin 3 → ℤ) (lam : ZMod 27) (x y z : ℕ)
    (h0 : ((a 0 : ℤ) : ZMod 27) = lam * x) (h1 : ((a 1 : ℤ) : ZMod 27) = lam * y)
    (h2 : ((a 2 : ℤ) : ZMod 27) = lam * z) :
    ψ3 (qO i a) = lam ^ 2 * ((qz (q27.getD (i / 2) []) x y z : ℤ) : ZMod 27) := by
  rw [ψ3_qO i hi a]
  have hc : (fun m : Fin 6 => ((q27c i m : ℤ) : ZMod 27)) =
      fun m : Fin 6 => (((q27.getD (i / 2) []).getD m 0 : ℤ) : ZMod 27) := rfl
  rw [hc, qev_list]
  simp only [h0, h1, h2, qz]
  push_cast
  ring

theorem ψ3_gProd (k : ℕ) (hk : k < 4) :
    ψ3 (gProd (survE k)) = ((g27.getD k 0 : ℤ) : ZMod 27) := by
  have h := beq_iff_eq.mp (List.all_eq_true.mp g27_ok k (List.mem_range.mpr hk))
  rw [← h, cast27_emod, selProd27, ← Fin.prod_univ_def, Int.cast_prod, gProd, subprod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact ψ3_zkO _
  · simp

/-! ## Squares, normalization, the kill -/

theorem sq27_of (t : ℤ) (s : ZMod 27) (h : (t : ZMod 27) = s ^ 2) : sq27 t = true := by
  unfold sq27
  rw [List.any_eq_true]
  refine ⟨s.val, List.mem_range.mpr (ZMod.val_lt s), ?_⟩
  rw [beq_iff_eq]
  apply emod27_of_cast
  rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, h]
  ring

theorem kill27_all (x y z : ℕ) (hx : x < 27) (hy : y < 27) (hz : z < 27)
    (h1 : x = 1 ∨ y = 1 ∨ z = 1) : kill27 x y z = true := by
  have hp : ∀ u : ℕ, u < 27 → ∀ v : ℕ, v < 27 →
      kill27 u v 1 = true ∧ kill27 1 u v = true ∧ kill27 u 1 v = true := by
    intro u hu v hv
    have h := List.all_eq_true.mp (List.all_eq_true.mp kill27_planes u (List.mem_range.mpr hu)) v
      (List.mem_range.mpr hv)
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  rcases h1 with rfl | rfl | rfl
  · simpa using (hp y hy z hz).2.1
  · simpa using (hp x hx z hz).2.2
  · simpa using (hp x hx y hy).1

/-- A primitive integer triple has a coordinate prime to 3. -/
theorem prim27 (a r : Fin 3 → ℤ) (hr : ∑ j, r j * a j = 1) :
    ((a 0 : ZMod 27)).val % 3 ≠ 0 ∨ ((a 1 : ZMod 27)).val % 3 ≠ 0 ∨
      ((a 2 : ZMod 27)).val % 3 ≠ 0 := by
  have hv : ∀ j, ((a j : ZMod 27)).val % 3 = 0 → (3 : ℤ) ∣ a j := by
    intro j hj
    have h := ZMod.val_intCast (n := 27) (a j)
    omega
  by_contra hc
  simp only [not_or, ne_eq, not_not] at hc
  obtain ⟨h0, h1, h2⟩ := hc
  rw [Fin.sum_univ_three] at hr
  have h3 : (3 : ℤ) ∣ r 0 * a 0 + r 1 * a 1 + r 2 * a 2 :=
    dvd_add (dvd_add ((hv 0 h0).mul_left _) ((hv 1 h1).mul_left _)) ((hv 2 h2).mul_left _)
  rw [hr] at h3
  omega

/-- **Normalization**: `A = λ P` with `λ` a unit and `P` in a plane `x = 1`, `y = 1` or `z = 1`. -/
theorem exists_plane (A : Fin 3 → ZMod 27)
    (hA : (A 0).val % 3 ≠ 0 ∨ (A 1).val % 3 ≠ 0 ∨ (A 2).val % 3 ≠ 0) :
    ∃ lam w : ZMod 27, lam * w = 1 ∧ ∃ x y z : ℕ, x < 27 ∧ y < 27 ∧ z < 27 ∧
      (x = 1 ∨ y = 1 ∨ z = 1) ∧ A 0 = lam * x ∧ A 1 = lam * y ∧ A 2 = lam * z := by
  rcases hA with h | h | h
  · have hu := unit27 _ h
    refine ⟨A 0, A 0 ^ 17, hu, 1, (A 1 * A 0 ^ 17).val, (A 2 * A 0 ^ 17).val, by norm_num,
      ZMod.val_lt _, ZMod.val_lt _, Or.inl rfl, ?_, ?_, ?_⟩
    · simp
    · rw [ZMod.natCast_zmod_val]; linear_combination -(A 1) * hu
    · rw [ZMod.natCast_zmod_val]; linear_combination -(A 2) * hu
  · have hu := unit27 _ h
    refine ⟨A 1, A 1 ^ 17, hu, (A 0 * A 1 ^ 17).val, 1, (A 2 * A 1 ^ 17).val, ZMod.val_lt _,
      by norm_num, ZMod.val_lt _, Or.inr (Or.inl rfl), ?_, ?_, ?_⟩
    · rw [ZMod.natCast_zmod_val]; linear_combination -(A 0) * hu
    · simp
    · rw [ZMod.natCast_zmod_val]; linear_combination -(A 2) * hu
  · have hu := unit27 _ h
    refine ⟨A 2, A 2 ^ 17, hu, (A 0 * A 2 ^ 17).val, (A 1 * A 2 ^ 17).val, 1, ZMod.val_lt _,
      ZMod.val_lt _, by norm_num, Or.inr (Or.inr rfl), ?_, ?_, ?_⟩
    · rw [ZMod.natCast_zmod_val]; linear_combination -(A 0) * hu
    · rw [ZMod.natCast_zmod_val]; linear_combination -(A 1) * hu
    · simp

/-- **The 3-adic step**: at a primitive integer point of `C`, the survivors `k < 4` of the good
prime sieve fail the square condition. -/
theorem kill3 (a r : Fin 3 → ℤ) (hr : ∑ j, r j * a j = 1)
    (hF : FurioLombardo.F (a 0) (a 1) (a 2) = 0) (k : ℕ) (hk : k < 4)
    (hsq : SqCond a (survE k)) : False := by
  obtain ⟨lam, w, hlw, x, y, z, hx, hy, hz, h1, h0', h1', h2'⟩ :=
    exists_plane (fun j => ((a j : ℤ) : ZMod 27)) (prim27 a r hr)
  have hkill := kill27_all x y z hx hy hz h1
  have hFP : FurioLombardo.F (x : ℤ) (y : ℤ) (z : ℤ) % 27 = 0 := by
    apply emod27_of_cast
    have hA : FurioLombardo.F ((a 0 : ℤ) : ZMod 27) ((a 1 : ℤ) : ZMod 27) ((a 2 : ℤ) : ZMod 27) = 0 := by
      rw [F_intCast, hF, Int.cast_zero]
    rw [h0', h1', h2'] at hA
    have hl : lam ^ 4 * FurioLombardo.F (x : ZMod 27) (y : ZMod 27) (z : ZMod 27) = 0 := by
      rw [← hA]; simp only [FurioLombardo.F]; ring
    rw [← F_intCast]
    simp only [Int.cast_natCast]
    have hw4 : (w * lam) ^ 4 = 1 := by rw [mul_comm, hlw, one_pow]
    calc FurioLombardo.F (x : ZMod 27) (y : ZMod 27) (z : ZMod 27)
        = (w * lam) ^ 4 * FurioLombardo.F (x : ZMod 27) (y : ZMod 27) (z : ZMod 27) := by
          rw [hw4, one_mul]
      _ = w ^ 4 * (lam ^ 4 * FurioLombardo.F (x : ZMod 27) (y : ZMod 27) (z : ZMod 27)) := by ring
      _ = 0 := by rw [hl, mul_zero]
  have hk' : (!(sq27 (qz (q27.getD 0 []) x y z * g27.getD k 0) &&
      sq27 (qz (q27.getD 1 []) x y z * g27.getD k 0))) = true := by
    rw [kill27, hFP] at hkill
    simp only [bne_self_eq_false, Bool.false_or] at hkill
    exact List.all_eq_true.mp hkill k (List.mem_range.mpr hk)
  have hG := ψ3_gProd k hk
  have hsq_i : ∀ i : Fin 3, (i = 0 ∨ i = 2) →
      sq27 (qz (q27.getD (i / 2) []) x y z * g27.getD k 0) = true := by
    intro i hi
    obtain ⟨s, hs⟩ : ∃ s : ZMod 27, ψ3 (qO i a) * ψ3 (gProd (survE k)) = s ^ 2 := by
      by_cases h0 : qO i a = 0
      · exact ⟨0, by rw [h0, map_zero, zero_mul]; ring⟩
      · obtain ⟨s, hs⟩ := hsq i hi h0
        exact ⟨ψ3 s, by rw [← map_mul, hs, map_pow]⟩
    rw [ψ3_qO_pt i hi a lam x y z h0' h1' h2', hG] at hs
    apply sq27_of _ (w * s)
    rw [Int.cast_mul]
    linear_combination w ^ 2 * hs -
      ((qz (q27.getD (i / 2) []) x y z : ℤ) : ZMod 27) * ((g27.getD k 0 : ℤ) : ZMod 27) *
        (lam * w + 1) * hlw
  have e0 := hsq_i 0 (Or.inl rfl)
  have e2 := hsq_i 2 (Or.inr rfl)
  rw [show ((0 : Fin 3) : ℕ) / 2 = 0 from rfl] at e0
  rw [show ((2 : Fin 3) : ℕ) / 2 = 1 from rfl] at e2
  rw [e0, e2] at hk'
  exact absurd hk' (by decide)

end FurioLombardo.M1
