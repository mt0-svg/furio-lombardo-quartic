import FurioLombardo.Discharge.SelmerBasis.Interfaces
import FurioLombardo.Discharge.SelmerBasis.Spanning

/-!
# From coordinates at a place to `IndepImage` and `CoordCond`

At a place `K'` of the base field, a monoid map `ev : (K'[T]/(f))ˣ →* G` (in practice the units map of
the product of the component maps `T ↦ τ_j`, `G = ∏ F_jˣ`) and a subgroup `Ksub` of `G` containing
the image of `K'ˣ` turn relations in `H f` into memberships in `Ksub ⊔ G²`. With a family `b`
independent modulo squares in `G`, generators `κ` of `Ksub` modulo squares and coordinates of every
element on `b` (square certificates), `sb_mem_iff` turns these memberships into linear conditions
over `ZMod 2`, and an `F₂` certificate closes:

* `indepImage_of_coords`: the points `D i` with `μ(D i) = [U i]` are independent (`IndepImage`);
* `coordCond_of_coords`: for global classes `[gu s]`, the condition at the place in coordinates
  (`CoordCond`) with `W` the closure of the images of the points.
-/

open Polynomial FurioLombardo.M3a.Genus2

namespace FurioLombardo.Discharge.SelmerBasis

section Glue

/-- `GoodSextic` passes to a field extension in characteristic `0` when the leading coefficient stays a
non-square (the certificate needed at each place). -/
theorem goodSextic_map {K K' : Type*} [Field K] [Field K'] [CharZero K] (φ : K →+* K') (f : K[X])
    [hf : GoodSextic f] (hlc : ¬ IsSquare (φ f.leadingCoeff)) : GoodSextic (f.map φ) where
  squarefree := ((PerfectField.separable_iff_squarefree.mpr hf.squarefree).map).squarefree
  natDegree_eq := by rw [natDegree_map_eq_of_injective φ.injective, hf.natDegree_eq]
  not_isSquare_leadingCoeff := by rwa [leadingCoeff_map]
  two_ne_zero := by
    have h := (map_ne_zero φ).mpr hf.two_ne_zero
    rwa [map_ofNat] at h

variable {K' : Type*} [Field K']

/-- `ev` maps `K'ˣ (Lˣ)²` into `Ksub ⊔ G²` when it maps the scalars into `Ksub`. -/
theorem ev_mem_of_mem_sqClass {f : K'[X]} {G : Type*} [CommGroup G] (ev : (AdjoinRoot f)ˣ →* G)
    (Ksub : Subgroup G)
    (hKev : ∀ c : K'ˣ, ev (Units.map (algebraMap K' (AdjoinRoot f)).toMonoidHom c) ∈ Ksub)
    {x : (AdjoinRoot f)ˣ} (hx : x ∈ sqClass f) :
    ev x ∈ Ksub ⊔ (powMonoidHom 2 : G →* G).range := by
  have hle : sqClass f ≤ (Ksub ⊔ (powMonoidHom 2 : G →* G).range).comap ev := by
    unfold sqClass
    refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      exact Subgroup.mem_sup_left (hKev c)
    · rintro _ ⟨y, rfl⟩
      exact Subgroup.mem_sup_right ⟨ev y, by simp [powMonoidHom]⟩
  exact hle hx

/-- Reducing exponents modulo `2` does not change membership in a subgroup containing the squares. -/
theorem prod_pow_mem_iff_mod_two {G : Type*} [CommGroup G] (S : Subgroup G)
    (hS : (powMonoidHom 2 : G →* G).range ≤ S) {n : ℕ} (g : Fin n → G) (a : Fin n → ℕ) :
    ∏ s, g s ^ a s ∈ S ↔ ∏ s, g s ^ ((a s : ZMod 2)).val ∈ S := by
  have hsplit : ∏ s, g s ^ a s = (∏ s, g s ^ ((a s : ZMod 2)).val) * (∏ s, g s ^ (a s / 2)) ^ 2 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← pow_mul, ← pow_add, ZMod.val_natCast]
    congr 1
    omega
  have hsq : (∏ s, g s ^ (a s / 2)) ^ 2 ∈ S := hS ⟨_, rfl⟩
  rw [hsplit]
  exact ⟨fun h => by simpa using S.mul_mem h (S.inv_mem hsq), fun h => S.mul_mem h hsq⟩

/-- **Independence at a place from coordinates.** -/
theorem indepImage_of_coords (f : K'[X]) [GoodSextic f] {r : ℕ} (D : Fin r → Jac f)
    (U : Fin r → (AdjoinRoot f)ˣ) (hU : ∀ i, muJ f (D i) = QuotientGroup.mk (U i))
    {G : Type*} [CommGroup G] (ev : (AdjoinRoot f)ˣ →* G) (Ksub : Subgroup G)
    (hKev : ∀ c : K'ˣ, ev (Units.map (algebraMap K' (AdjoinRoot f)).toMonoidHom c) ∈ Ksub)
    {nb : ℕ} (b : Fin nb → G)
    (hind : ∀ ε : Fin nb → ZMod 2, IsSquare (∏ i, b i ^ (ε i).val) → ε = 0)
    {mκ : ℕ} (κ : Fin mκ → G) (hκK : ∀ l, κ l ∈ Ksub)
    (hK : ∀ x ∈ Ksub, ∃ c : Fin mκ → ZMod 2, IsSquare (x * ∏ l, κ l ^ (c l).val))
    (Aκ : Fin mκ → Fin nb → ZMod 2) (hAκ : ∀ l, IsSquare (κ l * ∏ i, b i ^ (Aκ l i).val))
    (Aμ : Fin r → Fin nb → ZMod 2) (hAμ : ∀ i, IsSquare (ev (U i) * ∏ j, b j ^ (Aμ i j).val))
    (hcert : ∀ c : Fin r → ZMod 2,
      ∑ i, c i • Aμ i ∈ Submodule.span (ZMod 2) (Set.range Aκ) → c = 0) :
    IndepImage f D := by
  intro c hc
  have hmem : ∏ i, U i ^ c i ∈ sqClass f := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_prod]
    simpa only [QuotientGroup.mk_pow, ← hU] using hc
  have hev := ev_mem_of_mem_sqClass ev Ksub hKev hmem
  rw [map_prod] at hev
  simp only [map_pow] at hev
  have hS : (powMonoidHom 2 : G →* G).range ≤
      Ksub ⊔ Subgroup.closure (Set.range (Fin.elim0 : Fin 0 → G)) ⊔
        (powMonoidHom 2 : G →* G).range := le_sup_right
  have hev' : ∏ i, ev (U i) ^ c i ∈ Ksub ⊔ Subgroup.closure (Set.range (Fin.elim0 : Fin 0 → G)) ⊔
      (powMonoidHom 2 : G →* G).range := by
    have hle : Ksub ⊔ (powMonoidHom 2 : G →* G).range ≤
        Ksub ⊔ Subgroup.closure (Set.range (Fin.elim0 : Fin 0 → G)) ⊔
          (powMonoidHom 2 : G →* G).range :=
      sup_le_sup_right le_sup_left _
    exact hle hev
  rw [prod_pow_mem_iff_mod_two _ hS] at hev'
  rw [sb_mem_iff b hind Ksub κ hκK hK Aκ hAκ Fin.elim0 Fin.elim0 (fun l => l.elim0)
    (fun i => ev (U i)) Aμ hAμ] at hev'
  have hspan : ∑ i, ((c i : ℕ) : ZMod 2) • Aμ i ∈ Submodule.span (ZMod 2) (Set.range Aκ) := by
    have h0 : Submodule.span (ZMod 2) (Set.range (Fin.elim0 : Fin 0 → Fin nb → ZMod 2)) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨l, _⟩
      exact l.elim0
    simpa [h0] using hev'
  have hc0 := hcert _ hspan
  intro i
  have := congrFun hc0 i
  simpa [ZMod.natCast_eq_zero_iff] using this

/-- **Coordinate condition at a place from coordinates.** -/
theorem coordCond_of_coords {K : Type*} [Field K] (φ : K →+* K') (f : K[X])
    [GoodSextic (f.map φ)] {m r : ℕ} (gu : Fin m → (AdjoinRoot f)ˣ) (D : Fin r → Jac (f.map φ))
    (U : Fin r → (AdjoinRoot (f.map φ))ˣ) (hU : ∀ i, muJ (f.map φ) (D i) = QuotientGroup.mk (U i))
    {G : Type*} [CommGroup G] (ev : (AdjoinRoot (f.map φ))ˣ →* G) (Ksub : Subgroup G)
    (hKev : ∀ c : K'ˣ, ev (Units.map (algebraMap K' (AdjoinRoot (f.map φ))).toMonoidHom c) ∈ Ksub)
    {nb : ℕ} (b : Fin nb → G)
    (hind : ∀ ε : Fin nb → ZMod 2, IsSquare (∏ i, b i ^ (ε i).val) → ε = 0)
    {mκ : ℕ} (κ : Fin mκ → G) (hκK : ∀ l, κ l ∈ Ksub)
    (hK : ∀ x ∈ Ksub, ∃ c : Fin mκ → ZMod 2, IsSquare (x * ∏ l, κ l ^ (c l).val))
    (Aκ : Fin mκ → Fin nb → ZMod 2) (hAκ : ∀ l, IsSquare (κ l * ∏ i, b i ^ (Aκ l i).val))
    (Aμ : Fin r → Fin nb → ZMod 2) (hAμ : ∀ i, IsSquare (ev (U i) * ∏ j, b j ^ (Aμ i j).val))
    (Cg : Fin m → Fin nb → ZMod 2)
    (hCg : ∀ s, IsSquare (ev (Units.map (etaleMap φ f).toMonoidHom (gu s)) *
      ∏ j, b j ^ (Cg s j).val))
    {c : ℕ} (C : Matrix (Fin c) (Fin m) (ZMod 2))
    (hcert : ∀ a : Fin m → ZMod 2, ∑ s, a s • Cg s ∈
      Submodule.span (ZMod 2) (Set.range Aκ) ⊔ Submodule.span (ZMod 2) (Set.range Aμ) →
        C.mulVec a = 0) :
    CoordCond φ f (fun s => (QuotientGroup.mk (gu s) : H f))
      (Subgroup.closure (Set.range fun i => muJ (f.map φ) (D i))) C := by
  intro a ha
  set μ : Fin r → G := fun i => ev (U i) with hμ
  set gl : Fin m → (AdjoinRoot (f.map φ))ˣ := fun s => Units.map (etaleMap φ f).toMonoidHom (gu s)
  -- the image of `∏ g s ^ a s` is the class of `∏ gl s ^ a s`
  have himg : Hmap φ f (∏ s, (QuotientGroup.mk (gu s) : H f) ^ a s) =
      QuotientGroup.mk (∏ s, gl s ^ a s) := by
    rw [map_prod, QuotientGroup.mk_prod]
    simp only [map_pow, QuotientGroup.mk_pow]
    rfl
  rw [himg] at ha
  -- the closure of the images of the points is the image of the closure of the `U i`
  have hcl : Subgroup.closure (Set.range fun i => muJ (f.map φ) (D i)) =
      (Subgroup.closure (Set.range U)).map (QuotientGroup.mk' (sqClass (f.map φ))) := by
    have hfun : (fun i => muJ (f.map φ) (D i)) = (QuotientGroup.mk' (sqClass (f.map φ))) ∘ U :=
      funext fun i => hU i
    rw [hfun, Set.range_comp, MonoidHom.map_closure]
  rw [hcl] at ha
  obtain ⟨y, hy, hyx⟩ := ha
  have hdiv : y⁻¹ * ∏ s, gl s ^ a s ∈ sqClass (f.map φ) := by
    rw [← QuotientGroup.eq]
    exact hyx
  have hev := ev_mem_of_mem_sqClass ev Ksub hKev hdiv
  have hyμ : ev y ∈ Subgroup.closure (Set.range μ) := by
    have : (Subgroup.closure (Set.range U)).map ev ≤ Subgroup.closure (Set.range μ) := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    exact this ⟨y, hy, rfl⟩
  set S := Ksub ⊔ Subgroup.closure (Set.range μ) ⊔ (powMonoidHom 2 : G →* G).range
  have hmemS : ∏ s, ev (gl s) ^ a s ∈ S := by
    have h1 : ev y ∈ S := Subgroup.mem_sup_left (Subgroup.mem_sup_right hyμ)
    have h2 : ev (y⁻¹ * ∏ s, gl s ^ a s) ∈ S :=
      (sup_le_sup_right le_sup_left _ : Ksub ⊔ (powMonoidHom 2 : G →* G).range ≤ S) hev
    have h3 := S.mul_mem h1 h2
    simpa [map_mul, map_inv, map_prod, map_pow] using h3
  rw [prod_pow_mem_iff_mod_two S le_sup_right] at hmemS
  rw [sb_mem_iff b hind Ksub κ hκK hK Aκ hAκ μ Aμ hAμ (fun s => ev (gl s)) Cg hCg] at hmemS
  exact hcert _ hmemS

/-- **Independence modulo squares in a product of component fields.** Rows `b i` of
`G = ∀ j, (F j)ˣ` carry at each component `j` a datum (`k`, `u`, adjusting element `s`) whose
`DFact` holds; with `CompOK` at every component and a passing `echelonOK` on the positions
`ι × CPos`, the rows are independent modulo squares. -/
theorem indep_of_components {ι : Type*} {F : ι → Type*} [∀ j, NormedField (F j)]
    [∀ j, IsUltrametricDist (F j)] (Q : ι → CShape) (π : ∀ j, F j) (w : ∀ j, Fin (Q j).f → F j)
    (hQ : ∀ j, CompOK (Q j) (π j) (w j)) {r : ℕ} (b : Fin r → ∀ j, (F j)ˣ) (s : Fin r → ∀ j, F j)
    (k : ℕ → ι → ℤ) (u : ℕ → ι → UDatum)
    (hfact : ∀ (i : Fin r) j, DFact (Q j) (π j) (w j) ((b i j : (F j)ˣ) : F j) (s i j) (k i j) (u i j))
    (piv : ℕ → ι × CPos)
    (hech : echelonOK (fun i p => admB (Q p.1) (u i p.1) p.2)
      (fun i p => digB (Q p.1) (k i p.1) (u i p.1) p.2) piv r = true)
    (ε : Fin r → ZMod 2) (hsq : IsSquare (∏ i, b i ^ (ε i).val)) : ε = 0 :=
  sb_indep_of_echelonOK b _ _ piv
    (fun p ε hadm hsq => comp_test b (Pi.evalMonoidHom (fun j => (F j)ˣ) p.1) (Q p.1) (hQ p.1)
      (fun i => s i p.1) (fun i => k i p.1) (fun i => u i p.1) (fun i => hfact i p.1) p.2 ε hadm hsq)
    hech ε hsq

theorem isSquare_pi {ι : Type*} {G : ι → Type*} [∀ j, Monoid (G j)] (x : ∀ j, G j)
    (h : ∀ j, IsSquare (x j)) : IsSquare x := by
  choose r hr using h
  exact ⟨r, funext fun j => hr j⟩

/-- The generators `κ` of the scalars modulo squares, from a spanning statement in `K'`. -/
theorem hK_of_span {K' : Type*} [Field K'] {A : Type*} [CommRing A] [Algebra K' A]
    {G : Type*} [CommGroup G] (ev : Aˣ →* G) {mκ : ℕ} (κ0 : Fin mκ → K'ˣ)
    (hspan : ∀ x : K', x ≠ 0 → ∃ c : Fin mκ → ZMod 2,
      IsSquare (x * ∏ l, (κ0 l : K') ^ (c l).val)) :
    ∀ x ∈ (ev.comp (Units.map (algebraMap K' A).toMonoidHom)).range, ∃ c : Fin mκ → ZMod 2,
      IsSquare (x * ∏ l, ev (Units.map (algebraMap K' A).toMonoidHom (κ0 l)) ^ (c l).val) := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨c, hc⟩ := hspan y y.ne_zero
  refine ⟨c, ?_⟩
  have hu : IsSquare (y * ∏ l, κ0 l ^ (c l).val) :=
    isSquare_units_of_isSquare _ (by simpa [Units.coe_prod] using hc)
  obtain ⟨r, hr⟩ := hu
  refine ⟨ev (Units.map (algebraMap K' A).toMonoidHom r), ?_⟩
  have := congrArg (ev.comp (Units.map (algebraMap K' A).toMonoidHom)) hr
  simpa [map_prod, map_pow, map_mul] using this


end Glue

section Bits

/-- The `F₂` certificate of `indepImage_of_coords` on bitmasks: rows `Q k` annihilate the `κ`
coordinates (`annOK`), and the forms `Q k` read on the `μ` coordinates have a left inverse
(`leftInvOK`). -/
theorem hcert_indep_of_bits {nb r mκ nQ : ℕ} (AκB AμB Q T : ℕ → ℕ)
    (hann : annOK nb AκB mκ Q nQ = true)
    (hinv : leftInvOK (fun k => dotRow nb AμB (Q k) r) nQ r T = true) :
    ∀ c : Fin r → ZMod 2, ∑ i, c i • bitv nb (AμB i) ∈
      Submodule.span (ZMod 2) (Set.range fun l : Fin mκ => bitv nb (AκB l)) → c = 0 := by
  intro c hc
  have hc' : ∑ i, c i • bitv nb (AμB i) ∈
      Submodule.span (ZMod 2) (Set.range fun l : Fin mκ => bitv nb (AκB l)) ⊔
        Submodule.span (ZMod 2) (Set.range fun l : Fin mκ => bitv nb (AκB l)) := by
    rwa [sup_idem]
  refine eq_zero_of_leftInvOK hinv c fun k => ?_
  rw [← dotRow_sound]
  exact ann_of_mem_sup hann hann hc' k

/-- The `F₂` certificate of `coordCond_of_coords` on bitmasks: rows `Q i` annihilate the `κ` and `μ`
coordinates, and `C` is the matrix of the forms `Q i` read on the coordinates of the global
classes. -/
theorem hcert_coord_of_bits {nb m mκ r nQ : ℕ} (AκB AμB CgB Q : ℕ → ℕ)
    (h1 : annOK nb AκB mκ Q nQ = true) (h2 : annOK nb AμB r Q nQ = true) :
    ∀ a : Fin m → ZMod 2, ∑ s, a s • bitv nb (CgB s) ∈
      Submodule.span (ZMod 2) (Set.range fun l : Fin mκ => bitv nb (AκB l)) ⊔
        Submodule.span (ZMod 2) (Set.range fun l : Fin r => bitv nb (AμB l)) →
      (Matrix.of fun (i : Fin nQ) (s : Fin m) => bitv m (dotRow nb CgB (Q i) m) s).mulVec a = 0 := by
  intro a ha
  funext i
  have h := ann_of_mem_sup h1 h2 ha i
  rw [dotRow_sound] at h
  simpa [Matrix.mulVec, dotProduct] using h

end Bits

end FurioLombardo.Discharge.SelmerBasis
