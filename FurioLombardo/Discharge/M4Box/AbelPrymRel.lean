import FurioLombardo.Discharge.M4Box.Comp.AbelPrym
import FurioLombardo.Discharge.KvArith.Cantor

/-!
# The relational lemma of the Abel-Prym program (lane lean-m4box)

For `h : Ops.Rel o p R`, related inputs give related outputs, one lemma per sub-program of
`M4Box/Comp/AbelPrym.lean`, and `rel_apPhi`: whenever the run of `apPhi` on `p` succeeds, so does the
run on `o`, with related Mumford pairs. With `o = fieldOps Kv` and `p = ballOpsF k` a successful ball run
is a certificate of the exact run and encloses its pair.
-/

namespace FurioLombardo.Discharge.M4Box

open FurioLombardo.Discharge.KvArith

/-- Entrywise relation of symmetric matrices. -/
def Sym3.Rel {A B : Type*} (R : A → B → Prop) (m : Sym3 A) (m' : Sym3 B) : Prop :=
  R m.a00 m'.a00 ∧ R m.a01 m'.a01 ∧ R m.a02 m'.a02 ∧ R m.a11 m'.a11 ∧ R m.a12 m'.a12 ∧ R m.a22 m'.a22

/-- Coordinatewise relation of `Vec5`. -/
def Vec5.Rel {A B : Type*} (R : A → B → Prop) (v : Vec5 A) (v' : Vec5 B) : Prop :=
  R v.c0 v'.c0 ∧ R v.c1 v'.c1 ∧ R v.c2 v'.c2 ∧ R v.c3 v'.c3 ∧ R v.c4 v'.c4

/-- Coordinatewise relation of triples. -/
def Trip.Rel {A B : Type*} (R : A → B → Prop) (w : A × A × A) (w' : B × B × B) : Prop :=
  R w.1 w'.1 ∧ R w.2.1 w'.2.1 ∧ R w.2.2 w'.2.2

/-- Relation of the inputs of the program. -/
def APIn.Rel {A B : Type*} (R : A → B → Prop) (x : APIn A) (y : APIn B) : Prop :=
  Sym3.Rel R x.n1 y.n1 ∧ Sym3.Rel R x.n2 y.n2 ∧ Sym3.Rel R x.n3 y.n3 ∧ R x.dl y.dl ∧ R x.p0 y.p0 ∧
    R x.p1 y.p1 ∧ R x.p2 y.p2 ∧ R x.r y.r ∧ R x.s y.s

section Rel

variable {A B : Type*} {o : Ops A} {p : Ops B} {R : A → B → Prop}

theorem rel_mulVec (h : Ops.Rel o p R) {m : Sym3 A} {m' : Sym3 B} (hm : Sym3.Rel R m m')
    {a0 a1 a2 : A} {b0 b1 b2 : B} (h0 : R a0 b0) (h1 : R a1 b1) (h2 : R a2 b2) :
    Trip.Rel R (Sym3.mulVec o m a0 a1 a2) (Sym3.mulVec p m' b0 b1 b2) := by
  rcases hm with ⟨hm00, hm01, hm02, hm11, hm12, hm22⟩
  unfold Sym3.mulVec
  have hx := h.add (h.add (h.mul hm00 h0) (h.mul hm01 h1)) (h.mul hm02 h2)
  have hy := h.add (h.add (h.mul hm01 h0) (h.mul hm11 h1)) (h.mul hm12 h2)
  have hz := h.add (h.add (h.mul hm02 h0) (h.mul hm12 h1)) (h.mul hm22 h2)
  exact ⟨hx, hy, hz⟩

theorem rel_quad (h : Ops.Rel o p R) {m : Sym3 A} {m' : Sym3 B} (hm : Sym3.Rel R m m')
    {a0 a1 a2 : A} {b0 b1 b2 : B} (h0 : R a0 b0) (h1 : R a1 b1) (h2 : R a2 b2) :
    R (Sym3.quad o m a0 a1 a2) (Sym3.quad p m' b0 b1 b2) := by
  unfold Sym3.quad
  obtain ⟨hw0, hw1, hw2⟩ := rel_mulVec h hm h0 h1 h2
  have hmul0 := h.mul h0 hw0
  have hmul1 := h.mul h1 hw1
  have hmul2 := h.mul h2 hw2
  have hadd01 := h.add hmul0 hmul1
  exact h.add hadd01 hmul2

theorem rel_det3 (h : Ops.Rel o p R) {a b c d e f g k l : A} {a' b' c' d' e' f' g' k' l' : B}
    (ha : R a a') (hb : R b b') (hc : R c c') (hd : R d d') (he : R e e') (hf : R f f') (hg : R g g')
    (hk : R k k') (hl : R l l') :
    R (det3 o a b c d e f g k l) (det3 p a' b' c' d' e' f' g' k' l') := by
  unfold det3
  have h_el : R (o.mul e l) (p.mul e' l') := h.mul he hl
  have h_fk : R (o.mul f k) (p.mul f' k') := h.mul hf hk
  have h_sub1 : R (o.sub (o.mul e l) (o.mul f k)) (p.sub (p.mul e' l') (p.mul f' k')) := h.sub h_el h_fk
  have h_a_sub1 : R (o.mul a (o.sub (o.mul e l) (o.mul f k))) (p.mul a' (p.sub (p.mul e' l') (p.mul f' k'))) := h.mul ha h_sub1
  have h_dl : R (o.mul d l) (p.mul d' l') := h.mul hd hl
  have h_fg : R (o.mul f g) (p.mul f' g') := h.mul hf hg
  have h_sub2 : R (o.sub (o.mul d l) (o.mul f g)) (p.sub (p.mul d' l') (p.mul f' g')) := h.sub h_dl h_fg
  have h_b_sub2 : R (o.mul b (o.sub (o.mul d l) (o.mul f g))) (p.mul b' (p.sub (p.mul d' l') (p.mul f' g'))) := h.mul hb h_sub2
  have h_sub1_sub2 : R (o.sub (o.mul a (o.sub (o.mul e l) (o.mul f k))) (o.mul b (o.sub (o.mul d l) (o.mul f g)))) (p.sub (p.mul a' (p.sub (p.mul e' l') (p.mul f' k'))) (p.mul b' (p.sub (p.mul d' l') (p.mul f' g')))) := h.sub h_a_sub1 h_b_sub2
  have h_dk : R (o.mul d k) (p.mul d' k') := h.mul hd hk
  have h_eg : R (o.mul e g) (p.mul e' g') := h.mul he hg
  have h_sub3 : R (o.sub (o.mul d k) (o.mul e g)) (p.sub (p.mul d' k') (p.mul e' g')) := h.sub h_dk h_eg
  have h_c_sub3 : R (o.mul c (o.sub (o.mul d k) (o.mul e g))) (p.mul c' (p.sub (p.mul d' k') (p.mul e' g'))) := h.mul hc h_sub3
  exact h.add h_sub1_sub2 h_c_sub3

theorem rel_get {v : Vec5 A} {v' : Vec5 B} (hv : Vec5.Rel R v v') (n : ℕ) : R (v.get n) (v'.get n) := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  rcases n with (rfl|rfl|rfl|rfl|n)
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem rel_minor3 (h : Ops.Rel o p R) {J0 J1 J2 : Vec5 A} {J0' J1' J2' : Vec5 B}
    (h0 : Vec5.Rel R J0 J0') (h1 : Vec5.Rel R J1 J1') (h2 : Vec5.Rel R J2 J2') (a b c : ℕ) :
    R (minor3 o J0 J1 J2 a b c) (minor3 p J0' J1' J2' a b c) := by
  unfold minor3
  apply rel_det3 h
  · exact rel_get h0 a
  · exact rel_get h0 b
  · exact rel_get h0 c
  · exact rel_get h1 a
  · exact rel_get h1 b
  · exact rel_get h1 c
  · exact rel_get h2 a
  · exact rel_get h2 b
  · exact rel_get h2 c

theorem rel_kerVec (h : Ops.Rel o p R) {J0 J1 J2 : Vec5 A} {J0' J1' J2' : Vec5 B}
    (h0 : Vec5.Rel R J0 J0') (h1 : Vec5.Rel R J1 J1') (h2 : Vec5.Rel R J2 J2') (kd : ℕ) :
    Vec5.Rel R (kerVec o J0 J1 J2 kd) (kerVec p J0' J1' J2' kd) := by
  rcases kd with _ | _ | _ | _ | kd
  · -- kd = 0
    simp only [kerVec]
    exact ⟨Ops.Rel.zero h, rel_minor3 h h0 h1 h2 2 3 4, h.neg (rel_minor3 h h0 h1 h2 1 3 4),
      rel_minor3 h h0 h1 h2 1 2 4, h.neg (rel_minor3 h h0 h1 h2 1 2 3)⟩
  · -- kd = 1
    simp only [kerVec]
    exact ⟨rel_minor3 h h0 h1 h2 2 3 4, Ops.Rel.zero h, h.neg (rel_minor3 h h0 h1 h2 0 3 4),
      rel_minor3 h h0 h1 h2 0 2 4, h.neg (rel_minor3 h h0 h1 h2 0 2 3)⟩
  · -- kd = 2
    simp only [kerVec]
    exact ⟨rel_minor3 h h0 h1 h2 1 3 4, h.neg (rel_minor3 h h0 h1 h2 0 3 4), Ops.Rel.zero h,
      rel_minor3 h h0 h1 h2 0 1 4, h.neg (rel_minor3 h h0 h1 h2 0 1 3)⟩
  · -- kd = 3
    simp only [kerVec]
    exact ⟨rel_minor3 h h0 h1 h2 1 2 4, h.neg (rel_minor3 h h0 h1 h2 0 2 4),
      rel_minor3 h h0 h1 h2 0 1 4, Ops.Rel.zero h, h.neg (rel_minor3 h h0 h1 h2 0 1 2)⟩
  · -- kd = other (default case)
    simp only [kerVec]
    exact ⟨rel_minor3 h h0 h1 h2 1 2 3, h.neg (rel_minor3 h h0 h1 h2 0 2 3),
      rel_minor3 h h0 h1 h2 0 1 3, h.neg (rel_minor3 h h0 h1 h2 0 1 2), Ops.Rel.zero h⟩

theorem rel_tanRow (h : Ops.Rel o p R) {m : Sym3 A} {m' : Sym3 B} (hm : Sym3.Rel R m m')
    {a0 a1 a2 ρ τ : A} {b0 b1 b2 ρ' τ' : B} (h0 : R a0 b0) (h1 : R a1 b1) (h2 : R a2 b2)
    (hρ : R ρ ρ') (hτ : R τ τ') :
    Vec5.Rel R (tanRow o m a0 a1 a2 ρ τ) (tanRow p m' b0 b1 b2 ρ' τ') := by
  unfold tanRow
  have hw := rel_mulVec h hm h0 h1 h2
  rcases hw with ⟨hwa, hwb, hwc⟩
  refine ⟨h.add hwa hwa, h.add hwb hwb, h.add hwc hwc, hρ, hτ⟩

theorem rel_trip {w : A × A × A} {w' : B × B × B} (hw : Trip.Rel R w w') (n : ℕ) :
    R (trip w n) (trip w' n) := by
  rcases hw with ⟨h0, h1, h2⟩
  match n with
  | 0 => exact h0
  | 1 => exact h1
  | n+2 => exact h2

theorem rel_row {m : Sym3 A} {m' : Sym3 B} (hm : Sym3.Rel R m m') (l : ℕ) :
    Trip.Rel R (Sym3.row m l) (Sym3.row m' l) := by
  rcases hm with ⟨h00, h01, h02, h11, h12, h22⟩
  cases l with
  | zero =>
      unfold Sym3.row
      exact ⟨h00, h01, h02⟩
  | succ l =>
    cases l with
    | zero =>
        unfold Sym3.row
        exact ⟨h01, h11, h12⟩
    | succ l =>
      unfold Sym3.row
      exact ⟨h02, h12, h22⟩

theorem rel_minor2 (h : Ops.Rel o p R) {a0 a1 a2 c0 c1 c2 : A} {b0 b1 b2 d0 d1 d2 : B}
    (h0 : R a0 b0) (h1 : R a1 b1) (h2 : R a2 b2) (k0 : R c0 d0) (k1 : R c1 d1) (k2 : R c2 d2) (l : ℕ) :
    R (minor2 o a0 a1 a2 c0 c1 c2 l) (minor2 p b0 b1 b2 d0 d1 d2 l) := by
  rcases l with (l | l)
  · -- l = 0
    simp only [minor2]
    apply h.sub
    · apply h.mul; exact h1; exact k2
    · apply h.mul; exact h2; exact k1
  · rcases l with (l | l)
    · -- l = 1
      simp only [minor2]
      apply h.sub
      · apply h.mul; exact h2; exact k0
      · apply h.mul; exact h0; exact k2
    · -- l >= 2
      simp only [minor2]
      apply h.sub
      · apply h.mul; exact h0; exact k1
      · apply h.mul; exact h1; exact k0

theorem rel_apNv (h : Ops.Rel o p R) {x : APIn A} {y : APIn B} (hx : APIn.Rel R x y) :
    Trip.Rel R (apNv o x) (apNv p y) := by
  obtain ⟨hn1, hn2, hn3, hdl, hp0, hp1, hp2, hr, hs⟩ := hx
  have hw1 := rel_mulVec h hn1 hp0 hp1 hp2
  have hw2 := rel_mulVec h hn2 hp0 hp1 hp2
  have hw3 := rel_mulVec h hn3 hp0 hp1 hp2
  have hw1_1 : R (Sym3.mulVec o x.n1 x.p0 x.p1 x.p2).1 (Sym3.mulVec p y.n1 y.p0 y.p1 y.p2).1 := hw1.1
  have hw1_2 : R (Sym3.mulVec o x.n1 x.p0 x.p1 x.p2).2.1 (Sym3.mulVec p y.n1 y.p0 y.p1 y.p2).2.1 := hw1.2.1
  have hw1_3 : R (Sym3.mulVec o x.n1 x.p0 x.p1 x.p2).2.2 (Sym3.mulVec p y.n1 y.p0 y.p1 y.p2).2.2 := hw1.2.2
  have hw2_1 : R (Sym3.mulVec o x.n2 x.p0 x.p1 x.p2).1 (Sym3.mulVec p y.n2 y.p0 y.p1 y.p2).1 := hw2.1
  have hw2_2 : R (Sym3.mulVec o x.n2 x.p0 x.p1 x.p2).2.1 (Sym3.mulVec p y.n2 y.p0 y.p1 y.p2).2.1 := hw2.2.1
  have hw2_3 : R (Sym3.mulVec o x.n2 x.p0 x.p1 x.p2).2.2 (Sym3.mulVec p y.n2 y.p0 y.p1 y.p2).2.2 := hw2.2.2
  have hw3_1 : R (Sym3.mulVec o x.n3 x.p0 x.p1 x.p2).1 (Sym3.mulVec p y.n3 y.p0 y.p1 y.p2).1 := hw3.1
  have hw3_2 : R (Sym3.mulVec o x.n3 x.p0 x.p1 x.p2).2.1 (Sym3.mulVec p y.n3 y.p0 y.p1 y.p2).2.1 := hw3.2.1
  have hw3_3 : R (Sym3.mulVec o x.n3 x.p0 x.p1 x.p2).2.2 (Sym3.mulVec p y.n3 y.p0 y.p1 y.p2).2.2 := hw3.2.2
  have hss : R (o.mul x.s x.s) (p.mul y.s y.s) := h.mul hs hs
  have hrr : R (o.mul x.r x.r) (p.mul y.r y.r) := h.mul hr hr
  have hrs : R (o.mul x.r x.s) (p.mul y.r y.s) := h.mul hr hs
  have hrs_sum : R (o.add (o.mul x.r x.s) (o.mul x.r x.s)) (p.add (p.mul y.r y.s) (p.mul y.r y.s)) := h.add hrs hrs
  unfold apNv
  refine ⟨?_, ?_, ?_⟩
  · apply h.add
    · apply h.sub
      · apply h.mul hss hw1_1
      · apply h.mul hrs_sum hw2_1
    · apply h.mul hrr hw3_1
  · apply h.add
    · apply h.sub
      · apply h.mul hss hw1_2
      · apply h.mul hrs_sum hw2_2
    · apply h.mul hrr hw3_2
  · apply h.add
    · apply h.sub
      · apply h.mul hss hw1_3
      · apply h.mul hrs_sum hw2_3
    · apply h.mul hrr hw3_3

theorem rel_apJ0 (h : Ops.Rel o p R) {x : APIn A} {y : APIn B} (hx : APIn.Rel R x y) :
    Vec5.Rel R (apJ0 o x) (apJ0 p y) := by
  rcases hx with ⟨hn1, hn2, hn3, hdl, hp0, hp1, hp2, hr, hs⟩
  have hzero : R o.zero p.zero := Ops.Rel.zero h
  have hrho : R (o.neg (o.add (o.mul x.dl x.r) (o.mul x.dl x.r))) (p.neg (p.add (p.mul y.dl y.r) (p.mul y.dl y.r))) :=
    h.neg (h.add (h.mul hdl hr) (h.mul hdl hr))
  exact rel_tanRow h hn1 hp0 hp1 hp2 hrho hzero

theorem rel_apJ1 (h : Ops.Rel o p R) {x : APIn A} {y : APIn B} (hx : APIn.Rel R x y) :
    Vec5.Rel R (apJ1 o x) (apJ1 p y) := by
  rcases hx with ⟨hn1, hn2, hn3, hdl, hp0, hp1, hp2, hr, hs⟩
  exact rel_tanRow h hn2 hp0 hp1 hp2 (h.neg (h.mul hdl hs)) (h.neg (h.mul hdl hr))

theorem rel_apJ2 (h : Ops.Rel o p R) {x : APIn A} {y : APIn B} (hx : APIn.Rel R x y) :
    Vec5.Rel R (apJ2 o x) (apJ2 p y) := by
  rcases hx with ⟨hn1, hn2, hn3, hdl, hp0, hp1, hp2, hr, hs⟩
  have hzero : R o.zero p.zero := h.zero
  have hmul : R (o.mul x.dl x.s) (p.mul y.dl y.s) := h.mul hdl hs
  have hadd : R (o.add (o.mul x.dl x.s) (o.mul x.dl x.s)) (p.add (p.mul y.dl y.s) (p.mul y.dl y.s)) :=
    h.add hmul hmul
  have hneg : R (o.neg (o.add (o.mul x.dl x.s) (o.mul x.dl x.s))) (p.neg (p.add (p.mul y.dl y.s) (p.mul y.dl y.s))) :=
    h.neg hadd
  exact rel_tanRow h hn3 hp0 hp1 hp2 hzero hneg

theorem rel_apT (h : Ops.Rel o p R) {x : APIn A} {y : APIn B} (hx : APIn.Rel R x y) (kd : ℕ) :
    Vec5.Rel R (apT o x kd) (apT p y kd) := by
  unfold apT
  exact rel_kerVec h (rel_apJ0 h hx) (rel_apJ1 h hx) (rel_apJ2 h hx) kd

theorem rel_apA (h : Ops.Rel o p R) {x : APIn A} {y : APIn B} (hx : APIn.Rel R x y)
    {T : Vec5 A} {T' : Vec5 B} (hT : Vec5.Rel R T T') :
    Trip.Rel R (apA o x T) (apA p y T') := by
  obtain ⟨hn1, hn2, hn3, hdl, hp0, hp1, hp2, hr, hs⟩ := hx
  obtain ⟨hc0, hc1, hc2, hc3, hc4⟩ := hT
  unfold apA
  refine ⟨?_, ?_, ?_⟩
  · -- first component
    apply h.sub
    · exact rel_quad h hn1 hc0 hc1 hc2
    · exact h.mul hdl (h.mul hc3 hc3)
  · -- second component
    apply h.sub
    · exact rel_quad h hn2 hc0 hc1 hc2
    · exact h.mul hdl (h.mul hc3 hc4)
  · -- third component
    apply h.sub
    · exact rel_quad h hn3 hc0 hc1 hc2
    · exact h.mul hdl (h.mul hc4 hc4)

theorem rel_dot3 (h : Ops.Rel o p R) {m : A × A × A} {m' : B × B × B} (hm : Trip.Rel R m m')
    {a0 a1 a2 : A} {b0 b1 b2 : B} (h0 : R a0 b0) (h1 : R a1 b1) (h2 : R a2 b2) :
    R (dot3 o m a0 a1 a2) (dot3 p m' b0 b1 b2) := by
  unfold dot3
  rcases hm with ⟨hm0, hm1, hm2⟩
  have hmul0 := h.mul hm0 h0
  have hmul1 := h.mul hm1 h1
  have hmul2 := h.mul hm2 h2
  have hadd0 := h.add hmul0 hmul1
  exact h.add hadd0 hmul2

theorem rel_apE (h : Ops.Rel o p R) {x : APIn A} {y : APIn B} (hx : APIn.Rel R x y)
    {T : Vec5 A} {T' : Vec5 B} (hT : Vec5.Rel R T T') (l : ℕ) :
    Quart.Rel R (apE o x T l) (apE p y T' l) := by
  obtain ⟨hx_n1, hx_n2, hx_n3, hx_dl, hx_p0, hx_p1, hx_p2, hx_r, hx_s⟩ := hx
  obtain ⟨hT_c0, hT_c1, hT_c2, hT_c3, hT_c4⟩ := hT
  have hnd : R (o.neg x.dl) (p.neg y.dl) := h.neg hx_dl
  have hm1 : Trip.Rel R (Sym3.row x.n1 l) (Sym3.row y.n1 l) := rel_row hx_n1 l
  have hm2 : Trip.Rel R (Sym3.row x.n2 l) (Sym3.row y.n2 l) := rel_row hx_n2 l
  have hm3 : Trip.Rel R (Sym3.row x.n3 l) (Sym3.row y.n3 l) := rel_row hx_n3 l
  have hal0 : R (o.sub (o.mul x.p0 T.c3) (o.mul T.c0 x.r)) (p.sub (p.mul y.p0 T'.c3) (p.mul T'.c0 y.r)) :=
    h.sub (h.mul hx_p0 hT_c3) (h.mul hT_c0 hx_r)
  have hal1 : R (o.sub (o.mul x.p1 T.c3) (o.mul T.c1 x.r)) (p.sub (p.mul y.p1 T'.c3) (p.mul T'.c1 y.r)) :=
    h.sub (h.mul hx_p1 hT_c3) (h.mul hT_c1 hx_r)
  have hal2 : R (o.sub (o.mul x.p2 T.c3) (o.mul T.c2 x.r)) (p.sub (p.mul y.p2 T'.c3) (p.mul T'.c2 y.r)) :=
    h.sub (h.mul hx_p2 hT_c3) (h.mul hT_c2 hx_r)
  have hbe0 : R (o.sub (o.mul x.p0 T.c4) (o.mul T.c0 x.s)) (p.sub (p.mul y.p0 T'.c4) (p.mul T'.c0 y.s)) :=
    h.sub (h.mul hx_p0 hT_c4) (h.mul hT_c0 hx_s)
  have hbe1 : R (o.sub (o.mul x.p1 T.c4) (o.mul T.c1 x.s)) (p.sub (p.mul y.p1 T'.c4) (p.mul T'.c1 y.s)) :=
    h.sub (h.mul hx_p1 hT_c4) (h.mul hT_c1 hx_s)
  have hbe2 : R (o.sub (o.mul x.p2 T.c4) (o.mul T.c2 x.s)) (p.sub (p.mul y.p2 T'.c4) (p.mul T'.c2 y.s)) :=
    h.sub (h.mul hx_p2 hT_c4) (h.mul hT_c2 hx_s)
  have hdot1_al : R (dot3 o (Sym3.row x.n1 l) (o.sub (o.mul x.p0 T.c3) (o.mul T.c0 x.r)) (o.sub (o.mul x.p1 T.c3) (o.mul T.c1 x.r)) (o.sub (o.mul x.p2 T.c3) (o.mul T.c2 x.r)))
                      (dot3 p (Sym3.row y.n1 l) (p.sub (p.mul y.p0 T'.c3) (p.mul T'.c0 y.r)) (p.sub (p.mul y.p1 T'.c3) (p.mul T'.c1 y.r)) (p.sub (p.mul y.p2 T'.c3) (p.mul T'.c2 y.r))) :=
    rel_dot3 h hm1 hal0 hal1 hal2
  have hdot1_be : R (dot3 o (Sym3.row x.n1 l) (o.sub (o.mul x.p0 T.c4) (o.mul T.c0 x.s)) (o.sub (o.mul x.p1 T.c4) (o.mul T.c1 x.s)) (o.sub (o.mul x.p2 T.c4) (o.mul T.c2 x.s)))
                      (dot3 p (Sym3.row y.n1 l) (p.sub (p.mul y.p0 T'.c4) (p.mul T'.c0 y.s)) (p.sub (p.mul y.p1 T'.c4) (p.mul T'.c1 y.s)) (p.sub (p.mul y.p2 T'.c4) (p.mul T'.c2 y.s))) :=
    rel_dot3 h hm1 hbe0 hbe1 hbe2
  have hdot2_al : R (dot3 o (Sym3.row x.n2 l) (o.sub (o.mul x.p0 T.c3) (o.mul T.c0 x.r)) (o.sub (o.mul x.p1 T.c3) (o.mul T.c1 x.r)) (o.sub (o.mul x.p2 T.c3) (o.mul T.c2 x.r)))
                      (dot3 p (Sym3.row y.n2 l) (p.sub (p.mul y.p0 T'.c3) (p.mul T'.c0 y.r)) (p.sub (p.mul y.p1 T'.c3) (p.mul T'.c1 y.r)) (p.sub (p.mul y.p2 T'.c3) (p.mul T'.c2 y.r))) :=
    rel_dot3 h hm2 hal0 hal1 hal2
  have hdot2_be : R (dot3 o (Sym3.row x.n2 l) (o.sub (o.mul x.p0 T.c4) (o.mul T.c0 x.s)) (o.sub (o.mul x.p1 T.c4) (o.mul T.c1 x.s)) (o.sub (o.mul x.p2 T.c4) (o.mul T.c2 x.s)))
                      (dot3 p (Sym3.row y.n2 l) (p.sub (p.mul y.p0 T'.c4) (p.mul T'.c0 y.s)) (p.sub (p.mul y.p1 T'.c4) (p.mul T'.c1 y.s)) (p.sub (p.mul y.p2 T'.c4) (p.mul T'.c2 y.s))) :=
    rel_dot3 h hm2 hbe0 hbe1 hbe2
  have hdot3_al : R (dot3 o (Sym3.row x.n3 l) (o.sub (o.mul x.p0 T.c3) (o.mul T.c0 x.r)) (o.sub (o.mul x.p1 T.c3) (o.mul T.c1 x.r)) (o.sub (o.mul x.p2 T.c3) (o.mul T.c2 x.r)))
                      (dot3 p (Sym3.row y.n3 l) (p.sub (p.mul y.p0 T'.c3) (p.mul T'.c0 y.r)) (p.sub (p.mul y.p1 T'.c3) (p.mul T'.c1 y.r)) (p.sub (p.mul y.p2 T'.c3) (p.mul T'.c2 y.r))) :=
    rel_dot3 h hm3 hal0 hal1 hal2
  have hdot3_be : R (dot3 o (Sym3.row x.n3 l) (o.sub (o.mul x.p0 T.c4) (o.mul T.c0 x.s)) (o.sub (o.mul x.p1 T.c4) (o.mul T.c1 x.s)) (o.sub (o.mul x.p2 T.c4) (o.mul T.c2 x.s)))
                      (dot3 p (Sym3.row y.n3 l) (p.sub (p.mul y.p0 T'.c4) (p.mul T'.c0 y.s)) (p.sub (p.mul y.p1 T'.c4) (p.mul T'.c1 y.s)) (p.sub (p.mul y.p2 T'.c4) (p.mul T'.c2 y.s))) :=
    rel_dot3 h hm3 hbe0 hbe1 hbe2
  simp only [apE, Quart.Rel]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply h.mul hnd
    exact hdot1_al
  · apply h.mul hnd
    apply h.add hdot1_be
    apply h.add hdot2_al hdot2_al
  · apply h.mul hnd
    apply h.add
    · apply h.add hdot2_be hdot2_be
    · exact hdot3_al
  · apply h.mul hnd
    exact hdot3_be

/-- **The relational lemma of the Abel-Prym program.** -/
theorem rel_apPhi (h : Ops.Rel o p R) (prm : APPrm) {x : APIn A} {y : APIn B} (hx : APIn.Rel R x y) :
    OptRel (Mum.Rel R) (apPhi o prm x) (apPhi p prm y) := by
  have hN := rel_trip (rel_apNv h hx) prm.jN
  have hT := rel_apT h hx prm.kd
  have hA := rel_apA h hx hT
  have hE := rel_apE h hx hT prm.l
  obtain ⟨hA0, hA1, hA2⟩ := hA
  obtain ⟨hT0, hT1, hT2, -, -⟩ := hT
  obtain ⟨-, -, -, -, hp0, hp1, hp2, -, -⟩ := hx
  obtain ⟨hE0, hE1, hE2, hE3⟩ := hE
  unfold apPhi
  dsimp only
  apply OptRel.bind (R := R)
  · intro b hb
    exact h.inv hN hb
  intro _ _ _
  apply OptRel.bind (R := R)
  · intro b hb
    exact h.inv hA2 hb
  intro ia3 ia3' hi
  apply OptRel.bind (R := R)
  · intro b hb
    exact h.inv (rel_minor2 h hp0 hp1 hp2 hT0 hT1 hT2 prm.l) hb
  intro ic ic' hc b hb
  have hb' := Option.some.inj hb
  subst hb'
  have hu1 := h.mul (h.add hA1 hA1) hi
  have hu0 := h.mul hA0 hi
  exact ⟨_, rfl, hu0, hu1, h.mul (h.add (h.sub hE0 (h.mul hE2 hu0)) (h.mul hE3 (h.mul hu1 hu0))) hc,
    h.mul (h.add (h.sub hE1 (h.mul hE2 hu1)) (h.mul hE3 (h.sub (h.mul hu1 hu1) hu0))) hc⟩

end Rel

end FurioLombardo.Discharge.M4Box
