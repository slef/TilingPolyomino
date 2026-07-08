import TilingPolyomino.Polyomino.Fat
import Mathlib.Data.Int.LeastGreatest

/-!
# The boundary successor of a vertex

`NextVtx P u w`: `w` is the vertex following `u` on the boundary of `P`,
walked with the interior on the left; the edge between them is a straight
run (`HRunAbove` …) of one of the four axis directions.

For a 16-fat polyomino the successor exists (`exists_nextVtx`), is unique
in both directions (`NextVtx.unique`, `NextVtx.pred_unique`) — so the
boundary decomposes into disjoint cycles — and edges are long
(`NextVtx.far`) and consecutive edges perpendicular (`NextVtx.perp`).
The statements assume `Fat 16`; some pinch-exclusion hypothesis is
unavoidable (at a diagonal vertex the boundary has degree 4 and "next
vertex" is not a function).
-/

open Set

-- ============================================================
-- §5 The boundary walk: straight runs and the successor vertex
-- ============================================================
--
-- The boundary of `P` is walked with the interior on the left.  A vertex
-- of a fat polyomino has exactly one outgoing arm in that orientation
-- (the quadrant picture decides which); following it to its first turn
-- yields the *successor* vertex.  This section proves existence and
-- uniqueness of the successor; the next sessions build the orbit
-- machinery (single boundary cycle via ray-crossing parity) and the
-- corridor rectangles on top of it.

/-- A straight horizontal piece of the boundary of `P` on the grid line
    at height `y`, columns `[x0, x1)`, with the **interior above**;
    walked eastward it has the interior on the left. -/
def HRunAbove (P : Set Cell) (y x0 x1 : ℤ) : Prop :=
  ∀ x, x0 ≤ x → x < x1 → (x, y) ∈ P ∧ (x, y - 1) ∉ P

/-- Interior below; walked westward it has the interior on the left. -/
def HRunBelow (P : Set Cell) (y x0 x1 : ℤ) : Prop :=
  ∀ x, x0 ≤ x → x < x1 → (x, y - 1) ∈ P ∧ (x, y) ∉ P

/-- A straight vertical piece of the boundary of `P` on the grid line at
    abscissa `x`, rows `[y0, y1)`, with the **interior to the west**;
    walked northward it has the interior on the left. -/
def VRunLeft (P : Set Cell) (x y0 y1 : ℤ) : Prop :=
  ∀ y, y0 ≤ y → y < y1 → (x - 1, y) ∈ P ∧ (x, y) ∉ P

/-- Interior to the east; walked southward it has the interior on the
    left. -/
def VRunRight (P : Set Cell) (x y0 y1 : ℤ) : Prop :=
  ∀ y, y0 ≤ y → y < y1 → (x, y) ∈ P ∧ (x - 1, y) ∉ P

/-- `w` is the **successor** of the vertex `u` on the boundary walk of
    `P` with the interior on the left: the straight boundary run leaving
    `u` in the walking direction ends at the vertex `w`.  The four
    disjuncts are the four walking directions E, W, N, S. -/
def NextVtx (P : Set Cell) (u w : Cell) : Prop :=
  IsVertex P u ∧ IsVertex P w ∧
    ((u.2 = w.2 ∧ u.1 < w.1 ∧ HRunAbove P u.2 u.1 w.1) ∨
     (u.2 = w.2 ∧ w.1 < u.1 ∧ HRunBelow P u.2 w.1 u.1) ∨
     (u.1 = w.1 ∧ u.2 < w.2 ∧ VRunLeft P u.1 u.2 w.2) ∨
     (u.1 = w.1 ∧ w.2 < u.2 ∧ VRunRight P u.1 w.2 u.2))


-- No interior point of a straight run is a vertex: the 2×2 pattern there
-- is row- (resp. column-) constant.

lemma hrunAbove_not_vertex {P : Set Cell} {y x0 x1 : ℤ}
    (h : HRunAbove P y x0 x1) :
    ∀ x, x0 < x → x < x1 → ¬IsVertex P (x, y) := by
  intro x h1 h2 hv
  have ha := h (x - 1) (by omega) (by omega)
  have hb := h x (by omega) h2
  exact hv.1 ⟨iff_of_false ha.2 hb.2, iff_of_true ha.1 hb.1⟩

lemma hrunBelow_not_vertex {P : Set Cell} {y x0 x1 : ℤ}
    (h : HRunBelow P y x0 x1) :
    ∀ x, x0 < x → x < x1 → ¬IsVertex P (x, y) := by
  intro x h1 h2 hv
  have ha := h (x - 1) (by omega) (by omega)
  have hb := h x (by omega) h2
  exact hv.1 ⟨iff_of_true ha.1 hb.1, iff_of_false ha.2 hb.2⟩

lemma vrunLeft_not_vertex {P : Set Cell} {x y0 y1 : ℤ}
    (h : VRunLeft P x y0 y1) :
    ∀ y, y0 < y → y < y1 → ¬IsVertex P (x, y) := by
  intro y h1 h2 hv
  have ha := h (y - 1) (by omega) (by omega)
  have hb := h y (by omega) h2
  exact hv.2 ⟨iff_of_true ha.1 hb.1, iff_of_false ha.2 hb.2⟩

lemma vrunRight_not_vertex {P : Set Cell} {x y0 y1 : ℤ}
    (h : VRunRight P x y0 y1) :
    ∀ y, y0 < y → y < y1 → ¬IsVertex P (x, y) := by
  intro y h1 h2 hv
  have ha := h (y - 1) (by omega) (by omega)
  have hb := h y (by omega) h2
  exact hv.2 ⟨iff_of_false ha.2 hb.2, iff_of_true ha.1 hb.1⟩

-- The four walk lemmas: a straight run that starts (for ≥ 16 steps)
-- continues to its first turn, which is a vertex.

lemma walk_east {P : Set Cell} (hfin : P.Finite) {y x0 : ℤ}
    (hcell : (x0, y) ∈ P ∧ (x0, y - 1) ∉ P) :
    ∃ x1, x0 < x1 ∧ HRunAbove P y x0 x1 ∧ IsVertex P (x1, y) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.fst).bddAbove
  have hbound : ∀ p ∈ P, p.1 ≤ B := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ x, x0 ≤ x ∧ ¬((x, y) ∈ P ∧ (x, y - 1) ∉ P) := by
    refine ⟨max x0 (B + 1), le_max_left _ _, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : max x0 (B + 1) ≤ B := hbound _ hmem
    have := le_max_right x0 (B + 1)
    omega
  obtain ⟨x1, ⟨hx1ge, hx1fail⟩, hleast⟩ :=
    Int.exists_least_of_bdd
      (P := fun x => x0 ≤ x ∧ ¬((x, y) ∈ P ∧ (x, y - 1) ∉ P))
      ⟨x0, fun _ hz => hz.1⟩ hinh
  have hrun' : HRunAbove P y x0 x1 := by
    intro x h1 h2
    by_contra hx
    exact absurd (hleast x ⟨h1, hx⟩) (by omega)
  have hgt : x0 < x1 := by
    rcases eq_or_lt_of_le hx1ge with heq | h
    · exact absurd (heq ▸ hcell) hx1fail
    · exact h
  have hprev := hrun' (x1 - 1) (by omega) (by omega)
  refine ⟨x1, hgt, hrun', ?_, ?_⟩
  · exact fun ⟨h1, h2⟩ =>
      hx1fail ⟨h2.mp hprev.1, fun hSE => hprev.2 (h1.mpr hSE)⟩
  · exact fun ⟨h1, _⟩ => hprev.2 (h1.mpr hprev.1)

lemma walk_west {P : Set Cell} (hfin : P.Finite) {y x0 : ℤ}
    (hcell : (x0 - 1, y - 1) ∈ P ∧ (x0 - 1, y) ∉ P) :
    ∃ x1, x1 < x0 ∧ HRunBelow P y x1 x0 ∧ IsVertex P (x1, y) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.fst).bddBelow
  have hbound : ∀ p ∈ P, B ≤ p.1 := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ x, x < x0 ∧ ¬((x, y - 1) ∈ P ∧ (x, y) ∉ P) := by
    refine ⟨min (x0 - 1) (B - 1),
      by have := min_le_left (x0 - 1) (B - 1); omega, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : B ≤ min (x0 - 1) (B - 1) := hbound _ hmem
    have := min_le_right (x0 - 1) (B - 1)
    omega
  obtain ⟨xf, ⟨hxflt, hxffail⟩, hgreatest⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun x => x < x0 ∧ ¬((x, y - 1) ∈ P ∧ (x, y) ∉ P))
      ⟨x0, fun _ hz => le_of_lt hz.1⟩ hinh
  have hrun' : HRunBelow P y (xf + 1) x0 := by
    intro x h1 h2
    by_contra hx
    exact absurd (hgreatest x ⟨h2, hx⟩) (by omega)
  have hlt : xf + 1 < x0 := by
    rcases eq_or_lt_of_le (show xf ≤ x0 - 1 by omega) with heq | h
    · subst heq
      exact absurd hcell hxffail
    · omega
  have hcur := hrun' (xf + 1) le_rfl (by omega)
  have hfail' : ¬((xf + 1 - 1, y - 1) ∈ P ∧ (xf + 1 - 1, y) ∉ P) := by
    rw [show xf + 1 - 1 = xf from by ring]
    exact hxffail
  refine ⟨xf + 1, hlt, hrun', ?_, ?_⟩
  · exact fun ⟨h1, h2⟩ =>
      hfail' ⟨h1.mpr hcur.1, fun hNW => hcur.2 (h2.mp hNW)⟩
  · exact fun ⟨_, h2⟩ => hcur.2 (h2.mp hcur.1)

lemma walk_north {P : Set Cell} (hfin : P.Finite) {x y0 : ℤ}
    (hcell : (x - 1, y0) ∈ P ∧ (x, y0) ∉ P) :
    ∃ y1, y0 < y1 ∧ VRunLeft P x y0 y1 ∧ IsVertex P (x, y1) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddAbove
  have hbound : ∀ p ∈ P, p.2 ≤ B := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ y, y0 ≤ y ∧ ¬((x - 1, y) ∈ P ∧ (x, y) ∉ P) := by
    refine ⟨max y0 (B + 1), le_max_left _ _, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : max y0 (B + 1) ≤ B := hbound _ hmem
    have := le_max_right y0 (B + 1)
    omega
  obtain ⟨y1, ⟨hy1ge, hy1fail⟩, hleast⟩ :=
    Int.exists_least_of_bdd
      (P := fun y => y0 ≤ y ∧ ¬((x - 1, y) ∈ P ∧ (x, y) ∉ P))
      ⟨y0, fun _ hz => hz.1⟩ hinh
  have hrun' : VRunLeft P x y0 y1 := by
    intro y h1 h2
    by_contra hy
    exact absurd (hleast y ⟨h1, hy⟩) (by omega)
  have hgt : y0 < y1 := by
    rcases eq_or_lt_of_le hy1ge with heq | h
    · exact absurd (heq ▸ hcell) hy1fail
    · exact h
  have hprev := hrun' (y1 - 1) (by omega) (by omega)
  refine ⟨y1, hgt, hrun', ?_, ?_⟩
  · exact fun ⟨h1, _⟩ => hprev.2 (h1.mp hprev.1)
  · exact fun ⟨h1, h2⟩ =>
      hy1fail ⟨h1.mp hprev.1, fun hNE => hprev.2 (h2.mpr hNE)⟩

lemma walk_south {P : Set Cell} (hfin : P.Finite) {x y0 : ℤ}
    (hcell : (x, y0 - 1) ∈ P ∧ (x - 1, y0 - 1) ∉ P) :
    ∃ y1, y1 < y0 ∧ VRunRight P x y1 y0 ∧ IsVertex P (x, y1) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddBelow
  have hbound : ∀ p ∈ P, B ≤ p.2 := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ y, y < y0 ∧ ¬((x, y) ∈ P ∧ (x - 1, y) ∉ P) := by
    refine ⟨min (y0 - 1) (B - 1),
      by have := min_le_left (y0 - 1) (B - 1); omega, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : B ≤ min (y0 - 1) (B - 1) := hbound _ hmem
    have := min_le_right (y0 - 1) (B - 1)
    omega
  obtain ⟨yf, ⟨hyflt, hyffail⟩, hgreatest⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun y => y < y0 ∧ ¬((x, y) ∈ P ∧ (x - 1, y) ∉ P))
      ⟨y0, fun _ hz => le_of_lt hz.1⟩ hinh
  have hrun' : VRunRight P x (yf + 1) y0 := by
    intro y h1 h2
    by_contra hy
    exact absurd (hgreatest y ⟨h2, hy⟩) (by omega)
  have hlt : yf + 1 < y0 := by
    rcases eq_or_lt_of_le (show yf ≤ y0 - 1 by omega) with heq | h
    · subst heq
      exact absurd hcell hyffail
    · omega
  have hcur := hrun' (yf + 1) le_rfl (by omega)
  have hfail' : ¬((x, yf + 1 - 1) ∈ P ∧ (x - 1, yf + 1 - 1) ∉ P) := by
    rw [show yf + 1 - 1 = yf from by ring]
    exact hyffail
  refine ⟨yf + 1, hlt, hrun', ?_, ?_⟩
  · exact fun ⟨_, h2⟩ => hcur.2 (h2.mpr hcur.1)
  · exact fun ⟨h1, h2⟩ =>
      hfail' ⟨h2.mpr hcur.1, fun hSW => hcur.2 (h1.mp hSW)⟩

-- The four *reverse-end* walk lemmas: the other end of each oriented run.

/-- The **west end** of a horizontal boundary run with the interior
    above. -/
lemma walk_west' {P : Set Cell} (hfin : P.Finite) {y x0 : ℤ}
    (hcell : (x0, y) ∈ P ∧ (x0, y - 1) ∉ P) :
    ∃ x1, x1 ≤ x0 ∧ HRunAbove P y x1 (x0 + 1) ∧ IsVertex P (x1, y) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.fst).bddBelow
  have hbound : ∀ p ∈ P, B ≤ p.1 := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ x, x < x0 ∧ ¬((x, y) ∈ P ∧ (x, y - 1) ∉ P) := by
    refine ⟨min (x0 - 1) (B - 1),
      by have := min_le_left (x0 - 1) (B - 1); omega, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : B ≤ min (x0 - 1) (B - 1) := hbound _ hmem
    have := min_le_right (x0 - 1) (B - 1)
    omega
  obtain ⟨xf, ⟨hxflt, hxffail⟩, hgreatest⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun x => x < x0 ∧ ¬((x, y) ∈ P ∧ (x, y - 1) ∉ P))
      ⟨x0, fun _ hz => le_of_lt hz.1⟩ hinh
  have hrun' : HRunAbove P y (xf + 1) (x0 + 1) := by
    intro x h1 h2
    by_contra hx
    rcases eq_or_lt_of_le (show x ≤ x0 by omega) with heq | hlt
    · subst heq
      exact hx hcell
    · exact absurd (hgreatest x ⟨hlt, hx⟩) (by omega)
  have hcur := hrun' (xf + 1) le_rfl (by omega)
  have hfail' : ¬((xf + 1 - 1, y) ∈ P ∧ (xf + 1 - 1, y - 1) ∉ P) := by
    rw [show xf + 1 - 1 = xf from by ring]
    exact hxffail
  refine ⟨xf + 1, by omega, hrun', ?_, ?_⟩
  · exact fun ⟨h1, h2⟩ =>
      hfail' ⟨h2.mpr hcur.1, fun hSW => hcur.2 (h1.mp hSW)⟩
  · exact fun ⟨_, h2⟩ => hcur.2 (h2.mpr hcur.1)

/-- The **east end** of a horizontal boundary run with the interior
    below. -/
lemma walk_east' {P : Set Cell} (hfin : P.Finite) {y x0 : ℤ}
    (hcell : (x0, y - 1) ∈ P ∧ (x0, y) ∉ P) :
    ∃ x1, x0 < x1 ∧ HRunBelow P y x0 x1 ∧ IsVertex P (x1, y) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.fst).bddAbove
  have hbound : ∀ p ∈ P, p.1 ≤ B := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ x, x0 ≤ x ∧ ¬((x, y - 1) ∈ P ∧ (x, y) ∉ P) := by
    refine ⟨max x0 (B + 1), le_max_left _ _, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : max x0 (B + 1) ≤ B := hbound _ hmem
    have := le_max_right x0 (B + 1)
    omega
  obtain ⟨x1, ⟨hx1ge, hx1fail⟩, hleast⟩ :=
    Int.exists_least_of_bdd
      (P := fun x => x0 ≤ x ∧ ¬((x, y - 1) ∈ P ∧ (x, y) ∉ P))
      ⟨x0, fun _ hz => hz.1⟩ hinh
  have hrun' : HRunBelow P y x0 x1 := by
    intro x h1 h2
    by_contra hx
    exact absurd (hleast x ⟨h1, hx⟩) (by omega)
  have hgt : x0 < x1 := by
    rcases eq_or_lt_of_le hx1ge with heq | h
    · exact absurd (heq ▸ hcell) hx1fail
    · exact h
  have hprev := hrun' (x1 - 1) (by omega) (by omega)
  refine ⟨x1, hgt, hrun', ?_, ?_⟩
  · exact fun ⟨h1, h2⟩ =>
      hx1fail ⟨h1.mp hprev.1, fun hNE => hprev.2 (h2.mpr hNE)⟩
  · exact fun ⟨h1, _⟩ => hprev.2 (h1.mp hprev.1)

/-- The **south end** of a vertical boundary run with the interior to the
    west. -/
lemma walk_south' {P : Set Cell} (hfin : P.Finite) {x y0 : ℤ}
    (hcell : (x - 1, y0) ∈ P ∧ (x, y0) ∉ P) :
    ∃ y1, y1 ≤ y0 ∧ VRunLeft P x y1 (y0 + 1) ∧ IsVertex P (x, y1) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddBelow
  have hbound : ∀ p ∈ P, B ≤ p.2 := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ y, y < y0 ∧ ¬((x - 1, y) ∈ P ∧ (x, y) ∉ P) := by
    refine ⟨min (y0 - 1) (B - 1),
      by have := min_le_left (y0 - 1) (B - 1); omega, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : B ≤ min (y0 - 1) (B - 1) := hbound _ hmem
    have := min_le_right (y0 - 1) (B - 1)
    omega
  obtain ⟨yf, ⟨hyflt, hyffail⟩, hgreatest⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun y => y < y0 ∧ ¬((x - 1, y) ∈ P ∧ (x, y) ∉ P))
      ⟨y0, fun _ hz => le_of_lt hz.1⟩ hinh
  have hrun' : VRunLeft P x (yf + 1) (y0 + 1) := by
    intro y h1 h2
    by_contra hy
    rcases eq_or_lt_of_le (show y ≤ y0 by omega) with heq | hlt
    · subst heq
      exact hy hcell
    · exact absurd (hgreatest y ⟨hlt, hy⟩) (by omega)
  have hcur := hrun' (yf + 1) le_rfl (by omega)
  have hfail' : ¬((x - 1, yf + 1 - 1) ∈ P ∧ (x, yf + 1 - 1) ∉ P) := by
    rw [show yf + 1 - 1 = yf from by ring]
    exact hyffail
  refine ⟨yf + 1, by omega, hrun', ?_, ?_⟩
  · exact fun ⟨_, h2⟩ => hcur.2 (h2.mp hcur.1)
  · exact fun ⟨h1, h2⟩ =>
      hfail' ⟨h1.mpr hcur.1, fun hSE => hcur.2 (h2.mp hSE)⟩

/-- The **north end** of a vertical boundary run with the interior to the
    east. -/
lemma walk_north' {P : Set Cell} (hfin : P.Finite) {x y0 : ℤ}
    (hcell : (x, y0) ∈ P ∧ (x - 1, y0) ∉ P) :
    ∃ y1, y0 < y1 ∧ VRunRight P x y0 y1 ∧ IsVertex P (x, y1) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddAbove
  have hbound : ∀ p ∈ P, p.2 ≤ B := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ y, y0 ≤ y ∧ ¬((x, y) ∈ P ∧ (x - 1, y) ∉ P) := by
    refine ⟨max y0 (B + 1), le_max_left _ _, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : max y0 (B + 1) ≤ B := hbound _ hmem
    have := le_max_right y0 (B + 1)
    omega
  obtain ⟨y1, ⟨hy1ge, hy1fail⟩, hleast⟩ :=
    Int.exists_least_of_bdd
      (P := fun y => y0 ≤ y ∧ ¬((x, y) ∈ P ∧ (x - 1, y) ∉ P))
      ⟨y0, fun _ hz => hz.1⟩ hinh
  have hrun' : VRunRight P x y0 y1 := by
    intro y h1 h2
    by_contra hy
    exact absurd (hleast y ⟨h1, hy⟩) (by omega)
  have hgt : y0 < y1 := by
    rcases eq_or_lt_of_le hy1ge with heq | h
    · exact absurd (heq ▸ hcell) hy1fail
    · exact h
  have hprev := hrun' (y1 - 1) (by omega) (by omega)
  refine ⟨y1, hgt, hrun', ?_, ?_⟩
  · exact fun ⟨h1, _⟩ => hprev.2 (h1.mpr hprev.1)
  · exact fun ⟨h1, h2⟩ =>
      hy1fail ⟨h2.mp hprev.1, fun hNW => hprev.2 (h1.mpr hNW)⟩

/-- **Existence of the successor.**  Every vertex of a fat polyomino has a
    successor on the interior-on-the-left boundary walk: the quadrant
    picture provides the first cell of the outgoing arm, and the walk
    lemmas extend it to the first turn. -/
theorem exists_nextVtx {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u : Cell} (hu : IsVertex P u) : ∃ w, NextVtx P u w := by
  obtain ⟨a, b⟩ := u
  obtain ⟨c, hc | hc⟩ := hfat.mem_iff hu
  -- convex corners
  · cases c with
    | BL =>
      -- interior up-right: walk east along the bottom arm
      have hcell : ((a, b) : Cell) ∈ P ∧ ((a, b - 1) : Cell) ∉ P := by
        constructor
        · exact (hc (a, b) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          have h' := (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mp hmem
          simp only [quadrant, Set.mem_setOf_eq] at h'
          omega
      obtain ⟨x1, hgt, hrun', hvtx⟩ := walk_east hfin hcell
      exact ⟨(x1, b), hu, hvtx, Or.inl ⟨rfl, hgt, hrun'⟩⟩
    | BR =>
      -- interior up-left: walk north along the east arm
      have hcell : ((a - 1, b) : Cell) ∈ P ∧ ((a, b) : Cell) ∉ P := by
        constructor
        · exact (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          have h' := (hc (a, b) (by simp only [box, mem_rect]; omega)).mp hmem
          simp only [quadrant, Set.mem_setOf_eq] at h'
          omega
      obtain ⟨y1, hgt, hrun', hvtx⟩ := walk_north hfin hcell
      exact ⟨(a, y1), hu, hvtx, Or.inr (Or.inr (Or.inl ⟨rfl, hgt, hrun'⟩))⟩
    | TL =>
      -- interior down-right: walk south along the east arm
      have hcell : ((a, b - 1) : Cell) ∈ P ∧ ((a - 1, b - 1) : Cell) ∉ P := by
        constructor
        · exact (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          have h' := (hc (a - 1, b - 1)
            (by simp only [box, mem_rect]; omega)).mp hmem
          simp only [quadrant, Set.mem_setOf_eq] at h'
          omega
      obtain ⟨y1, hlt, hrun', hvtx⟩ := walk_south hfin hcell
      exact ⟨(a, y1), hu, hvtx, Or.inr (Or.inr (Or.inr ⟨rfl, hlt, hrun'⟩))⟩
    | TR =>
      -- interior down-left: walk west along the top arm
      have hcell : ((a - 1, b - 1) : Cell) ∈ P ∧ ((a - 1, b) : Cell) ∉ P := by
        constructor
        · exact (hc (a - 1, b - 1) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          have h' := (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mp hmem
          simp only [quadrant, Set.mem_setOf_eq] at h'
          omega
      obtain ⟨x1, hlt, hrun', hvtx⟩ := walk_west hfin hcell
      exact ⟨(x1, b), hu, hvtx, Or.inr (Or.inl ⟨rfl, hlt, hrun'⟩)⟩
  -- reflex corners
  · cases c with
    | BL =>
      -- hole up-right: walk north along the east arm
      have hcell : ((a - 1, b) : Cell) ∈ P ∧ ((a, b) : Cell) ∉ P := by
        constructor
        · exact (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          exact (hc (a, b) (by simp only [box, mem_rect]; omega)).mp hmem
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      obtain ⟨y1, hgt, hrun', hvtx⟩ := walk_north hfin hcell
      exact ⟨(a, y1), hu, hvtx, Or.inr (Or.inr (Or.inl ⟨rfl, hgt, hrun'⟩))⟩
    | BR =>
      -- hole up-left: walk west along the top arm
      have hcell : ((a - 1, b - 1) : Cell) ∈ P ∧ ((a - 1, b) : Cell) ∉ P := by
        constructor
        · exact (hc (a - 1, b - 1) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          exact (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mp hmem
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      obtain ⟨x1, hlt, hrun', hvtx⟩ := walk_west hfin hcell
      exact ⟨(x1, b), hu, hvtx, Or.inr (Or.inl ⟨rfl, hlt, hrun'⟩)⟩
    | TL =>
      -- hole down-right: walk east along the bottom arm
      have hcell : ((a, b) : Cell) ∈ P ∧ ((a, b - 1) : Cell) ∉ P := by
        constructor
        · exact (hc (a, b) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          exact (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mp hmem
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      obtain ⟨x1, hgt, hrun', hvtx⟩ := walk_east hfin hcell
      exact ⟨(x1, b), hu, hvtx, Or.inl ⟨rfl, hgt, hrun'⟩⟩
    | TR =>
      -- hole down-left: walk south along the east arm
      have hcell : ((a, b - 1) : Cell) ∈ P ∧ ((a - 1, b - 1) : Cell) ∉ P := by
        constructor
        · exact (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          exact (hc (a - 1, b - 1) (by simp only [box, mem_rect]; omega)).mp hmem
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      obtain ⟨y1, hlt, hrun', hvtx⟩ := walk_south hfin hcell
      exact ⟨(a, y1), hu, hvtx, Or.inr (Or.inr (Or.inr ⟨rfl, hlt, hrun'⟩))⟩

/-- **Uniqueness of the successor.**  Two outgoing arms in the same
    direction end at the same first turn; two different directions
    contradict each other on the first step or force the (excluded)
    diagonal pattern at `u`. -/
theorem NextVtx.unique {P : Set Cell} (hfat : Fat 16 P) {u w w' : Cell}
    (h : NextVtx P u w) (h' : NextVtx P u w') : w = w' := by
  obtain ⟨hu, hw, hcase⟩ := h
  obtain ⟨-, hw', hcase'⟩ := h'
  have hdiag := hfat.not_diagonal (by norm_num) hu
  rcases hcase with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ <;>
    rcases hcase' with ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩
  -- E, E
  · have hww : IsVertex P (w.1, u.2) := by
      rwa [show ((w.1, u.2) : Cell) = w from Prod.ext rfl e1]
    have hww' : IsVertex P (w'.1, u.2) := by
      rwa [show ((w'.1, u.2) : Cell) = w' from Prod.ext rfl f1]
    rcases lt_trichotomy w.1 w'.1 with hlt | heq | hgt
    · exact absurd hww (hrunAbove_not_vertex hr' w.1 e2 hlt)
    · exact Prod.ext heq (e1.symm.trans f1)
    · exact absurd hww' (hrunAbove_not_vertex hr w'.1 f2 hgt)
  -- E, W: diagonal at u
  · have hE := hr u.1 le_rfl e2
    have hW := hr' (u.1 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_true hW.1 hE.1, iff_of_false hW.2 hE.2⟩ hdiag
  -- E, N: first cells clash
  · exact absurd (hr u.1 le_rfl e2).1 (hr' u.2 le_rfl f2).2
  -- E, S
  · exact absurd (hr' (u.2 - 1) (by omega) (by omega)).1 (hr u.1 le_rfl e2).2
  -- W, E: diagonal at u
  · have hE := hr' u.1 le_rfl f2
    have hW := hr (u.1 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_true hW.1 hE.1, iff_of_false hW.2 hE.2⟩ hdiag
  -- W, W
  · have hww : IsVertex P (w.1, u.2) := by
      rwa [show ((w.1, u.2) : Cell) = w from Prod.ext rfl e1]
    have hww' : IsVertex P (w'.1, u.2) := by
      rwa [show ((w'.1, u.2) : Cell) = w' from Prod.ext rfl f1]
    rcases lt_trichotomy w.1 w'.1 with hlt | heq | hgt
    · exact absurd hww' (hrunBelow_not_vertex hr w'.1 hlt f2)
    · exact Prod.ext heq (e1.symm.trans f1)
    · exact absurd hww (hrunBelow_not_vertex hr' w.1 hgt e2)
  -- W, N
  · exact absurd (hr' u.2 le_rfl f2).1 (hr (u.1 - 1) (by omega) (by omega)).2
  -- W, S
  · exact absurd (hr (u.1 - 1) (by omega) (by omega)).1
      (hr' (u.2 - 1) (by omega) (by omega)).2
  -- N, E
  · exact absurd (hr' u.1 le_rfl f2).1 (hr u.2 le_rfl e2).2
  -- N, W
  · exact absurd (hr u.2 le_rfl e2).1 (hr' (u.1 - 1) (by omega) (by omega)).2
  -- N, N
  · have hww : IsVertex P (u.1, w.2) := by
      rwa [show ((u.1, w.2) : Cell) = w from Prod.ext e1 rfl]
    have hww' : IsVertex P (u.1, w'.2) := by
      rwa [show ((u.1, w'.2) : Cell) = w' from Prod.ext f1 rfl]
    rcases lt_trichotomy w.2 w'.2 with hlt | heq | hgt
    · exact absurd hww (vrunLeft_not_vertex hr' w.2 e2 hlt)
    · exact Prod.ext (e1.symm.trans f1) heq
    · exact absurd hww' (vrunLeft_not_vertex hr w'.2 f2 hgt)
  -- N, S: diagonal at u
  · have hN := hr u.2 le_rfl e2
    have hS := hr' (u.2 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_false hS.2 hN.2, iff_of_true hN.1 hS.1⟩ hdiag
  -- S, E
  · exact absurd (hr (u.2 - 1) (by omega) (by omega)).1 (hr' u.1 le_rfl f2).2
  -- S, W
  · exact absurd (hr' (u.1 - 1) (by omega) (by omega)).1
      (hr (u.2 - 1) (by omega) (by omega)).2
  -- S, N: diagonal at u
  · have hN := hr' u.2 le_rfl f2
    have hS := hr (u.2 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_false hS.2 hN.2, iff_of_true hN.1 hS.1⟩ hdiag
  -- S, S
  · have hww : IsVertex P (u.1, w.2) := by
      rwa [show ((u.1, w.2) : Cell) = w from Prod.ext e1 rfl]
    have hww' : IsVertex P (u.1, w'.2) := by
      rwa [show ((u.1, w'.2) : Cell) = w' from Prod.ext f1 rfl]
    rcases lt_trichotomy w.2 w'.2 with hlt | heq | hgt
    · exact absurd hww' (vrunRight_not_vertex hr w'.2 hlt f2)
    · exact Prod.ext (e1.symm.trans f1) heq
    · exact absurd hww (vrunRight_not_vertex hr' w.2 hgt e2)

/-- **Injectivity of the successor**: the incoming arm at a vertex is
    unique as well.  Mirror image of `NextVtx.unique`, with the last step
    of the run playing the role of the first. -/
theorem NextVtx.pred_unique {P : Set Cell} (hfat : Fat 16 P) {u u' w : Cell}
    (h : NextVtx P u w) (h' : NextVtx P u' w) : u = u' := by
  obtain ⟨hu, hw, hcase⟩ := h
  obtain ⟨hu', -, hcase'⟩ := h'
  have hdiagw := hfat.not_diagonal (by norm_num) hw
  rcases hcase with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ <;>
    rcases hcase' with ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ <;>
    [rw [e1] at hr; rw [e1] at hr; rw [e1] at hr; rw [e1] at hr;
     rw [e1] at hr; rw [e1] at hr; rw [e1] at hr; rw [e1] at hr;
     rw [e1] at hr; rw [e1] at hr; rw [e1] at hr; rw [e1] at hr;
     rw [e1] at hr; rw [e1] at hr; rw [e1] at hr; rw [e1] at hr] <;>
    [rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr';
     rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr';
     rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr';
     rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr']
  -- E, E
  · have hvu : IsVertex P (u.1, w.2) := by
      rwa [show ((u.1, w.2) : Cell) = u from Prod.ext rfl e1.symm]
    have hvu' : IsVertex P (u'.1, w.2) := by
      rwa [show ((u'.1, w.2) : Cell) = u' from Prod.ext rfl f1.symm]
    rcases lt_trichotomy u.1 u'.1 with hlt | heq | hgt
    · exact absurd hvu' (hrunAbove_not_vertex hr u'.1 hlt f2)
    · exact Prod.ext heq (e1.trans f1.symm)
    · exact absurd hvu (hrunAbove_not_vertex hr' u.1 hgt e2)
  -- E, W: diagonal at w
  · have hE := hr (w.1 - 1) (by omega) (by omega)
    have hW := hr' w.1 le_rfl f2
    exact absurd ⟨iff_of_false hE.2 hW.2, iff_of_true hE.1 hW.1⟩ hdiagw
  -- E, N
  · have hE := hr (w.1 - 1) (by omega) (by omega)
    have hN := hr' (w.2 - 1) (by omega) (by omega)
    exact absurd hN.1 hE.2
  -- E, S
  · have hE := hr (w.1 - 1) (by omega) (by omega)
    have hS := hr' w.2 le_rfl f2
    exact absurd hE.1 hS.2
  -- W, E: diagonal at w
  · have hW := hr w.1 le_rfl e2
    have hE := hr' (w.1 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_false hE.2 hW.2, iff_of_true hE.1 hW.1⟩ hdiagw
  -- W, W
  · have hvu : IsVertex P (u.1, w.2) := by
      rwa [show ((u.1, w.2) : Cell) = u from Prod.ext rfl e1.symm]
    have hvu' : IsVertex P (u'.1, w.2) := by
      rwa [show ((u'.1, w.2) : Cell) = u' from Prod.ext rfl f1.symm]
    rcases lt_trichotomy u.1 u'.1 with hlt | heq | hgt
    · exact absurd hvu (hrunBelow_not_vertex hr' u.1 e2 hlt)
    · exact Prod.ext heq (e1.trans f1.symm)
    · exact absurd hvu' (hrunBelow_not_vertex hr u'.1 f2 hgt)
  -- W, N
  · have hW := hr w.1 le_rfl e2
    have hN := hr' (w.2 - 1) (by omega) (by omega)
    exact absurd hW.1 hN.2
  -- W, S
  · have hW := hr w.1 le_rfl e2
    have hS := hr' w.2 le_rfl f2
    exact absurd hS.1 hW.2
  -- N, E
  · have hN := hr (w.2 - 1) (by omega) (by omega)
    have hE := hr' (w.1 - 1) (by omega) (by omega)
    exact absurd hN.1 hE.2
  -- N, W
  · have hN := hr (w.2 - 1) (by omega) (by omega)
    have hW := hr' w.1 le_rfl f2
    exact absurd hW.1 hN.2
  -- N, N
  · have hvu : IsVertex P (w.1, u.2) := by
      rwa [show ((w.1, u.2) : Cell) = u from Prod.ext e1.symm rfl]
    have hvu' : IsVertex P (w.1, u'.2) := by
      rwa [show ((w.1, u'.2) : Cell) = u' from Prod.ext f1.symm rfl]
    rcases lt_trichotomy u.2 u'.2 with hlt | heq | hgt
    · exact absurd hvu' (vrunLeft_not_vertex hr u'.2 hlt f2)
    · exact Prod.ext (e1.trans f1.symm) heq
    · exact absurd hvu (vrunLeft_not_vertex hr' u.2 hgt e2)
  -- N, S: diagonal at w
  · have hN := hr (w.2 - 1) (by omega) (by omega)
    have hS := hr' w.2 le_rfl f2
    exact absurd ⟨iff_of_true hN.1 hS.1, iff_of_false hS.2 hN.2⟩ hdiagw
  -- S, E
  · have hS := hr w.2 le_rfl e2
    have hE := hr' (w.1 - 1) (by omega) (by omega)
    exact absurd hE.1 hS.2
  -- S, W
  · have hS := hr w.2 le_rfl e2
    have hW := hr' w.1 le_rfl f2
    exact absurd hS.1 hW.2
  -- S, N: diagonal at w
  · have hS := hr w.2 le_rfl e2
    have hN := hr' (w.2 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_true hN.1 hS.1, iff_of_false hS.2 hN.2⟩ hdiagw
  -- S, S
  · have hvu : IsVertex P (w.1, u.2) := by
      rwa [show ((w.1, u.2) : Cell) = u from Prod.ext e1.symm rfl]
    have hvu' : IsVertex P (w.1, u'.2) := by
      rwa [show ((w.1, u'.2) : Cell) = u' from Prod.ext f1.symm rfl]
    rcases lt_trichotomy u.2 u'.2 with hlt | heq | hgt
    · exact absurd hvu (vrunRight_not_vertex hr' u.2 e2 hlt)
    · exact Prod.ext (e1.trans f1.symm) heq
    · exact absurd hvu' (vrunRight_not_vertex hr u'.2 f2 hgt)

/-- A finite polyomino has finitely many vertices: every vertex has one of
    its four incident cells in `P`. -/
lemma vertexSet_finite {P : Set Cell} (hfin : P.Finite) :
    {v : Cell | IsVertex P v}.Finite := by
  apply Set.Finite.subset
    (((hfin.union (hfin.image fun p => (p.1 + 1, p.2))).union
      (hfin.image fun p => (p.1, p.2 + 1))).union
      (hfin.image fun p => (p.1 + 1, p.2 + 1)))
  intro v hv
  by_cases hNE : (v.1, v.2) ∈ P
  · exact Or.inl (Or.inl (Or.inl (by rwa [show ((v.1, v.2) : Cell) = v from
      Prod.ext rfl rfl] at hNE)))
  by_cases hNW : (v.1 - 1, v.2) ∈ P
  · exact Or.inl (Or.inl (Or.inr ⟨_, hNW,
      Prod.ext (show v.1 - 1 + 1 = v.1 by ring) rfl⟩))
  by_cases hSE : (v.1, v.2 - 1) ∈ P
  · exact Or.inl (Or.inr ⟨_, hSE,
      Prod.ext rfl (show v.2 - 1 + 1 = v.2 by ring)⟩)
  by_cases hSW : (v.1 - 1, v.2 - 1) ∈ P
  · exact Or.inr ⟨_, hSW,
      Prod.ext (show v.1 - 1 + 1 = v.1 by ring)
        (show v.2 - 1 + 1 = v.2 by ring)⟩
  exact absurd ⟨iff_of_false hSW hSE, iff_of_false hNW hNE⟩ hv.1

/-- **Edges are long**: an edge of a 16-fat polyomino has length at least
    16 — a turn any earlier would put a vertex inside the box of `u`,
    where both cell columns (rows) beside the would-be turn lie on the
    same side of the quadrant and so carry identical membership. -/
theorem NextVtx.far {P : Set Cell} (hfat : Fat 16 P) {u w : Cell}
    (h : NextVtx P u w) :
    (u.2 = w.2 ∧ u.1 + 16 ≤ w.1 ∧ HRunAbove P u.2 u.1 w.1) ∨
    (u.2 = w.2 ∧ w.1 + 16 ≤ u.1 ∧ HRunBelow P u.2 w.1 u.1) ∨
    (u.1 = w.1 ∧ u.2 + 16 ≤ w.2 ∧ VRunLeft P u.1 u.2 w.2) ∨
    (u.1 = w.1 ∧ w.2 + 16 ≤ u.2 ∧ VRunRight P u.1 w.2 u.2) := by
  rcases h.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
  · refine Or.inl ⟨e1, ?_, hr⟩
    by_contra hlt
    push_neg at hlt
    obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h.1
    · have hQ : ∀ y' : ℤ,
          ((w.1 - 1, y') ∈ quadrant u c ↔ (w.1, y') ∈ quadrant u c) := by
        intro y'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).trans
          (hQ w.2)).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1, w.2 - 1) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ (w.2 - 1))).trans
          (hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.1 ⟨hr2, hr1⟩
    · have hQ : ∀ y' : ℤ,
          ((w.1 - 1, y') ∈ quadrant u c ↔ (w.1, y') ∈ quadrant u c) := by
        intro y'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ w.2))).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1, w.2 - 1) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ (w.2 - 1)))).trans
          (hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.1 ⟨hr2, hr1⟩
  · refine Or.inr (Or.inl ⟨e1, ?_, hr⟩)
    by_contra hlt
    push_neg at hlt
    obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h.1
    · have hQ : ∀ y' : ℤ,
          ((w.1 - 1, y') ∈ quadrant u c ↔ (w.1, y') ∈ quadrant u c) := by
        intro y'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).trans
          (hQ w.2)).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1, w.2 - 1) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ (w.2 - 1))).trans
          (hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.1 ⟨hr2, hr1⟩
    · have hQ : ∀ y' : ℤ,
          ((w.1 - 1, y') ∈ quadrant u c ↔ (w.1, y') ∈ quadrant u c) := by
        intro y'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ w.2))).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1, w.2 - 1) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ (w.2 - 1)))).trans
          (hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.1 ⟨hr2, hr1⟩
  · refine Or.inr (Or.inr (Or.inl ⟨e1, ?_, hr⟩))
    by_contra hlt
    push_neg at hlt
    obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h.1
    · have hQ : ∀ x' : ℤ,
          ((x', w.2 - 1) ∈ quadrant u c ↔ (x', w.2) ∈ quadrant u c) := by
        intro x'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1 - 1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ (w.1 - 1))).trans
          (hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1, w.2 - 1) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ w.1)).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.2 ⟨hr1, hr2⟩
    · have hQ : ∀ x' : ℤ,
          ((x', w.2 - 1) ∈ quadrant u c ↔ (x', w.2) ∈ quadrant u c) := by
        intro x'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1 - 1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ (w.1 - 1)))).trans
          (hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1, w.2 - 1) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ w.1))).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.2 ⟨hr1, hr2⟩
  · refine Or.inr (Or.inr (Or.inr ⟨e1, ?_, hr⟩))
    by_contra hlt
    push_neg at hlt
    obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h.1
    · have hQ : ∀ x' : ℤ,
          ((x', w.2 - 1) ∈ quadrant u c ↔ (x', w.2) ∈ quadrant u c) := by
        intro x'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1 - 1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ (w.1 - 1))).trans
          (hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1, w.2 - 1) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ w.1)).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.2 ⟨hr1, hr2⟩
    · have hQ : ∀ x' : ℤ,
          ((x', w.2 - 1) ∈ quadrant u c ↔ (x', w.2) ∈ quadrant u c) := by
        intro x'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1 - 1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ (w.1 - 1)))).trans
          (hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1, w.2 - 1) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ w.1))).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.2 ⟨hr1, hr2⟩

-- ------------------------------------------------------------
-- Boundary segments of `P`, as curve data for the parity toolkit
-- ------------------------------------------------------------


/-- **Consecutive edges are perpendicular**: the incoming and outgoing
    arms of a vertex never share an axis (same axis would make the 2×2
    pattern at the vertex row- or column-constant). -/
lemma NextVtx.perp {P : Set Cell} {p u w : Cell}
    (h1 : NextVtx P p u) (h2 : NextVtx P u w) :
    (p.2 = u.2 ∧ u.1 = w.1) ∨ (p.1 = u.1 ∧ u.2 = w.2) := by
  have hu := h2.1
  rcases h1.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ <;>
    rw [e1] at hr <;>
    rcases h2.2.2 with ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩
  -- in E
  · have ha := hr (u.1 - 1) (by omega) (by omega)
    have hb := hr' u.1 le_rfl f2
    exact absurd ⟨iff_of_false ha.2 hb.2, iff_of_true ha.1 hb.1⟩ hu.1
  · have ha := hr (u.1 - 1) (by omega) (by omega)
    have hb := hr' (u.1 - 1) (by omega) (by omega)
    exact absurd ha.1 hb.2
  · exact Or.inl ⟨e1, f1⟩
  · exact Or.inl ⟨e1, f1⟩
  -- in W
  · have ha := hr u.1 le_rfl e2
    have hb := hr' u.1 le_rfl f2
    exact absurd hb.1 ha.2
  · have ha := hr u.1 le_rfl e2
    have hb := hr' (u.1 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_true hb.1 ha.1, iff_of_false hb.2 ha.2⟩ hu.1
  · exact Or.inl ⟨e1, f1⟩
  · exact Or.inl ⟨e1, f1⟩
  -- in N
  · exact Or.inr ⟨e1, f1⟩
  · exact Or.inr ⟨e1, f1⟩
  · have ha := hr (u.2 - 1) (by omega) (by omega)
    have hb := hr' u.2 le_rfl f2
    exact absurd ⟨iff_of_true ha.1 hb.1, iff_of_false ha.2 hb.2⟩ hu.2
  · have ha := hr (u.2 - 1) (by omega) (by omega)
    have hb := hr' (u.2 - 1) (by omega) (by omega)
    exact absurd hb.1 ha.2
  -- in S
  · exact Or.inr ⟨e1, f1⟩
  · exact Or.inr ⟨e1, f1⟩
  · have ha := hr u.2 le_rfl e2
    have hb := hr' u.2 le_rfl f2
    exact absurd hb.1 ha.2
  · have ha := hr u.2 le_rfl e2
    have hb := hr' (u.2 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_false hb.2 ha.2, iff_of_true hb.1 ha.1⟩ hu.2

