import TilingPolyomino.TwoCornerDefects
import TilingPolyomino.Polyomino.Basic
import Mathlib.Tactic

/-!
# Vertex-on-grid polyominoes are L-tileable

A warm-up result on the way to the fat-polyomino theorem.  If every vertex of
a finite polyomino `P` lies on the **`3 × 2` grid** — that is, every vertex
`(x, y)` has `3 ∣ x` and `2 ∣ y` — then `P` is L-tileable.

The reason is elementary: such a `P` is exactly a union of complete `3 × 2`
grid cells (the coarse grid has no boundary of `P` running through the
interior of any cell), and each `3 × 2` rectangle is tiled by two L-trominoes.

## Proof outline

1. **Local constancy.**  If `3 ∤ x` then no point on the vertical line `x` is a
   vertex of `P` (a vertex there would force `3 ∣ x`).  Reading off the vertex
   definition, at each such point the membership pattern is either *row*- or
   *column*-constant; in **both** cases the predicate
   `(x−1, w) ∈ P ↔ (x, w) ∈ P` has the same truth value at `w` and at `w+1`.
   So it is constant in `w`, and for `w` beyond the (finite) support of `P` it
   is vacuously true — hence true everywhere (`gridAligned_hstep`).  The
   symmetric statement across a horizontal line `y` with `2 ∤ y` is
   `gridAligned_vstep`.
2. **Cell constancy.**  Chaining the single-line steps across the two interior
   lines of a grid column (resp. the one interior line of a grid row) shows
   membership only depends on the grid cell: `p ∈ P ↔ cornerOf p ∈ P`, where
   `cornerOf p` is the lower-left corner of the `3 × 2` cell containing `p`.
3. **Assembly.**  `P` is the disjoint union of the cells `gridCell c` over the
   finite set of occupied corners `C = cornerOf '' P`; each cell is a translate
   of `rect 0 0 3 2` and hence L-tileable, and a finite disjoint union of
   L-tileable sets is L-tileable.
-/

open Set

-- ============================================================
-- The hypothesis
-- ============================================================

/-- `P` has **all vertices on the `fx × fy` grid**: every vertex `(x, y)` of
    `P` satisfies `fx ∣ x` and `fy ∣ y`.  (`VertexAligned f` is the special
    case `fx = fy = f`.) -/
def VertexOnGrid (fx fy : ℤ) (P : Set Cell) : Prop :=
  ∀ v : Cell, IsVertex P v → fx ∣ v.1 ∧ fy ∣ v.2

-- ============================================================
-- §1 Local constancy across a single grid line
-- ============================================================

/-- Crossing a vertical line `x` with `3 ∤ x` never changes membership: the
    line is interior to a grid column, so no boundary of `P` runs along it. -/
private lemma gridAligned_hstep (P : Set Cell) (hfin : P.Finite)
    (hvert : VertexOnGrid 3 2 P) (x : ℤ) (hx : ¬ (3 : ℤ) ∣ x) :
    ∀ y : ℤ, ((x - 1, y) ∈ P ↔ (x, y) ∈ P) := by
  -- no point of the line `x` is a vertex (that would force `3 ∣ x`)
  have hnv : ∀ w : ℤ, ¬ IsVertex P (x, w) := fun w hv => hx (hvert (x, w) hv).1
  -- the predicate has the same value at `w` and `w+1`
  have hconst : ∀ w : ℤ,
      (((x - 1, w + 1) ∈ P ↔ (x, w + 1) ∈ P) ↔
        ((x - 1, w) ∈ P ↔ (x, w) ∈ P)) := by
    intro w
    have h := hnv (w + 1)
    simp only [IsVertex, add_sub_cancel_right] at h
    tauto
  -- a bound on the vertical extent of `P`
  obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddAbove
  have hbound : ∀ p ∈ P, p.2 ≤ B := fun p hp => hB ⟨p, hp, rfl⟩
  intro y
  -- constancy upward from `y`
  have hup : ∀ b : ℤ, y ≤ b →
      (((x - 1, y) ∈ P ↔ (x, y) ∈ P) ↔ ((x - 1, b) ∈ P ↔ (x, b) ∈ P)) := by
    intro b hb
    induction b, hb using Int.le_induction with
    | base => rfl
    | succ n _ ih => rw [ih]; exact (hconst n).symm
  -- beyond the support the predicate is vacuously true
  set w0 := max y (B + 1) with hw0def
  have h1 : (x - 1, w0) ∉ P := by
    intro hmem
    have hb2 : w0 ≤ B := hbound _ hmem
    have := le_max_right y (B + 1); omega
  have h2 : (x, w0) ∉ P := by
    intro hmem
    have hb2 : w0 ≤ B := hbound _ hmem
    have := le_max_right y (B + 1); omega
  exact (hup w0 (le_max_left _ _)).mpr (iff_of_false h1 h2)

/-- Crossing a horizontal line `y` with `2 ∤ y` never changes membership. -/
private lemma gridAligned_vstep (P : Set Cell) (hfin : P.Finite)
    (hvert : VertexOnGrid 3 2 P) (y : ℤ) (hy : ¬ (2 : ℤ) ∣ y) :
    ∀ x : ℤ, ((x, y - 1) ∈ P ↔ (x, y) ∈ P) := by
  have hnv : ∀ w : ℤ, ¬ IsVertex P (w, y) := fun w hv => hy (hvert (w, y) hv).2
  have hconst : ∀ w : ℤ,
      (((w + 1, y - 1) ∈ P ↔ (w + 1, y) ∈ P) ↔
        ((w, y - 1) ∈ P ↔ (w, y) ∈ P)) := by
    intro w
    have h := hnv (w + 1)
    simp only [IsVertex, add_sub_cancel_right] at h
    tauto
  obtain ⟨B, hB⟩ := (hfin.image Prod.fst).bddAbove
  have hbound : ∀ p ∈ P, p.1 ≤ B := fun p hp => hB ⟨p, hp, rfl⟩
  intro x
  have hup : ∀ b : ℤ, x ≤ b →
      (((x, y - 1) ∈ P ↔ (x, y) ∈ P) ↔ ((b, y - 1) ∈ P ↔ (b, y) ∈ P)) := by
    intro b hb
    induction b, hb using Int.le_induction with
    | base => rfl
    | succ n _ ih => rw [ih]; exact (hconst n).symm
  set w0 := max x (B + 1) with hw0def
  have h1 : (w0, y - 1) ∉ P := by
    intro hmem
    have hb2 : w0 ≤ B := hbound _ hmem
    have := le_max_right x (B + 1); omega
  have h2 : (w0, y) ∉ P := by
    intro hmem
    have hb2 : w0 ≤ B := hbound _ hmem
    have := le_max_right x (B + 1); omega
  exact (hup w0 (le_max_left _ _)).mpr (iff_of_false h1 h2)

-- ============================================================
-- §2 Membership depends only on the grid cell
-- ============================================================

/-- The lower-left corner of the `3 × 2` grid cell containing `p`. -/
def cornerOf (p : Cell) : Cell := (p.1 - p.1 % 3, p.2 - p.2 % 2)

/-- The `3 × 2` grid cell with lower-left corner `c`. -/
def gridCell (c : Cell) : Set Cell := rect c.1 c.2 (c.1 + 3) (c.2 + 2)

/-- Membership in `P` depends only on the grid cell of the point. -/
private lemma mem_iff_cornerOf (P : Set Cell) (hfin : P.Finite)
    (hvert : VertexOnGrid 3 2 P) (p : Cell) : p ∈ P ↔ cornerOf p ∈ P := by
  obtain ⟨a, b⟩ := p
  simp only [cornerOf]
  -- move `a` to `a - a % 3` across the (≤ 2) interior vertical lines
  have hcol : ∀ y : ℤ, ((a, y) ∈ P ↔ (a - a % 3, y) ∈ P) := by
    intro y
    have hr : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases hr with h | h | h
    · rw [h]; simp
    · have e1 := gridAligned_hstep P hfin hvert a (by omega) y
      have : a - a % 3 = a - 1 := by omega
      rw [this]; exact e1.symm
    · have e1 := gridAligned_hstep P hfin hvert a (by omega) y
      have e2 := gridAligned_hstep P hfin hvert (a - 1) (by omega) y
      have ea : a - 1 - 1 = a - a % 3 := by omega
      rw [ea] at e2
      exact e1.symm.trans e2.symm
  -- move `b` to `b - b % 2` across the (≤ 1) interior horizontal line
  have hrow : ∀ x : ℤ, ((x, b) ∈ P ↔ (x, b - b % 2) ∈ P) := by
    intro x
    have hr : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases hr with h | h
    · rw [h]; simp
    · have e1 := gridAligned_vstep P hfin hvert b (by omega) x
      have : b - b % 2 = b - 1 := by omega
      rw [this]; exact e1.symm
  exact (hcol b).trans (hrow (a - a % 3))

-- ============================================================
-- §3 Assembly: a finite disjoint union of tileable cells
-- ============================================================

/-- A finite disjoint union of L-tileable sets is L-tileable. -/
private lemma tileable_biUnion_finite {ι : Type*} {s : Set ι} (hs : s.Finite)
    (f : ι → Set Cell) (hf : ∀ i ∈ s, LTileable (f i))
    (hd : s.PairwiseDisjoint f) : LTileable (⋃ i ∈ s, f i) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simpa using Tileable.empty LProtoset
  | @insert a t ha _ ih =>
    rw [Set.biUnion_insert]
    have hLa : LTileable (f a) := hf a (Set.mem_insert _ _)
    have hLt : LTileable (⋃ i ∈ t, f i) :=
      ih (fun i hi => hf i (Set.mem_insert_of_mem _ hi))
        (hd.subset (Set.subset_insert _ _))
    refine Tileable.union hLa hLt ?_
    rw [Set.disjoint_iUnion₂_right]
    intro i hi
    exact hd (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hi)
      (by rintro rfl; exact ha hi)

/-- Each grid cell is a translate of `rect 0 0 3 2`, hence L-tileable. -/
private lemma LTileable_gridCell (c : Cell) : LTileable (gridCell c) := by
  have hbase : LTileable (rect 0 0 3 2) :=
    LTileable_rect_int 3 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have heq : gridCell c = translate c.1 c.2 (rect 0 0 3 2) := by
    ext ⟨x, y⟩
    simp only [gridCell, mem_rect, mem_translate]
    omega
  rw [heq]
  exact hbase.translate c.1 c.2

/-- A point lies in the grid cell of its own corner.  (Public: also used by
    `OffsetPolyomino.lean`.) -/
lemma mem_gridCell_cornerOf (p : Cell) : p ∈ gridCell (cornerOf p) := by
  obtain ⟨a, b⟩ := p
  simp only [gridCell, cornerOf, mem_rect]
  omega

/-- If `c` is a grid corner (`3 ∣ c.1`, `2 ∣ c.2`) then every point of
    `gridCell c` has corner `c`.  (Public: also used by
    `OffsetPolyomino.lean`.) -/
lemma cornerOf_of_mem_gridCell {c q : Cell} (h1 : 3 ∣ c.1) (h2 : 2 ∣ c.2)
    (hq : q ∈ gridCell c) : cornerOf q = c := by
  obtain ⟨cx, cy⟩ := c
  obtain ⟨x, y⟩ := q
  simp only [gridCell, mem_rect] at hq
  simp only [cornerOf, Prod.mk.injEq]
  omega

-- ============================================================
-- §4 The main theorem
-- ============================================================

/-- **A finite polyomino with all vertices on the `3 × 2` grid is
    L-tileable.**  Such a `P` is a disjoint union of `3 × 2` cells, each tiled
    by two L-trominoes. -/
theorem LTileable_of_vertexOnGrid3x2 (P : Set Cell) (hfin : P.Finite)
    (hvert : VertexOnGrid 3 2 P) : LTileable P := by
  set C : Set Cell := cornerOf '' P with hCdef
  have hCfin : C.Finite := hfin.image _
  -- corners are grid points
  have hCdvd : ∀ c ∈ C, 3 ∣ c.1 ∧ 2 ∣ c.2 := by
    rintro c ⟨p, _, rfl⟩
    simp only [cornerOf]; omega
  -- a corner of `C` lies in `P`
  have hCmem : ∀ c ∈ C, c ∈ P := by
    rintro c ⟨p, hp, rfl⟩
    exact (mem_iff_cornerOf P hfin hvert p).mp hp
  -- `P` is the union of its grid cells
  have hcover : P = ⋃ c ∈ C, gridCell c := by
    ext q
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hq
      exact ⟨cornerOf q, ⟨q, hq, rfl⟩, mem_gridCell_cornerOf q⟩
    · rintro ⟨c, hcC, hqc⟩
      obtain ⟨hd1, hd2⟩ := hCdvd c hcC
      have hcq : cornerOf q = c := cornerOf_of_mem_gridCell hd1 hd2 hqc
      rw [mem_iff_cornerOf P hfin hvert q, hcq]
      exact hCmem c hcC
  -- the cells are pairwise disjoint
  have hdisj : C.PairwiseDisjoint gridCell := by
    intro c hc c' hc' hne
    rw [Function.onFun, Set.disjoint_left]
    intro q hqc hqc'
    obtain ⟨hd1, hd2⟩ := hCdvd c hc
    obtain ⟨hd1', hd2'⟩ := hCdvd c' hc'
    apply hne
    rw [← cornerOf_of_mem_gridCell hd1 hd2 hqc,
      ← cornerOf_of_mem_gridCell hd1' hd2' hqc']
  rw [hcover]
  exact tileable_biUnion_finite hCfin gridCell
    (fun c _ => LTileable_gridCell c) hdisj
