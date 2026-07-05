import TilingPolyomino.TwoCornerDefects
import Mathlib.Tactic

/-!
# Fat polyominoes (Phase 1–3 skeleton — statements and `sorry`s)

Target theorem (informal, SL 2026-07-05): **every fat connected polyomino
whose area is a multiple of 3 is L-tileable**, where *fat* means every vertex
of the boundary is far (some fixed distance) from every other vertex and edge.

This file sets up the first, slightly weaker lemma on the way there
(`LTileable_of_vertexAligned`): instead of true fatness we assume every
vertex of the polyomino has both coordinates divisible by 20 (the polyomino
is *20-aligned*).  The bound 20 is provisional and generous — the
construction below needs pieces of side ≥ 6, and pitch-20 alignment yields
pieces of side ≥ 10.

## Proof sketch (SL)

1. **Vertical decomposition**: cut the polyomino along the vertical line
   through every vertical boundary edge, obtaining maximal rectangles;
   adjacent rectangles touch along **doors** (common sub-segments of their
   left/right edges).
2. Take a **spanning tree** of the dual graph (rectangles = nodes, doors =
   edges).
3. **Slice** every rectangle with doors on both sides in half vertically.
4. Carve a horizontal cut from the midpoint of each door to the vertical
   slice line (or the opposite edge), and between vertically consecutive
   doors on the same edge.  The resulting sub-rectangles, walked along an
   **Euler tour** of the tree, form a sequence visiting each sub-rectangle
   exactly once in which consecutive sub-rectangles share a corner point.
5. **Defect pushing**: walk the sequence; if the running area is not
   divisible by 3, leave a corner defect of size 1 or 2 at the shared corner
   and cover it with an L-tromino straddling into the next rectangle, where
   it creates the complementary defect of size 2 or 1.  Total area ≡ 0
   (mod 3) guarantees the last rectangle closes exactly.
6. **Tile each rectangle** with its ≤ 2 corner defects using the
   two-corner-defect theorem (`LTileable_rectMinusTwoCorners_of_area`) and
   the one- and zero-defect rectangle theorems.

## Formalization roadmap

* §1 Polyominoes: `CellAdj`, `CellConnected`, `IsVertex`, `VertexAligned`.
* §2 Main lemma statement: `LTileable_of_vertexAligned`.
* §3 Corner chains — the *output* of steps 1–4: `RectPiece`, `PushAdj`,
  `ChainLink`, `chainCells`, `IsCornerChain`.
* §4 The two halves of the proof:
  - `exists_cornerChain` (steps 1–4, the geometric decomposition — the one
    remaining `sorry`, to be broken into further lemmas in the next phase);
  - `exists_pushTromino` (step 5, one tromino push — proved: four core
    corner configurations with explicit trominoes, the rest by swapping
    the roles of the two pieces),
    `RectPiece.tileable_optDefects` (step 6, one piece — proved by
    translation to the origin from the rectangle and corner-defect
    theorems),
    `chainCells_tileable` (the induction along the chain — proved).
* §5 `LTileable_of_vertexAligned` from the two halves (proved, no `sorry`).
-/

open Set

-- ============================================================
-- §1 Polyominoes: adjacency, connectivity, vertices, alignment
-- ============================================================

/-- Two cells are **edge-adjacent**: they share a unit edge. -/
def CellAdj (p q : Cell) : Prop :=
  (p.1 = q.1 ∧ (q.2 = p.2 + 1 ∨ p.2 = q.2 + 1)) ∨
  (p.2 = q.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1))

lemma CellAdj.symm {p q : Cell} (h : CellAdj p q) : CellAdj q p := by
  unfold CellAdj at h ⊢
  omega

/-- A set of cells is **connected** if any two of its cells are joined by a
    path of edge-adjacent cells staying in the set.  (Named `CellConnected`
    to avoid Mathlib's topological `IsConnected`.) -/
def CellConnected (P : Set Cell) : Prop :=
  ∀ ⦃p⦄, p ∈ P → ∀ ⦃q⦄, q ∈ P →
    Relation.ReflTransGen (fun a b => b ∈ P ∧ CellAdj a b) p q

/-- The grid point `v = (x, y)` — the lattice point at the lower-left corner
    of cell `(x, y)` — is a **vertex** of `P` if the boundary of `P` turns
    at `v`.  The four cells incident to `v` are
    SW `(x−1, y−1)`, SE `(x, y−1)`, NW `(x−1, y)`, NE `(x, y)`;
    `v` is a vertex iff the 2×2 membership pattern around `v` is constant
    neither row-wise (which would make the local boundary horizontal or
    empty) nor column-wise (vertical or empty).  Equivalently: exactly 1 or
    3 of the four incident cells lie in `P`, or exactly 2 that are
    diagonally opposite. -/
def IsVertex (P : Set Cell) (v : Cell) : Prop :=
  ¬(((v.1 - 1, v.2 - 1) ∈ P ↔ (v.1, v.2 - 1) ∈ P) ∧
    ((v.1 - 1, v.2) ∈ P ↔ (v.1, v.2) ∈ P)) ∧
  ¬(((v.1 - 1, v.2 - 1) ∈ P ↔ (v.1 - 1, v.2) ∈ P) ∧
    ((v.1, v.2 - 1) ∈ P ↔ (v.1, v.2) ∈ P))

/-- Sanity check for `IsVertex`: the vertices of a (nondegenerate) rectangle
    are exactly its four corners. -/
example (x0 y0 x1 y1 : ℤ) (hx : x0 < x1) (hy : y0 < y1) (v : Cell) :
    IsVertex (rect x0 y0 x1 y1) v ↔
      v = (x0, y0) ∨ v = (x1, y0) ∨ v = (x0, y1) ∨ v = (x1, y1) := by
  obtain ⟨x, y⟩ := v
  simp only [IsVertex, mem_rect, Prod.mk.injEq]
  omega

/-- `P` is **`f`-aligned**: every vertex of `P` lies on the pitch-`f` grid
    `fℤ × fℤ`.  This is the provisional stand-in for fatness: it forces all
    boundary features of `P` to be at distance ≥ `f` from each other. -/
def VertexAligned (f : ℤ) (P : Set Cell) : Prop :=
  ∀ v : Cell, IsVertex P v → f ∣ v.1 ∧ f ∣ v.2

-- ============================================================
-- §3 Corner chains: the output of the geometric decomposition
-- ============================================================

-- Translation is compatible with the set operations (definitionally).
private lemma translate_union (dx dy : ℤ) (A B : Set Cell) :
    translate dx dy (A ∪ B) = translate dx dy A ∪ translate dx dy B := rfl

private lemma translate_diff (dx dy : ℤ) (A B : Set Cell) :
    translate dx dy (A \ B) = translate dx dy A \ translate dx dy B := rfl

/-- Any rectangle is the translate of an origin-anchored one. -/
private lemma rect_eq_translate_origin (x0 y0 x1 y1 : ℤ) :
    rect x0 y0 x1 y1 = translate x0 y0 (rect 0 0 (x1 - x0) (y1 - y0)) := by
  ext ⟨x, y⟩
  simp only [mem_rect, mem_translate]
  omega

/-- Size of an optional defect (`none` = no defect). -/
def optSize : Option DefectType → ℤ
  | none => 0
  | some d => d.size

@[simp] lemma optSize_none : optSize none = 0 := rfl
@[simp] lemma optSize_some (d : DefectType) : optSize (some d) = d.size := rfl

lemma optSize_nonneg (e : Option DefectType) : 0 ≤ optSize e := by
  cases e with
  | none => simp
  | some d => have := d.size_pos; simp; omega

lemma optSize_le_two (e : Option DefectType) : optSize e ≤ 2 := by
  cases e with
  | none => simp
  | some d => simpa using d.size_le_two

/-- An axis-aligned rectangular piece `[x0, x1) × [y0, y1)` of the
    decomposition, with both sides ≥ 6 — the bound required by the
    two-corner-defect theorem.  (The decomposition of a 20-aligned polyomino
    actually produces sides ≥ 10.) -/
structure RectPiece where
  x0 : ℤ
  y0 : ℤ
  x1 : ℤ
  y1 : ℤ
  wide : x0 + 6 ≤ x1
  tall : y0 + 6 ≤ y1

namespace RectPiece

/-- The cells of the piece. -/
def cells (R : RectPiece) : Set Cell := rect R.x0 R.y0 R.x1 R.y1

/-- The grid point at corner `c` of `R`. -/
def cornerPt (R : RectPiece) : Corner → Cell
  | .BL => (R.x0, R.y0)
  | .BR => (R.x1, R.y0)
  | .TL => (R.x0, R.y1)
  | .TR => (R.x1, R.y1)

/-- The cell of `R` sitting in its corner `c`. -/
def cornerCell (R : RectPiece) : Corner → Cell
  | .BL => (R.x0, R.y0)
  | .BR => (R.x1 - 1, R.y0)
  | .TL => (R.x0, R.y1 - 1)
  | .TR => (R.x1 - 1, R.y1 - 1)

/-- The cells of a defect of type `d` at corner `c` of `R` (the translate of
    `Corner.cells` from `TwoCornerDefects.lean`). -/
def defect (R : RectPiece) (c : Corner) (d : DefectType) : Set Cell :=
  translate R.x0 R.y0 (c.cells d (R.x1 - R.x0) (R.y1 - R.y0))

/-- Optional defect: `none` means no defect. -/
def optDefect (R : RectPiece) (c : Corner) : Option DefectType → Set Cell
  | none => ∅
  | some d => R.defect c d

@[simp] lemma optDefect_none (R : RectPiece) (c : Corner) :
    R.optDefect c none = ∅ := rfl

@[simp] lemma optDefect_some (R : RectPiece) (c : Corner) (d : DefectType) :
    R.optDefect c (some d) = R.defect c d := rfl

/-- A defect is contained in its piece. -/
lemma defect_subset (R : RectPiece) (c : Corner) (d : DefectType) :
    R.defect c d ⊆ R.cells := by
  have hw := R.wide
  have ht := R.tall
  rintro ⟨x, y⟩ h
  cases c <;> cases d <;>
    simp only [defect, Corner.cells, mem_translate, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq, cells, mem_rect] at h ⊢ <;>
    omega

lemma cells_finite (R : RectPiece) : R.cells.Finite := rect_finite _ _ _ _

lemma cells_eq_translate (R : RectPiece) :
    R.cells = translate R.x0 R.y0 (rect 0 0 (R.x1 - R.x0) (R.y1 - R.y0)) :=
  rect_eq_translate_origin _ _ _ _

lemma cells_ncard_int (R : RectPiece) :
    ((R.cells.ncard : ℕ) : ℤ) = (R.x1 - R.x0) * (R.y1 - R.y0) := by
  have hx : (0 : ℤ) ≤ R.x1 - R.x0 := by have := R.wide; omega
  have hy : (0 : ℤ) ≤ R.y1 - R.y0 := by have := R.tall; omega
  rw [cells, rect_ncard]
  push_cast
  rw [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy]

lemma defect_finite (R : RectPiece) (c : Corner) (d : DefectType) :
    (R.defect c d).Finite :=
  translate_finite _ _ _ (Corner.cells_finite c d _ _)

lemma defect_ncard (R : RectPiece) (c : Corner) (d : DefectType) :
    ((R.defect c d).ncard : ℤ) = d.size := by
  rw [defect, translate_ncard _ _ _ (Corner.cells_finite c d _ _)]
  exact Corner.cells_ncard c d _ _

/-- Defects at distinct corners of a piece are disjoint. -/
lemma defect_disjoint (R : RectPiece) {c c' : Corner} (hcc : c ≠ c')
    (d d' : DefectType) :
    Disjoint (R.defect c d) (R.defect c' d') := by
  have h := Corner.cells_disjoint (c1 := c) (c2 := c') d d'
    (R.x1 - R.x0) (R.y1 - R.y0)
    (by have := R.wide; omega) (by have := R.tall; omega) hcc
  rw [Set.disjoint_left] at h ⊢
  intro p hp hp'
  exact h (by simpa [defect] using hp) (by simpa [defect] using hp')

lemma optDefect_subset (R : RectPiece) (c : Corner) (e : Option DefectType) :
    R.optDefect c e ⊆ R.cells := by
  cases e with
  | none => simp
  | some d => exact R.defect_subset c d

lemma optDefect_finite (R : RectPiece) (c : Corner) (e : Option DefectType) :
    (R.optDefect c e).Finite := by
  cases e with
  | none => simp
  | some d => exact R.defect_finite c d

lemma optDefect_ncard (R : RectPiece) (c : Corner) (e : Option DefectType) :
    ((R.optDefect c e).ncard : ℤ) = optSize e := by
  cases e with
  | none => simp
  | some d => simpa using R.defect_ncard c d

/-- An optional defect and a defect at a different corner are disjoint. -/
lemma optDefect_disjoint_defect (R : RectPiece) {c c' : Corner} (hcc : c ≠ c')
    (e : Option DefectType) (d : DefectType) :
    Disjoint (R.optDefect c e) (R.defect c' d) := by
  cases e with
  | none => simp
  | some d' => exact R.defect_disjoint hcc d' d

end RectPiece

/-- Pieces `R` and `S` **meet at a pushing corner**: corner `c` of `R` and
    corner `c'` of `S` are the same grid point `v`, and the two corner cells
    are edge-adjacent.  So the pieces sit side by side (or stacked) at `v`,
    mirror images across their common boundary line — the edge-adjacency
    rules out the diagonal position, in which no L-tromino can straddle both
    pieces. -/
def PushAdj (R S : RectPiece) (c c' : Corner) : Prop :=
  R.cornerPt c = S.cornerPt c' ∧ CellAdj (R.cornerCell c) (S.cornerCell c')

lemma PushAdj.symm {R S : RectPiece} {c c' : Corner} (h : PushAdj R S c c') :
    PushAdj S R c' c :=
  ⟨h.1.symm, h.2.symm⟩

/-- One link of a corner chain: a piece together with the corners through
    which the Euler tour enters and leaves it.  For the first link `entry`
    is arbitrary (there is no inherited defect) and for the last link `exit`
    is arbitrary; both can always be chosen distinct from the meaningful
    corner, so `IsCornerChain` demands `entry ≠ exit` for every link. -/
structure ChainLink where
  piece : RectPiece
  entry : Corner
  exit : Corner

/-- Consecutive links meet at a pushing corner: the exit corner of `a` is
    the entry corner of `b`. -/
def LinkAdj (a b : ChainLink) : Prop :=
  PushAdj a.piece b.piece a.exit b.entry

/-- The union of the cells of the pieces of a list of links. -/
def chainCells (l : List ChainLink) : Set Cell :=
  ⋃ K ∈ l, K.piece.cells

@[simp] lemma chainCells_nil : chainCells [] = ∅ := by
  simp [chainCells]

@[simp] lemma chainCells_cons (L : ChainLink) (l : List ChainLink) :
    chainCells (L :: l) = L.piece.cells ∪ chainCells l := by
  simp [chainCells]

lemma chainCells_finite (l : List ChainLink) : (chainCells l).Finite := by
  induction l with
  | nil => simp
  | cons L t ih =>
    rw [chainCells_cons]
    exact L.piece.cells_finite.union ih

/-- A set disjoint from every piece of a chain is disjoint from its union. -/
lemma disjoint_chainCells {A : Set Cell} {l : List ChainLink}
    (h : ∀ K ∈ l, Disjoint A K.piece.cells) :
    Disjoint A (chainCells l) := by
  induction l with
  | nil => simp
  | cons M t ih =>
    rw [chainCells_cons]
    exact Set.disjoint_union_right.mpr
      ⟨h M (by simp), ih fun K hK => h K (by simp [hK])⟩

/-- `l` is a **corner chain** for `P`: a nonempty sequence of pairwise
    disjoint rectangular pieces covering exactly `P`, consecutive pieces
    meeting at pushing corners, and each piece entered and left through two
    *distinct* corners.  This is the interface between the geometric
    decomposition (steps 1–4 of the sketch) and the defect-pushing tiling
    argument (steps 5–6). -/
structure IsCornerChain (l : List ChainLink) (P : Set Cell) : Prop where
  nonempty : l ≠ []
  chain : l.IsChain LinkAdj
  disjoint : l.Pairwise fun a b => Disjoint a.piece.cells b.piece.cells
  covers : chainCells l = P
  entry_ne_exit : ∀ K ∈ l, K.entry ≠ K.exit

-- ============================================================
-- §4 The two halves of the proof
-- ============================================================

/-- **Decomposition lemma** (steps 1–4 of the sketch; the geometric half).
    Every nonempty finite connected 20-aligned polyomino admits a corner
    chain: vertical decomposition through the vertical edges, spanning tree
    of the dual graph, halving of two-door rectangles, horizontal cuts at
    door midpoints, Euler tour.  To be decomposed into further lemmas. -/
theorem exists_cornerChain (P : Set Cell) (hfin : P.Finite) (hne : P.Nonempty)
    (hconn : CellConnected P) (hal : VertexAligned 20 P) :
    ∃ l : List ChainLink, IsCornerChain l P := by
  sorry

/-- A single placed L-tromino is L-tileable. -/
private lemma LTileable_single (dx dy : ℤ) (r : Fin 4) :
    LTileable (translate dx dy (rotate r LShape_cells)) := by
  refine ⟨Fin 1, inferInstance, ⟨fun _ => ⟨(), (dx, dy), r⟩⟩, ?_, ?_⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · ext p
    constructor
    · intro hp
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
      exact hi
    · intro hp
      exact Set.mem_iUnion.mpr ⟨0, hp⟩

/-- Core pushing configuration BR–BL: `R` sits west of `S`, their bottom
    edges meeting at the shared corner `(R.x1, R.y0) = (S.x0, S.y0)`. -/
private lemma pushTromino_BR_BL (R S : RectPiece)
    (hx : S.x0 = R.x1) (hy : S.y0 = R.y0) (s : ℤ) (hs : s = 1 ∨ s = 2) :
    ∃ (d d' : DefectType) (T : Set Cell),
      d.size = s ∧ d'.size = 3 - s ∧ LTileable T ∧
      T ⊆ R.cells ∪ S.cells ∧
      T ∩ R.cells = R.defect .BR d ∧
      T ∩ S.cells = S.defect .BL d' := by
  have hw1 := R.wide
  have ht1 := R.tall
  have hw2 := S.wide
  have ht2 := S.tall
  rcases hs with rfl | rfl
  · -- export 1 cell: single defect in `R`, vertical domino in `S`
    refine ⟨.single, .vert, translate R.x1 R.y0 (rotate 1 LShape_cells),
      by simp, by norm_num, LTileable_single _ _ _, ?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ hT
      simp only [mem_translate, mem_rotate, inverseRot, rotateCell_3, LShape_cells,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hT
      simp only [Set.mem_union, RectPiece.cells, mem_rect]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_3,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_3,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
  · -- export 2 cells: vertical domino in `R`, single defect in `S`
    refine ⟨.vert, .single, translate (R.x1 - 1) R.y0 (rotate 0 LShape_cells),
      by simp, by norm_num, LTileable_single _ _ _, ?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ hT
      simp only [mem_translate, mem_rotate, inverseRot, rotateCell_0, LShape_cells,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hT
      simp only [Set.mem_union, RectPiece.cells, mem_rect]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_0,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_0,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega

/-- Core pushing configuration TR–TL: `R` sits west of `S`, their top edges
    meeting at the shared corner `(R.x1, R.y1) = (S.x0, S.y1)`. -/
private lemma pushTromino_TR_TL (R S : RectPiece)
    (hx : S.x0 = R.x1) (hy : S.y1 = R.y1) (s : ℤ) (hs : s = 1 ∨ s = 2) :
    ∃ (d d' : DefectType) (T : Set Cell),
      d.size = s ∧ d'.size = 3 - s ∧ LTileable T ∧
      T ⊆ R.cells ∪ S.cells ∧
      T ∩ R.cells = R.defect .TR d ∧
      T ∩ S.cells = S.defect .TL d' := by
  have hw1 := R.wide
  have ht1 := R.tall
  have hw2 := S.wide
  have ht2 := S.tall
  rcases hs with rfl | rfl
  · refine ⟨.single, .vert, translate R.x1 (R.y1 - 1) (rotate 2 LShape_cells),
      by simp, by norm_num, LTileable_single _ _ _, ?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ hT
      simp only [mem_translate, mem_rotate, inverseRot, rotateCell_2, LShape_cells,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hT
      simp only [Set.mem_union, RectPiece.cells, mem_rect]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_2,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_2,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
  · refine ⟨.vert, .single, translate (R.x1 - 1) (R.y1 - 1) (rotate 3 LShape_cells),
      by simp, by norm_num, LTileable_single _ _ _, ?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ hT
      simp only [mem_translate, mem_rotate, inverseRot, rotateCell_1, LShape_cells,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hT
      simp only [Set.mem_union, RectPiece.cells, mem_rect]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_1,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_1,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega

/-- Core pushing configuration TL–BL: `R` sits below `S`, their left edges
    meeting at the shared corner `(R.x0, R.y1) = (S.x0, S.y0)`. -/
private lemma pushTromino_TL_BL (R S : RectPiece)
    (hx : S.x0 = R.x0) (hy : S.y0 = R.y1) (s : ℤ) (hs : s = 1 ∨ s = 2) :
    ∃ (d d' : DefectType) (T : Set Cell),
      d.size = s ∧ d'.size = 3 - s ∧ LTileable T ∧
      T ⊆ R.cells ∪ S.cells ∧
      T ∩ R.cells = R.defect .TL d ∧
      T ∩ S.cells = S.defect .BL d' := by
  have hw1 := R.wide
  have ht1 := R.tall
  have hw2 := S.wide
  have ht2 := S.tall
  rcases hs with rfl | rfl
  · -- export 1 cell: single defect in `R`, horizontal domino in `S`
    refine ⟨.single, .horiz, translate R.x0 R.y1 (rotate 3 LShape_cells),
      by simp, by norm_num, LTileable_single _ _ _, ?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ hT
      simp only [mem_translate, mem_rotate, inverseRot, rotateCell_1, LShape_cells,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hT
      simp only [Set.mem_union, RectPiece.cells, mem_rect]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_1,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_1,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
  · -- export 2 cells: horizontal domino in `R`, single defect in `S`
    refine ⟨.horiz, .single, translate R.x0 (R.y1 - 1) (rotate 0 LShape_cells),
      by simp, by norm_num, LTileable_single _ _ _, ?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ hT
      simp only [mem_translate, mem_rotate, inverseRot, rotateCell_0, LShape_cells,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hT
      simp only [Set.mem_union, RectPiece.cells, mem_rect]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_0,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_0,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega

/-- Core pushing configuration TR–BR: `R` sits below `S`, their right edges
    meeting at the shared corner `(R.x1, R.y1) = (S.x1, S.y0)`. -/
private lemma pushTromino_TR_BR (R S : RectPiece)
    (hx : S.x1 = R.x1) (hy : S.y0 = R.y1) (s : ℤ) (hs : s = 1 ∨ s = 2) :
    ∃ (d d' : DefectType) (T : Set Cell),
      d.size = s ∧ d'.size = 3 - s ∧ LTileable T ∧
      T ⊆ R.cells ∪ S.cells ∧
      T ∩ R.cells = R.defect .TR d ∧
      T ∩ S.cells = S.defect .BR d' := by
  have hw1 := R.wide
  have ht1 := R.tall
  have hw2 := S.wide
  have ht2 := S.tall
  rcases hs with rfl | rfl
  · refine ⟨.single, .horiz, translate (R.x1 - 1) R.y1 (rotate 2 LShape_cells),
      by simp, by norm_num, LTileable_single _ _ _, ?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ hT
      simp only [mem_translate, mem_rotate, inverseRot, rotateCell_2, LShape_cells,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hT
      simp only [Set.mem_union, RectPiece.cells, mem_rect]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_2,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_2,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
  · refine ⟨.horiz, .single, translate (R.x1 - 1) (R.y1 - 1) (rotate 1 LShape_cells),
      by simp, by norm_num, LTileable_single _ _ _, ?_, ?_, ?_⟩
    · rintro ⟨x, y⟩ hT
      simp only [mem_translate, mem_rotate, inverseRot, rotateCell_3, LShape_cells,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hT
      simp only [Set.mem_union, RectPiece.cells, mem_rect]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_3,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    · ext ⟨x, y⟩
      simp only [Set.mem_inter_iff, mem_translate, mem_rotate, inverseRot, rotateCell_3,
        LShape_cells, RectPiece.cells, RectPiece.defect, Corner.cells, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega

/-- **Defect pushing** (step 5 of the sketch, one step).  If `R` and `S`
    meet at a pushing corner and a defect of total size `s ∈ {1, 2}` must be
    exported from `R`, there are defect types `d` at `R`'s corner and `d'`
    at `S`'s corner, of sizes `s` and `3 − s`, and a single L-tromino `T`
    (stated here as `LTileable T`) straddling the common boundary with
    `T ∩ R = ` the `d`-defect and `T ∩ S = ` the `d'`-defect.

    Note the *types* `d`, `d'` are produced, not chosen: which domino
    orientation can straddle the boundary depends on the orientation of the
    shared corner. -/
theorem exists_pushTromino (R S : RectPiece) (c c' : Corner)
    (hadj : PushAdj R S c c') (s : ℤ) (hs : s = 1 ∨ s = 2) :
    ∃ (d d' : DefectType) (T : Set Cell),
      d.size = s ∧ d'.size = 3 - s ∧ LTileable T ∧
      T ⊆ R.cells ∪ S.cells ∧
      T ∩ R.cells = R.defect c d ∧
      T ∩ S.cells = S.defect c' d' := by
  obtain ⟨hpt, hcell⟩ := hadj
  -- The 8 impossible corner pairs (equal or diagonally opposite corner
  -- cells) die by `omega`; the 8 possible ones are the four core
  -- configurations, half of them after swapping the roles of `R` and `S`
  -- (which exchanges `d ↔ d'` and `s ↔ 3 − s`).
  cases c <;> cases c' <;>
    simp only [RectPiece.cornerPt, RectPiece.cornerCell, CellAdj,
      Prod.mk.injEq] at hpt hcell
  -- (BL, BL)
  · exfalso; omega
  -- (BL, BR): mirror of BR–BL
  · obtain ⟨d, d', T, hd, hd', hT, hsub, hTS, hTR⟩ :=
      pushTromino_BR_BL S R hpt.1 hpt.2 (3 - s) (by omega)
    exact ⟨d', d, T, by omega, by omega, hT, by rwa [Set.union_comm], hTR, hTS⟩
  -- (BL, TL): mirror of TL–BL
  · obtain ⟨d, d', T, hd, hd', hT, hsub, hTS, hTR⟩ :=
      pushTromino_TL_BL S R hpt.1 hpt.2 (3 - s) (by omega)
    exact ⟨d', d, T, by omega, by omega, hT, by rwa [Set.union_comm], hTR, hTS⟩
  -- (BL, TR)
  · exfalso; omega
  -- (BR, BL): core
  · exact pushTromino_BR_BL R S hpt.1.symm hpt.2.symm s hs
  -- (BR, BR)
  · exfalso; omega
  -- (BR, TL)
  · exfalso; omega
  -- (BR, TR): mirror of TR–BR
  · obtain ⟨d, d', T, hd, hd', hT, hsub, hTS, hTR⟩ :=
      pushTromino_TR_BR S R hpt.1 hpt.2 (3 - s) (by omega)
    exact ⟨d', d, T, by omega, by omega, hT, by rwa [Set.union_comm], hTR, hTS⟩
  -- (TL, BL): core
  · exact pushTromino_TL_BL R S hpt.1.symm hpt.2.symm s hs
  -- (TL, BR)
  · exfalso; omega
  -- (TL, TL)
  · exfalso; omega
  -- (TL, TR): mirror of TR–TL
  · obtain ⟨d, d', T, hd, hd', hT, hsub, hTS, hTR⟩ :=
      pushTromino_TR_TL S R hpt.1 hpt.2 (3 - s) (by omega)
    exact ⟨d', d, T, by omega, by omega, hT, by rwa [Set.union_comm], hTR, hTS⟩
  -- (TR, BL)
  · exfalso; omega
  -- (TR, BR): core
  · exact pushTromino_TR_BR R S hpt.1.symm hpt.2.symm s hs
  -- (TR, TL): core
  · exact pushTromino_TR_TL R S hpt.1.symm hpt.2.symm s hs
  -- (TR, TR)
  · exfalso; omega

/-- No defect: the piece itself, via `LTileable_rect_int`. -/
private lemma tileable_noDefect (R : RectPiece)
    (harea : 3 ∣ R.cells.ncard) : LTileable R.cells := by
  have hn : (6 : ℤ) ≤ R.x1 - R.x0 := by have := R.wide; omega
  have hm : (6 : ℤ) ≤ R.y1 - R.y0 := by have := R.tall; omega
  have h2 : (3 : ℤ) ∣ (R.cells.ncard : ℤ) := by exact_mod_cast harea
  rw [R.cells_ncard_int] at h2
  rw [R.cells_eq_translate]
  exact Tileable.translate
    (LTileable_rect_int _ _ (by omega) (by omega)
      (Int.emod_eq_zero_of_dvd h2) (by omega) (by omega)) R.x0 R.y0

/-- One defect: translate to the origin and use `LTileable_oneCorner_piece`. -/
private lemma tileable_oneDefect (R : RectPiece) (c : Corner) (d : DefectType)
    (harea : 3 ∣ (R.cells \ R.defect c d).ncard) :
    LTileable (R.cells \ R.defect c d) := by
  have hn : (6 : ℤ) ≤ R.x1 - R.x0 := by have := R.wide; omega
  have hm : (6 : ℤ) ≤ R.y1 - R.y0 := by have := R.tall; omega
  have heq : R.cells \ R.defect c d =
      translate R.x0 R.y0
        (rectMinusOneCorner (R.x1 - R.x0) (R.y1 - R.y0) c d) := by
    rw [R.cells_eq_translate, RectPiece.defect, ← translate_diff]
    rfl
  rw [heq] at harea ⊢
  have hfin : (rectMinusOneCorner (R.x1 - R.x0) (R.y1 - R.y0) c d).Finite :=
    (rect_finite _ _ _ _).diff
  rw [translate_ncard _ _ _ hfin] at harea
  refine Tileable.translate
    (LTileable_oneCorner_piece _ _ c d (by omega) (by omega)
      (Or.inl (by omega)) ?_) R.x0 R.y0
  -- area arithmetic: `3 ∣ ncard` ⇒ `(n·m − size) % 3 = 0`
  have hncd : (rectMinusOneCorner (R.x1 - R.x0) (R.y1 - R.y0) c d).ncard
      = (rect 0 0 (R.x1 - R.x0) (R.y1 - R.y0)).ncard
        - (Corner.cells c d (R.x1 - R.x0) (R.y1 - R.y0)).ncard := by
    rw [rectMinusOneCorner]
    exact Set.ncard_diff
      (Corner.cells_subset_rect c d _ _ (by omega) (by omega))
      (Corner.cells_finite c d _ _)
  have h1 : (((rect 0 0 (R.x1 - R.x0) (R.y1 - R.y0)).ncard : ℕ) : ℤ)
      = (R.x1 - R.x0) * (R.y1 - R.y0) := by
    rw [rect_ncard]
    push_cast
    rw [sub_zero, sub_zero, Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ R.x1 - R.x0),
      Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ R.y1 - R.y0)]
  have h2 := Corner.cells_ncard c d (R.x1 - R.x0) (R.y1 - R.y0)
  have h3 := d.size_pos
  have h4 := d.size_le_two
  have h36 : (36 : ℤ) ≤ (R.x1 - R.x0) * (R.y1 - R.y0) :=
    calc (36 : ℤ) = 6 * 6 := by norm_num
    _ ≤ _ := mul_le_mul hn hm (by norm_num) (by omega)
  generalize hA : (R.x1 - R.x0) * (R.y1 - R.y0) = A at h1 h36 ⊢
  omega

/-- Two defects at distinct corners: translate to the origin and use
    `LTileable_rectMinusTwoCorners_of_area`. -/
private lemma tileable_twoDefects (R : RectPiece) {c c' : Corner}
    (hcc : c ≠ c') (d d' : DefectType)
    (harea : 3 ∣ (R.cells \ (R.defect c d ∪ R.defect c' d')).ncard) :
    LTileable (R.cells \ (R.defect c d ∪ R.defect c' d')) := by
  have hn : (6 : ℤ) ≤ R.x1 - R.x0 := by have := R.wide; omega
  have hm : (6 : ℤ) ≤ R.y1 - R.y0 := by have := R.tall; omega
  have heq : R.cells \ (R.defect c d ∪ R.defect c' d') =
      translate R.x0 R.y0
        (rectMinusTwoCorners (R.x1 - R.x0) (R.y1 - R.y0) c c' d d') := by
    rw [R.cells_eq_translate, RectPiece.defect, RectPiece.defect,
      ← translate_union, ← translate_diff]
    rfl
  rw [heq] at harea ⊢
  rw [translate_ncard _ _ _ (rectMinusTwoCorners_finite _ _ _ _ _ _)] at harea
  refine Tileable.translate
    (LTileable_rectMinusTwoCorners_of_area _ _ c c' d d' hn hm hcc ?_)
    R.x0 R.y0
  have hcard := rectMinusTwoCorners_ncard (R.x1 - R.x0) (R.y1 - R.y0) c c' d d'
    (by omega) (by omega) hcc
  have h3 := d.size_pos
  have h4 := d.size_le_two
  have h5 := d'.size_pos
  have h6 := d'.size_le_two
  generalize hA : (R.x1 - R.x0) * (R.y1 - R.y0) = A at hcard ⊢
  omega

/-- **Tiling one piece** (step 6 of the sketch).  A piece minus optional
    corner defects at two distinct corners is L-tileable as soon as the
    remaining area is divisible by 3.  Wrapper (by translation to the
    origin) around `LTileable_rect_int`, the one-corner theorems and
    `LTileable_rectMinusTwoCorners_of_area`; the piece's sides are ≥ 6, so
    all their hypotheses hold. -/
theorem RectPiece.tileable_optDefects (R : RectPiece) (c c' : Corner)
    (hcc : c ≠ c') (e e' : Option DefectType)
    (harea : 3 ∣ (R.cells \ (R.optDefect c e ∪ R.optDefect c' e')).ncard) :
    LTileable (R.cells \ (R.optDefect c e ∪ R.optDefect c' e')) := by
  match e, e' with
  | none, none => simpa using tileable_noDefect R (by simpa using harea)
  | some d, none => simpa using tileable_oneDefect R c d (by simpa using harea)
  | none, some d' => simpa using tileable_oneDefect R c' d' (by simpa using harea)
  | some d, some d' => exact tileable_twoDefects R hcc d d' harea

/-- **Chain tiling** (steps 5–6, the induction along the chain).  The union
    of a corner chain minus an inherited optional defect at the entry corner
    of its first piece is L-tileable when the remaining area is divisible
    by 3.

    Induction on `rest`: compute the size `s` of the defect the head piece
    must export; if `s = 0` tile the head by `tileable_optDefects` and
    recurse defect-free, otherwise obtain the straddling tromino from
    `exists_pushTromino`, tile the head minus both defects, and recurse on
    `rest` with the inherited defect `d'`. -/
theorem chainCells_tileable (L : ChainLink) (rest : List ChainLink)
    (hchain : (L :: rest).IsChain LinkAdj)
    (hdisj : (L :: rest).Pairwise fun a b => Disjoint a.piece.cells b.piece.cells)
    (hcc : ∀ K ∈ L :: rest, K.entry ≠ K.exit)
    (e : Option DefectType)
    (harea : 3 ∣ (chainCells (L :: rest) \ L.piece.optDefect L.entry e).ncard) :
    LTileable (chainCells (L :: rest) \ L.piece.optDefect L.entry e) := by
  revert L e
  induction rest with
  | nil =>
    intro L hchain hdisj hcc e harea
    have harea' : 3 ∣ (L.piece.cells \
        (L.piece.optDefect L.entry e ∪ L.piece.optDefect L.exit none)).ncard := by
      simpa using harea
    simpa using RectPiece.tileable_optDefects L.piece L.entry L.exit
      (hcc L (by simp)) e none harea'
  | cons M rest' ih =>
    intro L hchain hdisj hcc e harea
    obtain ⟨hadj, hchain'⟩ := List.isChain_cons_cons.mp hchain
    obtain ⟨hLdisj, hdisj'⟩ := List.pairwise_cons.mp hdisj
    have hccL : L.entry ≠ L.exit := hcc L (by simp)
    have hcc' : ∀ K ∈ M :: rest', K.entry ≠ K.exit :=
      fun K hK => hcc K (List.mem_cons_of_mem L hK)
    -- head piece `A := L.piece.cells`, inherited defect `D`, tail union `U`
    have hAfin : L.piece.cells.Finite := L.piece.cells_finite
    have hUfin : (chainCells (M :: rest')).Finite := chainCells_finite _
    have hDsub : L.piece.optDefect L.entry e ⊆ L.piece.cells :=
      L.piece.optDefect_subset _ _
    have hAU : Disjoint L.piece.cells (chainCells (M :: rest')) :=
      disjoint_chainCells hLdisj
    have hUD : Disjoint (chainCells (M :: rest')) (L.piece.optDefect L.entry e) :=
      hAU.symm.mono_right hDsub
    have hsplit : chainCells (L :: M :: rest') \ L.piece.optDefect L.entry e =
        (L.piece.cells \ L.piece.optDefect L.entry e) ∪ chainCells (M :: rest') := by
      rw [chainCells_cons, Set.union_diff_distrib, hUD.sdiff_eq_left]
    have hADU : Disjoint (L.piece.cells \ L.piece.optDefect L.entry e)
        (chainCells (M :: rest')) := hAU.mono_left Set.diff_subset
    have hcards : (chainCells (L :: M :: rest') \ L.piece.optDefect L.entry e).ncard =
        (L.piece.cells \ L.piece.optDefect L.entry e).ncard +
          (chainCells (M :: rest')).ncard := by
      rw [hsplit]
      exact Set.ncard_union_eq hADU (hAfin.diff) hUfin
    by_cases hs0 : ((L.piece.cells \ L.piece.optDefect L.entry e).ncard : ℤ) % 3 = 0
    · -- the head closes exactly: tile it and recurse defect-free
      rw [hsplit]
      refine Tileable.union ?_ ?_ hADU
      · have h3 : 3 ∣ (L.piece.cells \ L.piece.optDefect L.entry e).ncard := by
          omega
        simpa using RectPiece.tileable_optDefects L.piece L.entry L.exit hccL
          e none (by simpa using h3)
      · have hU3 : 3 ∣ (chainCells (M :: rest')).ncard := by omega
        simpa using ih M hchain' hdisj' hcc' none (by simpa using hU3)
    · -- push the residual area into `M` with a straddling tromino
      obtain ⟨d, d', T, hd, hd', hT, hTsub, hTL, hTM⟩ :=
        exists_pushTromino L.piece M.piece L.exit M.entry hadj
          (((L.piece.cells \ L.piece.optDefect L.entry e).ncard : ℤ) % 3)
          (by omega)
      have hExsub : L.piece.defect L.exit d ⊆ L.piece.cells :=
        L.piece.defect_subset _ _
      have hEnsub : M.piece.defect M.entry d' ⊆ M.piece.cells :=
        M.piece.defect_subset _ _
      have hMU : M.piece.cells ⊆ chainCells (M :: rest') := by
        rw [chainCells_cons]
        exact Set.subset_union_left
      have hEnU : M.piece.defect M.entry d' ⊆ chainCells (M :: rest') :=
        hEnsub.trans hMU
      have hDEx : Disjoint (L.piece.optDefect L.entry e)
          (L.piece.defect L.exit d) :=
        L.piece.optDefect_disjoint_defect hccL e d
      have hExAD : L.piece.defect L.exit d ⊆
          L.piece.cells \ L.piece.optDefect L.entry e :=
        Set.subset_diff.mpr ⟨hExsub, hDEx.symm⟩
      have hT_eq : T = L.piece.defect L.exit d ∪ M.piece.defect M.entry d' := by
        rw [← hTL, ← hTM, ← Set.inter_union_distrib_left,
          Set.inter_eq_left.mpr hTsub]
      -- the region splits as (head minus both defects) ∪ tromino ∪ tail
      have h1 : L.piece.cells \
            (L.piece.optDefect L.entry e ∪ L.piece.defect L.exit d) ∪
            L.piece.defect L.exit d =
          L.piece.cells \ L.piece.optDefect L.entry e := by
        rw [← Set.diff_diff]
        exact Set.diff_union_of_subset hExAD
      have h2 : M.piece.defect M.entry d' ∪
            (chainCells (M :: rest') \ M.piece.defect M.entry d') =
          chainCells (M :: rest') := Set.union_diff_cancel hEnU
      have heq' : ((L.piece.cells \
            (L.piece.optDefect L.entry e ∪ L.piece.defect L.exit d)) ∪ T) ∪
            (chainCells (M :: rest') \ M.piece.defect M.entry d') =
          (L.piece.cells \ L.piece.optDefect L.entry e) ∪
            chainCells (M :: rest') := by
        rw [hT_eq, ← Set.union_assoc, h1, Set.union_assoc, h2]
      have heq : chainCells (L :: M :: rest') \ L.piece.optDefect L.entry e =
          ((L.piece.cells \
              (L.piece.optDefect L.entry e ∪ L.piece.defect L.exit d)) ∪ T) ∪
            (chainCells (M :: rest') \ M.piece.defect M.entry d') := by
        rw [hsplit]
        exact heq'.symm
      -- cardinalities of the three parts
      have hExfin := L.piece.defect_finite L.exit d
      have hEnfin := M.piece.defect_finite M.entry d'
      have hExcard := L.piece.defect_ncard L.exit d
      have hEncard := M.piece.defect_ncard M.entry d'
      have hcardX : (L.piece.cells \
            (L.piece.optDefect L.entry e ∪ L.piece.defect L.exit d)).ncard =
          (L.piece.cells \ L.piece.optDefect L.entry e).ncard -
            (L.piece.defect L.exit d).ncard := by
        rw [show L.piece.cells \
              (L.piece.optDefect L.entry e ∪ L.piece.defect L.exit d) =
            (L.piece.cells \ L.piece.optDefect L.entry e) \
              L.piece.defect L.exit d from Set.diff_diff.symm]
        exact Set.ncard_diff hExAD hExfin
      have hcardY : (chainCells (M :: rest') \ M.piece.defect M.entry d').ncard =
          (chainCells (M :: rest')).ncard -
            (M.piece.defect M.entry d').ncard :=
        Set.ncard_diff hEnU hEnfin
      have hleEx : (L.piece.defect L.exit d).ncard ≤
          (L.piece.cells \ L.piece.optDefect L.entry e).ncard :=
        Set.ncard_le_ncard hExAD (hAfin.diff)
      have hleEn : (M.piece.defect M.entry d').ncard ≤
          (chainCells (M :: rest')).ncard :=
        Set.ncard_le_ncard hEnU hUfin
      -- pairwise disjointness of the three parts
      have dj1 : Disjoint (L.piece.cells \
            (L.piece.optDefect L.entry e ∪ L.piece.defect L.exit d)) T := by
        rw [hT_eq]
        exact Set.disjoint_union_right.mpr
          ⟨Set.disjoint_sdiff_left.mono_right Set.subset_union_right,
            (hLdisj M (by simp)).mono Set.diff_subset hEnsub⟩
      have dj2 : Disjoint ((L.piece.cells \
            (L.piece.optDefect L.entry e ∪ L.piece.defect L.exit d)) ∪ T)
          (chainCells (M :: rest') \ M.piece.defect M.entry d') := by
        rw [hT_eq]
        refine Set.disjoint_union_left.mpr
          ⟨?_, Set.disjoint_union_left.mpr ⟨?_, ?_⟩⟩
        · exact hAU.mono Set.diff_subset Set.diff_subset
        · exact (hAU.mono_left hExsub).mono_right Set.diff_subset
        · exact Set.disjoint_sdiff_right
      rw [heq]
      refine Tileable.union (Tileable.union ?_ hT dj1) ?_ dj2
      · have h3 : 3 ∣ (L.piece.cells \
            (L.piece.optDefect L.entry e ∪ L.piece.defect L.exit d)).ncard := by
          omega
        simpa using RectPiece.tileable_optDefects L.piece L.entry L.exit hccL
          e (some d) (by simpa using h3)
      · have harea3 : 3 ∣
            (chainCells (M :: rest') \ M.piece.defect M.entry d').ncard := by
          omega
        simpa using ih M hchain' hdisj' hcc' (some d') (by simpa using harea3)

/-- **Lemma B**: a polyomino carrying a corner chain is L-tileable as soon
    as its area is divisible by 3 (apply `chainCells_tileable` with no
    inherited defect). -/
theorem IsCornerChain.tileable {l : List ChainLink} {P : Set Cell}
    (hc : IsCornerChain l P) (harea : 3 ∣ P.ncard) : LTileable P := by
  obtain ⟨L, rest, rfl⟩ := List.exists_cons_of_ne_nil hc.nonempty
  have h := chainCells_tileable L rest hc.chain hc.disjoint hc.entry_ne_exit
    none (by simpa [hc.covers] using harea)
  simpa [hc.covers] using h

-- ============================================================
-- §5 Main lemma
-- ============================================================

/-- **Main lemma (20-aligned polyominoes).**  A finite connected polyomino
    all of whose vertices lie on the pitch-20 grid is L-tileable if its area
    is divisible by 3.

    This is the vertex-aligned weakening of the fat-polyomino theorem; the
    genuine fatness hypothesis (all vertices far from each other and from
    all edges) replaces `VertexAligned` in a later phase.  The converse
    (tileable → 3 ∣ area) is routine and will be added when the statement
    is upgraded to an iff. -/
theorem LTileable_of_vertexAligned (P : Set Cell) (hfin : P.Finite)
    (hconn : CellConnected P) (hal : VertexAligned 20 P)
    (harea : 3 ∣ P.ncard) : LTileable P := by
  rcases P.eq_empty_or_nonempty with rfl | hne
  · exact Tileable.empty _
  · obtain ⟨l, hl⟩ := exists_cornerChain P hfin hne hconn hal
    exact hl.tileable harea
