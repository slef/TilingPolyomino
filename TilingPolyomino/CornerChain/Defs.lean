import TilingPolyomino.TwoCornerDefects
import TilingPolyomino.Polyomino.Basic
import Mathlib.Tactic

/-!
# Corner chains: the interface between decomposition and tiling

A **corner chain** (`IsCornerChain`) is a sequence of pairwise disjoint
rectangular pieces (`RectPiece`, sides ≥ 6) covering a region, consecutive
pieces meeting at **pushing corners** (`PushAdj`) — the shared grid point of
two edge-adjacent corner cells, across which an L-tromino can straddle.
Each link records the corners through which the chain enters and leaves its
piece.

Both geometric decompositions of the project produce a corner chain (the
corridor of a fat polyomino in `Corridor/`, the Euler tour of the vertical
decomposition in `EulerTour.lean`); the defect-pushing argument in
`CornerChain/Tiling.lean` consumes one.
-/

open Set

-- ============================================================
-- §3 Corner chains: the output of the geometric decomposition
-- ============================================================

-- Translation is compatible with the set operations (definitionally).
lemma translate_union (dx dy : ℤ) (A B : Set Cell) :
    translate dx dy (A ∪ B) = translate dx dy A ∪ translate dx dy B := rfl

lemma translate_diff (dx dy : ℤ) (A B : Set Cell) :
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
    two-corner-defect theorem.  (The subdivision of a 12-aligned polyomino
    produces sub-pieces of side exactly ≥ 6.) -/
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
