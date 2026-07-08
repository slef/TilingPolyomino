import TilingPolyomino.LTromino
import TilingPolyomino.LTrominoSetBridge
import TilingPolyomino.RectOmega
import Mathlib.Tactic

/-!
# Rectangles with two corner defects

Main result (`LTileable_rectMinusTwoCorners_iff`): for `n, m ≥ 6` and two
*distinct* corners, an `n × m` rectangle with a defect of size 1 or 2 at each
of the two corners is L-tromino-tileable iff its area is divisible by 3.

This theorem and its proof are due to the **MIT-ULB CompGeom Group**; this
file contains its formalization.

## Proof map (sufficiency direction)

Symmetry normalization (`flipX`, `flipY`, `transpose`, argument swap) reduces
everything to two canonical corner pairs: (BL, BR) "adjacent" and (BL, TR)
"diagonal".

* `m % 3 ≠ 0` and `n ≥ minWidth d1 + minWidth d2`: vertical split into two
  one-defect pieces (`LTileable_vsplit`); the one-defect pieces come from the
  already-proven single-corner theorems in `LTromino.lean`, moved to the right
  corner by reflection.
* adjacent, `m % 3 ≠ 0`, `n` too small (only `n = 6`, defects {single, vert}
  and `n = 7`, defects {vert, vert} occur): peel a bottom band and use an
  explicit base tiling (`B1` 6×2, `B2` 7×4, `B3` 7×7).
* adjacent, `3 ∣ m`: the defect sizes sum to 3; peel the bottom two rows as
  corner gadgets plus `3 × 2` blocks, reducing to `m % 3 ≠ 0`.
* diagonal, `3 ∣ n`, `3 ∣ m`: same two-row peel around the bottom defect; the
  remainder keeps the top defect, has height `≡ 1 (mod 3)`, and falls to the
  `m % 3 ≠ 0` case (whose `n = 6` leftover peels once more, down to `B1`).
-/

-- ============================================================
-- Defect types and corners
-- ============================================================

/-- Shape of a corner defect: one cell, or a domino along the horizontal or
    vertical edge. -/
inductive DefectType
  | single
  | horiz
  | vert
  deriving DecidableEq

namespace DefectType

/-- Number of cells removed by the defect. -/
def size : DefectType → ℤ
  | single => 1
  | horiz => 2
  | vert => 2

@[simp] lemma size_single : single.size = 1 := rfl
@[simp] lemma size_horiz : horiz.size = 2 := rfl
@[simp] lemma size_vert : vert.size = 2 := rfl

lemma size_pos (d : DefectType) : 1 ≤ d.size := by cases d <;> simp
lemma size_le_two (d : DefectType) : d.size ≤ 2 := by cases d <;> simp

/-- Transposing the plane (swapping coordinates) swaps `horiz` and `vert`. -/
def transpose : DefectType → DefectType
  | single => single
  | horiz => vert
  | vert => horiz

@[simp] lemma size_transpose (d : DefectType) : d.transpose.size = d.size := by
  cases d <;> rfl

@[simp] lemma transpose_transpose (d : DefectType) : d.transpose.transpose = d := by
  cases d <;> rfl

end DefectType

-- `Corner` is defined in `TilingPolyomino.Grid`.

namespace Corner

/-- Cells removed by defect `d` placed at corner `c` of the rectangle
    `[0,n) × [0,m)`.  The defect always contains the corner cell; the second
    cell (if any) extends along the bottom/top edge (`horiz`) or the
    left/right edge (`vert`). -/
def cells : Corner → DefectType → ℤ → ℤ → Set Cell
  | BL, .single, _, _ => {(0, 0)}
  | BL, .horiz,  _, _ => {(0, 0), (1, 0)}
  | BL, .vert,   _, _ => {(0, 0), (0, 1)}
  | BR, .single, n, _ => {(n - 1, 0)}
  | BR, .horiz,  n, _ => {(n - 1, 0), (n - 2, 0)}
  | BR, .vert,   n, _ => {(n - 1, 0), (n - 1, 1)}
  | TL, .single, _, m => {(0, m - 1)}
  | TL, .horiz,  _, m => {(0, m - 1), (1, m - 1)}
  | TL, .vert,   _, m => {(0, m - 1), (0, m - 2)}
  | TR, .single, n, m => {(n - 1, m - 1)}
  | TR, .horiz,  n, m => {(n - 1, m - 1), (n - 2, m - 1)}
  | TR, .vert,   n, m => {(n - 1, m - 1), (n - 1, m - 2)}

/-- Where a corner goes under transposition `(x, y) ↦ (y, x)`. -/
def transpose : Corner → Corner
  | BL => BL
  | BR => TL
  | TL => BR
  | TR => TR

/-- Where a corner goes under horizontal reflection `x ↦ n - 1 - x`. -/
def flipX : Corner → Corner
  | BL => BR
  | BR => BL
  | TL => TR
  | TR => TL

/-- Where a corner goes under vertical reflection `y ↦ m - 1 - y`. -/
def flipY : Corner → Corner
  | BL => TL
  | TL => BL
  | BR => TR
  | TR => BR

@[simp] lemma flipX_flipX (c : Corner) : c.flipX.flipX = c := by cases c <;> rfl
@[simp] lemma flipY_flipY (c : Corner) : c.flipY.flipY = c := by cases c <;> rfl
@[simp] lemma transpose_transpose (c : Corner) : c.transpose.transpose = c := by
  cases c <;> rfl

end Corner

-- ============================================================
-- The regions
-- ============================================================

/-- `n × m` rectangle minus one corner defect. -/
def rectMinusOneCorner (n m : ℤ) (c : Corner) (d : DefectType) : Set Cell :=
  rect 0 0 n m \ c.cells d n m

/-- `n × m` rectangle minus a defect at each of two corners. -/
def rectMinusTwoCorners (n m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType) : Set Cell :=
  rect 0 0 n m \ (c1.cells d1 n m ∪ c2.cells d2 n m)

/-- Swapping the two defects gives the same region. -/
lemma rectMinusTwoCorners_comm (n m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType) :
    rectMinusTwoCorners n m c1 c2 d1 d2 = rectMinusTwoCorners n m c2 c1 d2 d1 := by
  simp [rectMinusTwoCorners, Set.union_comm]

-- ============================================================
-- Basic facts about defect cells
-- ============================================================

lemma Corner.cells_finite (c : Corner) (d : DefectType) (n m : ℤ) :
    (c.cells d n m).Finite := by
  cases c <;> cases d <;>
    simp only [Corner.cells] <;>
    first
      | exact Set.finite_singleton _
      | exact (Set.finite_singleton _).insert _

lemma Corner.cells_ncard (c : Corner) (d : DefectType) (n m : ℤ) :
    ((c.cells d n m).ncard : ℤ) = d.size := by
  cases c <;> cases d <;>
    simp only [Corner.cells, DefectType.size] <;>
    simp

lemma Corner.cells_subset_rect (c : Corner) (d : DefectType) (n m : ℤ)
    (hn : 2 ≤ n) (hm : 2 ≤ m) :
    c.cells d n m ⊆ rect 0 0 n m := by
  rintro ⟨x, y⟩ hxy
  cases c <;> cases d <;>
    simp only [Corner.cells, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at hxy <;>
    (simp only [mem_rect]; omega)

lemma Corner.cells_disjoint {c1 c2 : Corner} (d1 d2 : DefectType) (n m : ℤ)
    (hn : 4 ≤ n) (hm : 4 ≤ m) (hc : c1 ≠ c2) :
    Disjoint (c1.cells d1 n m) (c2.cells d2 n m) := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  cases c1 <;> cases c2 <;>
    (try exact hc rfl) <;>
    cases d1 <;> cases d2 <;>
    simp only [Corner.cells, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at h1 h2 <;>
    omega

-- ============================================================
-- Cardinality and the necessity direction
-- ============================================================

lemma rectMinusTwoCorners_finite (n m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType) :
    (rectMinusTwoCorners n m c1 c2 d1 d2).Finite :=
  (rect_finite 0 0 n m).subset Set.diff_subset

/-- For `n, m ≥ 4` the two defects are disjoint and inside the rectangle, so the
    area is exactly `n·m` minus the defect sizes. -/
lemma rectMinusTwoCorners_ncard (n m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType)
    (hn : 4 ≤ n) (hm : 4 ≤ m) (hc : c1 ≠ c2) :
    ((rectMinusTwoCorners n m c1 c2 d1 d2).ncard : ℤ) = n * m - d1.size - d2.size := by
  have hsub : c1.cells d1 n m ∪ c2.cells d2 n m ⊆ rect 0 0 n m :=
    Set.union_subset (Corner.cells_subset_rect c1 d1 n m (by omega) (by omega))
      (Corner.cells_subset_rect c2 d2 n m (by omega) (by omega))
  have hcard : (c1.cells d1 n m ∪ c2.cells d2 n m).ncard =
      (c1.cells d1 n m).ncard + (c2.cells d2 n m).ncard :=
    Set.ncard_union_eq (Corner.cells_disjoint d1 d2 n m hn hm hc)
      (Corner.cells_finite c1 d1 n m) (Corner.cells_finite c2 d2 n m)
  have hrect : (((rect 0 0 n m).ncard : ℕ) : ℤ) = n * m := by
    rw [rect_ncard]
    push_cast
    rw [sub_zero, sub_zero, Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ n),
      Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ m)]
  have h1 := Corner.cells_ncard c1 d1 n m
  have h2 := Corner.cells_ncard c2 d2 n m
  have hs1 := d1.size_pos
  have hs1' := d1.size_le_two
  have hs2 := d2.size_pos
  have hs2' := d2.size_le_two
  have h16 : (16 : ℤ) ≤ n * m := by
    calc (16 : ℤ) = 4 * 4 := by norm_num
    _ ≤ n * m := mul_le_mul hn hm (by norm_num) (by omega)
  rw [rectMinusTwoCorners,
    Set.ncard_diff hsub ((Corner.cells_finite c1 d1 n m).union
      (Corner.cells_finite c2 d2 n m)), hcard]
  omega

/-- Necessity: a tileable two-defect rectangle has area divisible by 3. -/
theorem LTileable_rectMinusTwoCorners_area (n m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType)
    (h : LTileable (rectMinusTwoCorners n m c1 c2 d1 d2)) :
    3 ∣ (rectMinusTwoCorners n m c1 c2 d1 d2).ncard := by
  have hdvd := Tileable.ncard_dvd (ι := Unit) (ps := LProtoset)
    (rectMinusTwoCorners_finite n m c1 c2 d1 d2) h ()
  simpa [LProtoset, LPrototile_set_ncard] using hdvd

-- ============================================================
-- Symmetry: reflections and transposition of regions
-- ============================================================

/-- Reflection of a region across the vertical axis of `[0,n) × ·`:
    `x ↦ n - 1 - x`.  An involution mapping `rect 0 0 n m` to itself. -/
def reflectXRegion (n : ℤ) (R : Set Cell) : Set Cell :=
  {p | ((n - 1 - p.1, p.2) : Cell) ∈ R}

/-- Reflection of a region across the horizontal axis of `· × [0,m)`:
    `y ↦ m - 1 - y`. -/
def reflectYRegion (m : ℤ) (R : Set Cell) : Set Cell :=
  {p | ((p.1, m - 1 - p.2) : Cell) ∈ R}

@[simp] lemma mem_reflectXRegion (n : ℤ) (R : Set Cell) (p : Cell) :
    p ∈ reflectXRegion n R ↔ ((n - 1 - p.1, p.2) : Cell) ∈ R := Iff.rfl

@[simp] lemma mem_reflectYRegion (m : ℤ) (R : Set Cell) (p : Cell) :
    p ∈ reflectYRegion m R ↔ ((p.1, m - 1 - p.2) : Cell) ∈ R := Iff.rfl

/-- How rotations behave under horizontal reflection of the L-tromino:
    reflecting `rotate r LShape` gives `rotate (xflipRot r) LShape` (negated x). -/
private def xflipRot : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2

private lemma reflectXRegion_placed (n dx dy : ℤ) (r : Fin 4) :
    reflectXRegion n (translate dx dy (rotate r LShape_cells)) =
      translate (n - 1 - dx) dy (rotate (xflipRot r) LShape_cells) := by
  fin_cases r <;>
  · ext ⟨x, y⟩
    simp only [mem_reflectXRegion, mem_translate, mem_rotate, xflipRot, LShape_cells,
      inverseRot, rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega

/-- Tilings transport along horizontal reflection (the L-protoset is closed
    under reflection up to rotation). -/
theorem LTileable_reflectX {R : Set Cell} (n : ℤ) (h : LTileable R) :
    LTileable (reflectXRegion n R) := by
  obtain ⟨ιₜ, hft, t, hv⟩ := h
  haveI : Fintype ιₜ := hft
  let t' : TileSet LProtoset ιₜ := ⟨fun i =>
    ⟨(), (n - 1 - (t.tiles i).translation.1, (t.tiles i).translation.2),
      xflipRot (t.tiles i).rotation⟩⟩
  have hcell : ∀ i, TileSet.cellsAt_finset t' i =
      reflectXRegion n (TileSet.cellsAt_finset t i) := by
    intro i
    rcases hti : t.tiles i with ⟨idx, tr, r⟩
    rcases tr with ⟨dx, dy⟩
    cases idx
    have h1 : TileSet.cellsAt_finset t' i =
        translate (n - 1 - dx) dy (rotate (xflipRot r) LShape_cells) := by
      simp only [TileSet.cellsAt_finset, t', hti]
      rfl
    have h2 : TileSet.cellsAt_finset t i =
        translate dx dy (rotate r LShape_cells) := by
      simp only [TileSet.cellsAt_finset, hti]
      rfl
    rw [h1, h2, reflectXRegion_placed]
  refine ⟨ιₜ, hft, t', ⟨?_, ?_⟩⟩
  · intro i j hij
    have hd := hv.disjoint i j hij
    rw [Set.disjoint_left] at hd ⊢
    exact fun p hp1 hp2 => hd (by simpa [hcell i, mem_reflectXRegion] using hp1)
                              (by simpa [hcell j, mem_reflectXRegion] using hp2)
  · ext p
    simp only [TileSet.coveredCells_finset, Set.mem_iUnion, hcell, mem_reflectXRegion]
    exact ⟨fun ⟨i, hi⟩ => hv.covers ▸
             (Set.mem_iUnion.mpr ⟨i, hi⟩ : _ ∈ TileSet.coveredCells_finset t),
           fun hpR => Set.mem_iUnion.mp
             (hv.covers.symm ▸ hpR : _ ∈ TileSet.coveredCells_finset t)⟩

/-- Tilings transport along vertical reflection. -/
theorem LTileable_reflectY {R : Set Cell} (m : ℤ) (h : LTileable R) :
    LTileable (reflectYRegion m R) := by
  have h3 := LTileable_swap (LTileable_reflectX m (LTileable_swap h))
  have heq : Set.swapRegion (reflectXRegion m (Set.swapRegion R)) = reflectYRegion m R := rfl
  rwa [heq] at h3

-- How defect cells move under the three symmetries.

private lemma mem_cells_flipX (c : Corner) (d : DefectType) (n m x y : ℤ) :
    ((n - 1 - x, y) : Cell) ∈ c.cells d n m ↔ ((x, y) : Cell) ∈ c.flipX.cells d n m := by
  cases c <;> cases d <;>
    simp only [Corner.cells, Corner.flipX, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] <;>
    omega

private lemma mem_cells_flipY (c : Corner) (d : DefectType) (n m x y : ℤ) :
    ((x, m - 1 - y) : Cell) ∈ c.cells d n m ↔ ((x, y) : Cell) ∈ c.flipY.cells d n m := by
  cases c <;> cases d <;>
    simp only [Corner.cells, Corner.flipY, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] <;>
    omega

private lemma mem_cells_transpose (c : Corner) (d : DefectType) (n m x y : ℤ) :
    ((y, x) : Cell) ∈ c.cells d n m ↔
      ((x, y) : Cell) ∈ c.transpose.cells d.transpose m n := by
  cases c <;> cases d <;>
    simp only [Corner.cells, Corner.transpose, DefectType.transpose, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq] <;>
    omega

-- How the regions move under the three symmetries.

lemma reflectXRegion_rectMinusTwoCorners (n m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType) :
    reflectXRegion n (rectMinusTwoCorners n m c1 c2 d1 d2) =
      rectMinusTwoCorners n m c1.flipX c2.flipX d1 d2 := by
  ext ⟨x, y⟩
  simp only [mem_reflectXRegion, rectMinusTwoCorners, Set.mem_diff, Set.mem_union, mem_rect]
  rw [mem_cells_flipX c1 d1 n m x y, mem_cells_flipX c2 d2 n m x y]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

lemma reflectYRegion_rectMinusTwoCorners (n m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType) :
    reflectYRegion m (rectMinusTwoCorners n m c1 c2 d1 d2) =
      rectMinusTwoCorners n m c1.flipY c2.flipY d1 d2 := by
  ext ⟨x, y⟩
  simp only [mem_reflectYRegion, rectMinusTwoCorners, Set.mem_diff, Set.mem_union, mem_rect]
  rw [mem_cells_flipY c1 d1 n m x y, mem_cells_flipY c2 d2 n m x y]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

lemma swapRegion_rectMinusTwoCorners (n m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType) :
    Set.swapRegion (rectMinusTwoCorners n m c1 c2 d1 d2) =
      rectMinusTwoCorners m n c1.transpose c2.transpose d1.transpose d2.transpose := by
  ext ⟨x, y⟩
  simp only [mem_swapRegion, rectMinusTwoCorners, Set.mem_diff, Set.mem_union, mem_rect]
  rw [mem_cells_transpose c1 d1 n m x y, mem_cells_transpose c2 d2 n m x y]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

lemma reflectXRegion_rectMinusOneCorner (n m : ℤ) (c : Corner) (d : DefectType) :
    reflectXRegion n (rectMinusOneCorner n m c d) =
      rectMinusOneCorner n m c.flipX d := by
  ext ⟨x, y⟩
  simp only [mem_reflectXRegion, rectMinusOneCorner, Set.mem_diff, mem_rect]
  rw [mem_cells_flipX c d n m x y]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

lemma reflectYRegion_rectMinusOneCorner (n m : ℤ) (c : Corner) (d : DefectType) :
    reflectYRegion m (rectMinusOneCorner n m c d) =
      rectMinusOneCorner n m c.flipY d := by
  ext ⟨x, y⟩
  simp only [mem_reflectYRegion, rectMinusOneCorner, Set.mem_diff, mem_rect]
  rw [mem_cells_flipY c d n m x y]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

lemma swapRegion_rectMinusOneCorner (n m : ℤ) (c : Corner) (d : DefectType) :
    Set.swapRegion (rectMinusOneCorner n m c d) =
      rectMinusOneCorner m n c.transpose d.transpose := by
  ext ⟨x, y⟩
  simp only [mem_swapRegion, rectMinusOneCorner, Set.mem_diff, mem_rect]
  rw [mem_cells_transpose c d n m x y]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

-- Transport corollaries: to tile a region, tile its mirror image.

theorem LTileable_twoCorners_of_flipX {n m : ℤ} {c1 c2 : Corner} {d1 d2 : DefectType}
    (h : LTileable (rectMinusTwoCorners n m c1.flipX c2.flipX d1 d2)) :
    LTileable (rectMinusTwoCorners n m c1 c2 d1 d2) := by
  have h2 := LTileable_reflectX n h
  rwa [reflectXRegion_rectMinusTwoCorners, Corner.flipX_flipX, Corner.flipX_flipX] at h2

theorem LTileable_twoCorners_of_flipY {n m : ℤ} {c1 c2 : Corner} {d1 d2 : DefectType}
    (h : LTileable (rectMinusTwoCorners n m c1.flipY c2.flipY d1 d2)) :
    LTileable (rectMinusTwoCorners n m c1 c2 d1 d2) := by
  have h2 := LTileable_reflectY m h
  rwa [reflectYRegion_rectMinusTwoCorners, Corner.flipY_flipY, Corner.flipY_flipY] at h2

theorem LTileable_twoCorners_of_transpose {n m : ℤ} {c1 c2 : Corner} {d1 d2 : DefectType}
    (h : LTileable (rectMinusTwoCorners m n c1.transpose c2.transpose
          d1.transpose d2.transpose)) :
    LTileable (rectMinusTwoCorners n m c1 c2 d1 d2) := by
  have h2 := LTileable_swap h
  rwa [swapRegion_rectMinusTwoCorners, Corner.transpose_transpose, Corner.transpose_transpose,
    DefectType.transpose_transpose, DefectType.transpose_transpose] at h2

-- ============================================================
-- One-defect pieces (building blocks)
-- ============================================================

-- Bridges from the single-corner theorems in `LTromino.lean` (defect at TR).

private lemma LTileable_oneCorner_TR_single (n m : ℤ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (h : (n * m - 1) % 3 = 0) :
    LTileable (rectMinusOneCorner n m .TR .single) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = n := ⟨n.toNat, by omega⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = m := ⟨m.toNat, by omega⟩
  subst hN; subst hM
  have hN2 : 2 ≤ N := by omega
  have hM2 : 2 ≤ M := by omega
  have h4 : 4 ≤ N * M := le_trans (by norm_num) (Nat.mul_le_mul hN2 hM2)
  have hcast : ((N * M : ℕ) : ℤ) = (N : ℤ) * (M : ℤ) := by push_cast; ring
  rw [← hcast] at h
  have harea : (N * M - 1) % 3 = 0 := by omega
  exact (LTileable_rectMinusCorner_iff N M hN2 hM2).mpr harea

private lemma LTileable_oneCorner_TR_horiz (n m : ℤ) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (h : (n * m - 2) % 3 = 0) :
    LTileable (rectMinusOneCorner n m .TR .horiz) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = n := ⟨n.toNat, by omega⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = m := ⟨m.toNat, by omega⟩
  subst hN; subst hM
  have hN3 : 3 ≤ N := by omega
  have hM3 : 3 ≤ M := by omega
  have h4 : 9 ≤ N * M := le_trans (by norm_num) (Nat.mul_le_mul hN3 hM3)
  have hcast : ((N * M : ℕ) : ℤ) = (N : ℤ) * (M : ℤ) := by push_cast; ring
  rw [← hcast] at h
  have harea : N * M % 3 = 2 := by omega
  have hres := LTileable_rectMinus2Corner N M hN3 hM3 harea
  have hrw : rect 0 0 (N : ℤ) M \ ({((N : ℤ) - 1, (M : ℤ) - 1)} ∪ {((N : ℤ) - 2, (M : ℤ) - 1)}) =
      rectMinusOneCorner (N : ℤ) (M : ℤ) .TR .horiz := by
    rw [rectMinusOneCorner]
    simp only [Corner.cells, Set.insert_eq]
  rwa [hrw] at hres

/-- Single-cell defect at any corner: tileable when area ≡ 0 (mod 3), `n, m ≥ 2`. -/
theorem LTileable_oneCorner_single (n m : ℤ) (c : Corner) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (h : (n * m - 1) % 3 = 0) :
    LTileable (rectMinusOneCorner n m c .single) := by
  have hTR := LTileable_oneCorner_TR_single n m hn hm h
  have hTL : LTileable (rectMinusOneCorner n m .TL .single) := by
    have h2 := LTileable_reflectX n hTR
    rw [reflectXRegion_rectMinusOneCorner] at h2
    simpa [Corner.flipX] using h2
  have hBR : LTileable (rectMinusOneCorner n m .BR .single) := by
    have h2 := LTileable_reflectY m hTR
    rw [reflectYRegion_rectMinusOneCorner] at h2
    simpa [Corner.flipY] using h2
  have hBL : LTileable (rectMinusOneCorner n m .BL .single) := by
    have h2 := LTileable_reflectY m hTL
    rw [reflectYRegion_rectMinusOneCorner] at h2
    simpa [Corner.flipY] using h2
  cases c <;> assumption

private lemma LTileable_oneCorner_horiz (n m : ℤ) (c : Corner) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (h : (n * m - 2) % 3 = 0) :
    LTileable (rectMinusOneCorner n m c .horiz) := by
  have hTR := LTileable_oneCorner_TR_horiz n m hn hm h
  have hTL : LTileable (rectMinusOneCorner n m .TL .horiz) := by
    have h2 := LTileable_reflectX n hTR
    rw [reflectXRegion_rectMinusOneCorner] at h2
    simpa [Corner.flipX] using h2
  have hBR : LTileable (rectMinusOneCorner n m .BR .horiz) := by
    have h2 := LTileable_reflectY m hTR
    rw [reflectYRegion_rectMinusOneCorner] at h2
    simpa [Corner.flipY] using h2
  have hBL : LTileable (rectMinusOneCorner n m .BL .horiz) := by
    have h2 := LTileable_reflectY m hTL
    rw [reflectYRegion_rectMinusOneCorner] at h2
    simpa [Corner.flipY] using h2
  cases c <;> assumption

/-- Domino defect at any corner: tileable when area ≡ 0 (mod 3), `n, m ≥ 3`. -/
theorem LTileable_oneCorner_size2 (n m : ℤ) (c : Corner) (d : DefectType)
    (hd : d ≠ .single) (hn : 3 ≤ n) (hm : 3 ≤ m) (h : (n * m - 2) % 3 = 0) :
    LTileable (rectMinusOneCorner n m c d) := by
  cases d with
  | single => exact absurd rfl hd
  | horiz => exact LTileable_oneCorner_horiz n m c hn hm h
  | vert =>
    have hh := LTileable_oneCorner_horiz m n c.transpose hm hn
      (by rw [mul_comm]; exact h)
    have h2 := LTileable_swap hh
    rw [swapRegion_rectMinusOneCorner, Corner.transpose_transpose] at h2
    simpa [DefectType.transpose] using h2

/-- Degenerate width-2 piece: a `horiz` defect in a width-2 rectangle removes a
    full row, leaving a `2 × (m-1)` rectangle. -/
theorem LTileable_oneCorner_horiz_width2 (m : ℤ) (c : Corner) (hm : 2 ≤ m)
    (h : (2 * m - 2) % 3 = 0) :
    LTileable (rectMinusOneCorner 2 m c .horiz) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (K : ℤ) = m - 1 := ⟨(m - 1).toNat, by omega⟩
  have h3 : 3 ∣ K := by omega
  have hrect : LTileable (rect 0 0 2 (K : ℤ)) := (LTileable_2xn_iff K).mpr h3
  cases c with
  | BL =>
    have heq : rectMinusOneCorner 2 m .BL .horiz = translate 0 1 (rect 0 0 2 (K : ℤ)) := by
      ext ⟨x, y⟩
      simp only [rectMinusOneCorner, Corner.cells, Set.mem_diff, mem_rect, mem_translate,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    rw [heq]; exact hrect.translate 0 1
  | BR =>
    have heq : rectMinusOneCorner 2 m .BR .horiz = translate 0 1 (rect 0 0 2 (K : ℤ)) := by
      ext ⟨x, y⟩
      simp only [rectMinusOneCorner, Corner.cells, Set.mem_diff, mem_rect, mem_translate,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    rw [heq]; exact hrect.translate 0 1
  | TL =>
    have heq : rectMinusOneCorner 2 m .TL .horiz = rect 0 0 2 (K : ℤ) := by
      ext ⟨x, y⟩
      simp only [rectMinusOneCorner, Corner.cells, Set.mem_diff, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    rw [heq]; exact hrect
  | TR =>
    have heq : rectMinusOneCorner 2 m .TR .horiz = rect 0 0 2 (K : ℤ) := by
      ext ⟨x, y⟩
      simp only [rectMinusOneCorner, Corner.cells, Set.mem_diff, mem_rect,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    rw [heq]; exact hrect

/-- Packaged piece lemma used by the vertical split: covers all widths that
    `minWidth` can produce. -/
theorem LTileable_oneCorner_piece (n m : ℤ) (c : Corner) (d : DefectType)
    (hn : 2 ≤ n) (hm : 3 ≤ m)
    (hshape : 3 ≤ n ∨ d = .single ∨ (d = .horiz ∧ n = 2))
    (h : (n * m - d.size) % 3 = 0) :
    LTileable (rectMinusOneCorner n m c d) := by
  cases d with
  | single =>
    exact LTileable_oneCorner_single n m c hn (by omega) (by simpa using h)
  | horiz =>
    rcases hshape with h3 | hs | ⟨_, rfl⟩
    · exact LTileable_oneCorner_size2 n m c .horiz (by decide) h3 (by omega) (by simpa using h)
    · exact absurd hs (by decide)
    · exact LTileable_oneCorner_horiz_width2 m c (by omega) (by simpa using h)
  | vert =>
    rcases hshape with h3 | hs | ⟨hh, _⟩
    · exact LTileable_oneCorner_size2 n m c .vert (by decide) h3 (by omega) (by simpa using h)
    · exact absurd hs (by decide)
    · exact absurd hh (by decide)

-- ============================================================
-- Vertical split into two one-defect pieces
-- ============================================================

/-- Splitting the two-defect rectangle at `x = n1`: left piece keeps the
    left-corner defect, right piece the right-corner defect. -/
lemma rectMinusTwoCorners_vsplit (n1 n2 m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType)
    (hc1 : c1 = .BL ∨ c1 = .TL) (hc2 : c2 = .BR ∨ c2 = .TR)
    (hn1 : 2 ≤ n1) (hn2 : 2 ≤ n2) (hm : 2 ≤ m) :
    rectMinusTwoCorners (n1 + n2) m c1 c2 d1 d2 =
      rectMinusOneCorner n1 m c1 d1 ∪
        translate n1 0 (rectMinusOneCorner n2 m c2 d2) := by
  rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
    cases d1 <;> cases d2 <;>
    · ext ⟨x, y⟩
      simp only [rectMinusTwoCorners, rectMinusOneCorner, Corner.cells, Set.mem_diff,
        Set.mem_union, mem_rect, mem_translate, Set.mem_insert_iff, Set.mem_singleton_iff,
        Prod.mk.injEq]
      omega

private lemma vsplit_disjoint (n1 n2 m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType) :
    Disjoint (rectMinusOneCorner n1 m c1 d1)
      (translate n1 0 (rectMinusOneCorner n2 m c2 d2)) := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [rectMinusOneCorner, Set.mem_diff, mem_rect, mem_translate] at h1 h2
  obtain ⟨⟨_, hx1, _, _⟩, _⟩ := h1
  obtain ⟨⟨hx2, _, _, _⟩, _⟩ := h2
  omega

theorem LTileable_vsplit (n1 n2 m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType)
    (hc1 : c1 = .BL ∨ c1 = .TL) (hc2 : c2 = .BR ∨ c2 = .TR)
    (hn1 : 2 ≤ n1) (hn2 : 2 ≤ n2) (hm : 2 ≤ m)
    (h1 : LTileable (rectMinusOneCorner n1 m c1 d1))
    (h2 : LTileable (rectMinusOneCorner n2 m c2 d2)) :
    LTileable (rectMinusTwoCorners (n1 + n2) m c1 c2 d1 d2) := by
  rw [rectMinusTwoCorners_vsplit n1 n2 m c1 c2 d1 d2 hc1 hc2 hn1 hn2 hm]
  exact Tileable.union h1 (h2.translate n1 0) (vsplit_disjoint n1 n2 m c1 c2 d1 d2)

/-- Minimal width of a usable one-defect piece, as a function of `m % 3 ∈ {1,2}`
    and the defect type. -/
def minWidth (r : ℤ) (d : DefectType) : ℤ :=
  if r = 1 then
    match d with
    | .single => 4
    | .horiz => 2
    | .vert => 5
  else
    match d with
    | .single => 2
    | .horiz => 4
    | .vert => 4

lemma minWidth_le_five (r : ℤ) (d : DefectType) : minWidth r d ≤ 5 := by
  unfold minWidth; split <;> cases d <;> norm_num

lemma two_le_minWidth (r : ℤ) (d : DefectType) : 2 ≤ minWidth r d := by
  unfold minWidth; split <;> cases d <;> norm_num

private lemma minWidth_area (m : ℤ) (d : DefectType) (hm3 : m % 3 ≠ 0) :
    (minWidth (m % 3) d * m - d.size) % 3 = 0 := by
  have hmr : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hmr with h1 | h1 <;> cases d <;>
    simp only [minWidth, h1, DefectType.size_single, DefectType.size_horiz,
      DefectType.size_vert] <;>
    norm_num <;>
    omega

private lemma minWidth_shape (m : ℤ) (d : DefectType) :
    3 ≤ minWidth (m % 3) d ∨ d = .single ∨ (d = .horiz ∧ minWidth (m % 3) d = 2) := by
  unfold minWidth
  split <;> cases d <;> simp

private lemma minWidth_vert_ge_four (r : ℤ) : 4 ≤ minWidth r .vert := by
  unfold minWidth; split <;> norm_num

/-- Main workhorse: vertical cut, valid whenever `m % 3 ≠ 0` and `n` is at
    least the sum of the two minimal widths. -/
theorem LTileable_twoCorners_vcut (n m : ℤ) (c1 c2 : Corner) (d1 d2 : DefectType)
    (hc1 : c1 = .BL ∨ c1 = .TL) (hc2 : c2 = .BR ∨ c2 = .TR)
    (hm : 3 ≤ m) (hm3 : m % 3 ≠ 0)
    (hn : minWidth (m % 3) d1 + minWidth (m % 3) d2 ≤ n)
    (harea : (n * m - d1.size - d2.size) % 3 = 0) :
    LTileable (rectMinusTwoCorners n m c1 c2 d1 d2) := by
  set w1 := minWidth (m % 3) d1 with hw1
  set w2 := n - w1 with hw2
  have hminw1 := two_le_minWidth (m % 3) d1
  have hminw2 := two_le_minWidth (m % 3) d2
  have harea1 : (w1 * m - d1.size) % 3 = 0 := minWidth_area m d1 hm3
  have harea2 : (w2 * m - d2.size) % 3 = 0 := by
    have he : w2 * m = n * m - w1 * m := by rw [hw2]; ring
    omega
  have hshape1 := minWidth_shape m d1
  have hw2ge : minWidth (m % 3) d2 ≤ w2 := by omega
  have hshape2 : 3 ≤ w2 ∨ d2 = .single ∨ (d2 = .horiz ∧ w2 = 2) := by
    cases d2 with
    | single => exact Or.inr (Or.inl rfl)
    | horiz =>
      by_cases h3 : 3 ≤ w2
      · exact Or.inl h3
      · exact Or.inr (Or.inr ⟨rfl, by omega⟩)
    | vert =>
      have := minWidth_vert_ge_four (m % 3)
      exact Or.inl (by omega)
  have hn_eq : n = w1 + w2 := by omega
  rw [hn_eq]
  exact LTileable_vsplit w1 w2 m c1 c2 d1 d2 hc1 hc2 (by omega) (by omega) (by omega)
    (LTileable_oneCorner_piece w1 m c1 d1 (by omega) hm hshape1 harea1)
    (LTileable_oneCorner_piece w2 m c2 d2 (by omega) hm hshape2 harea2)

-- ============================================================
-- Horizontal bands (for the adjacent pair (BL, BR))
-- ============================================================

/-- Cutting off the bottom band of height `h ≥ 2`: it contains both defects,
    the rest is a clean rectangle. -/
lemma rectMinusTwoCorners_band_bottom (n m h : ℤ) (d1 d2 : DefectType)
    (hh : 2 ≤ h) (hhm : h ≤ m) :
    rectMinusTwoCorners n m .BL .BR d1 d2 =
      rectMinusTwoCorners n h .BL .BR d1 d2 ∪
        translate 0 h (rect 0 0 n (m - h)) := by
  cases d1 <;> cases d2 <;>
  · ext ⟨x, y⟩
    simp only [rectMinusTwoCorners, Corner.cells, Set.mem_diff, Set.mem_union, mem_rect,
      mem_translate, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega

theorem LTileable_band_bottom (n m h : ℤ) (d1 d2 : DefectType)
    (hh : 2 ≤ h) (hhm : h ≤ m)
    (hband : LTileable (rectMinusTwoCorners n h .BL .BR d1 d2))
    (hrect : LTileable (rect 0 0 n (m - h))) :
    LTileable (rectMinusTwoCorners n m .BL .BR d1 d2) := by
  rw [rectMinusTwoCorners_band_bottom n m h d1 d2 hh hhm]
  apply Tileable.union hband (hrect.translate 0 h)
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [rectMinusTwoCorners, Set.mem_diff, mem_rect, mem_translate] at h1 h2
  obtain ⟨⟨_, _, _, hy1⟩, _⟩ := h1
  obtain ⟨_, _, hy2, _⟩ := h2
  omega

-- Explicit base tilings (found by exhaustive search), verified by `decide`
-- in the Finset framework and moved across the bridge.

private def tiling_B1 : TileSet_finset LTrominoSet_finset (Fin 3) := ⟨![
  ⟨(), (1, 1), 2⟩,  -- covers (0,1), (1,0), (1,1)
  ⟨(), (2, 0), 0⟩,  -- covers (2,0), (2,1), (3,0)
  ⟨(), (4, 1), 2⟩   -- covers (3,1), (4,0), (4,1)
]⟩

private theorem tiling_B1_valid :
    tiling_B1.Valid_finset (rectangle 6 2 \ {(0, 0), (5, 0), (5, 1)}) := by decide

/-- B1: `6 × 2` minus single@BL and vert@BR (9 cells, 3 trominoes). -/
theorem LTileable_base_6x2_single_vert :
    LTileable (rectMinusTwoCorners 6 2 .BL .BR .single .vert) := by
  have h : LTileable_finset (rectangle 6 2 \ {(0, 0), (5, 0), (5, 1)}) :=
    ⟨Fin 3, inferInstance, inferInstance, tiling_B1, tiling_B1_valid⟩
  rw [LTileable_iff] at h
  have heq : (↑(rectangle 6 2 \ {(0, 0), (5, 0), (5, 1)} : Finset Cell) : Set Cell) =
      rectMinusTwoCorners 6 2 .BL .BR .single .vert := by
    rw [Finset.coe_sdiff]
    have hr := coe_rectangle_eq_rect 6 2
    norm_num at hr
    rw [hr]
    ext ⟨x, y⟩
    simp only [rectMinusTwoCorners, Corner.cells, Set.mem_diff, Set.mem_union, mem_rect,
      Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  rwa [heq] at h

private def tiling_B2 : TileSet_finset LTrominoSet_finset (Fin 8) := ⟨![
  ⟨(), (0, 2), 0⟩,  -- covers (0,2), (0,3), (1,2)
  ⟨(), (1, 0), 0⟩,  -- covers (1,0), (1,1), (2,0)
  ⟨(), (2, 3), 2⟩,  -- covers (1,3), (2,2), (2,3)
  ⟨(), (3, 1), 2⟩,  -- covers (2,1), (3,0), (3,1)
  ⟨(), (3, 3), 3⟩,  -- covers (3,2), (3,3), (4,3)
  ⟨(), (4, 0), 0⟩,  -- covers (4,0), (4,1), (5,0)
  ⟨(), (5, 2), 2⟩,  -- covers (4,2), (5,1), (5,2)
  ⟨(), (6, 3), 2⟩   -- covers (5,3), (6,2), (6,3)
]⟩

private theorem tiling_B2_valid :
    tiling_B2.Valid_finset (rectangle 7 4 \ {(0, 0), (0, 1), (6, 0), (6, 1)}) := by decide

/-- B2: `7 × 4` minus vert@BL and vert@BR (24 cells, 8 trominoes). -/
theorem LTileable_base_7x4_vert_vert :
    LTileable (rectMinusTwoCorners 7 4 .BL .BR .vert .vert) := by
  have h : LTileable_finset (rectangle 7 4 \ {(0, 0), (0, 1), (6, 0), (6, 1)}) :=
    ⟨Fin 8, inferInstance, inferInstance, tiling_B2, tiling_B2_valid⟩
  rw [LTileable_iff] at h
  have heq : (↑(rectangle 7 4 \ {(0, 0), (0, 1), (6, 0), (6, 1)} : Finset Cell) : Set Cell) =
      rectMinusTwoCorners 7 4 .BL .BR .vert .vert := by
    rw [Finset.coe_sdiff]
    have hr := coe_rectangle_eq_rect 7 4
    norm_num at hr
    rw [hr]
    ext ⟨x, y⟩
    simp only [rectMinusTwoCorners, Corner.cells, Set.mem_diff, Set.mem_union, mem_rect,
      Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  rwa [heq] at h

private def tiling_B3 : TileSet_finset LTrominoSet_finset (Fin 15) := ⟨![
  ⟨(), (0, 2), 0⟩,  -- covers (0,2), (0,3), (1,2)
  ⟨(), (0, 4), 0⟩,  -- covers (0,4), (0,5), (1,4)
  ⟨(), (1, 6), 2⟩,  -- covers (0,6), (1,5), (1,6)
  ⟨(), (1, 0), 0⟩,  -- covers (1,0), (1,1), (2,0)
  ⟨(), (2, 3), 1⟩,  -- covers (1,3), (2,3), (2,4)
  ⟨(), (3, 1), 2⟩,  -- covers (2,1), (3,0), (3,1)
  ⟨(), (3, 2), 1⟩,  -- covers (2,2), (3,2), (3,3)
  ⟨(), (2, 5), 0⟩,  -- covers (2,5), (2,6), (3,5)
  ⟨(), (4, 4), 2⟩,  -- covers (3,4), (4,3), (4,4)
  ⟨(), (4, 6), 2⟩,  -- covers (3,6), (4,5), (4,6)
  ⟨(), (4, 0), 0⟩,  -- covers (4,0), (4,1), (5,0)
  ⟨(), (5, 2), 2⟩,  -- covers (4,2), (5,1), (5,2)
  ⟨(), (6, 3), 2⟩,  -- covers (5,3), (6,2), (6,3)
  ⟨(), (5, 4), 0⟩,  -- covers (5,4), (5,5), (6,4)
  ⟨(), (6, 6), 2⟩   -- covers (5,6), (6,5), (6,6)
]⟩

private theorem tiling_B3_valid :
    tiling_B3.Valid_finset (rectangle 7 7 \ {(0, 0), (0, 1), (6, 0), (6, 1)}) := by decide

/-- B3: `7 × 7` minus vert@BL and vert@BR (45 cells, 15 trominoes).
    Needed because its band decomposition `7×4 + 7×3` fails (7×3 is not
    tileable). -/
theorem LTileable_base_7x7_vert_vert :
    LTileable (rectMinusTwoCorners 7 7 .BL .BR .vert .vert) := by
  have h : LTileable_finset (rectangle 7 7 \ {(0, 0), (0, 1), (6, 0), (6, 1)}) :=
    ⟨Fin 15, inferInstance, inferInstance, tiling_B3, tiling_B3_valid⟩
  rw [LTileable_iff] at h
  have heq : (↑(rectangle 7 7 \ {(0, 0), (0, 1), (6, 0), (6, 1)} : Finset Cell) : Set Cell) =
      rectMinusTwoCorners 7 7 .BL .BR .vert .vert := by
    rw [Finset.coe_sdiff]
    have hr := coe_rectangle_eq_rect 7 7
    norm_num at hr
    rw [hr]
    ext ⟨x, y⟩
    simp only [rectMinusTwoCorners, Corner.cells, Set.mem_diff, Set.mem_union, mem_rect,
      Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  rwa [heq] at h

-- ============================================================
-- Rectangle helper (ℤ-valued wrapper around LTileable_rect_iff)
-- ============================================================

/-- An `n × m` rectangle with `3 ∣ n·m`, avoiding the `3 × odd` exceptions,
    is tileable (`n, m ≥ 2`). -/
theorem LTileable_rect_int (n m : ℤ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (h3 : (n * m) % 3 = 0)
    (hexc1 : ¬(n = 3 ∧ m % 2 = 1)) (hexc2 : ¬(m = 3 ∧ n % 2 = 1)) :
    LTileable (rect 0 0 n m) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = n := ⟨n.toNat, by omega⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = m := ⟨m.toNat, by omega⟩
  subst hN; subst hM
  apply LTileable_rect_of_conditions
  unfold RectTileableConditions
  right; right
  have hcast : ((N * M : ℕ) : ℤ) = (N : ℤ) * (M : ℤ) := by push_cast; ring
  rw [← hcast] at h3
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · rintro ⟨h3', hodd⟩
    rw [Nat.odd_iff] at hodd
    exact hexc1 ⟨by omega, by omega⟩
  · rintro ⟨hodd, h3'⟩
    rw [Nat.odd_iff] at hodd
    exact hexc2 ⟨by omega, by omega⟩

/-- Bridge a `decide`-verified Finset tiling certificate to its `Set` region. -/
private lemma LTileable_of_finset_coe {s : Finset Cell} (h : LTileable_finset s)
    {R : Set Cell} (heq : (↑s : Set Cell) = R) :
    LTileable R := by
  rw [LTileable_iff] at h
  rwa [heq] at h

-- ============================================================
-- Peeling the bottom two rows (adjacent pair, 3 ∣ m)
-- ============================================================
--
-- The bottom two rows are tiled by a run of `3 × 2` blocks together with a
-- small gadget at each corner absorbing the defect.  A gadget may "snatch"
-- one or two cells of row `y = 2`; the region above is then an
-- `n × (m - 2)` rectangle with single/horiz defects at its bottom corners,
-- and since `m - 2 ≡ 1 (mod 3)` it is covered by the `m % 3 ≠ 0` results.

/-- Left gadget, single defect, no snatch (width 2, one tromino). -/
private def gadgetL0 : Set Cell := {(0, 1), (1, 0), (1, 1)}

/-- Left gadget, single defect, snatching `(0, 2)` (width 3). -/
private def gadgetL1 : Set Cell := {(0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (2, 1)}

/-- Left gadget, single defect, snatching `(0, 2)` and `(1, 2)` (width 1,
    one tromino; the `3 × 2` blocks then start at `x = 1`). -/
private def gadgetL2 : Set Cell := {(0, 1), (0, 2), (1, 2)}

/-- Right gadget (local coordinates), horiz defect at the right edge,
    snatching the cell above the outer corner (width 2, one tromino). -/
private def gadgetRh : Set Cell := {(0, 1), (1, 1), (1, 2)}

private def tiling_gadgetL0 : TileSet_finset LTrominoSet_finset (Fin 1) :=
  ⟨![⟨(), (1, 1), 2⟩]⟩
private theorem tiling_gadgetL0_valid :
    tiling_gadgetL0.Valid_finset {(0, 1), (1, 0), (1, 1)} := by decide

private def tiling_gadgetL1 : TileSet_finset LTrominoSet_finset (Fin 2) :=
  ⟨![⟨(), (0, 1), 0⟩, ⟨(), (2, 0), 1⟩]⟩
private theorem tiling_gadgetL1_valid :
    tiling_gadgetL1.Valid_finset {(0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (2, 1)} := by decide

private def tiling_gadgetL2 : TileSet_finset LTrominoSet_finset (Fin 1) :=
  ⟨![⟨(), (0, 2), 3⟩]⟩
private theorem tiling_gadgetL2_valid :
    tiling_gadgetL2.Valid_finset {(0, 1), (0, 2), (1, 2)} := by decide

private def tiling_gadgetRh : TileSet_finset LTrominoSet_finset (Fin 1) :=
  ⟨![⟨(), (1, 1), 1⟩]⟩
private theorem tiling_gadgetRh_valid :
    tiling_gadgetRh.Valid_finset {(0, 1), (1, 1), (1, 2)} := by decide

private theorem LTileable_gadgetL0 : LTileable gadgetL0 :=
  LTileable_of_finset_coe
    ⟨Fin 1, inferInstance, inferInstance, tiling_gadgetL0, tiling_gadgetL0_valid⟩
    (by ext ⟨x, y⟩; simp [gadgetL0])

private theorem LTileable_gadgetL1 : LTileable gadgetL1 :=
  LTileable_of_finset_coe
    ⟨Fin 2, inferInstance, inferInstance, tiling_gadgetL1, tiling_gadgetL1_valid⟩
    (by ext ⟨x, y⟩; simp [gadgetL1])

private theorem LTileable_gadgetL2 : LTileable gadgetL2 :=
  LTileable_of_finset_coe
    ⟨Fin 1, inferInstance, inferInstance, tiling_gadgetL2, tiling_gadgetL2_valid⟩
    (by ext ⟨x, y⟩; simp [gadgetL2])

private theorem LTileable_gadgetRh : LTileable gadgetRh :=
  LTileable_of_finset_coe
    ⟨Fin 1, inferInstance, inferInstance, tiling_gadgetRh, tiling_gadgetRh_valid⟩
    (by ext ⟨x, y⟩; simp [gadgetRh])

/-- A `w × 2` rectangle with `3 ∣ w`, `w ≥ 0`, is tileable (including `w = 0`). -/
private lemma LTileable_rect_w2 (w : ℤ) (hw0 : 0 ≤ w) (hw3 : w % 3 = 0) :
    LTileable (rect 0 0 w 2) := by
  rcases eq_or_lt_of_le hw0 with h0 | hpos
  · have hempty : rect 0 0 w 2 = ∅ := by
      ext ⟨x, y⟩; simp only [mem_rect, Set.mem_empty_iff_false, iff_false]; omega
    rw [hempty]; exact Tileable.empty _
  · exact LTileable_rect_int w 2 (by omega) (by norm_num) (by omega) (by omega) (by omega)

/-- The `n × 2` strip with single@BL and vert@BR, `3 ∣ n`: one left gadget plus
    a run of `3 × 2` blocks (the vert defect removes its whole column). -/
private theorem LTileable_adjStrip_single_vert (n : ℤ) (hn : 6 ≤ n) (hn3 : n % 3 = 0) :
    LTileable (rectMinusTwoCorners n 2 .BL .BR .single .vert) := by
  have hid : rectMinusTwoCorners n 2 .BL .BR .single .vert =
      gadgetL0 ∪ translate 2 0 (rect 0 0 (n - 3) 2) := by
    ext ⟨x, y⟩
    simp only [rectMinusTwoCorners, Corner.cells, gadgetL0, Set.mem_diff, Set.mem_union,
      mem_rect, mem_translate, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  rw [hid]
  refine Tileable.union LTileable_gadgetL0
    ((LTileable_rect_w2 (n - 3) (by omega) (by omega)).translate 2 0) ?_
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ h1 h2
  simp only [gadgetL0, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
    mem_translate, mem_rect] at h1 h2
  omega

/-- The bottom band containing single@BL + vert@BR at `n = 6` (B1 plus a clean
    rectangle on top).  Works for any `m ≥ 4` with `m ≡ 1 (mod 3)`. -/
private theorem LTileable_6xm_single_vert (m : ℤ) (hm : 4 ≤ m) :
    LTileable (rectMinusTwoCorners 6 m .BL .BR .single .vert) := by
  exact LTileable_band_bottom 6 m 2 .single .vert (by norm_num) (by omega)
    LTileable_base_6x2_single_vert
    (LTileable_rect_int 6 (m - 2) (by norm_num) (by omega) (by omega) (by omega) (by omega))

/-- Workhorse for the adjacent pair when `m % 3 ≠ 0` (valid down to `m ≥ 4`,
    which is needed after peeling two rows). -/
private theorem LTileable_adjacent_aux (n m : ℤ) (d1 d2 : DefectType)
    (hn : 6 ≤ n) (hm : 4 ≤ m) (hm3 : m % 3 ≠ 0)
    (harea : (n * m - d1.size - d2.size) % 3 = 0) :
    LTileable (rectMinusTwoCorners n m .BL .BR d1 d2) := by
  by_cases hw : minWidth (m % 3) d1 + minWidth (m % 3) d2 ≤ n
  · exact LTileable_twoCorners_vcut n m .BL .BR d1 d2 (Or.inl rfl) (Or.inl rfl)
      (by omega) hm3 hw harea
  · have hm12 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hm12 with hm1 | hm1
    · -- m ≡ 1 (mod 3): the only small-n failures are
      -- n = 6 with {single, vert} and n = 7 with {vert, vert}
      obtain ⟨k, hk⟩ : ∃ k, m = 3 * k + 1 := ⟨m / 3, by omega⟩
      have hnm : n * m = 3 * (n * k) + n := by rw [hk]; ring
      rw [hm1] at hw
      cases d1 with
      | single =>
        cases d2 with
        | single =>
          simp only [DefectType.size_single] at harea
          norm_num [minWidth] at hw
          omega
        | horiz =>
          simp only [DefectType.size_single, DefectType.size_horiz] at harea
          norm_num [minWidth] at hw
          omega
        | vert =>
          simp only [DefectType.size_single, DefectType.size_vert] at harea
          norm_num [minWidth] at hw
          have hn6 : n = 6 := by omega
          subst hn6
          exact LTileable_6xm_single_vert m hm
      | horiz =>
        cases d2 with
        | single =>
          simp only [DefectType.size_horiz, DefectType.size_single] at harea
          norm_num [minWidth] at hw
          omega
        | horiz =>
          simp only [DefectType.size_horiz] at harea
          norm_num [minWidth] at hw
          omega
        | vert =>
          simp only [DefectType.size_horiz, DefectType.size_vert] at harea
          norm_num [minWidth] at hw
          omega
      | vert =>
        cases d2 with
        | single =>
          simp only [DefectType.size_vert, DefectType.size_single] at harea
          norm_num [minWidth] at hw
          have hn6 : n = 6 := by omega
          subst hn6
          apply LTileable_twoCorners_of_flipX (c1 := .BL) (c2 := .BR)
          change LTileable (rectMinusTwoCorners 6 m .BR .BL .vert .single)
          rw [rectMinusTwoCorners_comm]
          exact LTileable_6xm_single_vert m hm
        | horiz =>
          simp only [DefectType.size_vert, DefectType.size_horiz] at harea
          norm_num [minWidth] at hw
          omega
        | vert =>
          simp only [DefectType.size_vert] at harea
          norm_num [minWidth] at hw
          have hn7 : n = 7 := by omega
          subst hn7
          by_cases hm4 : m = 4
          · subst hm4; exact LTileable_base_7x4_vert_vert
          by_cases hm7 : m = 7
          · subst hm7; exact LTileable_base_7x7_vert_vert
          · have hm10 : 10 ≤ m := by omega
            exact LTileable_band_bottom 7 m 4 .vert .vert (by norm_num) (by omega)
              LTileable_base_7x4_vert_vert
              (LTileable_rect_int 7 (m - 4) (by norm_num) (by omega) (by omega)
                (by omega) (by omega))
    · -- m ≡ 2 (mod 3): the minimal widths always fit in n ≥ 6
      obtain ⟨k, hk⟩ : ∃ k, m = 3 * k + 2 := ⟨m / 3, by omega⟩
      have hnm : n * m = 3 * (n * k) + 2 * n := by rw [hk]; ring
      rw [hm1] at hw
      cases d1 <;> cases d2 <;>
          simp only [DefectType.size_single, DefectType.size_horiz,
            DefectType.size_vert] at harea <;>
          norm_num [minWidth] at hw <;>
          omega

/-- Peel core, `d2 = vert`: the bottom two rows form the single/vert strip or
    a snatching left gadget plus `3 × 2` blocks; what remains is an
    `n × (m - 2)` rectangle with at most one bottom-corner defect and
    `m - 2 ≡ 1 (mod 3)`. -/
private theorem LTileable_adjacent_peel_vert (n m : ℤ)
    (hn : 6 ≤ n) (hm : 6 ≤ m) (hm0 : m % 3 = 0) :
    LTileable (rectMinusTwoCorners n m .BL .BR .single .vert) := by
  obtain ⟨c, hc⟩ : ∃ c, m - 2 = 3 * c + 1 := ⟨(m - 3) / 3, by omega⟩
  have hprod : n * (m - 2) = 3 * (n * c) + n := by rw [hc]; ring
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with hr | hr | hr
  · -- 3 ∣ n: bottom strip is the single/vert strip, top is a clean rectangle
    exact LTileable_band_bottom n m 2 .single .vert (by norm_num) (by omega)
      (LTileable_adjStrip_single_vert n hn hr)
      (LTileable_rect_int n (m - 2) (by omega) (by omega) (by omega) (by omega) (by omega))
  · -- n ≡ 1: width-3 gadget snatches (0,2); top has a single defect at BL
    have hid : rectMinusTwoCorners n m .BL .BR .single .vert =
        (gadgetL1 ∪ translate 3 0 (rect 0 0 (n - 4) 2)) ∪
          translate 0 2 (rectMinusOneCorner n (m - 2) .BL .single) := by
      ext ⟨x, y⟩
      simp only [rectMinusTwoCorners, rectMinusOneCorner, Corner.cells, gadgetL1,
        Set.mem_diff, Set.mem_union, mem_rect, mem_translate, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    rw [hid]
    refine Tileable.union
      (Tileable.union LTileable_gadgetL1
        ((LTileable_rect_w2 (n - 4) (by omega) (by omega)).translate 3 0) ?_)
      ((LTileable_oneCorner_single n (m - 2) .BL (by omega) (by omega)
        (by omega)).translate 0 2) ?_
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL1, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
        mem_translate, mem_rect] at h1 h2
      omega
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL1, rectMinusOneCorner, Corner.cells, Set.mem_union, Set.mem_diff,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, mem_translate,
        mem_rect] at h1 h2
      omega
  · -- n ≡ 2: width-1 gadget snatches (0,2),(1,2); top has a horiz defect at BL
    have hid : rectMinusTwoCorners n m .BL .BR .single .vert =
        (gadgetL2 ∪ translate 1 0 (rect 0 0 (n - 2) 2)) ∪
          translate 0 2 (rectMinusOneCorner n (m - 2) .BL .horiz) := by
      ext ⟨x, y⟩
      simp only [rectMinusTwoCorners, rectMinusOneCorner, Corner.cells, gadgetL2,
        Set.mem_diff, Set.mem_union, mem_rect, mem_translate, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      omega
    rw [hid]
    refine Tileable.union
      (Tileable.union LTileable_gadgetL2
        ((LTileable_rect_w2 (n - 2) (by omega) (by omega)).translate 1 0) ?_)
      ((LTileable_oneCorner_size2 n (m - 2) .BL .horiz (by decide) (by omega) (by omega)
        (by omega)).translate 0 2) ?_
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL2, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
        mem_translate, mem_rect] at h1 h2
      omega
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL2, rectMinusOneCorner, Corner.cells, Set.mem_union, Set.mem_diff,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, mem_translate,
        mem_rect] at h1 h2
      omega

/-- Peel core, `d2 = horiz`: as in the `vert` case, with a right gadget
    absorbing the horiz defect. -/
private theorem LTileable_adjacent_peel_horiz (n m : ℤ)
    (hn : 6 ≤ n) (hm : 6 ≤ m) (hm0 : m % 3 = 0) :
    LTileable (rectMinusTwoCorners n m .BL .BR .single .horiz) := by
  obtain ⟨c, hc⟩ : ∃ c, m - 2 = 3 * c + 1 := ⟨(m - 3) / 3, by omega⟩
  have hprod : n * (m - 2) = 3 * (n * c) + n := by rw [hc]; ring
  have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hmod with hr | hr | hr
  · -- 3 ∣ n: width-1 left gadget, right gadget; top is (horiz@BL, single@BR)
    have hid : rectMinusTwoCorners n m .BL .BR .single .horiz =
        ((gadgetL2 ∪ translate 1 0 (rect 0 0 (n - 3) 2)) ∪
          translate (n - 2) 0 gadgetRh) ∪
          translate 0 2 (rectMinusTwoCorners n (m - 2) .BL .BR .horiz .single) := by
      ext ⟨x, y⟩
      simp only [rectMinusTwoCorners, Corner.cells, gadgetL2, gadgetRh,
        Set.mem_diff, Set.mem_union, mem_rect, mem_translate, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      by_cases hy : y < 2 <;> omega
    rw [hid]
    refine Tileable.union
      (Tileable.union
        (Tileable.union LTileable_gadgetL2
          ((LTileable_rect_w2 (n - 3) (by omega) (by omega)).translate 1 0) ?_)
        (LTileable_gadgetRh.translate (n - 2) 0) ?_)
      ((LTileable_adjacent_aux n (m - 2) .horiz .single hn (by omega) (by omega)
        (by simp only [DefectType.size_horiz, DefectType.size_single]; omega)).translate 0 2) ?_
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL2, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
        mem_translate, mem_rect] at h1 h2
      omega
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL2, gadgetRh, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq, mem_translate, mem_rect] at h1 h2
      omega
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL2, gadgetRh, rectMinusTwoCorners, Corner.cells, Set.mem_union,
        Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
        mem_translate, mem_rect] at h1 h2
      omega
  · -- n ≡ 1: width-2 left gadget, right gadget; top has a single defect at BR
    have hid : rectMinusTwoCorners n m .BL .BR .single .horiz =
        ((gadgetL0 ∪ translate 2 0 (rect 0 0 (n - 4) 2)) ∪
          translate (n - 2) 0 gadgetRh) ∪
          translate 0 2 (rectMinusOneCorner n (m - 2) .BR .single) := by
      ext ⟨x, y⟩
      simp only [rectMinusTwoCorners, rectMinusOneCorner, Corner.cells, gadgetL0, gadgetRh,
        Set.mem_diff, Set.mem_union, mem_rect, mem_translate, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      by_cases hy : y < 2 <;> omega
    rw [hid]
    refine Tileable.union
      (Tileable.union
        (Tileable.union LTileable_gadgetL0
          ((LTileable_rect_w2 (n - 4) (by omega) (by omega)).translate 2 0) ?_)
        (LTileable_gadgetRh.translate (n - 2) 0) ?_)
      ((LTileable_oneCorner_single n (m - 2) .BR (by omega) (by omega)
        (by omega)).translate 0 2) ?_
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL0, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
        mem_translate, mem_rect] at h1 h2
      omega
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL0, gadgetRh, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq, mem_translate, mem_rect] at h1 h2
      omega
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL0, gadgetRh, rectMinusOneCorner, Corner.cells, Set.mem_union,
        Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
        mem_translate, mem_rect] at h1 h2
      omega
  · -- n ≡ 2: width-3 left gadget, right gadget; top is (single@BL, single@BR)
    have hid : rectMinusTwoCorners n m .BL .BR .single .horiz =
        ((gadgetL1 ∪ translate 3 0 (rect 0 0 (n - 5) 2)) ∪
          translate (n - 2) 0 gadgetRh) ∪
          translate 0 2 (rectMinusTwoCorners n (m - 2) .BL .BR .single .single) := by
      ext ⟨x, y⟩
      simp only [rectMinusTwoCorners, Corner.cells, gadgetL1, gadgetRh,
        Set.mem_diff, Set.mem_union, mem_rect, mem_translate, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      by_cases hy : y < 2 <;> omega
    rw [hid]
    refine Tileable.union
      (Tileable.union
        (Tileable.union LTileable_gadgetL1
          ((LTileable_rect_w2 (n - 5) (by omega) (by omega)).translate 3 0) ?_)
        (LTileable_gadgetRh.translate (n - 2) 0) ?_)
      ((LTileable_adjacent_aux n (m - 2) .single .single hn (by omega) (by omega)
        (by simp only [DefectType.size_single]; omega)).translate 0 2) ?_
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL1, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
        mem_translate, mem_rect] at h1 h2
      omega
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL1, gadgetRh, Set.mem_union, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq, mem_translate, mem_rect] at h1 h2
      omega
    · rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [gadgetL1, gadgetRh, rectMinusTwoCorners, Corner.cells, Set.mem_union,
        Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
        mem_translate, mem_rect] at h1 h2
      omega

/-- Core of the `3 ∣ m` adjacent case (`d1 = single` WLOG): peel the bottom two
    rows as corner gadgets plus `3 × 2` blocks; what remains is an
    `n × (m - 2)` rectangle with at most single/horiz bottom-corner defects,
    and `m - 2 ≡ 1 (mod 3)`. -/
private theorem LTileable_adjacent_peel (n m : ℤ) (d2 : DefectType) (hd2 : d2 ≠ .single)
    (hn : 6 ≤ n) (hm : 6 ≤ m) (hm0 : m % 3 = 0) :
    LTileable (rectMinusTwoCorners n m .BL .BR .single d2) := by
  cases d2 with
  | single => exact absurd rfl hd2
  | vert => exact LTileable_adjacent_peel_vert n m hn hm hm0
  | horiz => exact LTileable_adjacent_peel_horiz n m hn hm hm0

/-- Adjacent pair with `3 ∣ m`: peel the bottom two rows (no induction). -/
theorem LTileable_adjacent_H5 (n m : ℤ) (d1 d2 : DefectType)
    (hn : 6 ≤ n) (hm : 6 ≤ m) (hm0 : m % 3 = 0)
    (harea : (n * m - d1.size - d2.size) % 3 = 0) :
    LTileable (rectMinusTwoCorners n m .BL .BR d1 d2) := by
  have hsz : d1.size + d2.size = 3 := by
    obtain ⟨b, hb⟩ : ∃ b, m = 3 * b := ⟨m / 3, by omega⟩
    have hnm : n * m = 3 * (n * b) := by rw [hb]; ring
    have h1 := d1.size_pos; have h2 := d1.size_le_two
    have h3 := d2.size_pos; have h4 := d2.size_le_two
    omega
  cases d1 with
  | single =>
    have hd2 : d2 ≠ .single := by
      intro h; subst h; simp [DefectType.size] at hsz
    exact LTileable_adjacent_peel n m d2 hd2 hn hm hm0
  | horiz =>
    have hd2 : d2 = .single := by
      cases d2 <;> simp [DefectType.size] at hsz ⊢
    subst hd2
    apply LTileable_twoCorners_of_flipX (c1 := .BL) (c2 := .BR)
    change LTileable (rectMinusTwoCorners n m .BR .BL .horiz .single)
    rw [rectMinusTwoCorners_comm]
    exact LTileable_adjacent_peel n m .horiz (by decide) hn hm hm0
  | vert =>
    have hd2 : d2 = .single := by
      cases d2 <;> simp [DefectType.size] at hsz ⊢
    subst hd2
    apply LTileable_twoCorners_of_flipX (c1 := .BL) (c2 := .BR)
    change LTileable (rectMinusTwoCorners n m .BR .BL .vert .single)
    rw [rectMinusTwoCorners_comm]
    exact LTileable_adjacent_peel n m .vert (by decide) hn hm hm0

/-- Sufficiency for the adjacent pair (BL, BR), `n, m ≥ 6`. -/
theorem LTileable_adjacent (n m : ℤ) (d1 d2 : DefectType)
    (hn : 6 ≤ n) (hm : 6 ≤ m)
    (harea : (n * m - d1.size - d2.size) % 3 = 0) :
    LTileable (rectMinusTwoCorners n m .BL .BR d1 d2) := by
  by_cases hm3 : m % 3 = 0
  · exact LTileable_adjacent_H5 n m d1 d2 hn hm hm3 harea
  · exact LTileable_adjacent_aux n m d1 d2 hn (by omega) hm3 harea

-- ============================================================
-- Canonical case: diagonal pair (BL, TR)
-- ============================================================

/-- Diagonal pair at `n = 6`, `m ≡ 1 (mod 3)`, defects single@BL + vert@TR
    (the one diagonal shape the vertical cut cannot fit): peel the bottom two
    rows as `gadgetL1` (snatching `(0, 2)`) plus one `3 × 2` block.  The
    remainder is the same shape with height `m - 2 ≡ 2 (mod 3)`, where the
    vertical cut fits exactly (widths `2 + 4 = 6`); at `m = 4` the remainder
    is the base strip `B1`. -/
private theorem LTileable_diagonal_D1_sv (m : ℤ) (hm : 4 ≤ m) (hm1 : m % 3 = 1) :
    LTileable (rectMinusTwoCorners 6 m .BL .TR .single .vert) := by
  have hid : rectMinusTwoCorners 6 m .BL .TR .single .vert =
      (gadgetL1 ∪ translate 3 0 (rect 0 0 3 2)) ∪
        translate 0 2 (rectMinusTwoCorners 6 (m - 2) .BL .TR .single .vert) := by
    ext ⟨x, y⟩
    simp only [rectMinusTwoCorners, Corner.cells, gadgetL1, Set.mem_diff, Set.mem_union,
      mem_rect, mem_translate, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have hrem : LTileable (rectMinusTwoCorners 6 (m - 2) .BL .TR .single .vert) := by
    by_cases hm4 : m = 4
    · subst hm4
      norm_num
      have h2 : rectMinusTwoCorners 6 2 .BL .TR .single .vert =
          rectMinusTwoCorners 6 2 .BL .BR .single .vert := by
        ext ⟨x, y⟩
        simp only [rectMinusTwoCorners, Corner.cells, Set.mem_diff, Set.mem_union, mem_rect,
          Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        omega
      rw [h2]
      exact LTileable_base_6x2_single_vert
    · have h2 : (m - 2) % 3 = 2 := by omega
      exact LTileable_twoCorners_vcut 6 (m - 2) .BL .TR .single .vert
        (Or.inl rfl) (Or.inr rfl) (by omega) (by omega)
        (by rw [h2]; norm_num [minWidth])
        (by simp only [DefectType.size_single, DefectType.size_vert]; omega)
  rw [hid]
  refine Tileable.union
    (Tileable.union LTileable_gadgetL1
      ((LTileable_rect_w2 3 (by norm_num) (by norm_num)).translate 3 0) ?_)
    (hrem.translate 0 2) ?_
  · rw [Set.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [gadgetL1, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
      mem_translate, mem_rect] at h1 h2
    omega
  · rw [Set.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [gadgetL1, rectMinusTwoCorners, Corner.cells, Set.mem_union, Set.mem_diff,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, mem_translate,
      mem_rect] at h1 h2
    omega

/-- Workhorse for the diagonal pair when `m % 3 ≠ 0` (valid down to `m ≥ 4`,
    which is needed after peeling two rows). -/
private theorem LTileable_diagonal_aux (n m : ℤ) (d1 d2 : DefectType)
    (hn : 6 ≤ n) (hm : 4 ≤ m) (hm3 : m % 3 ≠ 0)
    (harea : (n * m - d1.size - d2.size) % 3 = 0) :
    LTileable (rectMinusTwoCorners n m .BL .TR d1 d2) := by
  by_cases hw : minWidth (m % 3) d1 + minWidth (m % 3) d2 ≤ n
  · exact LTileable_twoCorners_vcut n m .BL .TR d1 d2 (Or.inl rfl) (Or.inr rfl)
      (by omega) hm3 hw harea
  · have hm12 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hm12 with hm1 | hm1
    · -- m ≡ 1 (mod 3): small-n leftovers are {single, vert} at n = 6 (peel, D1)
      -- and {vert, vert} at n = 7 (transpose: horiz has width 2)
      obtain ⟨k, hk⟩ : ∃ k, m = 3 * k + 1 := ⟨m / 3, by omega⟩
      have hnm : n * m = 3 * (n * k) + n := by rw [hk]; ring
      rw [hm1] at hw
      cases d1 with
      | single =>
        cases d2 with
        | single =>
          simp only [DefectType.size_single] at harea
          norm_num [minWidth] at hw
          omega
        | horiz =>
          simp only [DefectType.size_single, DefectType.size_horiz] at harea
          norm_num [minWidth] at hw
          omega
        | vert =>
          simp only [DefectType.size_single, DefectType.size_vert] at harea
          norm_num [minWidth] at hw
          have hn6 : n = 6 := by omega
          subst hn6
          exact LTileable_diagonal_D1_sv m hm hm1
      | horiz =>
        cases d2 with
        | single =>
          simp only [DefectType.size_horiz, DefectType.size_single] at harea
          norm_num [minWidth] at hw
          omega
        | horiz =>
          simp only [DefectType.size_horiz] at harea
          norm_num [minWidth] at hw
          omega
        | vert =>
          simp only [DefectType.size_horiz, DefectType.size_vert] at harea
          norm_num [minWidth] at hw
          omega
      | vert =>
        cases d2 with
        | single =>
          simp only [DefectType.size_vert, DefectType.size_single] at harea
          norm_num [minWidth] at hw
          have hn6 : n = 6 := by omega
          subst hn6
          -- rotate 180° (flipX ∘ flipY) and swap the defect arguments to
          -- reach single@BL + vert@TR
          apply LTileable_twoCorners_of_flipX (c1 := .BL) (c2 := .TR)
          change LTileable (rectMinusTwoCorners 6 m .BR .TL .vert .single)
          apply LTileable_twoCorners_of_flipY (c1 := .BR) (c2 := .TL)
          change LTileable (rectMinusTwoCorners 6 m .TR .BL .vert .single)
          rw [rectMinusTwoCorners_comm]
          exact LTileable_diagonal_D1_sv m hm hm1
        | horiz =>
          simp only [DefectType.size_vert, DefectType.size_horiz] at harea
          norm_num [minWidth] at hw
          omega
        | vert =>
          simp only [DefectType.size_vert] at harea
          norm_num [minWidth] at hw
          have hn7 : n = 7 := by omega
          subst hn7
          apply LTileable_twoCorners_of_transpose
          change LTileable (rectMinusTwoCorners m 7 .BL .TR .horiz .horiz)
          exact LTileable_twoCorners_vcut m 7 .BL .TR .horiz .horiz
            (Or.inl rfl) (Or.inr rfl) (by norm_num) (by norm_num)
            (by norm_num [minWidth]; omega)
            (by simp only [DefectType.size_horiz]; omega)
    · -- m ≡ 2 (mod 3): the minimal widths always fit in n ≥ 6
      obtain ⟨k, hk⟩ : ∃ k, m = 3 * k + 2 := ⟨m / 3, by omega⟩
      have hnm : n * m = 3 * (n * k) + 2 * n := by rw [hk]; ring
      rw [hm1] at hw
      cases d1 <;> cases d2 <;>
          simp only [DefectType.size_single, DefectType.size_horiz,
            DefectType.size_vert] at harea <;>
          norm_num [minWidth] at hw <;>
          omega

/-- Diagonal pair with `3 ∣ n`, `3 ∣ m`, defects single@BL + vert@TR: peel the
    bottom two rows around the single defect (`gadgetL1` snatches `(0, 2)`);
    the remainder has height `≡ 1 (mod 3)` and falls to the `m % 3 ≠ 0`
    workhorse. -/
private theorem LTileable_diagonal_sv (n m : ℤ) (hn : 6 ≤ n) (hm : 6 ≤ m)
    (hn3 : n % 3 = 0) (hm0 : m % 3 = 0) :
    LTileable (rectMinusTwoCorners n m .BL .TR .single .vert) := by
  have hid : rectMinusTwoCorners n m .BL .TR .single .vert =
      (gadgetL1 ∪ translate 3 0 (rect 0 0 (n - 3) 2)) ∪
        translate 0 2 (rectMinusTwoCorners n (m - 2) .BL .TR .single .vert) := by
    ext ⟨x, y⟩
    simp only [rectMinusTwoCorners, Corner.cells, gadgetL1, Set.mem_diff, Set.mem_union,
      mem_rect, mem_translate, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  rw [hid]
  refine Tileable.union
    (Tileable.union LTileable_gadgetL1
      ((LTileable_rect_w2 (n - 3) (by omega) (by omega)).translate 3 0) ?_)
    ((LTileable_diagonal_aux n (m - 2) .single .vert hn (by omega) (by omega)
      (by
        obtain ⟨j, hj⟩ : ∃ j, n = 3 * j := ⟨n / 3, by omega⟩
        have hprod : n * (m - 2) = 3 * (j * (m - 2)) := by rw [hj]; ring
        simp only [DefectType.size_single, DefectType.size_vert]
        omega)).translate 0 2) ?_
  · rw [Set.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [gadgetL1, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
      mem_translate, mem_rect] at h1 h2
    omega
  · rw [Set.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [gadgetL1, rectMinusTwoCorners, Corner.cells, Set.mem_union, Set.mem_diff,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, mem_translate,
      mem_rect] at h1 h2
    omega

/-- Diagonal pair with `3 ∣ n` and `3 ∣ m`: the defect sizes sum to 3, so up
    to symmetry the defects are single@BL + vert@TR; peel the bottom two rows
    (no induction). -/
theorem LTileable_diagonal_H4 (n m : ℤ) (d1 d2 : DefectType)
    (hn : 6 ≤ n) (hm : 6 ≤ m) (hn0 : n % 3 = 0) (hm0 : m % 3 = 0)
    (harea : (n * m - d1.size - d2.size) % 3 = 0) :
    LTileable (rectMinusTwoCorners n m .BL .TR d1 d2) := by
  have hsz : d1.size + d2.size = 3 := by
    obtain ⟨b, hb⟩ : ∃ b, m = 3 * b := ⟨m / 3, by omega⟩
    have hnm : n * m = 3 * (n * b) := by rw [hb]; ring
    have h1 := d1.size_pos; have h2 := d1.size_le_two
    have h3 := d2.size_pos; have h4 := d2.size_le_two
    omega
  cases d1 with
  | single =>
    cases d2 with
    | single => simp [DefectType.size] at hsz
    | horiz =>
      -- transpose to single@BL + vert@TR in the `m × n` rectangle
      apply LTileable_twoCorners_of_transpose
      change LTileable (rectMinusTwoCorners m n .BL .TR .single .vert)
      exact LTileable_diagonal_sv m n hm hn hm0 hn0
    | vert => exact LTileable_diagonal_sv n m hn hm hn0 hm0
  | horiz =>
    cases d2 with
    | single =>
      -- rotate 180° (flipX ∘ flipY), swap the defect arguments, transpose
      apply LTileable_twoCorners_of_flipX (c1 := .BL) (c2 := .TR)
      change LTileable (rectMinusTwoCorners n m .BR .TL .horiz .single)
      apply LTileable_twoCorners_of_flipY (c1 := .BR) (c2 := .TL)
      change LTileable (rectMinusTwoCorners n m .TR .BL .horiz .single)
      rw [rectMinusTwoCorners_comm]
      apply LTileable_twoCorners_of_transpose
      change LTileable (rectMinusTwoCorners m n .BL .TR .single .vert)
      exact LTileable_diagonal_sv m n hm hn hm0 hn0
    | horiz => simp [DefectType.size] at hsz
    | vert => simp [DefectType.size] at hsz
  | vert =>
    cases d2 with
    | single =>
      -- rotate 180° (flipX ∘ flipY) and swap the defect arguments
      apply LTileable_twoCorners_of_flipX (c1 := .BL) (c2 := .TR)
      change LTileable (rectMinusTwoCorners n m .BR .TL .vert .single)
      apply LTileable_twoCorners_of_flipY (c1 := .BR) (c2 := .TL)
      change LTileable (rectMinusTwoCorners n m .TR .BL .vert .single)
      rw [rectMinusTwoCorners_comm]
      exact LTileable_diagonal_sv n m hn hm hn0 hm0
    | horiz => simp [DefectType.size] at hsz
    | vert => simp [DefectType.size] at hsz

/-- Sufficiency for the diagonal pair (BL, TR), `n, m ≥ 6`. -/
theorem LTileable_diagonal (n m : ℤ) (d1 d2 : DefectType)
    (hn : 6 ≤ n) (hm : 6 ≤ m)
    (harea : (n * m - d1.size - d2.size) % 3 = 0) :
    LTileable (rectMinusTwoCorners n m .BL .TR d1 d2) := by
  by_cases hm3 : m % 3 = 0
  · by_cases hn3 : n % 3 = 0
    · exact LTileable_diagonal_H4 n m d1 d2 hn hm hn3 hm3 harea
    · -- transpose: the diagonal pair stays diagonal, and now the second
      -- dimension is ≢ 0 (mod 3)
      apply LTileable_twoCorners_of_transpose
      change LTileable (rectMinusTwoCorners m n .BL .TR d1.transpose d2.transpose)
      apply LTileable_diagonal_aux m n d1.transpose d2.transpose hm (by omega) hn3
      simp only [DefectType.size_transpose]
      rw [mul_comm]
      exact harea
  · exact LTileable_diagonal_aux n m d1 d2 hn (by omega) hm3 harea

-- ============================================================
-- Main theorem
-- ============================================================

/-- Sufficiency, all corner pairs: reduce to (BL, BR) or (BL, TR) by symmetry. -/
theorem LTileable_rectMinusTwoCorners_of_area (n m : ℤ) (c1 c2 : Corner)
    (d1 d2 : DefectType) (hn : 6 ≤ n) (hm : 6 ≤ m) (hc : c1 ≠ c2)
    (harea : (n * m - d1.size - d2.size) % 3 = 0) :
    LTileable (rectMinusTwoCorners n m c1 c2 d1 d2) := by
  have hareaT : (m * n - d1.transpose.size - d2.transpose.size) % 3 = 0 := by
    simp only [DefectType.size_transpose]
    rw [mul_comm]
    exact harea
  have hareaT' : (m * n - d2.transpose.size - d1.transpose.size) % 3 = 0 := by
    have h1 := d1.size_pos
    have h2 := d2.size_pos
    omega
  have harea' : (n * m - d2.size - d1.size) % 3 = 0 := by
    have h1 := d1.size_pos
    have h2 := d2.size_pos
    omega
  cases c1 <;> cases c2 <;> (try exact absurd rfl hc)
  -- (BL, BR)
  · exact LTileable_adjacent n m d1 d2 hn hm harea
  -- (BL, TL): transpose gives (BL, BR)
  · exact LTileable_twoCorners_of_transpose
      (LTileable_adjacent m n d1.transpose d2.transpose hm hn hareaT)
  -- (BL, TR)
  · exact LTileable_diagonal n m d1 d2 hn hm harea
  -- (BR, BL): swap defects
  · rw [rectMinusTwoCorners_comm]
    exact LTileable_adjacent n m d2 d1 hn hm harea'
  -- (BR, TL): flipX gives (BL, TR)
  · exact LTileable_twoCorners_of_flipX
      (LTileable_diagonal n m d1 d2 hn hm harea)
  -- (BR, TR): transpose gives (TL, TR), then flipY gives (BL, BR)
  · apply LTileable_twoCorners_of_transpose
    change LTileable (rectMinusTwoCorners m n .TL .TR d1.transpose d2.transpose)
    exact LTileable_twoCorners_of_flipY (c1 := Corner.TL) (c2 := Corner.TR)
      (LTileable_adjacent m n d1.transpose d2.transpose hm hn hareaT)
  -- (TL, BL): swap defects, then transpose
  · rw [rectMinusTwoCorners_comm]
    exact LTileable_twoCorners_of_transpose
      (LTileable_adjacent m n d2.transpose d1.transpose hm hn hareaT')
  -- (TL, BR): flipX gives (TR, BL); instead swap defects then flipX gives (BL, TR)
  · rw [rectMinusTwoCorners_comm]
    exact LTileable_twoCorners_of_flipX
      (LTileable_diagonal n m d2 d1 hn hm harea')
  -- (TL, TR): flipY gives (BL, BR)
  · exact LTileable_twoCorners_of_flipY (c1 := Corner.TL) (c2 := Corner.TR)
      (LTileable_adjacent n m d1 d2 hn hm harea)
  -- (TR, BL): swap defects gives (BL, TR)
  · rw [rectMinusTwoCorners_comm]
    exact LTileable_diagonal n m d2 d1 hn hm harea'
  -- (TR, BR): swap, transpose, flipY
  · rw [rectMinusTwoCorners_comm]
    apply LTileable_twoCorners_of_transpose
    change LTileable (rectMinusTwoCorners m n .TL .TR d2.transpose d1.transpose)
    exact LTileable_twoCorners_of_flipY (c1 := Corner.TL) (c2 := Corner.TR)
      (LTileable_adjacent m n d2.transpose d1.transpose hm hn hareaT')
  -- (TR, TL): swap, flipY
  · rw [rectMinusTwoCorners_comm]
    exact LTileable_twoCorners_of_flipY (c1 := Corner.TL) (c2 := Corner.TR)
      (LTileable_adjacent n m d2 d1 hn hm harea')

/-- **A rectangle with two corner defects, each of size 1 or 2, is L-tileable
    iff its area is a multiple of 3** (for `n, m ≥ 6` and distinct corners). -/
theorem LTileable_rectMinusTwoCorners_iff (n m : ℤ) (c1 c2 : Corner)
    (d1 d2 : DefectType) (hn : 6 ≤ n) (hm : 6 ≤ m) (hc : c1 ≠ c2) :
    LTileable (rectMinusTwoCorners n m c1 c2 d1 d2) ↔
      3 ∣ (rectMinusTwoCorners n m c1 c2 d1 d2).ncard := by
  constructor
  · exact LTileable_rectMinusTwoCorners_area n m c1 c2 d1 d2
  · intro h
    apply LTileable_rectMinusTwoCorners_of_area n m c1 c2 d1 d2 hn hm hc
    have hcard := rectMinusTwoCorners_ncard n m c1 c2 d1 d2 (by omega) (by omega) hc
    rw [← hcard]
    omega
