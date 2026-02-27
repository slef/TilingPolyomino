/-
# Bridge between Finset and Set frameworks for L-tromino tilings

`LProtoset_set` (from LTrominoSet) equals the canonical `toSetProtoset lTrominoSet`,
so the bridge reduces to a single rewrite + `Tileable_iff_toSet`.

Main results:
- `lTromino_coe_eq_LShape_set`: coercion lemma `↑lTromino = LShape_cells`
- `coe_rectangle_eq_rect`: coercion lemma `↑(rectangle n m) = rect 0 0 n m`
- `LTileable_iff_set`: `LTileable R ↔ SetTileable ↑R LProtoset_set`
- `LTileable_rect_iff_set`: full rectangle characterization in the Set framework
- `LTileable_rectMinusCorner_iff_set`: Ash–Golomb's dog-eared rectangle theorem (Set framework)
- `LTileable_rectMinus2Corner_set`: two-corner-deficient rectangle theorem (Set framework)
-/

import TilingPolyomino.LTromino
import TilingPolyomino.LTrominoSet

open Set Function

/-- The lTromino Finset coerces to LShape_cells as a Set -/
lemma lTromino_coe_eq_LShape_set : (↑(lTromino : Finset Cell) : Set Cell) = LShape_cells := by
  ext c
  constructor
  · intro hm
    rw [Finset.mem_coe, Prototile.mem_coe] at hm
    simp only [lTromino, List.mem_cons, List.mem_nil_iff, or_false] at hm
    simp only [LShape_cells, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hm
  · intro hm
    rw [Finset.mem_coe, Prototile.mem_coe]
    simp only [lTromino, List.mem_cons, List.mem_nil_iff, or_false]
    simp only [LShape_cells, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact hm

/-- Coercion of rectangle (Finset) to rect (Set) -/
lemma coe_rectangle_eq_rect (n m : ℕ) :
    (↑(rectangle n m) : Set Cell) = rect 0 0 n m := by
  ext ⟨x, y⟩
  simp only [Finset.mem_coe, mem_rectangle, mem_rect]

private lemma lTrominoSet_nonempty (i : Unit) : (lTrominoSet i : Finset Cell).Nonempty :=
  ⟨(0, 0), by simp [lTrominoSet, lTromino]⟩

/-- `LProtoset_set` equals the canonical `toSetProtoset lTrominoSet`. -/
private lemma LProtoset_set_eq_toSet :
    LProtoset_set = toSetProtoset lTrominoSet lTrominoSet_nonempty := by
  funext ⟨⟩; exact SetPrototile.ext lTromino_coe_eq_LShape_set.symm

/-- **Bridge Theorem**: `LTileable` and `SetTileable LProtoset_set` coincide on finite sets -/
theorem LTileable_iff_set (R : Finset Cell) :
    LTileable R ↔ SetTileable (↑R : Set Cell) LProtoset_set := by
  rw [LProtoset_set_eq_toSet]
  exact Tileable_iff_toSet lTrominoSet R lTrominoSet_nonempty

/-- The full characterization of L-tileable rectangles in the Set framework.
    Follows from `rect_tileable_iff` (Finset) via the bridge theorem. -/
theorem LTileable_rect_iff_set (n m : ℕ) :
    SetTileable (rect 0 0 (n : ℤ) m) LProtoset_set ↔ RectTileableConditions n m := by
  rw [← coe_rectangle_eq_rect, ← LTileable_iff_set]
  exact rect_tileable_iff n m

-- ============================================================
-- Priority 2: rectMinusCorner in the Set framework
-- ============================================================

/-- Helper: integer coordinates of the top-right corner when n,m ≥ 1. -/
private lemma cornerTR_cast (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) :
    cornerTR n m = ((n : ℤ) - 1, (m : ℤ) - 1) := by
  simp only [cornerTR, Prod.mk.injEq]
  exact ⟨by exact_mod_cast Nat.cast_sub hn, by exact_mod_cast Nat.cast_sub hm⟩

/-- Coercion: `rectangleMinusCorner n m` as a Set equals `rect 0 0 n m \ {(n-1, m-1)}`. -/
lemma coe_rectangleMinusCorner_eq (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) :
    (↑(rectangleMinusCorner n m) : Set Cell) =
    rect 0 0 (n : ℤ) m \ {((n : ℤ) - 1, (m : ℤ) - 1)} := by
  rw [rectangleMinusCorner, Finset.coe_erase, coe_rectangle_eq_rect, cornerTR_cast n m hn hm]

/-- **Set framework version of Ash–Golomb's three-cornered rectangle theorem.**
    `rect 0 0 n m \ {(n-1, m-1)}` is L-tileable iff `(n * m - 1) % 3 = 0`,
    for n, m ≥ 2. -/
theorem LTileable_rectMinusCorner_iff_set (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2) :
    LTileable_set (rect 0 0 (n : ℤ) m \ {((n : ℤ) - 1, (m : ℤ) - 1)}) ↔
    (n * m - 1) % 3 = 0 := by
  simp only [LTileable_set, ← coe_rectangleMinusCorner_eq n m (by omega) (by omega),
             ← LTileable_iff_set]
  exact rectMinusCorner_tileable_iff n m hn hm

-- ============================================================
-- Priority 3: rectMinus2Corner in the Set framework
-- ============================================================

/-- Helper: integer coordinates of the second top-right corner when n ≥ 2, m ≥ 1. -/
private lemma cornerTR2_cast (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 1) :
    cornerTR2 n m = ((n : ℤ) - 2, (m : ℤ) - 1) := by
  simp only [cornerTR2, Prod.mk.injEq]
  exact ⟨by exact_mod_cast Nat.cast_sub (show 2 ≤ n from hn),
         by exact_mod_cast Nat.cast_sub hm⟩

/-- Coercion: `rectangleMinus2Corner n m` as a Set equals `rect 0 0 n m \ {(n-1, m-1), (n-2, m-1)}`.
    Here `{a, b}` denotes `{a} ∪ {b}`. -/
lemma coe_rectangleMinus2Corner_eq (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 1) :
    (↑(rectangleMinus2Corner n m) : Set Cell) =
    rect 0 0 (n : ℤ) m \ ({((n : ℤ) - 1, (m : ℤ) - 1)} ∪ {((n : ℤ) - 2, (m : ℤ) - 1)}) := by
  rw [rectangleMinus2Corner, Finset.coe_erase, Finset.coe_erase,
      coe_rectangle_eq_rect,
      cornerTR_cast n m (by omega) hm, cornerTR2_cast n m hn hm]
  rw [Set.diff_diff, Set.union_comm]

/-- **Set framework version of the two-corner-deficient rectangle theorem.**
    `rect 0 0 n m \ {(n-1, m-1), (n-2, m-1)}` is L-tileable when `n * m % 3 = 2`,
    for n, m ≥ 3. -/
theorem LTileable_rectMinus2Corner_set (n m : ℕ) (hn : n ≥ 3) (hm : m ≥ 3)
    (hmod : n * m % 3 = 2) :
    LTileable_set (rect 0 0 (n : ℤ) m \ ({((n : ℤ) - 1, (m : ℤ) - 1)} ∪
                                          {((n : ℤ) - 2, (m : ℤ) - 1)})) := by
  rw [← coe_rectangleMinus2Corner_eq n m (by omega) (by omega)]
  rw [LTileable_set, ← LTileable_iff_set]
  exact rectMinus2Corner_tileable_of_area_mod2 n m hn hm hmod
