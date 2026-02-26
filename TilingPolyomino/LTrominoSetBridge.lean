/-
# Bridge between Finset and Set frameworks for L-tromino tilings

`LProtoset_set` (from LTrominoSet) equals the canonical `toSetProtoset lTrominoSet`,
so the bridge reduces to a single rewrite + `Tileable_iff_toSet`.

Main results:
- `lTromino_coe_eq_LShape_set`: coercion lemma `↑lTromino = LShape_cells`
- `coe_rectangle_eq_rect`: coercion lemma `↑(rectangle n m) = rect 0 0 n m`
- `LTileable_iff_set`: `LTileable R ↔ SetTileable ↑R LProtoset_set`
- `LTileable_rect_iff_set`: full rectangle characterization in the Set framework
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
