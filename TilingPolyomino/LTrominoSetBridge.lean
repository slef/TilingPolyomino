/-
# Bridge between Finset and Set frameworks for L-tromino tilings

Uses the generic `Tileable_iff_set` theorem from TilingSet.lean to derive
the L-tromino bridge as a one-line corollary.

Main results:
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

/-- lTrominoSet is compatible with LProtoset_set -/
private lemma lTrominoSet_compat : ProtosetCompatible lTrominoSet LProtoset_set :=
  fun _ => lTromino_coe_eq_LShape_set.symm

/-- Coercion of rectangle (Finset) to rect (Set) -/
lemma coe_rectangle_eq_rect (n m : ℕ) :
    (↑(rectangle n m) : Set Cell) = rect 0 0 n m := by
  ext ⟨x, y⟩
  simp only [Finset.mem_coe, mem_rectangle, mem_rect]

/-- **Bridge Theorem**: `LTileable` and `SetTileable LProtoset_set` coincide on finite sets -/
theorem LTileable_iff_set (R : Finset Cell) :
    LTileable R ↔ SetTileable (↑R : Set Cell) LProtoset_set :=
  Tileable_iff_set lTrominoSet LProtoset_set lTrominoSet_compat R

/-- The full characterization of L-tileable rectangles in the Set framework.
    Follows from `rect_tileable_iff` (Finset) via the bridge theorem. -/
theorem LTileable_rect_iff_set (n m : ℕ) :
    SetTileable (rect 0 0 (n : ℤ) m) LProtoset_set ↔ RectTileableConditions n m := by
  rw [← coe_rectangle_eq_rect, ← LTileable_iff_set]
  exact rect_tileable_iff n m
