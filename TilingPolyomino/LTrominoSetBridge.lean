/-
# Bridge between Finset and Set frameworks for L-tromino tilings

`LProtoset_set` (from LTrominoSet) equals the canonical `toProtoset_set lTrominoSet`,
so the bridge reduces to a single rewrite + `Tileable_iff_to_set`.

Main results:
- `lTromino_coe_eq_LShape_set`: coercion lemma `↑lTromino = LShape_cells`
- `coe_rectangle_eq_rect`: coercion lemma `↑(rectangle n m) = rect 0 0 n m`
- `LTileable_iff_set`: `LTileable R ↔ Tileable_set ↑R LProtoset_set`
- `LTileable_rect_iff_set`: full rectangle characterization in the Set framework
- `LTileable_rectMinusCorner_iff_set`: proved natively in LTrominoSet.lean (bridge copy removed)
- `LTileable_rectMinus2Corner_set`: proved natively in LTrominoSet.lean (bridge copy removed)
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

private lemma lTrominoSet_nonempty (i : Unit) : (lTrominoSet i : Finset Cell).Nonempty :=
  ⟨(0, 0), by simp [lTrominoSet, lTromino]⟩

/-- `LProtoset_set` equals the canonical `toProtoset_set lTrominoSet`. -/
private lemma LProtoset_set_eq_toSet :
    LProtoset_set = toProtoset_set lTrominoSet lTrominoSet_nonempty := by
  funext ⟨⟩; exact Prototile_set.ext lTromino_coe_eq_LShape_set.symm

/-- **Bridge Theorem**: `LTileable` and `Tileable_set LProtoset_set` coincide on finite sets -/
theorem LTileable_iff_set (R : Finset Cell) :
    LTileable R ↔ Tileable_set (↑R : Set Cell) LProtoset_set := by
  rw [LProtoset_set_eq_toSet]
  exact Tileable_iff_to_set lTrominoSet R lTrominoSet_nonempty

-- NOTE: LTileable_rect_iff_set is now proved natively in LTrominoSet.lean
-- (no longer using the bridge)

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

-- NOTE: `LTileable_rectMinusCorner_iff_set` is now proved natively in LTrominoSet.lean
-- (via direct Set-framework proof). The bridge copy has been removed.

-- NOTE: `LTileable_rectMinus2Corner_set` is now proved natively in LTrominoSet.lean
-- (via direct Set-framework proof, commit to be pushed). The bridge copy has been removed.
