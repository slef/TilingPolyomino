/-
# Bridge between Finset and Set frameworks for L-tromino tilings

`LProtoset` (from LTrominoSet_finset) equals the canonical `toProtoset LTrominoSet_finset`,
so the bridge reduces to a single rewrite + `Tileable_iff_to`.

Main results:
- `LTromino_coe_eq_LShape`: coercion lemma `↑LTromino_finset = LShape_cells`
- `coe_rectangle_eq_rect`: coercion lemma `↑(rectangle n m) = rect 0 0 n m`
- `LTileable_iff`: `LTileable_finset R ↔ Tileable ↑R LProtoset`
- `LTileable_rect_iff`: full rectangle characterization in the Set framework
- `LTileable_rectMinusCorner_iff`: proved natively in LTrominoSet_finset.lean (bridge copy removed)
- `LTileable_rectMinus2Corner`: proved natively in LTrominoSet_finset.lean (bridge copy removed)
-/

import TilingPolyomino.LTrominoBase
import TilingPolyomino.LTromino

open Set Function

/-- The LTromino_finset Finset coerces to LShape_cells as a Set -/
lemma LTromino_coe_eq_LShape : (↑(LTromino_finset : Finset Cell) : Set Cell) = LShape_cells := by
  ext c
  constructor
  · intro hm
    rw [Finset.mem_coe, Prototile_finset.mem_coe] at hm
    simp only [LTromino_finset, List.mem_cons, List.mem_nil_iff, or_false] at hm
    simp only [LShape_cells, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hm
  · intro hm
    rw [Finset.mem_coe, Prototile_finset.mem_coe]
    simp only [LTromino_finset, List.mem_cons, List.mem_nil_iff, or_false]
    simp only [LShape_cells, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact hm

private lemma LTrominoSet_nonempty (i : Unit) : (LTrominoSet_finset i : Finset Cell).Nonempty :=
  ⟨(0, 0), by simp [LTrominoSet_finset, LTromino_finset]⟩

/-- `LProtoset` equals the canonical `toProtoset LTrominoSet_finset`. -/
private lemma LProtoset_set_eq_toSet :
    LProtoset = toProtoset LTrominoSet_finset LTrominoSet_nonempty := by
  funext ⟨⟩; exact Prototile.ext LTromino_coe_eq_LShape.symm

/-- **Bridge Theorem**: `LTileable_finset` and `Tileable LProtoset` coincide on finite sets -/
theorem LTileable_iff (R : Finset Cell) :
    LTileable_finset R ↔ Tileable (↑R : Set Cell) LProtoset := by
  rw [LProtoset_set_eq_toSet]
  exact Tileable_iff_to LTrominoSet_finset R LTrominoSet_nonempty

-- NOTE: LTileable_rect_iff is now proved natively in LTrominoSet_finset.lean
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

-- NOTE: `LTileable_rectMinusCorner_iff` is now proved natively in LTrominoSet_finset.lean
-- (via direct Set-framework proof). The bridge copy has been removed.

-- NOTE: `LTileable_rectMinus2Corner` is now proved natively in LTrominoSet_finset.lean
-- (via direct Set-framework proof, commit to be pushed). The bridge copy has been removed.

theorem rectMinusCorner_tileable_iff (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2) :
    LTileable_finset (rectangleMinusCorner n m) ↔ (n * m - 1) % 3 = 0 := by
  rw [LTileable_iff, coe_rectangleMinusCorner_eq n m (by omega) (by omega)]
  exact LTileable_rectMinusCorner_iff n m hn hm

lemma cornerTR2_cast (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 1) :
    cornerTR2 n m = ((n : ℤ) - 2, (m : ℤ) - 1) := by
  simp only [cornerTR2, Prod.mk.injEq]
  exact ⟨by exact_mod_cast Nat.cast_sub hn, by exact_mod_cast Nat.cast_sub hm⟩

lemma coe_rectangleMinus2Corner_eq (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 1) :
    (↑(rectangleMinus2Corner n m) : Set Cell) =
    rect 0 0 (n : ℤ) m \ ({((n : ℤ) - 1, (m : ℤ) - 1)} ∪ {((n : ℤ) - 2, (m : ℤ) - 1)}) := by
  rw [rectangleMinus2Corner, Finset.coe_erase, Finset.coe_erase, coe_rectangle_eq_rect]
  rw [cornerTR_cast n m (by omega) hm, cornerTR2_cast n m hn hm]
  ext c
  simp
  tauto

theorem rectMinus2Corner_tileable_of_area_mod2
    (n m : ℕ) (hn : n ≥ 3) (hm : m ≥ 3) (hmod : n * m % 3 = 2) :
    LTileable_finset (rectangleMinus2Corner n m) := by
  rw [LTileable_iff, coe_rectangleMinus2Corner_eq n m (by omega) (by omega)]
  exact LTileable_rectMinus2Corner n m hn hm hmod
