/-
# Bridge between Finset and Set frameworks for L-tromino tilings

This file proves the equivalence between the two L-tromino tiling frameworks:
- `LTileable` (from LTromino.lean): uses `Region = Finset Cell`
- `SetTileable ... LSetProtoset` (from LTrominoSet.lean): uses `Set Cell`

Main results:
- `LTileable_iff_SetTileable`: the two notions of tileability coincide
- `rect_setTileable_iff`: full characterization of L-tileable rectangles
  (Set framework analog of `rect_tileable_iff` from LTromino.lean)
-/

import TilingPolyomino.LTromino
import TilingPolyomino.LTrominoSet

open Set Function

-- ============================================================
-- Section 1: Connecting the two cell representations
-- ============================================================

/-- The lTromino shape as a Finset coerces to LShape_cells as a Set -/
lemma lTromino_coe_eq_LShape : (↑(lTromino : Finset Cell) : Set Cell) = LShape_cells := by
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

/-- rotateCell and inverseRot are inverses: cancel in r-then-inverseRot order -/
lemma rotateCell_inverseRot_cancel (c : Cell) (r : Fin 4) :
    rotateCell (rotateCell c r) (inverseRot r) = c := by
  fin_cases r <;>
  simp only [inverseRot, rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3] <;>
  ext <;> simp [rotateCell_1, rotateCell_2, rotateCell_3]

/-- rotateCell and inverseRot are inverses: cancel in inverseRot-then-r order -/
lemma rotateCell_inverseRot_cancel' (c : Cell) (r : Fin 4) :
    rotateCell (rotateCell c (inverseRot r)) r = c := by
  fin_cases r <;>
  simp only [inverseRot, rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3] <;>
  ext <;> simp [rotateCell_1, rotateCell_2, rotateCell_3]

/-- Key lemma: cells of a Finset-framework PlacedTile, coerced to a Set,
    equal the cells of the corresponding Set-framework SetPlacedTile. -/
lemma placedTile_cells_as_set (pt : PlacedTile Unit) :
    (↑(pt.cells lTrominoSet) : Set Cell) =
    SetPlacedTile.cells LSetProtoset ⟨pt.index, pt.translation, pt.rotation⟩ := by
  ext ⟨x, y⟩
  simp only [Finset.mem_coe, PlacedTile.cells, rotateProto, Finset.mem_image,
             Prototile.mem_coe, translateCell,
             SetPlacedTile.cells, lTrominoSet, LSetProtoset, LSetPrototile,
             mem_translate, mem_rotate]
  constructor
  · rintro ⟨c, ⟨c₀, hc₀_list, rfl⟩, hxy⟩
    -- hxy : (c.1 + t.1, c.2 + t.2) = (x, y)  where c = rotateCell c₀ pt.rotation
    have hx : x - pt.translation.1 = (rotateCell c₀ pt.rotation).1 :=
      by have := congr_arg Prod.fst hxy; simp at this; omega
    have hy : y - pt.translation.2 = (rotateCell c₀ pt.rotation).2 :=
      by have := congr_arg Prod.snd hxy; simp at this; omega
    rw [show (x - pt.translation.1, y - pt.translation.2) = rotateCell c₀ pt.rotation
        from Prod.ext hx hy,
        rotateCell_inverseRot_cancel, ← lTromino_coe_eq_LShape]
    exact Finset.mem_coe.mpr (Prototile.mem_coe lTromino c₀ |>.mpr hc₀_list)
  · intro h
    rw [← lTromino_coe_eq_LShape] at h
    let c₀ := rotateCell (x - pt.translation.1, y - pt.translation.2) (inverseRot pt.rotation)
    have hc₀_list : c₀ ∈ (lTromino : Prototile).cells :=
      (Prototile.mem_coe lTromino c₀).mp (Finset.mem_coe.mp h)
    have hrot : rotateCell c₀ pt.rotation =
        (x - pt.translation.1, y - pt.translation.2) := rotateCell_inverseRot_cancel' _ _
    exact ⟨rotateCell c₀ pt.rotation, ⟨c₀, hc₀_list, rfl⟩,
           Prod.ext (by rw [hrot]; ring) (by rw [hrot]; ring)⟩

-- ============================================================
-- Section 2: Relating covered cells
-- ============================================================

/-- For corresponding tile sets, covered cells agree. -/
private lemma cellsAt_eq {ιₜ : Type} [Fintype ιₜ]
    (t : TileSet lTrominoSet ιₜ)
    (t' : SetTileSet LSetProtoset ιₜ)
    (htiles : ∀ i : ιₜ, t'.tiles i =
      ⟨(t.tiles i).index, (t.tiles i).translation, (t.tiles i).rotation⟩)
    (i : ιₜ) : t'.cellsAt i = ↑(t.cellsAt i) := by
  simp only [SetTileSet.cellsAt, TileSet.cellsAt, htiles i]
  exact (placedTile_cells_as_set (t.tiles i)).symm

private lemma coveredCells_eq_coe {ιₜ : Type} [Fintype ιₜ] [DecidableEq ιₜ]
    (t : TileSet lTrominoSet ιₜ)
    (t' : SetTileSet LSetProtoset ιₜ)
    (htiles : ∀ i : ιₜ, t'.tiles i =
      ⟨(t.tiles i).index, (t.tiles i).translation, (t.tiles i).rotation⟩) :
    t'.coveredCells = (↑(t.coveredCells) : Set Cell) := by
  ext c
  simp only [SetTileSet.coveredCells, Set.mem_iUnion, cellsAt_eq t t' htiles,
             Finset.mem_coe, TileSet.coveredCells, TileSet.cellsAt]
  constructor
  · rintro ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_coe.mp hi⟩
  · intro hc
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hc
    exact ⟨i, Finset.mem_coe.mpr hi⟩

-- ============================================================
-- Section 3: The bridge theorem
-- ============================================================

/-- Coercion of rectangle (Finset) to rect (Set) -/
lemma coe_rectangle_eq_rect (n m : ℕ) :
    (↑(rectangle n m) : Set Cell) = rect 0 0 n m := by
  ext ⟨x, y⟩
  simp only [Finset.mem_coe, mem_rectangle, mem_rect]

/-- Forward direction: a Finset tiling yields a Set tiling -/
private lemma LTileable_to_SetTileable {R : Finset Cell}
    (h : LTileable R) : SetTileable (↑R : Set Cell) LSetProtoset := by
  obtain ⟨ιₜ, hFin, hDec, t, hValid⟩ := h
  let t' : SetTileSet LSetProtoset ιₜ :=
    ⟨fun i => ⟨(t.tiles i).index, (t.tiles i).translation, (t.tiles i).rotation⟩⟩
  refine ⟨ιₜ, hFin, t', ?_⟩
  constructor
  · intro i j hij
    rw [cellsAt_eq t t' (fun _ => rfl) i, cellsAt_eq t t' (fun _ => rfl) j]
    exact Finset.disjoint_coe.mpr (hValid.disjoint i j hij)
  · rw [coveredCells_eq_coe t t' (fun _ => rfl), hValid.covers]

/-- Backward direction: a Set tiling yields a Finset tiling -/
private lemma SetTileable_to_LTileable {R : Finset Cell}
    (h : SetTileable (↑R : Set Cell) LSetProtoset) : LTileable R := by
  obtain ⟨ιₜ, hFin, t', hValid⟩ := h
  haveI hDec : DecidableEq ιₜ := Classical.decEq ιₜ
  let t : TileSet lTrominoSet ιₜ :=
    ⟨fun i => ⟨(t'.tiles i).index, (t'.tiles i).translation, (t'.tiles i).rotation⟩⟩
  -- Note: t'.tiles i = ⟨(t.tiles i).index, ...⟩ holds by definition (eta-expansion)
  have htiles : ∀ i : ιₜ, t'.tiles i =
      ⟨(t.tiles i).index, (t.tiles i).translation, (t.tiles i).rotation⟩ := by
    intro i; simp only [t, TileSet.tiles]
  refine ⟨ιₜ, hFin, hDec, t, ?_⟩
  constructor
  · intro i j hij
    have := hValid.disjoint i j hij
    rw [cellsAt_eq t t' htiles i, cellsAt_eq t t' htiles j] at this
    exact Finset.disjoint_coe.mp this
  · have hcov := coveredCells_eq_coe t t' htiles
    have hcovers := hValid.covers
    have heq : (↑(t.coveredCells) : Set Cell) = ↑R := by rw [← hcov]; exact hcovers
    exact Finset.coe_injective heq

/-- **Bridge Theorem**: `LTileable` and `SetTileable LSetProtoset` coincide on finite sets -/
theorem LTileable_iff_SetTileable (R : Finset Cell) :
    LTileable R ↔ SetTileable (↑R : Set Cell) LSetProtoset :=
  ⟨LTileable_to_SetTileable, SetTileable_to_LTileable⟩

-- ============================================================
-- Section 4: rect_setTileable_iff via bridge
-- ============================================================

/-- The full characterization of L-tileable rectangles in the Set framework.
    This follows from `rect_tileable_iff` (Finset) via the bridge theorem. -/
theorem rect_setTileable_iff (n m : ℕ) :
    SetTileable (rect 0 0 (n : ℤ) m) LSetProtoset ↔ RectTileableConditions n m := by
  rw [← coe_rectangle_eq_rect, ← LTileable_iff_SetTileable]
  exact rect_tileable_iff n m
