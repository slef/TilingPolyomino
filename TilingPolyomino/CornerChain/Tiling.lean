import TilingPolyomino.CornerChain.Defs

/-!
# Tiling a corner chain by defect pushing

The tiling engine of the project: the union of a corner chain is L-tileable
as soon as its area is divisible by 3 (`IsCornerChain.tileable`).

Walk the chain; if the running area of the current piece (minus the defect
inherited at its entry corner) is not divisible by 3, leave a corner defect
of size 1 or 2 at the exit corner and cover it with a single L-tromino
straddling into the next piece (`exists_pushTromino`), where it creates the
complementary defect of size 2 or 1.  Each piece minus its ≤ 2 corner
defects is tiled by the two-corner-defect theorem and its one- and
zero-defect specializations (`RectPiece.tileable_optDefects`); total area
≡ 0 (mod 3) guarantees the last piece closes exactly
(`chainCells_tileable`).
-/

open Set

-- ============================================================
-- §4 The tiling half of the proof
-- ============================================================
--
-- The geometric half — the existence of a corner chain
-- (`exists_cornerChain`) — is proved in `VerticalDecomposition.lean` and
-- `EulerTour.lean`, which build on this file; `EulerTour.lean` also states
-- the main lemma `LTileable_of_vertexAligned`.

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
