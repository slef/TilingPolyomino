import Mathlib.Tactic
import TilingPolyomino.TilingSet

open Set Function

-- ============================================================
-- L-tromino shape definitions
-- ============================================================

/-- The L-tromino shape (standard orientation): {(0,0),(0,1),(1,0)} -/
def LShape_cells : Set Cell := {(0, 0), (0, 1), (1, 0)}

def LPrototile_set : SetPrototile :=
  ⟨LShape_cells, by simp [Set.finite_insert, LShape_cells], ⟨(0, 0), by simp [LShape_cells]⟩⟩

def LProtoset_set : SetProtoset Unit := fun _ => LPrototile_set

/-- L-tromino tileability in the Set framework -/
def LTileable_set (R : Set Cell) : Prop := SetTileable R LProtoset_set

private def lPlaced_set (dx dy : ℤ) (r : Fin 4) : Set Cell :=
  SetPlacedTile.cells LProtoset_set ⟨(), (dx, dy), r⟩

@[simp] private theorem lPlaced_set_eq (dx dy : ℤ) (r : Fin 4) :
    lPlaced_set dx dy r = translate dx dy (rotate r LShape_cells) := by
  rfl

private theorem LShape_eq_rects : LShape_cells = rect 0 0 1 2 ∪ rect 1 0 2 1 := by
  ext ⟨x, y⟩
  simp [LShape_cells]
  omega

theorem LPrototile_set_ncard : LPrototile_set.cells.ncard = 3 := by
  dsimp [LPrototile_set, LShape_cells]
  rw [Set.ncard_insert_of_notMem]
  · rw [Set.ncard_insert_of_notMem]
    · rw [Set.ncard_singleton]
    · simp
  · simp

/-- swapRegion of a standard rect is the transposed rect -/
private lemma swapRegion_rect (a b : ℤ) :
    Set.swapRegion (rect 0 0 a b) = rect 0 0 b a := by
  ext ⟨x, y⟩; simp only [mem_swapRegion, mem_rect]; omega

-- ============================================================
-- Swap rotation: swapRegion commutes with lPlaced_set
-- ============================================================

private def swapRot : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | 3 => 1

private theorem swapRegion_lPlaced_set (dx dy : ℤ) (r : Fin 4) :
    Set.swapRegion (lPlaced_set dx dy r) = lPlaced_set dy dx (swapRot r) := by
  rw [lPlaced_set_eq, lPlaced_set_eq, LShape_eq_rects]
  fin_cases r
  · dsimp [swapRot]
    rect_omega
  · dsimp [swapRot]
    rect_omega
  · dsimp [swapRot]
    rect_omega
  · dsimp [swapRot]
    rect_omega

theorem LTileable_swap_set {R : Set Cell} (h : SetTileable R LProtoset_set) :
    SetTileable (Set.swapRegion R) LProtoset_set := by
  obtain ⟨ιₜ, hft, t, hv⟩ := h
  haveI : Fintype ιₜ := hft
  let t' : SetTileSet LProtoset_set ιₜ := ⟨fun i =>
    ⟨(), ((t.tiles i).translation.2, (t.tiles i).translation.1), swapRot (t.tiles i).rotation⟩⟩
  have hcell : ∀ i, SetTileSet.cellsAt t' i = Set.swapRegion (SetTileSet.cellsAt t i) := by
    intro i
    rcases hti : t.tiles i with ⟨idx, tr, r⟩; rcases tr with ⟨dx, dy⟩; cases idx
    simpa [SetTileSet.cellsAt, t', hti, lPlaced_set] using (swapRegion_lPlaced_set dx dy r).symm
  refine ⟨ιₜ, hft, t', ⟨?_, ?_⟩⟩
  · intro i j hij
    have hd := hv.disjoint i j hij
    rw [Set.disjoint_left] at hd ⊢
    exact fun p hp1 hp2 => hd (by simpa [hcell i, mem_swapRegion] using hp1)
                              (by simpa [hcell j, mem_swapRegion] using hp2)
  · ext p
    simp only [SetTileSet.coveredCells, Set.mem_iUnion, hcell, mem_swapRegion]
    exact ⟨fun ⟨i, hi⟩ => hv.covers ▸
             (Set.mem_iUnion.mpr ⟨i, hi⟩ : (p.2, p.1) ∈ SetTileSet.coveredCells t),
           fun hpR => Set.mem_iUnion.mp
             (hv.covers.symm ▸ hpR : (p.2, p.1) ∈ SetTileSet.coveredCells t)⟩

-- ============================================================
-- Base cases
-- ============================================================

theorem LTileable_2x3_set : SetTileable (rect 0 0 2 3) LProtoset_set := by
  refine ⟨Fin 2, inferInstance, ⟨![⟨(), (0, 0), 0⟩, ⟨(), (1, 2), 2⟩]⟩, ⟨?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Set.disjoint_iff_inter_eq_empty, SetTileSet.cellsAt, SetPlacedTile.cells,
        LProtoset_set, LPrototile_set, LShape_cells] <;>
      rect_omega
  · ext ⟨x, y⟩
    simp [SetTileSet.coveredCells, Set.mem_iUnion, Fin.exists_fin_two,
      SetTileSet.cellsAt, SetPlacedTile.cells,
      LProtoset_set, LPrototile_set, LShape_cells,
      mem_translate, mem_rotate, mem_rect, inverseRot,
      rotateCell_0, rotateCell_2]
    omega

theorem LTileable_3x2_set : SetTileable (rect 0 0 3 2) LProtoset_set := by
  refine ⟨Fin 2, inferInstance, ⟨![⟨(), (0, 0), 0⟩, ⟨(), (2, 1), 2⟩]⟩, ⟨?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Set.disjoint_iff_inter_eq_empty, SetTileSet.cellsAt, SetPlacedTile.cells,
        LProtoset_set, LPrototile_set, LShape_cells] <;>
      rect_omega
  · ext ⟨x, y⟩
    simp [SetTileSet.coveredCells, Set.mem_iUnion, Fin.exists_fin_two,
      SetTileSet.cellsAt, SetPlacedTile.cells,
      LProtoset_set, LPrototile_set, LShape_cells,
      mem_translate, mem_rotate, mem_rect, inverseRot,
      rotateCell_0, rotateCell_2]
    omega

theorem LTileable_2x2_minus_set : SetTileable (rect 0 0 2 2 \ {(1, 1)}) LProtoset_set := by
  refine ⟨Fin 1, inferInstance, ⟨![⟨(), (0, 0), 0⟩]⟩, ⟨?_, ?_⟩⟩
  · intro i j hij; fin_cases i; fin_cases j; exact (hij rfl).elim
  · ext ⟨x, y⟩
    simp [SetTileSet.coveredCells, Set.mem_iUnion,
      SetTileSet.cellsAt, SetPlacedTile.cells,
      LProtoset_set, LPrototile_set, LShape_cells,
      mem_translate, mem_rotate, mem_rect, inverseRot,
      rotateCell_0, Prod.mk.injEq]
    omega

-- ============================================================
-- Inductive rectangle families
-- ============================================================

theorem LTileable_2x6_set : SetTileable (rect 0 0 2 6) LProtoset_set := by
  have h := LTileable_2x3_set.scale_rect (by norm_num) (by norm_num) 1 2 (by omega) (by omega)
  convert h using 2

theorem LTileable_6x2_set : SetTileable (rect 0 0 6 2) LProtoset_set := by
  have h := LTileable_3x2_set.scale_rect (by norm_num) (by norm_num) 2 1 (by omega) (by omega)
  convert h using 2

theorem LTileable_3x4_set : SetTileable (rect 0 0 3 4) LProtoset_set := by
  have h := LTileable_3x2_set.scale_rect (by norm_num) (by norm_num) 1 2 (by omega) (by omega)
  convert h using 2

theorem LTileable_3x6_set : SetTileable (rect 0 0 3 6) LProtoset_set := by
  have h := LTileable_3x2_set.scale_rect (by norm_num) (by norm_num) 1 3 (by omega) (by omega)
  convert h using 2

theorem LTileable_6x3_set : SetTileable (rect 0 0 6 3) LProtoset_set := by
  have h := LTileable_2x3_set.scale_rect (by norm_num) (by norm_num) 3 1 (by omega) (by omega)
  convert h using 2

theorem LTileable_6x6_set : SetTileable (rect 0 0 6 6) LProtoset_set := by
  have h := LTileable_2x3_set.scale_rect (by norm_num) (by norm_num) 3 2 (by omega) (by omega)
  convert h using 2

theorem LTileable_2x_mult3_set (k : ℕ) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 2 (3 * k)) LProtoset_set := by
  have h := LTileable_2x3_set.scale_rect (by norm_num) (by norm_num) 1 k (by omega) hk
  convert h using 2; ring

theorem LTileable_3x_even_set (k : ℕ) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 3 (2 * k)) LProtoset_set := by
  have h := LTileable_3x2_set.scale_rect (by norm_num) (by norm_num) 1 k (by omega) hk
  convert h using 2; ring

theorem LTileable_mult3_x_2_set (k : Nat) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 (3 * k) 2) LProtoset_set := by
  have h := LTileable_3x2_set.scale_rect (by norm_num) (by norm_num) k 1 hk (by omega)
  convert h using 2; ring

theorem LTileable_even_x_3_set (k : Nat) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 (2 * k) 3) LProtoset_set := by
  have h := LTileable_2x3_set.scale_rect (by norm_num) (by norm_num) k 1 hk (by omega)
  convert h using 2; ring

theorem LTileable_6x_of_ge2_set (k : Nat) (hk : 2 ≤ k) :
    SetTileable (rect 0 0 6 k) LProtoset_set := by
  revert hk; induction k using Nat.strong_induction_on; rename_i n ih; intro hk
  rcases eq_or_lt_of_le hk with rfl | hn2
  · exact LTileable_6x2_set
  · rcases eq_or_lt_of_le (show 3 ≤ n from hn2) with rfl | hn3
    · exact LTileable_6x3_set
    · have h_prev : SetTileable (rect 0 0 6 ((n : ℤ) - 2)) LProtoset_set := by
        have h := ih (n - 2) (by omega) (by omega)
        convert h using 2; omega
      have h_stripe : SetTileable (rect 0 ((n : ℤ) - 2) 6 ((n : ℤ) - 2 + 2)) LProtoset_set := by
        convert setTileable_translate LTileable_6x2_set 0 ((n : ℤ) - 2) using 1
        ext ⟨x, y⟩; simp only [mem_rect, mem_translate]; omega
      have h_un := SetTileable.vertical_union (by omega) (by omega) h_prev h_stripe
      rwa [show ((n : ℤ) - 2 + 2) = n from by omega] at h_un

theorem LTileable_kx6_of_ge2_set (k : Nat) (hk : 2 ≤ k) :
    SetTileable (rect 0 0 k 6) LProtoset_set := by
  simpa [swapRegion_rect] using LTileable_swap_set (LTileable_6x_of_ge2_set k hk)

-- ============================================================
-- Area divisibility
-- ============================================================

theorem LTileable_rect_area_dvd_set (m n : Nat) (h : SetTileable (rect 0 0 m n) LProtoset_set) :
    3 ∣ m * n := by
  simpa [LProtoset_set, LPrototile_set_ncard, rect_ncard] using
    SetTileable.ncard_dvd (ι := Unit) (ps := LProtoset_set) (rect_finite 0 0 m n) h ()

-- ============================================================
-- Impossibility theorems
-- ============================================================

private lemma lPlaced_set_contains_origin_offset (dx dy : ℤ) (r : Fin 4) :
    (dx, dy) ∈ lPlaced_set dx dy r := by
  fin_cases r <;>
    simp [lPlaced_set_eq, mem_translate, mem_rotate, LShape_cells, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]

private lemma lPlaced_set_x_span (dx dy : ℤ) (r : Fin 4) :
    (dx + 1, dy) ∈ lPlaced_set dx dy r ∨ (dx - 1, dy) ∈ lPlaced_set dx dy r := by
  fin_cases r <;>
    simp [lPlaced_set_eq, mem_translate, mem_rotate, LShape_cells, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]

/-- No 1×n strip (n ≥ 1) is L-tileable: placed copies always span ≥ 2 x-values -/
theorem not_LTileable_1xn_set (n : ℕ) (hn : 1 ≤ n) :
    ¬ SetTileable (rect 0 0 1 n) LProtoset_set := by
  intro ⟨ιₜ, hft, t, hv⟩; haveI : Fintype ιₜ := hft
  -- Get the tile covering (0,0)
  have hcell : ((0 : ℤ), (0 : ℤ)) ∈ rect 0 0 1 (n : ℤ) := by simp [mem_rect]; omega
  rw [← hv.covers, SetTileSet.coveredCells, Set.mem_iUnion] at hcell
  obtain ⟨i, hi⟩ := hcell
  let dx := (t.tiles i).translation.1; let dy := (t.tiles i).translation.2
  let r  := (t.tiles i).rotation
  have hrep : SetTileSet.cellsAt t i = lPlaced_set dx dy r := by
    simp [SetTileSet.cellsAt, lPlaced_set, dx, dy, r]
  -- Any cell in tile i has x-coordinate in [0, 1)
  have h_sub : ∀ q, q ∈ lPlaced_set dx dy r → 0 ≤ q.1 ∧ q.1 < 1 := fun q hq => by
    have h : q ∈ rect 0 0 1 (n : ℤ) := hv.covers ▸ Set.mem_iUnion.mpr ⟨i, hrep ▸ hq⟩
    simp only [mem_rect] at h; exact ⟨h.1, h.2.1⟩
  -- The origin offset (dx, dy) is in the tile → 0 ≤ dx < 1
  have hbnd := h_sub _ (lPlaced_set_contains_origin_offset dx dy r)
  -- The tile spans ≥ 2 x-values → contradiction
  rcases lPlaced_set_x_span dx dy r with h2 | h2
  · have := (h_sub _ h2).2; omega
  · have := (h_sub _ h2).1; omega

/-- Same result for the transposed strip (n×1) -/
theorem not_LTileable_nx1_set (n : ℕ) (hn : 1 ≤ n) :
    ¬ SetTileable (rect 0 0 n 1) LProtoset_set := by
  intro h
  exact not_LTileable_1xn_set n hn (swapRegion_rect n 1 ▸ LTileable_swap_set h)

-- ============================================================
-- 3×(2k+1) Impossibility
-- ============================================================

/-- ncard of any lPlaced_set is 3 -/
private lemma lPlaced_set_ncard (dx dy : ℤ) (r : Fin 4) :
    (lPlaced_set dx dy r).ncard = 3 := by
  have heq : lPlaced_set dx dy r = SetPlacedTile.cells LProtoset_set ⟨(), (dx, dy), r⟩ := by
    simp [lPlaced_set]
  rw [heq, SetPlacedTile.cells_ncard_eq]
  simp [LProtoset_set, LPrototile_set_ncard]

/-- lPlaced_set is always finite -/
private lemma lPlaced_set_finite (dx dy : ℤ) (r : Fin 4) :
    (lPlaced_set dx dy r).Finite := by
  have heq : lPlaced_set dx dy r = SetPlacedTile.cells LProtoset_set ⟨(), (dx, dy), r⟩ := by
    simp [lPlaced_set]
  rw [heq]; exact SetPlacedTile.cells_finite _

/-- A single L-tromino cannot contain both (0,0) and (2,0): x-span is at most 1 -/
private lemma lPlaced_set_not_cover_x02 (dx dy : ℤ) (r : Fin 4)
    (h0 : ((0 : ℤ), (0 : ℤ)) ∈ lPlaced_set dx dy r)
    (h2 : ((2 : ℤ), (0 : ℤ)) ∈ lPlaced_set dx dy r) : False := by
  fin_cases r <;>
    simp only [lPlaced_set_eq, mem_translate, mem_rotate, LShape_cells, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h0 h2 <;>
    omega

/-- A tile with any cell at y=0 must have all cells at y<2 -/
private lemma lPlaced_set_ybnd_of_y0 (dx dy : ℤ) (r : Fin 4)
    (hc : ∃ cx : ℤ, (cx, (0 : ℤ)) ∈ lPlaced_set dx dy r)
    (q : Cell) (hq : q ∈ lPlaced_set dx dy r) : q.2 < 2 := by
  obtain ⟨cx, hcx⟩ := hc
  fin_cases r <;>
    simp only [lPlaced_set_eq, mem_translate, mem_rotate, LShape_cells, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hcx hq <;>
    omega

/-- A 3×(2k+1) rectangle is not L-tileable (Set framework) -/
theorem not_LTileable_3x_odd_set (k : ℕ) : ¬ SetTileable (rect 0 0 3 (2*k+1)) LProtoset_set := by
  induction k with
  | zero =>
    -- rect 0 0 3 (2*0+1) = rect 0 0 3 1 = rect 0 0 3 1 (cast is (1:ℤ))
    norm_cast
    exact not_LTileable_nx1_set 3 (by omega)
  | succ k' ih =>
    -- Rewrite goal: ¬ SetTileable (rect 0 0 3 (2*↑k' + 3))
    rw [show (2 : ℤ) * ↑(k' + 1) + 1 = 2 * (k' : ℤ) + 3 from by push_cast; omega]
    intro ⟨ιₜ, hft, t, hv⟩
    haveI : Fintype ιₜ := hft; haveI : DecidableEq ιₜ := Classical.decEq _
    -- Get tiles covering opposite corners (0,0) and (2,0)
    have h00_in : ((0 : ℤ), (0 : ℤ)) ∈ rect 0 0 3 (2 * (k' : ℤ) + 3) := by simp [mem_rect]; omega
    have h20_in : ((2 : ℤ), (0 : ℤ)) ∈ rect 0 0 3 (2 * (k' : ℤ) + 3) := by simp [mem_rect]; omega
    rw [← hv.covers, SetTileSet.coveredCells, Set.mem_iUnion] at h00_in h20_in
    obtain ⟨i, hi⟩ := h00_in; obtain ⟨j, hj⟩ := h20_in
    -- Name tile parameters
    let dxi := (t.tiles i).translation.1; let dyi := (t.tiles i).translation.2
    let ri  := (t.tiles i).rotation
    let dxj := (t.tiles j).translation.1; let dyj := (t.tiles j).translation.2
    let rj  := (t.tiles j).rotation
    have hi_eq : t.cellsAt i = lPlaced_set dxi dyi ri := by
      simp [SetTileSet.cellsAt, lPlaced_set, dxi, dyi, ri]
    have hj_eq : t.cellsAt j = lPlaced_set dxj dyj rj := by
      simp [SetTileSet.cellsAt, lPlaced_set, dxj, dyj, rj]
    have hi' : ((0 : ℤ), (0 : ℤ)) ∈ lPlaced_set dxi dyi ri := hi_eq ▸ hi
    have hj' : ((2 : ℤ), (0 : ℤ)) ∈ lPlaced_set dxj dyj rj := hj_eq ▸ hj
    -- i ≠ j and tiles are disjoint
    have hij : i ≠ j := by
      intro heq; subst heq; exact lPlaced_set_not_cover_x02 dxi dyi ri hi' hj'
    have hdisj : Disjoint (lPlaced_set dxi dyi ri) (lPlaced_set dxj dyj rj) := by
      rw [← hi_eq, ← hj_eq]; exact hv.disjoint i j hij
    -- Any cell of any tile is in rect 0 0 3 (2k'+3)
    have sub_full : ∀ (ii : ιₜ), SetTileSet.cellsAt t ii ⊆ rect 0 0 3 (2 * (k' : ℤ) + 3) :=
      fun ii q hq => hv.covers ▸ Set.mem_iUnion.mpr ⟨ii, hq⟩
    -- Each corner tile is contained in the bottom strip rect 0 0 3 2
    have hi_sub_3x2 : lPlaced_set dxi dyi ri ⊆ rect 0 0 3 2 := fun q hq => by
      have hf := sub_full i (hi_eq ▸ hq); simp only [mem_rect] at hf ⊢
      exact ⟨hf.1, hf.2.1, hf.2.2.1, lPlaced_set_ybnd_of_y0 dxi dyi ri ⟨0, hi'⟩ q hq⟩
    have hj_sub_3x2 : lPlaced_set dxj dyj rj ⊆ rect 0 0 3 2 := fun q hq => by
      have hf := sub_full j (hj_eq ▸ hq); simp only [mem_rect] at hf ⊢
      exact ⟨hf.1, hf.2.1, hf.2.2.1, lPlaced_set_ybnd_of_y0 dxj dyj rj ⟨2, hj'⟩ q hq⟩
    -- Their union fills rect 0 0 3 2 exactly (two disjoint 3-cell tiles in a 6-cell rect)
    have hunion_eq : lPlaced_set dxi dyi ri ∪ lPlaced_set dxj dyj rj = rect 0 0 3 2 := by
      have hcard : (lPlaced_set dxi dyi ri ∪ lPlaced_set dxj dyj rj).ncard = 6 := by
        rw [Set.ncard_union_eq hdisj (lPlaced_set_finite _ _ _) (lPlaced_set_finite _ _ _),
            lPlaced_set_ncard, lPlaced_set_ncard]
      exact Set.eq_of_subset_of_ncard_le (Set.union_subset hi_sub_3x2 hj_sub_3x2)
        (by simp [rect_ncard] at hcard ⊢; omega) (rect_finite _ _ _ _)
    -- Remove the two bottom tiles; the remainder is the translated smaller rect
    have hS : t.cellsAt i ∪ t.cellsAt j = rect 0 0 3 2 := by rw [hi_eq, hj_eq]; exact hunion_eq
    have h_remain := SetTileable.remove_two t hv i j hij hS
    have h_diff_eq : rect 0 0 3 (2 * (k' : ℤ) + 3) \ rect 0 0 3 2 =
        translate 0 2 (rect 0 0 3 (2 * (k' : ℤ) + 1)) := by
      ext ⟨x, y⟩; simp only [Set.mem_diff, mem_rect, mem_translate]; omega
    rw [h_diff_eq] at h_remain
    -- Translate back and apply IH
    have h_back : SetTileable (rect 0 0 3 (2 * (k' : ℤ) + 1)) LProtoset_set := by
      convert h_remain.translate 0 (-2) using 1
      ext ⟨x, y⟩; simp only [mem_translate, mem_rect]; omega
    exact ih h_back

-- ============================================================
-- 2×n biconditional
-- ============================================================

/-- 2×n is L-tileable iff 3 ∣ n -/
theorem LTileable_2xn_iff_set (n : ℕ) : SetTileable (rect 0 0 2 n) LProtoset_set ↔ 3 ∣ n := by
  constructor
  · intro h
    have hdvd := LTileable_rect_area_dvd_set 2 n h
    rcases hdvd with ⟨k, hk⟩
    exact ⟨n - k, by omega⟩
  · rintro ⟨k, hk⟩
    subst hk
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp only [Nat.mul_zero, Nat.cast_zero]
      rw [rect_empty_of_eq]
      exact SetTileable.empty LProtoset_set
    · exact LTileable_2x_mult3_set k hk_pos

-- ============================================================
-- 3×n biconditional
-- ============================================================

/-- 3×n is L-tileable iff n is even -/
theorem LTileable_3xn_iff_set (n : ℕ) : SetTileable (rect 0 0 3 n) LProtoset_set ↔ 2 ∣ n := by
  constructor
  · intro h
    rcases Nat.even_or_odd n with he | ⟨k, hk⟩
    · exact even_iff_two_dvd.mp he
    · have hk' : (n : ℤ) = 2 * k + 1 := by exact_mod_cast hk
      exact absurd (hk' ▸ h) (not_LTileable_3x_odd_set k)
  · rintro ⟨k, hk⟩
    subst hk
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp only [Nat.mul_zero, Nat.cast_zero]
      rw [rect_empty_of_eq]
      exact SetTileable.empty LProtoset_set
    · exact LTileable_3x_even_set k hk_pos

/-- n×3 is L-tileable iff n is even (by symmetry with 3×n) -/
theorem LTileable_nx3_iff_set (n : ℕ) : SetTileable (rect 0 0 n 3) LProtoset_set ↔ 2 ∣ n := by
  rw [← LTileable_3xn_iff_set]
  constructor <;> intro h <;> simpa [swapRegion_rect] using LTileable_swap_set h

/-- n×2 is L-tileable iff 3 ∣ n (by symmetry with 2×n) -/
theorem LTileable_nx2_iff_set (n : ℕ) : SetTileable (rect 0 0 n 2) LProtoset_set ↔ 3 ∣ n := by
  rw [← LTileable_2xn_iff_set]
  constructor <;> intro h <;> simpa [swapRegion_rect] using LTileable_swap_set h

-- ============================================================
-- General 2D families via refine
-- ============================================================

/-- Any (3a) × (2b) rectangle is L-tileable (a, b ≥ 1) -/
theorem LTileable_mult3_mult2_set (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    SetTileable (rect 0 0 (3 * a) (2 * b)) LProtoset_set := by
  have h := LTileable_3x2_set.scale_rect (by norm_num) (by norm_num) a b ha hb
  convert h using 2 <;> ring

/-- Any (2a) × (3b) rectangle is L-tileable (a, b ≥ 1) -/
theorem LTileable_mult2_mult3_set (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    SetTileable (rect 0 0 (2 * a) (3 * b)) LProtoset_set := by
  have h := LTileable_swap_set (LTileable_mult3_mult2_set b a hb ha)
  have heq : Set.swapRegion (rect 0 0 (3 * b) (2 * a)) = rect 0 0 (2 * a) (3 * b) := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rwa [heq] at h

-- ============================================================
-- New families: odd × 6k
-- ============================================================

/-- n×6 is L-tileable for all odd n ≥ 3 -/
theorem LTileable_odd_x_6_set (n : ℕ) (hn_odd : n % 2 = 1) (hn_ge : 3 ≤ n) :
    SetTileable (rect 0 0 n 6) LProtoset_set := by
  revert hn_odd hn_ge; induction n using Nat.strong_induction_on; rename_i n ih; intro hn_odd hn_ge
  rcases Nat.eq_or_lt_of_le hn_ge with rfl | hn_gt
  · exact LTileable_3x6_set
  · have h_prev : SetTileable (rect 0 0 ((n : ℤ) - 2) 6) LProtoset_set := by
      have h := ih (n - 2) (by omega) (by omega) (by omega)
      convert h using 2; omega
    have h_stripe : SetTileable (rect ((n : ℤ) - 2) 0 ((n : ℤ) - 2 + 2) 6) LProtoset_set := by
      convert setTileable_translate LTileable_2x6_set ((n : ℤ) - 2) 0 using 1
      ext ⟨x, y⟩; simp only [mem_rect, mem_translate]; omega
    have h_un := SetTileable.horizontal_union (by omega) (by omega) h_prev h_stripe
    rwa [show ((n : ℤ) - 2 + 2) = n from by omega] at h_un

/-- 6×n is L-tileable for all odd n ≥ 3 (by swap) -/
theorem LTileable_6x_odd_set (n : ℕ) (hn_odd : n % 2 = 1) (hn_ge : 3 ≤ n) :
    SetTileable (rect 0 0 6 n) LProtoset_set := by
  simpa [swapRegion_rect] using LTileable_swap_set (LTileable_odd_x_6_set n hn_odd hn_ge)

/-- n × (6k) is L-tileable for odd n ≥ 3 and k ≥ 1 -/
theorem LTileable_odd_x_mult6_set (n k : ℕ) (hn_odd : n % 2 = 1) (hn_ge : 3 ≤ n) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 n (6 * k)) LProtoset_set := by
  have hn_pos : (0:ℤ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := (LTileable_odd_x_6_set n hn_odd hn_ge).scale_rect hn_pos (by norm_num) 1 k (by omega) hk
  convert h using 2 <;> ring
