import Mathlib.Tactic
import TilingPolyomino.TilingSet
import TilingPolyomino.LTromino

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

theorem LShape_eq_rects : LShape_cells = rect 0 0 1 2 ∪ rect 1 0 2 1 := by
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
lemma swapRegion_rect (a b : ℤ) :
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

theorem LTileable_3x2_set : SetTileable (rect 0 0 3 2) LProtoset_set :=
  swapRegion_rect 2 3 ▸ LTileable_swap_set LTileable_2x3_set

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

-- ============================================================
-- Main theorem: native proof of LTileable_rect_iff_set
-- ============================================================

/-- Base case: 5×9 rectangle with explicit tiling of 15 L-trominoes -/
theorem LTileable_5x9_set : SetTileable (rect 0 0 5 9) LProtoset_set := by
  refine ⟨Fin 15, inferInstance, ⟨![
    ⟨(), (1, 0), 1⟩, ⟨(), (0, 2), 3⟩, ⟨(), (0, 4), 3⟩, ⟨(), (2, 3), 2⟩,
    ⟨(), (0, 6), 3⟩, ⟨(), (2, 5), 2⟩, ⟨(), (0, 8), 3⟩, ⟨(), (2, 7), 1⟩,
    ⟨(), (3, 6), 1⟩, ⟨(), (4, 8), 2⟩, ⟨(), (4, 5), 1⟩, ⟨(), (2, 1), 3⟩,
    ⟨(), (4, 0), 1⟩, ⟨(), (4, 2), 1⟩, ⟨(), (3, 4), 3⟩]⟩,
    ⟨?_, ?_⟩⟩
  · -- Disjointness: 225 cases, each handled by rect_omega after LShape_eq_rects
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all only [ne_eq, not_false_eq_true, Set.disjoint_iff_inter_eq_empty,
        SetTileSet.cellsAt, SetPlacedTile.cells, LProtoset_set, LPrototile_set, LShape_cells,
        LShape_eq_rects] <;>
      rect_omega
  · -- Coverage: the 15 tiles exactly cover rect 0 0 5 9
    ext ⟨x, y⟩
    simp only [SetTileSet.coveredCells, Set.mem_iUnion, SetTileSet.cellsAt, SetPlacedTile.cells,
      LProtoset_set, LPrototile_set, LShape_cells, LShape_eq_rects,
      mem_translate, mem_rotate, mem_rect, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3]
    constructor
    · -- forward: membership in union → membership in rect 0 0 5 9
      rintro ⟨i, hi⟩
      fin_cases i <;> simp_all <;> omega
    · -- backward: membership in rect 0 0 5 9 → in some tile
      intro ⟨hx1, hx2, hy1, hy2⟩
      interval_cases x <;> interval_cases y <;> simp_all <;>
        first
        | exact ⟨0, by simp_all; omega⟩
        | exact ⟨1, by simp_all; omega⟩
        | exact ⟨2, by simp_all; omega⟩
        | exact ⟨3, by simp_all; omega⟩
        | exact ⟨4, by simp_all; omega⟩
        | exact ⟨5, by simp_all; omega⟩
        | exact ⟨6, by simp_all; omega⟩
        | exact ⟨7, by simp_all; omega⟩
        | exact ⟨8, by simp_all; omega⟩
        | exact ⟨9, by simp_all; omega⟩
        | exact ⟨10, by simp_all; omega⟩
        | exact ⟨11, by simp_all; omega⟩
        | exact ⟨12, by simp_all; omega⟩
        | exact ⟨13, by simp_all; omega⟩
        | exact ⟨14, by simp_all; omega⟩

/-- 5 × (6i+3) is L-tileable for i ≥ 1 -/
theorem LTileable_5x_6iplus3_set (i : ℕ) (hi : i ≥ 1) :
    SetTileable (rect 0 0 5 (6 * i + 3)) LProtoset_set := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  -- i = j + 1, 6*(j+1)+3 = 9 + 6*j
  induction j with
  | zero => 
    norm_num
    exact LTileable_5x9_set
  | succ k ih =>
    -- 6*(k+2)+3 = 6*(k+1)+3 + 6
    have h_left : SetTileable (rect 0 0 5 (6*(k+1)+3)) LProtoset_set := ih
    have h_right_base : SetTileable (rect 0 0 5 6) LProtoset_set := 
      LTileable_kx6_of_ge2_set 5 (by omega)
    have h_right : SetTileable (rect 0 (↑(6*(k+1)+3) : ℤ) 5 (↑(6*(k+1)+3) + 6)) LProtoset_set := by
      convert setTileable_translate h_right_base 0 (↑(6*(k+1)+3) : ℤ) using 1
      ext ⟨x,y⟩; simp [mem_rect, mem_translate]; push_cast; omega
    have hun := SetTileable.vertical_union (by norm_num) (by norm_num) h_left h_right
    convert hun using 2; push_cast; ring

/-- n × (6i+3) is L-tileable for odd n ≥ 5 and i ≥ 1 -/
theorem LTileable_odd_ge5_x_6iplus3_set (n : ℕ) (hn : n ≥ 5) (hodd : n % 2 = 1)
    (i : ℕ) (hi : i ≥ 1) :
    SetTileable (rect 0 0 n (6 * i + 3)) LProtoset_set := by
  induction n using Nat.strong_induction_on with
  | _ n ih => 
    rcases Nat.eq_or_lt_of_le hn with rfl | hn_gt
    · exact LTileable_5x_6iplus3_set i hi
    · -- n ≥ 7 odd: strip a 2×(6i+3) column on the right
      have hn2 : n - 2 ≥ 5 := by omega
      have hodd2 : (n - 2) % 2 = 1 := by omega
      have h_left := ih (n - 2) (by omega) (by omega) hodd2
      -- h_left : SetTileable (rect 0 0 (n-2) (6i+3))
      have h_strip_base : SetTileable (rect 0 0 2 (6*i+3)) LProtoset_set := by
        -- 2×(6i+3) = 2×(3*(2i+1)) — use LTileable_2x_mult3_set
        have := LTileable_2x_mult3_set (2*i+1) (by omega)
        convert this using 2; ring
      have h_strip : SetTileable (rect (↑(n-2) : ℤ) 0 (↑(n-2) + 2) (6*i+3)) LProtoset_set := by
        convert setTileable_translate h_strip_base (↑(n-2) : ℤ) 0 using 1
        ext ⟨x,y⟩; simp [mem_rect, mem_translate]; push_cast; omega
      have hun := SetTileable.horizontal_union (by positivity) (by positivity) h_left h_strip
      convert hun using 2; push_cast; omega

/-- n × (3k) is L-tileable for odd n ≥ 3, k ≥ 2, and ¬(n=3 ∧ k odd) -/
theorem LTileable_odd_x_mult3_set (n k : ℕ) (hn : n ≥ 3) (hodd : n % 2 = 1) (hk : k ≥ 2)
    (h_not : ¬(n = 3 ∧ k % 2 = 1)) :
    SetTileable (rect 0 0 n (3 * k)) LProtoset_set := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · -- k = 2j even, 3k = 6j, j ≥ 1
    have hj : j ≥ 1 := by omega
    exact LTileable_odd_x_mult6_set n j hodd (by omega) hj
  · -- k = 2j+1 odd, 3k = 6j+3, need n ≥ 5
    have hj : j ≥ 1 := by omega
    have hn5 : n ≥ 5 := by
      rcases Nat.eq_or_lt_of_le hn with rfl | hn_gt
      · -- n = 3
        exfalso; apply h_not
        exact ⟨rfl, by omega⟩
      · -- n ≥ 4, n odd → n ≥ 5
        omega
    exact LTileable_odd_ge5_x_6iplus3_set n hn5 hodd j hj

/-- Main theorem: native proof of rect tileability characterization -/
theorem LTileable_rect_iff_set (n m : ℕ) :
    SetTileable (rect 0 0 (n : ℤ) m) LProtoset_set ↔ RectTileableConditions n m := by
  unfold RectTileableConditions
  constructor
  · intro h
    -- Necessary conditions
    rcases Nat.eq_or_lt_of_le (Nat.zero_le n) with rfl | hn_pos
    · left; simp
    rcases Nat.eq_or_lt_of_le (Nat.zero_le m) with rfl | hm_pos
    · right; left; simp
    right; right
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- 3 ∣ n * m
      have := LTileable_rect_area_dvd_set n m h
      simp [Nat.dvd_iff_mod_eq_zero] at this ⊢
      omega
    · -- n ≥ 2
      by_contra h_not
      push_neg at h_not
      interval_cases n
      · omega
      · exact not_LTileable_1xn_set m (by omega) h
    · -- m ≥ 2
      by_contra h_not
      push_neg at h_not
      interval_cases m
      · omega
      · exact not_LTileable_nx1_set n (by omega) h
    · -- ¬(n = 3 ∧ Odd m)
      intro ⟨rfl, hm_odd⟩
      obtain ⟨k, rfl⟩ := hm_odd
      exact not_LTileable_3x_odd_set k h
    · -- ¬(Odd n ∧ m = 3)
      intro ⟨hn_odd, rfl⟩
      rw [LTileable_nx3_iff_set] at h
      have : ¬(2 ∣ n) := by
        rw [← Nat.not_even_iff_odd]
        exact hn_odd
      omega
  · intro ⟨rfl | rfl | ⟨hdiv, hn2, hm2, h_not_3_odd, h_not_odd_3⟩⟩
    · -- n = 0: rect 0 0 0 m = ∅
      norm_num [rect]
      exact SetTileable.empty LProtoset_set
    · -- m = 0: rect 0 0 n 0 = ∅
      norm_num [rect]
      exact SetTileable.empty LProtoset_set
    · -- Main case: 3 ∣ n*m, n ≥ 2, m ≥ 2, ¬(n=3 ∧ Odd m), ¬(Odd n ∧ m=3)
      have h3div : 3 ∣ n ∨ 3 ∣ m := by
        rw [Nat.dvd_iff_mod_eq_zero] at hdiv ⊢
        apply (Nat.Prime.dvd_mul Nat.prime_three).mp
        exact Nat.dvd_of_mod_eq_zero hdiv
      rcases h3div with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · -- n = 3a
        rcases Nat.even_or_odd m with ⟨c, rfl⟩ | hm_odd
        · -- m = 2c, use LTileable_mult3_mult2_set
          have ha1 : 1 ≤ a := by omega
          have hc1 : 1 ≤ c := by omega
          exact LTileable_mult3_mult2_set a c ha1 hc1
        · -- m = 2c+1 odd
          have ha2 : a ≥ 2 := by
            by_contra h
            push_neg at h
            interval_cases a
            · omega
            · exact h_not_3_odd ⟨rfl, hm_odd⟩
          have hm_ge3 : m ≥ 3 := by omega
          have h_not' : ¬(m = 3 ∧ a % 2 = 1) := by
            intro ⟨hm_eq, ha_odd_mod⟩
            subst hm_eq
            apply h_not_odd_3
            constructor
            · -- Odd (3*a)
              rw [Nat.odd_iff, Nat.odd_mul]
              left
              exact ⟨by decide, ha_odd_mod⟩
            · rfl
          have := LTileable_swap_set (LTileable_odd_x_mult3_set m a hm_ge3 
            (Nat.odd_iff.mp hm_odd) ha2 h_not')
          rwa [swapRegion_rect] at this
      · -- m = 3b
        rcases Nat.even_or_odd n with ⟨c, rfl⟩ | hn_odd
        · -- n = 2c, use LTileable_mult3_mult2_set (swap)
          have hb1 : 1 ≤ b := by omega
          have hc1 : 1 ≤ c := by omega
          have h_tiling := LTileable_mult3_mult2_set b c hb1 hc1
          simpa [swapRegion_rect] using LTileable_swap_set h_tiling
        · -- n = 2c+1 odd
          have hb2 : b ≥ 2 := by
            by_contra h
            push_neg at h
            interval_cases b
            · omega
            · exact h_not_odd_3 ⟨hn_odd, rfl⟩
          have hn_ge3 : n ≥ 3 := by omega
          have h_not' : ¬(n = 3 ∧ b % 2 = 1) := by
            intro ⟨hn_eq, hb_odd⟩
            subst hn_eq
            apply h_not_3_odd
            constructor
            · rfl
            · -- Odd m: m = 3*b with b odd
              rw [Nat.odd_iff, Nat.odd_mul]
              left
              exact ⟨by decide, hb_odd⟩
          exact LTileable_odd_x_mult3_set n b hn_ge3 (Nat.odd_iff.mp hn_odd) hb2 h_not'


-- ============================================================
-- Deficient Rectangles: rectMinusCorner_set
-- ============================================================

/-- n×m rectangle with the top-right corner cell (n-1, m-1) removed. -/
def rectMinusCorner_set (n m : ℤ) : Set Cell :=
  rect 0 0 n m \ {(n - 1, m - 1)}

/-- rectMinusCorner_set is finite -/
theorem rectMinusCorner_set_finite (n m : ℤ) : (rectMinusCorner_set n m).Finite :=
  (rect_finite 0 0 n m).diff {(n - 1, m - 1)}

/-- ncard of rectMinusCorner_set -/
theorem rectMinusCorner_set_ncard (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (rectMinusCorner_set n m).ncard = n * m - 1 := by
  unfold rectMinusCorner_set
  have h_mem : (n - 1 : ℤ, m - 1 : ℤ) ∈ rect 0 0 (n : ℤ) m := by
    simp only [mem_rect]; push_cast; omega
  rw [diff_ncard (rect 0 0 (n : ℤ) m) {(n - 1, m - 1)} (rect_finite 0 0 (n : ℤ) m)]
  simp only [Set.inter_singleton_eq_if_mem, h_mem, ite_true]
  rw [rect_ncard 0 0 (n : ℤ) m, Set.ncard_singleton]
  simp only [Int.toNat_natCast]
  omega


/-- Swapping coordinates sends rectMinusCorner_set n m to rectMinusCorner_set m n -/
theorem swapRegion_rectMinusCorner_set (n m : ℤ) :
    swapRegion (rectMinusCorner_set n m) = rectMinusCorner_set m n := by
  ext ⟨x, y⟩
  simp only [mem_swapRegion, rectMinusCorner_set, Set.mem_diff, mem_rect,
    Set.mem_singleton_iff, Prod.mk.injEq]
  omega

/-- Horizontal split: rectMinusCorner_set (a+b) m = left_rect ∪ shifted_defect_rect -/
theorem rectMinusCorner_set_split_horiz (a b m : ℤ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) :
    rectMinusCorner_set (a + b) m =
    rect 0 0 a m ∪ translate a 0 (rectMinusCorner_set b m) := by
  ext ⟨x, y⟩
  simp only [rectMinusCorner_set, Set.mem_diff, mem_rect, Set.mem_singleton_iff,
    Prod.mk.injEq, Set.mem_union, mem_translate]
  omega

/-- Vertical split: rectMinusCorner_set n (a+b) = bottom_rect ∪ shifted_defect_rect -/
theorem rectMinusCorner_set_split_vert (n a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) :
    rectMinusCorner_set n (a + b) =
    rect 0 0 n a ∪ translate 0 a (rectMinusCorner_set n b) := by
  ext ⟨x, y⟩
  simp only [rectMinusCorner_set, Set.mem_diff, mem_rect, Set.mem_singleton_iff,
    Prod.mk.injEq, Set.mem_union, mem_translate]
  omega

/-- If ps tiles rect 0 0 a m and ps tiles translate a 0 (rectMinusCorner_set b m),
    then ps tiles rectMinusCorner_set (a+b) m. -/
theorem LTileable_horiz_union_rectMinusCorner_set {a b m : ℤ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (hleft : SetTileable (rect 0 0 a m) LProtoset_set)
    (hright : SetTileable (translate a 0 (rectMinusCorner_set b m)) LProtoset_set) :
    SetTileable (rectMinusCorner_set (a + b) m) LProtoset_set := by
  rw [rectMinusCorner_set_split_horiz a b m ha hb hm]
  apply SetTileable.union hleft hright
  rw [Set.disjoint_left]
  intro ⟨x, y⟩ h1 h2
  simp only [mem_rect] at h1
  simp only [mem_translate, rectMinusCorner_set, Set.mem_diff, mem_rect] at h2
  obtain ⟨⟨x', y', ⟨⟨hx'1, _, _, _⟩, _⟩, hxeq, _⟩⟩ := h2
  linarith [h1.2, hxeq ▸ hx'1]

/-- Vertical union analogue -/
theorem LTileable_vert_union_rectMinusCorner_set {n a b : ℤ} (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (hbottom : SetTileable (rect 0 0 n a) LProtoset_set)
    (htop : SetTileable (translate 0 a (rectMinusCorner_set n b)) LProtoset_set) :
    SetTileable (rectMinusCorner_set n (a + b)) LProtoset_set := by
  rw [rectMinusCorner_set_split_vert n a b ha hb hn]
  apply SetTileable.union hbottom htop
  rw [Set.disjoint_left]
  intro ⟨x, y⟩ h1 h2
  simp only [mem_rect] at h1
  simp only [mem_translate, rectMinusCorner_set, Set.mem_diff, mem_rect] at h2
  obtain ⟨⟨x', y', ⟨⟨_, _, hy'1, _⟩, _⟩, _, hyeq⟩⟩ := h2
  linarith [h1.4, hyeq ▸ hy'1]

/-- Swap tileability for rectMinusCorner_set -/
theorem LTileable_swap_rectMinusCorner_set {n m : ℤ}
    (h : SetTileable (rectMinusCorner_set n m) LProtoset_set) :
    SetTileable (rectMinusCorner_set m n) LProtoset_set := by
  have := LTileable_swap_set h
  rwa [swapRegion_rectMinusCorner_set] at this
