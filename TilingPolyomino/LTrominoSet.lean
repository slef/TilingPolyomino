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

set_option maxHeartbeats 20000000 in
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
      rintro ⟨hx1, hx2, hy1, hy2⟩
      interval_cases x <;> interval_cases y <;> simp_all
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨6, by simp_all <;> omega⟩
      · exact ⟨6, by simp_all <;> omega⟩
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨5, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨7, by simp_all <;> omega⟩
      · exact ⟨6, by simp_all <;> omega⟩
      · exact ⟨11, by simp_all <;> omega⟩
      · exact ⟨11, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩
      · exact ⟨5, by simp_all <;> omega⟩
      · exact ⟨5, by simp_all <;> omega⟩
      · exact ⟨8, by simp_all <;> omega⟩
      · exact ⟨7, by simp_all <;> omega⟩
      · exact ⟨7, by simp_all <;> omega⟩
      · exact ⟨12, by simp_all <;> omega⟩
      · exact ⟨11, by simp_all <;> omega⟩
      · exact ⟨13, by simp_all <;> omega⟩
      · exact ⟨14, by simp_all <;> omega⟩
      · exact ⟨14, by simp_all <;> omega⟩
      · exact ⟨10, by simp_all <;> omega⟩
      · exact ⟨8, by simp_all <;> omega⟩
      · exact ⟨8, by simp_all <;> omega⟩
      · exact ⟨9, by simp_all <;> omega⟩
      · exact ⟨12, by simp_all <;> omega⟩
      · exact ⟨12, by simp_all <;> omega⟩
      · exact ⟨13, by simp_all <;> omega⟩
      · exact ⟨13, by simp_all <;> omega⟩
      · exact ⟨14, by simp_all <;> omega⟩
      · exact ⟨10, by simp_all <;> omega⟩
      · exact ⟨10, by simp_all <;> omega⟩
      · exact ⟨9, by simp_all <;> omega⟩
      · exact ⟨9, by simp_all <;> omega⟩

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
    have h_left : SetTileable (rect 0 0 5 (↑(6*(k+1)+3) : ℤ)) LProtoset_set := by
      have := ih (by omega); convert this using 2
    have h_right_base : SetTileable (rect 0 0 5 6) LProtoset_set := 
      LTileable_kx6_of_ge2_set 5 (by omega)
    have h_right : SetTileable (rect 0 (↑(6*(k+1)+3) : ℤ) 5 (↑(6*(k+1)+3) + 6)) LProtoset_set := by
      convert setTileable_translate h_right_base (0 : ℤ) (↑(6*(k+1)+3) : ℤ) using 1
      ext ⟨x,y⟩; simp [mem_rect, mem_translate]; push_cast; omega
    have hun := SetTileable.vertical_union (by positivity) (by norm_num) h_left h_right
    have heq : (↑(6*(k+1)+3) : ℤ) + 6 = 6*(↑(k+1+1):ℤ)+3 := by push_cast; ring
    rw [heq] at hun; exact hun

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
        convert this using 2 <;> (push_cast; ring)
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
    convert LTileable_odd_x_mult6_set n j hodd (by omega) hj using 2 <;> (push_cast; ring)
  · -- k = 2j+1 odd, 3k = 6j+3, need n ≥ 5
    have hj : j ≥ 1 := by omega
    have hn5 : n ≥ 5 := by
      rcases Nat.eq_or_lt_of_le hn with rfl | hn_gt
      · -- n = 3
        exfalso; apply h_not
        exact ⟨rfl, by omega⟩
      · -- n ≥ 4, n odd → n ≥ 5
        omega
    convert LTileable_odd_ge5_x_6iplus3_set n hn5 hodd j hj using 2 <;> (push_cast; ring)

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
      have : n = 1 := by omega
      subst this
      exact not_LTileable_1xn_set m (by omega) h
    · -- m ≥ 2
      by_contra h_not
      push_neg at h_not
      have : m = 1 := by omega
      subst this
      exact not_LTileable_nx1_set n (by omega) h
    · -- ¬(n = 3 ∧ Odd m)
      rintro ⟨rfl, hm_odd⟩
      obtain ⟨k, rfl⟩ := hm_odd
      apply not_LTileable_3x_odd_set k
      convert h using 2 <;> norm_cast
    · -- ¬(Odd n ∧ m = 3)
      rintro ⟨hn_odd, rfl⟩
      have h2div : 2 ∣ n := (LTileable_nx3_iff_set n).mp (by convert h using 2 <;> norm_cast)
      obtain ⟨j, hj⟩ := h2div
      rw [Nat.odd_iff] at hn_odd
      omega
  · rintro (rfl | rfl | ⟨hdiv, hn2, hm2, h_not_3_odd, h_not_odd_3⟩)
    · -- n = 0: rect 0 0 0 m = ∅
      have hempty : rect 0 0 (0:ℤ) ↑m = ∅ := by
        ext ⟨x, y⟩; simp only [mem_rect, Set.mem_empty_iff_false]
        constructor
        · rintro ⟨h1, h2, h3, h4⟩; linarith
        · intro h; exact h.elim
      simp only [Nat.cast_zero]; rw [hempty]; exact SetTileable.empty LProtoset_set
    · -- m = 0: rect 0 0 n 0 = ∅
      have hempty : rect 0 0 ↑n (0:ℤ) = ∅ := by
        ext ⟨x, y⟩; simp only [mem_rect, Set.mem_empty_iff_false]
        constructor
        · rintro ⟨h1, h2, h3, h4⟩; linarith
        · intro h; exact h.elim
      simp only [Nat.cast_zero]; rw [hempty]; exact SetTileable.empty LProtoset_set
    · -- Main case: 3 ∣ n*m, n ≥ 2, m ≥ 2, ¬(n=3 ∧ Odd m), ¬(Odd n ∧ m=3)
      have h3div : 3 ∣ n ∨ 3 ∣ m := by
        apply (Nat.Prime.dvd_mul Nat.prime_three).mp
        exact Nat.dvd_of_mod_eq_zero hdiv
      rcases h3div with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · -- n = 3a
        rcases Nat.even_or_odd m with ⟨c, rfl⟩ | hm_odd
        · -- m = 2c, use LTileable_mult3_mult2_set
          have ha1 : 1 ≤ a := by omega
          have hc1 : 1 ≤ c := by omega
          convert LTileable_mult3_mult2_set a c ha1 hc1 using 2 <;> push_cast <;> ring
        · -- m = 2c+1 odd
          have ha2 : a ≥ 2 := by
            by_contra h
            push_neg at h
            interval_cases a
            · omega
            · exact h_not_3_odd ⟨rfl, hm_odd⟩
          have hm_odd_mod : m % 2 = 1 := Nat.odd_iff.mp hm_odd
          have hm_ge3 : m ≥ 3 := by omega
          have h_not' : ¬(m = 3 ∧ a % 2 = 1) := by
            rintro ⟨hm_eq, ha_odd_mod⟩
            subst hm_eq
            apply h_not_odd_3
            constructor
            · -- Odd (3*a)
              simp only [Nat.odd_iff]; omega
            · rfl
          have := LTileable_swap_set (LTileable_odd_x_mult3_set m a hm_ge3
            hm_odd_mod ha2 h_not')
          rwa [swapRegion_rect] at this
      · -- m = 3b
        rcases Nat.even_or_odd n with ⟨c, rfl⟩ | hn_odd
        · -- n = 2c, use LTileable_mult3_mult2_set (swap)
          have hb1 : 1 ≤ b := by omega
          have hc1 : 1 ≤ c := by omega
          have h_tiling := LTileable_mult3_mult2_set b c hb1 hc1
          have h_swap := LTileable_swap_set h_tiling
          rw [swapRegion_rect] at h_swap
          convert h_swap using 2 <;> push_cast <;> ring
        · -- n = 2c+1 odd
          have hb2 : b ≥ 2 := by
            by_contra h
            push_neg at h
            interval_cases b
            · omega
            · exact h_not_odd_3 ⟨hn_odd, rfl⟩
          have hn_odd_mod : n % 2 = 1 := Nat.odd_iff.mp hn_odd
          have hn_ge3 : n ≥ 3 := by omega
          have h_not' : ¬(n = 3 ∧ b % 2 = 1) := by
            rintro ⟨hn_eq, hb_odd⟩
            subst hn_eq
            apply h_not_3_odd
            constructor
            · rfl
            · -- Odd m = 3*b with b odd
              simp only [Nat.odd_iff]; omega
          exact LTileable_odd_x_mult3_set n b hn_ge3 hn_odd_mod hb2 h_not'


/-- Corollary: tileability conditions imply SetTileable for rectangles. -/
theorem LTileable_rect_of_conditions_set (n m : ℕ) (h : RectTileableConditions n m) :
    SetTileable (rect 0 0 (n : ℤ) m) LProtoset_set :=
  (LTileable_rect_iff_set n m).mpr h

-- Helper instantiations used in rectMinusCorner family lemmas below
theorem LTileable_4x3_set : SetTileable (rect 0 0 4 3) LProtoset_set :=
  swapRegion_rect 3 4 ▸ LTileable_swap_set LTileable_3x4_set

theorem LTileable_4x6_set : SetTileable (rect 0 0 4 6) LProtoset_set :=
  LTileable_kx6_of_ge2_set 4 (by omega)

theorem LTileable_5x6_set : SetTileable (rect 0 0 5 6) LProtoset_set :=
  LTileable_kx6_of_ge2_set 5 (by omega)

-- ============================================================
-- Deficient Rectangles: rectMinusCorner_set
-- ============================================================

/-- n×m rectangle with the top-right corner cell (n-1, m-1) removed. -/
def rectMinusCorner_set (n m : ℤ) : Set Cell :=
  rect 0 0 n m \ {(n - 1, m - 1)}

/-- rectMinusCorner_set is finite -/
theorem rectMinusCorner_set_finite (n m : ℤ) : (rectMinusCorner_set n m).Finite :=
  (rect_finite 0 0 n m).diff

/-- ncard of rectMinusCorner_set -/
theorem rectMinusCorner_set_ncard (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (rectMinusCorner_set n m).ncard = n * m - 1 := by
  unfold rectMinusCorner_set
  have h_mem : ((n : ℤ) - 1, (m : ℤ) - 1) ∈ rect 0 0 (n : ℤ) m := by
    simp only [mem_rect]; push_cast; omega
  rw [Set.ncard_diff_singleton_of_mem h_mem, rect_ncard]
  push_cast
  omega


/-- Swapping coordinates sends rectMinusCorner_set n m to rectMinusCorner_set m n -/
theorem swapRegion_rectMinusCorner_set (n m : ℤ) :
    Set.swapRegion (rectMinusCorner_set n m) = rectMinusCorner_set m n := by
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
  simp only [mem_rect, mem_translate, rectMinusCorner_set, Set.mem_diff,
    Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
  omega

/-- Vertical union analogue -/
theorem LTileable_vert_union_rectMinusCorner_set {n a b : ℤ} (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (hbottom : SetTileable (rect 0 0 n a) LProtoset_set)
    (htop : SetTileable (translate 0 a (rectMinusCorner_set n b)) LProtoset_set) :
    SetTileable (rectMinusCorner_set n (a + b)) LProtoset_set := by
  rw [rectMinusCorner_set_split_vert n a b ha hb hn]
  apply SetTileable.union hbottom htop
  rw [Set.disjoint_left]
  intro ⟨x, y⟩ h1 h2
  simp only [mem_rect, mem_translate, rectMinusCorner_set, Set.mem_diff,
    Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
  omega

/-- Swap tileability for rectMinusCorner_set -/
theorem LTileable_swap_rectMinusCorner_set {n m : ℤ}
    (h : SetTileable (rectMinusCorner_set n m) LProtoset_set) :
    SetTileable (rectMinusCorner_set m n) LProtoset_set := by
  have := LTileable_swap_set h
  rwa [swapRegion_rectMinusCorner_set] at this

-- ============================================================
-- Base Cases: rectMinusCorner_set explicit tilings
-- ============================================================

/-- The 2×2 rectangle with a missing top-right corner is L-tileable. -/
theorem LTileable_2x2_minus_corner_set :
    SetTileable (rectMinusCorner_set 2 2) LProtoset_set := by
  have : rectMinusCorner_set 2 2 = rect 0 0 2 2 \ {(1, 1)} := by
    simp [rectMinusCorner_set]
  rw [this]; exact LTileable_2x2_minus_set

/-- The 5×2 rectangle with a missing top-right corner is L-tileable. -/
theorem LTileable_5x2_minus_corner_set :
    SetTileable (rectMinusCorner_set 5 2) LProtoset_set := by
  refine ⟨Fin 3, inferInstance, ⟨![
    ⟨(), (0, 0), 0⟩,
    ⟨(), (2, 1), 2⟩,
    ⟨(), (3, 0), 0⟩]⟩, ⟨?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all only [ne_eq, not_false_eq_true, Set.disjoint_iff_inter_eq_empty,
        SetTileSet.cellsAt, SetPlacedTile.cells, LProtoset_set, LPrototile_set,
        LShape_cells, LShape_eq_rects] <;>
      rect_omega
  · ext ⟨x, y⟩
    simp only [SetTileSet.coveredCells, Set.mem_iUnion, SetTileSet.cellsAt,
      SetPlacedTile.cells, LProtoset_set, LPrototile_set, LShape_cells, LShape_eq_rects,
      mem_translate, mem_rotate, mem_rect, inverseRot, rotateCell_0, rotateCell_1,
      rotateCell_2, rotateCell_3, rectMinusCorner_set, Set.mem_diff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all <;> omega
    · rintro ⟨⟨h1, h2, h3, h4⟩, hne⟩
      interval_cases x <;> interval_cases y <;> simp_all
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩

/-- The 4×4 rectangle with a missing top-right corner is L-tileable. -/
theorem LTileable_4x4_minus_corner_set :
    SetTileable (rectMinusCorner_set 4 4) LProtoset_set := by
  refine ⟨Fin 5, inferInstance, ⟨![
    ⟨(), (0, 0), 0⟩,
    ⟨(), (3, 0), 1⟩,
    ⟨(), (0, 3), 3⟩,
    ⟨(), (2, 2), 0⟩,
    ⟨(), (1, 1), 0⟩]⟩, ⟨?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all only [ne_eq, not_false_eq_true, Set.disjoint_iff_inter_eq_empty,
        SetTileSet.cellsAt, SetPlacedTile.cells, LProtoset_set, LPrototile_set,
        LShape_cells, LShape_eq_rects] <;>
      rect_omega
  · ext ⟨x, y⟩
    simp only [SetTileSet.coveredCells, Set.mem_iUnion, SetTileSet.cellsAt,
      SetPlacedTile.cells, LProtoset_set, LPrototile_set, LShape_cells, LShape_eq_rects,
      mem_translate, mem_rotate, mem_rect, inverseRot, rotateCell_0, rotateCell_1,
      rotateCell_2, rotateCell_3, rectMinusCorner_set, Set.mem_diff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all <;> omega
    · rintro ⟨⟨h1, h2, h3, h4⟩, hne⟩
      interval_cases x <;> interval_cases y <;> simp_all
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩

/-- The 5×5 rectangle with a missing top-right corner is L-tileable. -/
set_option maxHeartbeats 4000000 in
theorem LTileable_5x5_minus_corner_set :
    SetTileable (rectMinusCorner_set 5 5) LProtoset_set := by
  refine ⟨Fin 8, inferInstance, ⟨![
    ⟨(), (0, 0), 0⟩,
    ⟨(), (1, 2), 2⟩,
    ⟨(), (2, 0), 0⟩,
    ⟨(), (4, 1), 2⟩,
    ⟨(), (0, 4), 3⟩,
    ⟨(), (2, 3), 2⟩,
    ⟨(), (3, 4), 2⟩,
    ⟨(), (4, 2), 1⟩]⟩, ⟨?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all only [ne_eq, not_false_eq_true, Set.disjoint_iff_inter_eq_empty,
        SetTileSet.cellsAt, SetPlacedTile.cells, LProtoset_set, LPrototile_set,
        LShape_cells, LShape_eq_rects] <;>
      rect_omega
  · ext ⟨x, y⟩
    simp only [SetTileSet.coveredCells, Set.mem_iUnion, SetTileSet.cellsAt,
      SetPlacedTile.cells, LProtoset_set, LPrototile_set, LShape_cells, LShape_eq_rects,
      mem_translate, mem_rotate, mem_rect, inverseRot, rotateCell_0, rotateCell_1,
      rotateCell_2, rotateCell_3, rectMinusCorner_set, Set.mem_diff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all <;> omega
    · rintro ⟨⟨h1, h2, h3, h4⟩, hne⟩
      interval_cases x <;> interval_cases y <;> simp_all
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨5, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨5, by simp_all <;> omega⟩
      · exact ⟨5, by simp_all <;> omega⟩
      · exact ⟨6, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩
      · exact ⟨7, by simp_all <;> omega⟩
      · exact ⟨6, by simp_all <;> omega⟩
      · exact ⟨6, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩
      · exact ⟨7, by simp_all <;> omega⟩
      · exact ⟨7, by simp_all <;> omega⟩

/-- The 7×7 rectangle with a missing top-right corner is L-tileable. -/
set_option maxHeartbeats 8000000 in
theorem LTileable_7x7_minus_corner_set :
    SetTileable (rectMinusCorner_set 7 7) LProtoset_set := by
  refine ⟨Fin 16, inferInstance, ⟨![
    ⟨(), (0, 1), 3⟩,
    ⟨(), (2, 0), 1⟩,
    ⟨(), (0, 3), 3⟩,
    ⟨(), (2, 2), 1⟩,
    ⟨(), (1, 4), 1⟩,
    ⟨(), (0, 6), 3⟩,
    ⟨(), (3, 6), 2⟩,
    ⟨(), (2, 4), 0⟩,
    ⟨(), (4, 0), 1⟩,
    ⟨(), (3, 2), 3⟩,
    ⟨(), (4, 3), 1⟩,
    ⟨(), (4, 6), 3⟩,
    ⟨(), (6, 0), 1⟩,
    ⟨(), (5, 2), 3⟩,
    ⟨(), (6, 3), 1⟩,
    ⟨(), (5, 5), 3⟩]⟩, ⟨?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all only [ne_eq, not_false_eq_true, Set.disjoint_iff_inter_eq_empty,
        SetTileSet.cellsAt, SetPlacedTile.cells, LProtoset_set, LPrototile_set,
        LShape_cells, LShape_eq_rects] <;>
      rect_omega
  · ext ⟨x, y⟩
    simp only [SetTileSet.coveredCells, Set.mem_iUnion, SetTileSet.cellsAt,
      SetPlacedTile.cells, LProtoset_set, LPrototile_set, LShape_cells, LShape_eq_rects,
      mem_translate, mem_rotate, mem_rect, inverseRot, rotateCell_0, rotateCell_1,
      rotateCell_2, rotateCell_3, rectMinusCorner_set, Set.mem_diff, Set.mem_singleton_iff,
      Prod.mk.injEq]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all <;> omega
    · rintro ⟨⟨h1, h2, h3, h4⟩, hne⟩
      interval_cases x <;> interval_cases y <;> simp_all
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨5, by simp_all <;> omega⟩
      · exact ⟨5, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨0, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩
      · exact ⟨2, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨4, by simp_all <;> omega⟩
      · exact ⟨5, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨1, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩
      · exact ⟨3, by simp_all <;> omega⟩
      · exact ⟨7, by simp_all <;> omega⟩
      · exact ⟨7, by simp_all <;> omega⟩
      · exact ⟨6, by simp_all <;> omega⟩
      · exact ⟨8, by simp_all <;> omega⟩
      · exact ⟨9, by simp_all <;> omega⟩
      · exact ⟨9, by simp_all <;> omega⟩
      · exact ⟨10, by simp_all <;> omega⟩
      · exact ⟨7, by simp_all <;> omega⟩
      · exact ⟨6, by simp_all <;> omega⟩
      · exact ⟨6, by simp_all <;> omega⟩
      · exact ⟨8, by simp_all <;> omega⟩
      · exact ⟨8, by simp_all <;> omega⟩
      · exact ⟨9, by simp_all <;> omega⟩
      · exact ⟨10, by simp_all <;> omega⟩
      · exact ⟨10, by simp_all <;> omega⟩
      · exact ⟨11, by simp_all <;> omega⟩
      · exact ⟨11, by simp_all <;> omega⟩
      · exact ⟨12, by simp_all <;> omega⟩
      · exact ⟨13, by simp_all <;> omega⟩
      · exact ⟨13, by simp_all <;> omega⟩
      · exact ⟨14, by simp_all <;> omega⟩
      · exact ⟨15, by simp_all <;> omega⟩
      · exact ⟨15, by simp_all <;> omega⟩
      · exact ⟨11, by simp_all <;> omega⟩
      · exact ⟨12, by simp_all <;> omega⟩
      · exact ⟨12, by simp_all <;> omega⟩
      · exact ⟨13, by simp_all <;> omega⟩
      · exact ⟨14, by simp_all <;> omega⟩
      · exact ⟨14, by simp_all <;> omega⟩
      · exact ⟨15, by simp_all <;> omega⟩

-- ============================================================
-- Family Lemmas: rectMinusCorner_set by decomposition
-- ============================================================

/-- For any k, the (3k+2) × 2 rectangle with a missing corner is L-tileable.
    
    Base case: 2 × 2 minus corner is tileable (1 L-tromino).
    Step: split off a 3 × 2 rectangle (tileable), leaving (3k+2) × 2 minus corner.
-/
theorem LTileable_3kplus2_x2_minus_corner_set (k : ℕ) :
    SetTileable (rectMinusCorner_set (3 * k + 2) 2) LProtoset_set := by
  induction k with
  | zero => exact LTileable_2x2_minus_corner_set
  | succ k ih =>
    -- Split: (3*(k+1)+2) = 3 + (3*k+2)
    have heq : (3 * (↑(k+1) : ℤ) + 2) = 3 + (3 * ↑k + 2) := by push_cast; ring
    rw [heq]
    exact LTileable_horiz_union_rectMinusCorner_set (by norm_num) (by push_cast; omega)
      (by norm_num) LTileable_3x2_set
      (by exact setTileable_translate ih 3 0)

/-- The 4×7 rectangle with a missing corner is L-tileable. -/
set_option maxHeartbeats 4000000 in
theorem LTileable_4x7_minus_corner_set :
    SetTileable (rectMinusCorner_set 4 7) LProtoset_set := by
  -- Split vertically: 7 = 3 + 4
  have h_rect : SetTileable (rect 0 0 4 3) LProtoset_set := LTileable_4x3_set
  have h_minus : SetTileable (rectMinusCorner_set 4 4) LProtoset_set :=
    LTileable_4x4_minus_corner_set
  have h_union :
      SetTileable (rectMinusCorner_set 4 (3 + 4)) LProtoset_set :=
    LTileable_vert_union_rectMinusCorner_set (by norm_num) (by norm_num) (by norm_num) h_rect
      (setTileable_translate h_minus 0 3)
  simpa using h_union

/-- For any k, the 4 × (7 + 6k) rectangle with a missing corner is L-tileable.
    
    Base case: 4 × 7 is tileable.
    Step: split off a 4 × 6 rectangle (tileable), leaving 4 × (7 + 6k) minus corner.
-/
theorem LTileable_4x_7plus6k_minus_corner_set (k : ℕ) :
    SetTileable (rectMinusCorner_set 4 (7 + 6 * k)) LProtoset_set := by
  induction k with
  | zero => simp; exact LTileable_4x7_minus_corner_set
  | succ k ih =>
    -- Split: 7 + 6*(k+1) = 6 + (7 + 6*k)
    have heq : (7 + 6 * (↑(k+1) : ℤ)) = 6 + (7 + 6 * ↑k) := by push_cast; ring
    rw [heq]
    apply LTileable_vert_union_rectMinusCorner_set (a := 6) (b := 7 + 6 * ↑k) (n := 4)
    · norm_num
    · push_cast; omega
    · norm_num
    · exact LTileable_4x6_set
    · exact setTileable_translate ih 0 6

/-- For any k, the 5 × (6k+2) rectangle with a missing corner is L-tileable. -/
theorem LTileable_5x_6kplus2_minus_corner_set (k : ℕ) :
    SetTileable (rectMinusCorner_set 5 (6 * k + 2)) LProtoset_set := by
  induction k with
  | zero => simp; exact LTileable_5x2_minus_corner_set
  | succ k ih =>
    -- Split: 6*(k+1)+2 = 6 + (6*k+2)
    have heq : (6 * (↑(k+1) : ℤ) + 2) = 6 + (6 * ↑k + 2) := by push_cast; ring
    rw [heq]
    apply LTileable_vert_union_rectMinusCorner_set (a := 6) (b := 6 * ↑k + 2) (n := 5)
    · norm_num
    · push_cast; omega
    · norm_num
    · exact LTileable_5x6_set
    · exact setTileable_translate ih 0 6

/-- For any k, the 5 × (6k+5) rectangle with a missing corner is L-tileable. -/
theorem LTileable_5x_6kplus5_minus_corner_set (k : ℕ) :
    SetTileable (rectMinusCorner_set 5 (6 * k + 5)) LProtoset_set := by
  induction k with
  | zero =>
    simp
    -- 6*0+5 = 5, so this is 5×5 minus corner
    exact LTileable_5x5_minus_corner_set
  | succ k ih =>
    -- Split: 6*(k+1)+5 = 6 + (6*k+5)
    have heq : (6 * (↑(k+1) : ℤ) + 5) = 6 + (6 * ↑k + 5) := by push_cast; ring
    rw [heq]
    apply LTileable_vert_union_rectMinusCorner_set (a := 6) (b := 6 * ↑k + 5) (n := 5)
    · norm_num
    · push_cast; omega
    · norm_num
    · exact LTileable_5x6_set
    · exact setTileable_translate ih 0 6

-- ============================================================
-- Main Cases: rectMinusCorner_set iff conditions
-- ============================================================

/-- Main mod-2 case: when n ≡ m ≡ 2 (mod 3) and both ≥ 2,
    the three-cornered rectangle is L-tileable.
    
    The proof splits vertically: m = (3k) + 2
    - Bottom: n × (3k) full rectangle (tileable by classification)
    - Top: n × 2 three-cornered rectangle (Family 1 lemma)
-/
theorem LTileable_rectMinusCorner_mod2_set
    (j k : ℕ) (hj2 : j ≥ 2) (hk2 : k ≥ 2) :
    SetTileable (rectMinusCorner_set (3 * j + 2) (3 * k + 2)) LProtoset_set := by
  -- n = 3j+2, m = 3k+2
  let n := 3 * j + 2
  let m := 3 * k + 2
  have hn : (n : ℤ) ≥ 2 := by push_cast; omega
  have hm : (m : ℤ) ≥ 2 := by push_cast; omega
  
  -- Bottom part: full n × (3k) rectangle (use rect classification)
  have h_bottom : SetTileable (rect 0 0 (n : ℤ) (3 * k)) LProtoset_set := by
    apply LTileable_rect_of_conditions_set
    right; right
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- n * (3k) % 3 = 0
      have h3k : 3 ∣ 3 * k := dvd_mul_right 3 k
      have hdvd := dvd_mul_of_dvd_right h3k n
      rwa [Nat.dvd_iff_mod_eq_zero] at hdvd
    · -- n ≥ 2
      push_cast; omega
    · -- 3k ≥ 2
      push_cast; omega
    · -- ¬(n = 3 ∧ Odd (3k))
      rintro ⟨hn3, _⟩
      simp only [n] at hn3
      omega
    · -- ¬(Odd n ∧ 3k = 3)
      rintro ⟨_, hm3⟩
      have : (3 * k : ℤ) ≥ 6 := by push_cast; omega
      omega
  
  -- Top part: n × 2 three-cornered (use Family 1)
  have h_top : SetTileable (rectMinusCorner_set (n : ℤ) 2) LProtoset_set :=
    LTileable_3kplus2_x2_minus_corner_set j
  
  -- Combine: m = (3k) + 2
  have h_union : SetTileable (rectMinusCorner_set (n : ℤ) ((3 * k) + 2)) LProtoset_set :=
    LTileable_vert_union_rectMinusCorner_set (by push_cast; omega)
      (by norm_num) (by push_cast; omega) h_bottom
      (setTileable_translate h_top 0 (3 * k))
  
  exact h_union

-- ============================================================
-- Mod-1 family: 4 × (3k+1) minus corner for all k ≥ 1
-- ============================================================

/-- For any k ≥ 1, the 4 × (3k+1) rectangle with a missing corner is L-tileable.
    Base: k=1 gives 4×4. Step: split off a 4×3 strip from the bottom. -/
theorem LTileable_4x_3kplus1_minus_corner_set (k : ℕ) (hk : k ≥ 1) :
    SetTileable (rectMinusCorner_set 4 (3 * k + 1)) LProtoset_set := by
  induction k with
  | zero => exact absurd hk (by omega)
  | succ k' ih =>
    rcases k' with _ | k''
    · -- k = 1: 4 × 4
      simp only [Nat.zero_add, Nat.mul_one]
      norm_num
      exact LTileable_4x4_minus_corner_set
    · -- k = k''+2: split 3*(k''+2)+1 = 3 + (3*(k''+1)+1)
      have ih' : SetTileable (rectMinusCorner_set 4 (3 * (k'' + 1) + 1)) LProtoset_set :=
        ih (by omega)
      have heq : (3 * (↑(k'' + 2) : ℤ) + 1) = 3 + (3 * ↑(k'' + 1) + 1) := by
        push_cast; ring
      rw [heq]
      apply LTileable_vert_union_rectMinusCorner_set (a := 3) (n := 4)
      · norm_num
      · push_cast; omega
      · norm_num
      · exact LTileable_4x3_set
      · exact setTileable_translate ih' 0 3

-- ============================================================
-- Mod-1 recurrence for j ≥ 3: (3k+1) × (3j+1) via bottom full rect + top corner rect
-- ============================================================

/-- For j ≥ 3 and k ≥ 1, the (3k+1) × (3j+1) rectangle with missing corner is L-tileable.
    Proof: bottom full (3k+1) × (3*(j-1)) rect + top (3k+1) × 4 corner rect. -/
theorem LTileable_rectMinusCorner_mod1_jk_ge_set
    (j k : ℕ) (hj3 : j ≥ 3) (hk1 : k ≥ 1) :
    SetTileable (rectMinusCorner_set (3 * k + 1) (3 * j + 1)) LProtoset_set := by
  -- Let a = 3*(j-1) (bottom height), n = 3*k+1
  let n := 3 * k + 1
  let a := 3 * (j - 1)
  have hn2 : (n : ℤ) ≥ 2 := by simp only [n]; push_cast; omega
  have ha_pos : (a : ℤ) > 0 := by simp only [a]; push_cast; omega
  have hn_pos : (n : ℤ) > 0 := by simp only [n]; push_cast; omega
  -- Bottom: full n × a rectangle
  have h_bottom : SetTileable (rect 0 0 (n : ℤ) (a : ℤ)) LProtoset_set := by
    apply LTileable_rect_of_conditions_set
    right; right
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- n * a % 3 = 0: a = 3*(j-1), so 3 ∣ n*a
      have h3a : 3 ∣ a := ⟨j - 1, by simp only [a]⟩
      have hdvd := dvd_mul_of_dvd_right h3a n
      rwa [Nat.dvd_iff_mod_eq_zero] at hdvd
    · -- n ≥ 2
      simp only [n]; omega
    · -- a ≥ 2: j ≥ 3 → j-1 ≥ 2 → 3*(j-1) ≥ 6 ≥ 2
      simp only [a]; omega
    · -- ¬(n = 3 ∧ Odd a): n = 3*k+1 ≥ 4, so n ≠ 3
      rintro ⟨hn3, _⟩; simp only [n] at hn3; omega
    · -- ¬(Odd n ∧ a = 3): a ≥ 6, so a ≠ 3
      rintro ⟨_, ha3⟩; simp only [a] at ha3; omega
  -- Top: (3k+1) × 4 corner rect (via swap of 4 × (3k+1))
  have h4xn : SetTileable (rectMinusCorner_set 4 (n : ℤ)) LProtoset_set :=
    LTileable_4x_3kplus1_minus_corner_set k hk1
  have h_top : SetTileable (rectMinusCorner_set (n : ℤ) 4) LProtoset_set :=
    LTileable_swap_rectMinusCorner_set h4xn
  -- Combine: height = a + 4 = 3*(j-1) + 4 = 3*j+1
  have heq : (a : ℤ) + 4 = 3 * ↑j + 1 := by simp only [a]; push_cast; omega
  have h_union : SetTileable (rectMinusCorner_set (n : ℤ) ((a : ℤ) + 4)) LProtoset_set :=
    LTileable_vert_union_rectMinusCorner_set ha_pos (by norm_num) hn_pos
      h_bottom (setTileable_translate h_top 0 (a : ℤ))
  rw [heq] at h_union
  exact h_union

-- ============================================================
-- Mod-1 recurrence for k ≥ 3: (3k+1) × (3j+1) via left full rect + right corner rect
-- ============================================================

/-- For k ≥ 3 and j ≥ 1, the (3k+1) × (3j+1) rectangle with missing corner is L-tileable.
    Proof: left full (3*(k-1)) × (3j+1) rect + right 4 × (3j+1) corner rect. -/
theorem LTileable_rectMinusCorner_mod1_recurrence_k_ge3_set
    (j k : ℕ) (hj1 : j ≥ 1) (hk3 : k ≥ 3) :
    SetTileable (rectMinusCorner_set (3 * k + 1) (3 * j + 1)) LProtoset_set := by
  -- Let b = 3*(k-1) (left width), m = 3*j+1
  let m := 3 * j + 1
  let b := 3 * (k - 1)
  have hm_pos : (m : ℤ) > 0 := by simp only [m]; push_cast; omega
  have hb_pos : (b : ℤ) > 0 := by simp only [b]; push_cast; omega
  -- Left: full b × m rectangle
  have h_left : SetTileable (rect 0 0 (b : ℤ) (m : ℤ)) LProtoset_set := by
    apply LTileable_rect_of_conditions_set
    right; right
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- b * m % 3 = 0: b = 3*(k-1), so 3 ∣ b*m
      have h3b : 3 ∣ b := ⟨k - 1, by simp only [b]⟩
      have hdvd := dvd_mul_of_dvd_left h3b m
      rwa [Nat.dvd_iff_mod_eq_zero] at hdvd
    · -- b ≥ 2: k ≥ 3 → k-1 ≥ 2 → 3*(k-1) ≥ 6 ≥ 2
      simp only [b]; omega
    · -- m ≥ 2: j ≥ 1 → 3*j+1 ≥ 4 ≥ 2
      simp only [m]; omega
    · -- ¬(b = 3 ∧ Odd m): b ≥ 6, so b ≠ 3
      rintro ⟨hb3, _⟩; simp only [b] at hb3; omega
    · -- ¬(Odd b ∧ m = 3): m ≥ 4, so m ≠ 3
      rintro ⟨_, hm3⟩; simp only [m] at hm3; omega
  -- Right: 4 × (3j+1) corner rect
  have h_right : SetTileable (rectMinusCorner_set 4 (m : ℤ)) LProtoset_set :=
    LTileable_4x_3kplus1_minus_corner_set j hj1
  -- Combine (horizontal): width = b + 4 = 3*(k-1) + 4 = 3*k+1
  have heq : (b : ℤ) + 4 = 3 * ↑k + 1 := by simp only [b]; push_cast; omega
  have h_union : SetTileable (rectMinusCorner_set ((b : ℤ) + 4) (m : ℤ)) LProtoset_set :=
    LTileable_horiz_union_rectMinusCorner_set hb_pos (by norm_num) hm_pos
      h_left (setTileable_translate h_right (b : ℤ) 0)
  rw [heq] at h_union
  exact h_union

-- ============================================================
-- Main mod-1 case: (3k+1) × (3j+1) for all k,j ≥ 1
-- ============================================================

/-- For any j, k ≥ 1, the (3k+1) × (3j+1) rectangle with missing corner is L-tileable. -/
theorem LTileable_rectMinusCorner_mod1_set (j k : ℕ) (hj1 : j ≥ 1) (hk1 : k ≥ 1) :
    SetTileable (rectMinusCorner_set (3 * k + 1) (3 * j + 1)) LProtoset_set := by
  rcases le_or_gt k 2 with hk2 | hk3
  · -- k ≤ 2
    rcases le_or_gt j 2 with hj2 | hj3
    · -- k ≤ 2, j ≤ 2: small cases (k,j) ∈ {1,2}²
      interval_cases k <;> interval_cases j <;> simp <;>
        first
        | exact LTileable_4x4_minus_corner_set
        | exact LTileable_4x7_minus_corner_set
        | exact LTileable_swap_rectMinusCorner_set LTileable_4x7_minus_corner_set
        | exact LTileable_7x7_minus_corner_set
    · -- k ≤ 2, j ≥ 3: use jk_ge lemma
      exact LTileable_rectMinusCorner_mod1_jk_ge_set j k hj3 hk1
  · -- k ≥ 3: use recurrence
    exact LTileable_rectMinusCorner_mod1_recurrence_k_ge3_set j k hj1 (by omega)

-- ============================================================
-- Mod-2 coverage: 5 × n for any n ≡ 2 mod 3
-- ============================================================

/-- For any n with n % 3 = 2, the 5 × n rectangle with missing corner is L-tileable. -/
theorem LTileable_5x_mod2_minus_corner_set (n : ℕ) (hn : n % 3 = 2) :
    SetTileable (rectMinusCorner_set 5 n) LProtoset_set := by
  -- Write n = 6*t+2 or n = 6*t+5 depending on parity of n/3
  have hcase : (∃ t, n = 6 * t + 2) ∨ (∃ t, n = 6 * t + 5) := by
    rcases Nat.even_or_odd (n / 3) with ⟨t, ht⟩ | ⟨t, ht⟩
    · left; exact ⟨t, by omega⟩
    · right; exact ⟨t, by omega⟩
  rcases hcase with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · -- n = 6*t+2
    exact LTileable_5x_6kplus2_minus_corner_set t
  · -- n = 6*t+5
    exact LTileable_5x_6kplus5_minus_corner_set t

-- ============================================================
-- Complete mod-2 case: (3j+2) × (3k+2) for all j, k ≥ 0
-- ============================================================

/-- For any j, k ≥ 0, the (3j+2) × (3k+2) rectangle with missing corner is L-tileable. -/
theorem LTileable_mod2_minus_corner_set_all (j k : ℕ) :
    SetTileable (rectMinusCorner_set (3 * j + 2) (3 * k + 2)) LProtoset_set := by
  rcases le_or_gt k 1 with hk1 | hk2
  · interval_cases k
    · -- k = 0: (3j+2) × 2
      norm_num
      exact LTileable_3kplus2_x2_minus_corner_set j
    · -- k = 1: (3j+2) × 5
      norm_num
      apply LTileable_swap_rectMinusCorner_set
      exact LTileable_5x_mod2_minus_corner_set (3 * j + 2) (by omega)
  · rcases le_or_gt j 1 with hj1 | hj2
    · interval_cases j
      · -- j = 0: 2 × (3k+2)
        norm_num
        apply LTileable_swap_rectMinusCorner_set
        exact LTileable_3kplus2_x2_minus_corner_set k
      · -- j = 1: 5 × (3k+2)
        norm_num
        exact LTileable_5x_mod2_minus_corner_set (3 * k + 2) (by omega)
    · -- j ≥ 2, k ≥ 2
      exact LTileable_rectMinusCorner_mod2_set j k (by omega) (by omega)

-- ============================================================
-- Necessity: L-tileability implies area condition
-- ============================================================

/-- If rectMinusCorner_set n m is L-tileable, then (n*m-1) % 3 = 0. -/
theorem LTileable_rectMinusCorner_ncard_set (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2)
    (h : SetTileable (rectMinusCorner_set (n : ℤ) m) LProtoset_set) :
    (n * m - 1) % 3 = 0 := by
  have hdvd := SetTileable.ncard_dvd (ι := Unit) (ps := LProtoset_set)
    (rectMinusCorner_set_finite (n : ℤ) (m : ℤ)) h ()
  simp only [LProtoset_set, LPrototile_set_ncard,
    rectMinusCorner_set_ncard n m (by omega) (by omega)] at hdvd
  rwa [Nat.dvd_iff_mod_eq_zero] at hdvd

-- ============================================================
-- Main iff: Ash–Golomb dog-eared rectangle theorem (Set version)
-- ============================================================

/-- **Native Set-framework version of Ash–Golomb's dog-eared rectangle theorem.**
    An n×m rectangle with the top-right corner removed is L-tileable iff
    (n*m - 1) is divisible by 3, for n,m ≥ 2. -/
theorem LTileable_rectMinusCorner_iff_set (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2) :
    LTileable_set (rect 0 0 (n : ℤ) m \ {((n : ℤ) - 1, (m : ℤ) - 1)}) ↔
    (n * m - 1) % 3 = 0 := by
  simp only [LTileable_set]
  -- Rewrite the region as rectMinusCorner_set
  have hrw : rect 0 0 (n : ℤ) m \ {((n : ℤ) - 1, (m : ℤ) - 1)} =
      rectMinusCorner_set (n : ℤ) (m : ℤ) := rfl
  rw [hrw]
  constructor
  · -- Necessity
    exact LTileable_rectMinusCorner_ncard_set n m hn hm
  · -- Sufficiency: (n*m-1) % 3 = 0 ⇒ tileable
    intro hmod
    -- n*m % 3 = 1 (since n*m ≥ 4, n*m - 1 ≥ 1, and (n*m-1) % 3 = 0)
    have hpos : n * m ≥ 1 := Nat.mul_pos (by omega) (by omega)
    have hnm1 : n * m % 3 = 1 := by omega
    -- Either n ≡ m ≡ 1 mod 3, or n ≡ m ≡ 2 mod 3
    have hres := mod3_both_one_or_two_of_area_mod3_zero hnm1
    rcases hres with ⟨hn1, hm1⟩ | ⟨hn2, hm2⟩
    · -- Mod-1 case: n = 3*k+1, m = 3*j+1 with k,j ≥ 1
      let k := n / 3; let j := m / 3
      have hk1 : k ≥ 1 := by simp only [k]; omega
      have hj1 : j ≥ 1 := by simp only [j]; omega
      have hn_eq : n = 3 * k + 1 := by simp only [k]; omega
      have hm_eq : m = 3 * j + 1 := by simp only [j]; omega
      have h := LTileable_rectMinusCorner_mod1_set j k hj1 hk1
      convert h using 2
      · push_cast; omega
      · push_cast; omega
    · -- Mod-2 case: n = 3*j+2, m = 3*k+2 with j,k ≥ 0
      let j := n / 3; let k := m / 3
      have hn_eq : n = 3 * j + 2 := by simp only [j]; omega
      have hm_eq : m = 3 * k + 2 := by simp only [k]; omega
      have h := LTileable_mod2_minus_corner_set_all j k
      convert h using 2
      · push_cast; omega
      · push_cast; omega

-- ============================================================
-- Deficient Rectangles: rectMinus2Corner_set
-- ============================================================

/-- n×m rectangle with two adjacent top-right corners removed. -/
def rectMinus2Corner_set (n m : ℤ) : Set Cell :=
  rect 0 0 n m \ ({(n - 1, m - 1)} ∪ {(n - 2, m - 1)})

-- ============================================================
-- Helper: piece2_set (rect 0 0 4 (3k+1) minus top-left corner)
-- ============================================================

/-- The 4×4 rectangle minus the top-left corner {(0,3)} is L-tileable.
    Tiles: r=0 at (0,0), r=1 at (1,2), r=1 at (2,1), r=1 at (3,0), r=2 at (3,3). -/
set_option maxHeartbeats 4000000 in
lemma LTileable_piece2_base_set :
    SetTileable (rect 0 0 4 4 \ {(0 : ℤ, 3 : ℤ)}) LProtoset_set := by
  refine ⟨Fin 5, inferInstance, ⟨![
    ⟨(), (0, 0), 0⟩,
    ⟨(), (1, 2), 1⟩,
    ⟨(), (2, 1), 1⟩,
    ⟨(), (3, 0), 1⟩,
    ⟨(), (3, 3), 2⟩]⟩, ⟨?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all only [ne_eq, not_false_eq_true, Set.disjoint_iff_inter_eq_empty,
        SetTileSet.cellsAt, SetPlacedTile.cells, LProtoset_set, LPrototile_set,
        LShape_cells, LShape_eq_rects] <;>
      rect_omega
  · ext ⟨x, y⟩
    simp only [SetTileSet.coveredCells, Set.mem_iUnion, SetTileSet.cellsAt,
      SetPlacedTile.cells, LProtoset_set, LPrototile_set, LShape_cells, LShape_eq_rects,
      mem_translate, mem_rotate, mem_rect, inverseRot, rotateCell_0, rotateCell_1,
      rotateCell_2, rotateCell_3, Set.mem_diff, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all <;> omega
    · rintro ⟨⟨h1, h2, h3, h4⟩, hne⟩
      interval_cases x <;> interval_cases y <;> simp_all
      · exact ⟨0, by simp_all <;> omega⟩  -- (0,0)
      · exact ⟨0, by simp_all <;> omega⟩  -- (0,1)
      · exact ⟨1, by simp_all <;> omega⟩  -- (0,2)
      · exact ⟨0, by simp_all <;> omega⟩  -- (1,0)
      · exact ⟨2, by simp_all <;> omega⟩  -- (1,1)
      · exact ⟨1, by simp_all <;> omega⟩  -- (1,2)
      · exact ⟨1, by simp_all <;> omega⟩  -- (1,3)
      · exact ⟨3, by simp_all <;> omega⟩  -- (2,0)
      · exact ⟨2, by simp_all <;> omega⟩  -- (2,1)
      · exact ⟨2, by simp_all <;> omega⟩  -- (2,2)
      · exact ⟨4, by simp_all <;> omega⟩  -- (2,3)
      · exact ⟨3, by simp_all <;> omega⟩  -- (3,0)
      · exact ⟨3, by simp_all <;> omega⟩  -- (3,1)
      · exact ⟨4, by simp_all <;> omega⟩  -- (3,2)
      · exact ⟨4, by simp_all <;> omega⟩  -- (3,3)

/-- rect 0 0 4 (3k+1) minus the top-left corner {(0, 3k)} is L-tileable for k ≥ 1. -/
private lemma LTileable_piece2_set (k : ℕ) (hk : k ≥ 1) :
    SetTileable (rect 0 0 4 (3 * (k : ℤ) + 1) \ {(0 : ℤ, 3 * k)}) LProtoset_set := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      convert LTileable_piece2_base_set using 2 <;> norm_num
    · have ih' := ih hn
      have heq : rect 0 0 4 (3 * (↑(n + 1) : ℤ) + 1) \ {(0 : ℤ, 3 * ↑(n + 1))} =
          rect 0 0 4 3 ∪ translate 0 3 (rect 0 0 4 (3 * (n : ℤ) + 1) \ {(0 : ℤ, 3 * ↑n)}) := by
        ext ⟨x, y⟩
        simp only [Set.mem_diff, mem_rect, Set.mem_union, mem_translate, Set.mem_singleton_iff,
          Prod.mk.injEq]
        push_cast; omega
      rw [heq]
      apply SetTileable.union LTileable_4x3_set (setTileable_translate ih' 0 3)
      rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [mem_rect, mem_translate, Set.mem_diff, Set.mem_singleton_iff,
        Prod.mk.injEq] at h1 h2
      omega

-- ============================================================
-- Step 3: 4 × (3k+2) minus 2 corners
-- ============================================================

/-- 4×(3k+2) rectangle minus two top-right corners is L-tileable for k ≥ 1. -/
theorem LTileable_4x_3kplus2_minus_2corner_set (k : ℕ) (hk : k ≥ 1) :
    SetTileable (rectMinus2Corner_set 4 (3 * (k : ℤ) + 2)) LProtoset_set := by
  have hdecomp : rectMinus2Corner_set 4 (3 * (k : ℤ) + 2) =
      ({(0 : ℤ, 3 * k + 1), (1, 3 * k + 1), (0, 3 * k)} : Set Cell) ∪
      (rect 0 0 4 (3 * (k : ℤ) + 1) \ {(0 : ℤ, 3 * k)}) := by
    ext ⟨x, y⟩
    simp only [rectMinus2Corner_set, Set.mem_diff, mem_rect, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    push_cast; omega
  have hdisj : Disjoint
      ({(0 : ℤ, 3 * k + 1), (1, 3 * k + 1), (0, 3 * k)} : Set Cell)
      (rect 0 0 4 (3 * (k : ℤ) + 1) \ {(0 : ℤ, 3 * k)}) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
      Set.mem_diff, mem_rect, Set.mem_singleton_iff] at h1 h2
    push_cast at *; omega
  have hpiece1 : SetTileable
      ({(0 : ℤ, 3 * k + 1), (1, 3 * k + 1), (0, 3 * k)} : Set Cell) LProtoset_set := by
    refine ⟨Fin 1, inferInstance, ⟨![⟨(), (0, 3 * (k : ℤ) + 1), 3⟩]⟩, ⟨?_, ?_⟩⟩
    · intro i j hij; fin_cases i; fin_cases j; exact (hij rfl).elim
    · ext ⟨x, y⟩
      simp only [SetTileSet.coveredCells, Set.mem_iUnion, Fin.exists_fin_one,
        SetTileSet.cellsAt, SetPlacedTile.cells, LProtoset_set, LPrototile_set, LShape_cells,
        mem_translate, mem_rotate, inverseRot, rotateCell_3,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      push_cast; omega
  rw [hdecomp]
  exact SetTileable.union hpiece1 (LTileable_piece2_set k hk) hdisj

-- ============================================================
-- Step 5: (3j+2) × (3k+1) minus 2 corners (proved before Step 4)
-- ============================================================

/-- Modular arithmetic helper: ((3j+2)*(3k-1) - 1) % 3 = 0 for j,k ≥ 1. -/
private lemma piece5_area_mod (j k : ℕ) (hj : j ≥ 1) (hk : k ≥ 1) :
    ((3 * j + 2) * (3 * k - 1) - 1) % 3 = 0 := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 : 3 * (k' + 1) - 1 = 3 * k' + 2 := by omega
  simp only [h1]
  have h2 : (3 * (j' + 1) + 2) * (3 * k' + 2) =
      3 * (3 * j' * k' + 2 * j' + 5 * k' + 3) + 1 := by ring
  have h3 : 0 < (3 * (j' + 1) + 2) * (3 * k' + 2) := by positivity
  omega

/-- (3j+2)×(3k+1) minus two top-right corners is L-tileable for j,k ≥ 1. -/
theorem LTileable_3jplus2_x_3kplus1_minus_2corner_set (j k : ℕ) (hj : j ≥ 1) (hk : k ≥ 1) :
    SetTileable (rectMinus2Corner_set (3 * (j : ℤ) + 2) (3 * k + 1)) LProtoset_set := by
  -- Decompose into A ∪ B ∪ C:
  -- A = rectMinusCorner_set (3j+2) (3k-1)
  -- B = translate 0 (3k-1) (rect 0 0 (3j) 2)
  -- C = {(3j+1, 3k-1), (3j+1, 3k-2), (3j, 3k-1)} (L-tromino, r=2 at (3j+1, 3k-1))
  have hdecomp : rectMinus2Corner_set (3 * (j : ℤ) + 2) (3 * k + 1) =
      rectMinusCorner_set (3 * (j : ℤ) + 2) (3 * k - 1) ∪
      translate 0 (3 * (k : ℤ) - 1) (rect 0 0 (3 * j) 2) ∪
      ({(3 * (j : ℤ) + 1, 3 * (k : ℤ) - 1), (3 * (j : ℤ) + 1, 3 * (k : ℤ) - 2), (3 * (j : ℤ), 3 * (k : ℤ) - 1)} : Set Cell) := by
    ext ⟨x, y⟩
    simp only [rectMinus2Corner_set, rectMinusCorner_set, Set.mem_diff, mem_rect, Set.mem_union,
      mem_translate, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    push_cast; omega
  have hdisj_AB : Disjoint
      (rectMinusCorner_set (3 * (j : ℤ) + 2) (3 * k - 1))
      (translate 0 (3 * (k : ℤ) - 1) (rect 0 0 (3 * j) 2)) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [rectMinusCorner_set, Set.mem_diff, mem_rect, Set.mem_singleton_iff,
      mem_translate, Prod.mk.injEq] at h1 h2
    push_cast at *; omega
  have hdisj_ABC : Disjoint
      (rectMinusCorner_set (3 * (j : ℤ) + 2) (3 * k - 1) ∪
       translate 0 (3 * (k : ℤ) - 1) (rect 0 0 (3 * j) 2))
      ({(3 * (j : ℤ) + 1, 3 * (k : ℤ) - 1), (3 * (j : ℤ) + 1, 3 * (k : ℤ) - 2), (3 * (j : ℤ), 3 * (k : ℤ) - 1)} : Set Cell) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    simp only [Set.mem_union, rectMinusCorner_set, Set.mem_diff, mem_rect,
      Set.mem_singleton_iff, mem_translate, Set.mem_insert_iff, Prod.mk.injEq] at h1 h2
    push_cast at *; omega
  have hA : SetTileable (rectMinusCorner_set (3 * (j : ℤ) + 2) (3 * k - 1)) LProtoset_set := by
    have h := (LTileable_rectMinusCorner_iff_set (3 * j + 2) (3 * k - 1) (by omega) (by omega)).mpr
      (piece5_area_mod j k hj hk)
    simp only [LTileable_set] at h
    convert h using 1
    ext ⟨x, y⟩
    simp only [rectMinusCorner_set, Set.mem_diff, mem_rect, Set.mem_singleton_iff, Prod.mk.injEq]
    push_cast; omega
  have hB : SetTileable (translate 0 (3 * (k : ℤ) - 1) (rect 0 0 (3 * (j : ℤ)) 2))
      LProtoset_set := by
    apply setTileable_translate
    apply LTileable_rect_of_conditions_set
    unfold RectTileableConditions
    right; right
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have : 3 * j * 2 % 3 = 0 := by omega
      exact_mod_cast this
    · omega
    · omega
    · intro ⟨h1, h2⟩; omega
    · intro ⟨h1, h2⟩; norm_num at h2
  have hC : SetTileable
      ({(3 * (j : ℤ) + 1, 3 * (k : ℤ) - 1), (3 * (j : ℤ) + 1, 3 * (k : ℤ) - 2), (3 * (j : ℤ), 3 * (k : ℤ) - 1)} : Set Cell)
      LProtoset_set := by
    refine ⟨Fin 1, inferInstance, ⟨![⟨(), (3 * (j : ℤ) + 1, 3 * k - 1), 2⟩]⟩, ⟨?_, ?_⟩⟩
    · intro i j' hij; fin_cases i; fin_cases j'; exact (hij rfl).elim
    · ext ⟨x, y⟩
      simp only [SetTileSet.coveredCells, Set.mem_iUnion, Fin.exists_fin_one,
        SetTileSet.cellsAt, SetPlacedTile.cells, LProtoset_set, LPrototile_set, LShape_cells,
        mem_translate, mem_rotate, inverseRot, rotateCell_2,
        Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
      push_cast; omega
  rw [hdecomp]
  exact SetTileable.union (SetTileable.union hA hB hdisj_AB) hC hdisj_ABC

-- ============================================================
-- Step 4: (3j+1) × (3k+2) minus 2 corners
-- ============================================================

/-- (3j+1)×(3k+2) minus two top-right corners is L-tileable for j,k ≥ 1. -/
set_option maxHeartbeats 4000000 in
theorem LTileable_3jplus1_x_3kplus2_minus_2corner_set (j k : ℕ) (hj : j ≥ 1) (hk : k ≥ 1) :
    SetTileable (rectMinus2Corner_set (3 * (j : ℤ) + 1) (3 * k + 2)) LProtoset_set := by
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
    · -- j = 1: base case
      subst hn0
      convert LTileable_4x_3kplus2_minus_2corner_set k hk using 2 <;> norm_num
    · rcases Nat.eq_or_lt_of_le hn_pos with hn1 | hn2
      · -- j = 2 (n = 1): special case, split on k parity
        have hn1eq : n = 1 := by omega
        rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
        · -- k even: simple split
          have hdecomp : rectMinus2Corner_set (3 * (↑(n + 1) : ℤ) + 1) (3 * ↑k + 2) =
              rect 0 0 3 (3 * (k : ℤ) + 2) ∪
              translate 3 0 (rectMinus2Corner_set 4 (3 * ↑k + 2)) := by
            ext ⟨x, y⟩
            simp only [rectMinus2Corner_set, Set.mem_diff, mem_rect, Set.mem_union,
              mem_translate, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
            push_cast; omega
          have hdisj : Disjoint
              (rect 0 0 3 (3 * (k : ℤ) + 2))
              (translate 3 0 (rectMinus2Corner_set 4 (3 * ↑k + 2))) := by
            rw [Set.disjoint_left]
            rintro ⟨x, y⟩ h1 h2
            simp only [mem_rect, mem_translate, rectMinus2Corner_set, Set.mem_diff, mem_rect,
              Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
            push_cast at *; omega
          have hleft : SetTileable (rect 0 0 3 (3 * (k : ℤ) + 2)) LProtoset_set := by
            apply LTileable_rect_of_conditions_set
            unfold RectTileableConditions; right; right
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · have : 3 * (3 * k + 2) % 3 = 0 := by omega
              exact_mod_cast this
            · omega
            · omega
            · intro ⟨_, hodd⟩
              rw [Nat.odd_iff] at hodd
              subst hm; omega
            · intro ⟨hodd, h2⟩; omega
          rw [hdecomp]
          exact SetTileable.union hleft
            (setTileable_translate (LTileable_4x_3kplus2_minus_2corner_set k hk) 3 0) hdisj
        · -- k odd: pieceA ∪ pieceB ∪ pieceC decomposition of 7×(3k+2)
          -- pieceA = rect 0 0 4 (3k+2) \ {(3,3k+1),(3,3k)}
          -- pieceB = {(3,3k+1),(4,3k+1),(3,3k)} (L-tromino r=3 at (3,3k+1))
          -- pieceC = translate 4 0 (rect 0 0 3 (3k+1))
          have hdecomp7 : rectMinus2Corner_set (3 * (↑(n + 1) : ℤ) + 1) (3 * ↑k + 2) =
              (rect 0 0 4 (3 * (k : ℤ) + 2) \ ({(3, 3 * k + 1)} ∪ {(3, 3 * k)})) ∪
              ({(3 : ℤ, 3 * k + 1), (4, 3 * k + 1), (3, 3 * k)} : Set Cell) ∪
              translate 4 0 (rect 0 0 3 (3 * (k : ℤ) + 1)) := by
            ext ⟨x, y⟩
            simp only [rectMinus2Corner_set, Set.mem_diff, mem_rect, Set.mem_union,
              Set.mem_insert_iff, Set.mem_singleton_iff, mem_translate, Prod.mk.injEq]
            push_cast; omega
          have hdisj_AB : Disjoint
              (rect 0 0 4 (3 * (k : ℤ) + 2) \ ({(3, 3 * k + 1)} ∪ {(3, 3 * k)}))
              ({(3 : ℤ, 3 * k + 1), (4, 3 * k + 1), (3, 3 * k)} : Set Cell) := by
            rw [Set.disjoint_left]
            rintro ⟨x, y⟩ h1 h2
            simp only [Set.mem_diff, mem_rect, Set.mem_union, Set.mem_singleton_iff,
              Set.mem_insert_iff, Prod.mk.injEq] at h1 h2
            push_cast at *; omega
          have hdisj_ABC : Disjoint
              (rect 0 0 4 (3 * (k : ℤ) + 2) \ ({(3, 3 * k + 1)} ∪ {(3, 3 * k)}) ∪
               ({(3 : ℤ, 3 * k + 1), (4, 3 * k + 1), (3, 3 * k)} : Set Cell))
              (translate 4 0 (rect 0 0 3 (3 * (k : ℤ) + 1))) := by
            rw [Set.disjoint_left]
            rintro ⟨x, y⟩ h1 h2
            simp only [Set.mem_union, Set.mem_diff, mem_rect, Set.mem_insert_iff,
              Set.mem_singleton_iff, Prod.mk.injEq, mem_translate] at h1 h2
            push_cast at *; omega
          -- Tileability of pieceA via swapRegion
          have hA : SetTileable
              (rect 0 0 4 (3 * (k : ℤ) + 2) \ ({(3, 3 * k + 1)} ∪ {(3, 3 * k)}))
              LProtoset_set := by
            have heq : rect 0 0 4 (3 * (k : ℤ) + 2) \ ({(3, 3 * k + 1)} ∪ {(3, 3 * k)}) =
                Set.swapRegion (rectMinus2Corner_set (3 * (k : ℤ) + 2) 4) := by
              ext ⟨x, y⟩
              simp only [Set.mem_diff, mem_rect, Set.mem_union, Set.mem_singleton_iff,
                Set.mem_swapRegion, rectMinus2Corner_set, Prod.mk.injEq]
              push_cast; omega
            rw [heq]
            exact LTileable_swap_set
              (LTileable_3jplus2_x_3kplus1_minus_2corner_set k 1 hk (by omega))
          -- Tileability of pieceB (L-tromino r=3 at (3,3k+1))
          have hB : SetTileable
              ({(3 : ℤ, 3 * k + 1), (4, 3 * k + 1), (3, 3 * k)} : Set Cell) LProtoset_set := by
            refine ⟨Fin 1, inferInstance, ⟨![⟨(), (3, 3 * (k : ℤ) + 1), 3⟩]⟩, ⟨?_, ?_⟩⟩
            · intro i j' hij; fin_cases i; fin_cases j'; exact (hij rfl).elim
            · ext ⟨x, y⟩
              simp only [SetTileSet.coveredCells, Set.mem_iUnion, Fin.exists_fin_one,
                SetTileSet.cellsAt, SetPlacedTile.cells, LProtoset_set, LPrototile_set,
                LShape_cells, mem_translate, mem_rotate, inverseRot, rotateCell_3,
                Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
              push_cast; omega
          -- Tileability of pieceC = translate 4 0 (rect 0 0 3 (3k+1))
          -- When k is odd, 3k+1 is even, so rect 0 0 3 (3k+1) is tileable
          have hC : SetTileable (translate 4 0 (rect 0 0 3 (3 * (k : ℤ) + 1))) LProtoset_set := by
            have : n = 1 := hn1eq
            apply setTileable_translate
            apply LTileable_rect_of_conditions_set
            unfold RectTileableConditions; right; right
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · have : 3 * (3 * k + 1) % 3 = 0 := by omega
              exact_mod_cast this
            · omega
            · omega
            · -- ¬(3=3 ∧ Odd(3k+1)): k odd → 3k is odd → 3k+1 is even → ¬Odd(3k+1)
              rintro ⟨_, hodd⟩
              rw [Nat.odd_iff] at hodd
              subst hm; omega
            · intro ⟨_, h2⟩; omega
          rw [hdecomp7]
          exact SetTileable.union (SetTileable.union hA hB hdisj_AB) hC hdisj_ABC
      · -- j ≥ 3 (n ≥ 2): split off 3*n columns on the left
        -- Left: rect 0 0 (3n) (3k+2), Right: translate (3n) 0 (rectMinus2Corner_set 4 (3k+2))
        have hdecomp : rectMinus2Corner_set (3 * (↑(n + 1) : ℤ) + 1) (3 * ↑k + 2) =
            rect 0 0 (3 * (n : ℤ)) (3 * k + 2) ∪
            translate (3 * (n : ℤ)) 0 (rectMinus2Corner_set 4 (3 * ↑k + 2)) := by
          ext ⟨x, y⟩
          simp only [rectMinus2Corner_set, Set.mem_diff, mem_rect, Set.mem_union, mem_translate,
            Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          push_cast; omega
        have hdisj : Disjoint
            (rect 0 0 (3 * (n : ℤ)) (3 * k + 2))
            (translate (3 * (n : ℤ)) 0 (rectMinus2Corner_set 4 (3 * ↑k + 2))) := by
          rw [Set.disjoint_left]
          rintro ⟨x, y⟩ h1 h2
          simp only [mem_rect, mem_translate, rectMinus2Corner_set, Set.mem_diff, mem_rect,
            Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
          push_cast at *; omega
        -- n ≥ 2, so 3*n ≥ 6, avoiding the 3×odd forbidden case
        have hleft : SetTileable (rect 0 0 (3 * (n : ℤ)) (3 * k + 2)) LProtoset_set := by
          apply LTileable_rect_of_conditions_set
          unfold RectTileableConditions; right; right
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · have : 3 * n * (3 * k + 2) % 3 = 0 := by omega
            exact_mod_cast this
          · omega
          · omega
          · intro ⟨h1, _⟩; omega  -- 3*n = 3 → n=1, but n ≥ 2
          · intro ⟨_, h2⟩; omega  -- 3*k+2 = 3 → impossible since k ≥ 1
        rw [hdecomp]
        exact SetTileable.union hleft
          (setTileable_translate (LTileable_4x_3kplus2_minus_2corner_set k hk) _ _) hdisj

-- ============================================================
-- Step 6: Main theorem
-- ============================================================

/-- **Native Set-framework version of the two-corner-deficient rectangle theorem.**
    An n×m rectangle with two adjacent top-right corners removed is L-tileable
    when n*m ≡ 2 (mod 3), for n, m ≥ 3. -/
theorem LTileable_rectMinus2Corner_set (n m : ℕ) (hn : n ≥ 3) (hm : m ≥ 3)
    (hmod : n * m % 3 = 2) :
    LTileable_set (rect 0 0 (n : ℤ) m \ ({((n : ℤ) - 1, (m : ℤ) - 1)} ∪
                                          {((n : ℤ) - 2, (m : ℤ) - 1)})) := by
  simp only [LTileable_set]
  have hrw : rect 0 0 (n : ℤ) m \ ({((n : ℤ) - 1, (m : ℤ) - 1)} ∪ {((n : ℤ) - 2, (m : ℤ) - 1)}) =
      rectMinus2Corner_set (n : ℤ) m := rfl
  rw [hrw]
  have h_cases := mod3_one_two_or_two_one_of_area_mod3_two hmod
  rcases h_cases with ⟨hn1, hm2⟩ | ⟨hn2, hm1⟩
  · -- n ≡ 1 mod 3, m ≡ 2 mod 3
    let j := n / 3; let k := m / 3
    have hj1 : j ≥ 1 := by simp only [j]; omega
    have hk1 : k ≥ 1 := by simp only [k]; omega
    have h := LTileable_3jplus1_x_3kplus2_minus_2corner_set j k hj1 hk1
    convert h using 2
    · push_cast; simp only [j]; omega
    · push_cast; simp only [k]; omega
  · -- n ≡ 2 mod 3, m ≡ 1 mod 3
    let j := n / 3; let k := m / 3
    have hj1 : j ≥ 1 := by simp only [j]; omega
    have hk1 : k ≥ 1 := by simp only [k]; omega
    have h := LTileable_3jplus2_x_3kplus1_minus_2corner_set j k hj1 hk1
    convert h using 2
    · push_cast; simp only [j]; omega
    · push_cast; simp only [k]; omega
