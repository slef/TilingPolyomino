import Mathlib.Tactic
import TilingPolyomino.TilingSet

open Set Function

-- ============================================================
-- L-tromino shape definitions
-- ============================================================

/-- The L-tromino shape (standard orientation): {(0,0),(0,1),(1,0)} -/
def lShape_cells : Set Cell := {(0, 0), (0, 1), (1, 0)}

def lSetPrototile : SetPrototile :=
  ⟨lShape_cells, by simp [Set.finite_insert, lShape_cells], ⟨(0, 0), by simp [lShape_cells]⟩⟩

def lProtoset : SetProtoset Unit := fun _ => lSetPrototile

def lPlacedCopy (dx dy : ℤ) (r : Fin 4) : Set Cell :=
  SetPlacedTile.cells lProtoset ⟨(), (dx, dy), r⟩

@[simp] theorem lPlacedCopy_eq (dx dy : ℤ) (r : Fin 4) :
    lPlacedCopy dx dy r = translate dx dy (rotate r lShape_cells) := by
  rfl

theorem lShape_eq_rects : lShape_cells = rect 0 0 1 2 ∪ rect 1 0 2 1 := by
  ext ⟨x, y⟩
  simp [lShape_cells]
  omega

theorem lSetPrototile_ncard : lSetPrototile.cells.ncard = 3 := by
  dsimp [lSetPrototile, lShape_cells]
  rw [Set.ncard_insert_of_notMem]
  · rw [Set.ncard_insert_of_notMem]
    · rw [Set.ncard_singleton]
    · simp
  · simp

-- ============================================================
-- Swap rotation: swapRegion commutes with lPlacedCopy
-- ============================================================

def swapRot : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | 3 => 1

theorem swapRegion_lPlacedCopy (dx dy : ℤ) (r : Fin 4) :
    Set.swapRegion (lPlacedCopy dx dy r) = lPlacedCopy dy dx (swapRot r) := by
  rw [lPlacedCopy_eq, lPlacedCopy_eq, lShape_eq_rects]
  fin_cases r
  · dsimp [swapRot]
    rect_omega
  · dsimp [swapRot]
    rect_omega
  · dsimp [swapRot]
    rect_omega
  · dsimp [swapRot]
    rect_omega

theorem setTileable_swap {R : Set Cell} (h : SetTileable R lProtoset) :
    SetTileable (Set.swapRegion R) lProtoset := by
  obtain ⟨ιₜ, hft, t, hv⟩ := h
  haveI : Fintype ιₜ := hft
  let t' : SetTileSet lProtoset ιₜ := ⟨fun i =>
    ⟨(), ((t.tiles i).translation.2, (t.tiles i).translation.1), swapRot (t.tiles i).rotation⟩⟩
  have hcell : ∀ i, SetTileSet.cellsAt t' i = Set.swapRegion (SetTileSet.cellsAt t i) := by
    intro i
    rcases hti : t.tiles i with ⟨idx, tr, r⟩
    rcases tr with ⟨dx, dy⟩
    cases idx
    simpa [SetTileSet.cellsAt, t', hti, lPlacedCopy] using (swapRegion_lPlacedCopy dx dy r).symm
  refine ⟨ιₜ, hft, t', ⟨?_, ?_⟩⟩
  · intro i j hij
    have hd := hv.disjoint i j hij
    rw [Set.disjoint_left] at hd ⊢
    intro p hp1 hp2
    have hp1' : (p.2, p.1) ∈ SetTileSet.cellsAt t i := by
      simpa [hcell i, mem_swapRegion] using hp1
    have hp2' : (p.2, p.1) ∈ SetTileSet.cellsAt t j := by
      simpa [hcell j, mem_swapRegion] using hp2
    exact hd hp1' hp2'
  · ext p
    simp only [SetTileSet.coveredCells, Set.mem_iUnion, hcell, mem_swapRegion]
    constructor
    · rintro ⟨i, hi⟩
      have hpi : (p.2, p.1) ∈ SetTileSet.cellsAt t i := hi
      have hpcover : (p.2, p.1) ∈ SetTileSet.coveredCells t := Set.mem_iUnion.mpr ⟨i, hpi⟩
      have hpR : (p.2, p.1) ∈ R := by rwa [hv.covers] at hpcover
      exact hpR
    · intro hpR
      have hpcover : (p.2, p.1) ∈ SetTileSet.coveredCells t := by rwa [hv.covers]
      rcases Set.mem_iUnion.mp hpcover with ⟨i, hi⟩
      exact ⟨i, hi⟩

-- ============================================================
-- Base cases
-- ============================================================

theorem setTileable_2x3 : SetTileable (rect 0 0 2 3) lProtoset := by
  refine ⟨Fin 2, inferInstance, ⟨![⟨(), (0, 0), 0⟩, ⟨(), (1, 2), 2⟩]⟩, ⟨?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Set.disjoint_iff_inter_eq_empty, SetTileSet.cellsAt, SetPlacedTile.cells,
        lProtoset, lSetPrototile, lShape_cells,
        mem_translate, mem_rotate, inverseRot,
        rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3] <;>
      rect_omega
  · ext ⟨x, y⟩
    simp [SetTileSet.coveredCells, Set.mem_iUnion, Fin.exists_fin_two,
      SetTileSet.cellsAt, SetPlacedTile.cells,
      lProtoset, lSetPrototile, lShape_cells,
      mem_translate, mem_rotate, mem_rect, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3]
    omega

theorem setTileable_3x2 : SetTileable (rect 0 0 3 2) lProtoset := by
  refine ⟨Fin 2, inferInstance, ⟨![⟨(), (0, 0), 0⟩, ⟨(), (2, 1), 2⟩]⟩, ⟨?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Set.disjoint_iff_inter_eq_empty, SetTileSet.cellsAt, SetPlacedTile.cells,
        lProtoset, lSetPrototile, lShape_cells,
        mem_translate, mem_rotate, inverseRot,
        rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3] <;>
      rect_omega
  · ext ⟨x, y⟩
    simp [SetTileSet.coveredCells, Set.mem_iUnion, Fin.exists_fin_two,
      SetTileSet.cellsAt, SetPlacedTile.cells,
      lProtoset, lSetPrototile, lShape_cells,
      mem_translate, mem_rotate, mem_rect, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3]
    omega

theorem setTileable_2x2_minus : SetTileable (rect 0 0 2 2 \ {(1, 1)}) lProtoset := by
  refine ⟨Fin 1, inferInstance, ⟨![⟨(), (0, 0), 0⟩]⟩, ⟨?_, ?_⟩⟩
  · intro i j hij
    fin_cases i
    fin_cases j
    exact (hij rfl).elim
  · have h_sing : ({(1, 1)} : Set Cell) = rect 1 1 2 2 := by
      ext ⟨x, y⟩
      simp
      omega
    ext ⟨x, y⟩
    simp [SetTileSet.coveredCells, Set.mem_iUnion, Fin.exists_fin_one,
      SetTileSet.cellsAt, SetPlacedTile.cells,
      lProtoset, lSetPrototile, lShape_cells,
      mem_translate, mem_rotate, mem_rect, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3, h_sing]
    omega

-- ============================================================
-- Inductive rectangle families
-- ============================================================

theorem setTileable_2x6 : SetTileable (rect 0 0 2 6) lProtoset := by
  have ha : SetTileable (rect 0 0 2 3) lProtoset := setTileable_2x3
  have hb : SetTileable (rect 0 3 2 6) lProtoset := by
    have h_trans : rect 0 3 2 6 = translate 0 3 (rect 0 0 2 3) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_2x3 0 3
  exact @SetTileable.vertical_union Unit lProtoset 2 3 3 (by omega) (by omega) ha hb

theorem setTileable_6x2 : SetTileable (rect 0 0 6 2) lProtoset := by
  have h := setTileable_swap setTileable_2x6
  have h_eq : Set.swapRegion (rect 0 0 2 6) = rect 0 0 6 2 := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rw [h_eq] at h
  exact h

theorem setTileable_3x4 : SetTileable (rect 0 0 3 4) lProtoset := by
  have ha : SetTileable (rect 0 0 3 2) lProtoset := setTileable_3x2
  have hb : SetTileable (rect 0 2 3 4) lProtoset := by
    have h_trans : rect 0 2 3 4 = translate 0 2 (rect 0 0 3 2) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_3x2 0 2
  exact @SetTileable.vertical_union Unit lProtoset 3 2 2 (by omega) (by omega) ha hb

theorem setTileable_3x6 : SetTileable (rect 0 0 3 6) lProtoset := by
  have ha : SetTileable (rect 0 0 3 2) lProtoset := setTileable_3x2
  have hb : SetTileable (rect 0 2 3 6) lProtoset := by
    have h_trans : rect 0 2 3 6 = translate 0 2 (rect 0 0 3 4) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_3x4 0 2
  exact @SetTileable.vertical_union Unit lProtoset 3 2 4 (by omega) (by omega) ha hb

theorem setTileable_6x3 : SetTileable (rect 0 0 6 3) lProtoset := by
  have h := setTileable_swap setTileable_3x6
  have h_eq : Set.swapRegion (rect 0 0 3 6) = rect 0 0 6 3 := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rw [h_eq] at h
  exact h

theorem setTileable_6x6 : SetTileable (rect 0 0 6 6) lProtoset := by
  have ha : SetTileable (rect 0 0 6 3) lProtoset := setTileable_6x3
  have hb : SetTileable (rect 0 3 6 6) lProtoset := by
    have h_trans : rect 0 3 6 6 = translate 0 3 (rect 0 0 6 3) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_6x3 0 3
  exact @SetTileable.vertical_union Unit lProtoset 6 3 3 (by omega) (by omega) ha hb

theorem setTileable_2x_mult3 (k : ℕ) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 2 (3 * k)) lProtoset := by
  have h := setTileable_2x3.scale_rect (by norm_num) (by norm_num) 1 k (by omega) hk
  convert h using 2 <;> push_cast <;> ring

theorem setTileable_3x_even (k : ℕ) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 3 (2 * k)) lProtoset := by
  have h := setTileable_3x2.scale_rect (by norm_num) (by norm_num) 1 k (by omega) hk
  convert h using 2 <;> push_cast <;> ring

theorem setTileable_mult3_x_2 (k : Nat) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 (3 * k) 2) lProtoset := by
  have h := setTileable_swap (setTileable_2x_mult3 k hk)
  have h_eq : Set.swapRegion (rect 0 0 2 (3 * k)) = rect 0 0 (3 * k) 2 := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rw [h_eq] at h
  exact h

theorem setTileable_even_x_3 (k : Nat) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 (2 * k) 3) lProtoset := by
  have h := setTileable_swap (setTileable_3x_even k hk)
  have h_eq : Set.swapRegion (rect 0 0 3 (2 * k)) = rect 0 0 (2 * k) 3 := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rw [h_eq] at h
  exact h

theorem setTileable_6x_of_ge2 (k : Nat) (hk : 2 ≤ k) :
    SetTileable (rect 0 0 6 k) lProtoset := by
  induction' k using Nat.strong_induction_on with n ih
  rcases eq_or_lt_of_le hk with rfl | hn2
  · exact setTileable_6x2
  · rcases eq_or_lt_of_le (show 3 ≤ n from hn2) with rfl | hn3
    · exact setTileable_6x3
    · have h_prev_nat : SetTileable (rect 0 0 6 (n - 2 : Nat)) lProtoset :=
        ih (n - 2) (by omega) (by omega)
      have h_prev : SetTileable (rect 0 0 6 (n - 2 : ℤ)) lProtoset := by
        have h_eq : ((n - 2 : Nat) : ℤ) = (n : ℤ) - 2 := by omega
        exact h_eq ▸ h_prev_nat
      have h_2 : SetTileable (rect 0 (n - 2 : ℤ) 6 n) lProtoset := by
        have h_trans : rect 0 (n - 2 : ℤ) 6 n = translate 0 (n - 2 : ℤ) (rect 0 0 6 2) := by
          ext ⟨x, y⟩
          simp only [mem_rect, mem_translate]
          omega
        rw [h_trans]
        exact setTileable_translate setTileable_6x2 0 (n - 2 : ℤ)
      have h_union := @SetTileable.vertical_union Unit lProtoset 6 (n - 2 : ℤ) 2 (by omega) (by omega)
        h_prev (by
          have h_eq : (n - 2 : ℤ) + 2 = (n : ℤ) := by omega
          exact h_eq.symm ▸ h_2)
      have h_eq : (n - 2 : ℤ) + 2 = n := by omega
      rw [h_eq] at h_union
      exact h_union

theorem setTileable_kx6_of_ge2 (k : Nat) (hk : 2 ≤ k) :
    SetTileable (rect 0 0 k 6) lProtoset := by
  have h := setTileable_swap (setTileable_6x_of_ge2 k hk)
  have h_eq : Set.swapRegion (rect 0 0 6 k) = rect 0 0 k 6 := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rw [h_eq] at h
  exact h

-- ============================================================
-- Area divisibility
-- ============================================================

theorem setTileable_rect_area_dvd (m n : Nat) (h : SetTileable (rect 0 0 m n) lProtoset) :
    3 ∣ m * n := by
  have h1 := SetTileable.ncard_dvd (ι := Unit) (ps := lProtoset) (rect_finite 0 0 m n) h ()
  have h3 : (rect 0 0 (m : ℤ) (n : ℤ)).ncard = m * n := by
    rw [rect_ncard]
    simp
  simpa [lProtoset, lSetPrototile_ncard, h3] using h1

-- ============================================================
-- Impossibility theorems
-- ============================================================

private lemma lPlacedCopy_contains_origin_offset (dx dy : ℤ) (r : Fin 4) :
    (dx, dy) ∈ lPlacedCopy dx dy r := by
  fin_cases r <;>
    simp [lPlacedCopy_eq, mem_translate, mem_rotate, lShape_cells, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]

private lemma lPlacedCopy_x_span (dx dy : ℤ) (r : Fin 4) :
    (dx + 1, dy) ∈ lPlacedCopy dx dy r ∨ (dx - 1, dy) ∈ lPlacedCopy dx dy r := by
  fin_cases r <;>
    simp [lPlacedCopy_eq, mem_translate, mem_rotate, lShape_cells, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] <;>
    omega

/-- No 1×n strip (n ≥ 1) is L-tileable: placed copies always span ≥ 2 x-values -/
theorem not_setTileable_1xn (n : ℕ) (hn : 1 ≤ n) : ¬ SetTileable (rect 0 0 1 n) lProtoset := by
  intro h
  obtain ⟨ιₜ, hft, t, hv⟩ := h
  haveI : Fintype ιₜ := hft
  have hcell : ((0 : ℤ), (0 : ℤ)) ∈ rect 0 0 1 (n : ℤ) := by
    simp only [mem_rect]
    exact ⟨le_refl _, by norm_num, le_refl _, by exact_mod_cast hn⟩
  rw [← hv.covers, SetTileSet.coveredCells, Set.mem_iUnion] at hcell
  obtain ⟨i, hi⟩ := hcell
  let dx : ℤ := (t.tiles i).translation.1
  let dy : ℤ := (t.tiles i).translation.2
  let r : Fin 4 := (t.tiles i).rotation
  have hrep : SetTileSet.cellsAt t i = lPlacedCopy dx dy r := by
    simp [SetTileSet.cellsAt, lPlacedCopy, dx, dy, r]
  have h_sub : ∀ q, q ∈ SetTileSet.cellsAt t i → 0 ≤ q.1 ∧ q.1 < 1 := by
    intro q hq
    have hmem : q ∈ rect 0 0 1 (n : ℤ) := by
      have : q ∈ ⋃ j, SetTileSet.cellsAt t j := Set.mem_iUnion.mpr ⟨i, hq⟩
      have : q ∈ SetTileSet.coveredCells t := by simpa [SetTileSet.coveredCells] using this
      rwa [hv.covers] at this
    simp only [mem_rect] at hmem
    exact ⟨hmem.1, hmem.2.1⟩
  rw [hrep] at hi h_sub
  have h_base : (dx, dy) ∈ lPlacedCopy dx dy r :=
    lPlacedCopy_contains_origin_offset dx dy r
  have _hbase := h_sub _ h_base
  rcases lPlacedCopy_x_span dx dy r with h2 | h2
  · have := (h_sub _ h2).2
    omega
  · have := (h_sub _ h2).1
    omega

/-- Same result for the transposed strip (n×1) -/
theorem not_setTileable_nx1 (n : ℕ) (hn : 1 ≤ n) : ¬ SetTileable (rect 0 0 n 1) lProtoset := by
  intro h
  have hswap : SetTileable (Set.swapRegion (rect 0 0 n 1)) lProtoset :=
    setTileable_swap h
  have heq : Set.swapRegion (rect 0 0 (n : ℤ) 1) = rect 0 0 1 n := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rw [heq] at hswap
  exact not_setTileable_1xn n hn hswap

-- ============================================================
-- 3×(2k+1) Impossibility
-- ============================================================

/-- ncard of any lPlacedCopy is 3 -/
private lemma lPlacedCopy_ncard (dx dy : ℤ) (r : Fin 4) :
    (lPlacedCopy dx dy r).ncard = 3 := by
  have heq : lPlacedCopy dx dy r = SetPlacedTile.cells lProtoset ⟨(), (dx, dy), r⟩ := by
    simp [lPlacedCopy]
  rw [heq, SetPlacedTile.cells_ncard_eq]
  simp [lProtoset, lSetPrototile_ncard]

/-- lPlacedCopy is always finite -/
private lemma lPlacedCopy_finite (dx dy : ℤ) (r : Fin 4) :
    (lPlacedCopy dx dy r).Finite := by
  have heq : lPlacedCopy dx dy r = SetPlacedTile.cells lProtoset ⟨(), (dx, dy), r⟩ := by
    simp [lPlacedCopy]
  rw [heq]; exact SetPlacedTile.cells_finite _

/-- A single L-tromino cannot contain both (0,0) and (2,0): x-span is at most 1 -/
private lemma lPlacedCopy_not_cover_x02 (dx dy : ℤ) (r : Fin 4)
    (h0 : ((0 : ℤ), (0 : ℤ)) ∈ lPlacedCopy dx dy r)
    (h2 : ((2 : ℤ), (0 : ℤ)) ∈ lPlacedCopy dx dy r) : False := by
  fin_cases r <;>
    simp only [lPlacedCopy_eq, mem_translate, mem_rotate, lShape_cells, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h0 h2 <;>
    omega

/-- A tile containing (0,0) with all cells y ≥ 0 must have all cells y < 2 -/
private lemma lPlacedCopy_ybnd_of_cover_00 (dx dy : ℤ) (r : Fin 4)
    (h00 : ((0 : ℤ), (0 : ℤ)) ∈ lPlacedCopy dx dy r)
    (q : Cell) (hq : q ∈ lPlacedCopy dx dy r) (hq_nn : (0 : ℤ) ≤ q.2) : q.2 < 2 := by
  fin_cases r <;>
    simp only [lPlacedCopy_eq, mem_translate, mem_rotate, lShape_cells, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h00 hq <;>
    omega

/-- A tile containing (2,0) with all cells y ≥ 0 must have all cells y < 2 -/
private lemma lPlacedCopy_ybnd_of_cover_20 (dx dy : ℤ) (r : Fin 4)
    (h20 : ((2 : ℤ), (0 : ℤ)) ∈ lPlacedCopy dx dy r)
    (q : Cell) (hq : q ∈ lPlacedCopy dx dy r) (hq_nn : (0 : ℤ) ≤ q.2) : q.2 < 2 := by
  fin_cases r <;>
    simp only [lPlacedCopy_eq, mem_translate, mem_rotate, lShape_cells, inverseRot,
      rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h20 hq <;>
    omega

/-- A 3×(2k+1) rectangle is not L-tileable (Set framework) -/
theorem not_setTileable_3x_odd (k : ℕ) : ¬ SetTileable (rect 0 0 3 (2*k+1)) lProtoset := by
  induction k with
  | zero =>
    -- rect 0 0 3 (2*0+1) = rect 0 0 3 1 = rect 0 0 3 1 (cast is (1:ℤ))
    norm_cast
    exact not_setTileable_nx1 3 (by omega)
  | succ k' ih =>
    -- The goal has form: ¬ SetTileable (rect 0 0 3 (2 * ↑(k'+1) + 1)) lProtoset
    -- Rewrite to: ¬ SetTileable (rect 0 0 3 (2 * ↑k' + 3)) lProtoset
    have hgoal : (2 : ℤ) * ↑(k' + 1) + 1 = 2 * (k' : ℤ) + 3 := by push_cast; omega
    rw [hgoal]
    intro ⟨ιₜ, hft, t, hv⟩
    haveI : Fintype ιₜ := hft
    haveI : DecidableEq ιₜ := Classical.decEq _
    -- (0,0) and (2,0) are in the rectangle
    have h00_in : ((0 : ℤ), (0 : ℤ)) ∈ rect 0 0 3 (2 * (k' : ℤ) + 3) := by
      simp only [mem_rect]; omega
    have h20_in : ((2 : ℤ), (0 : ℤ)) ∈ rect 0 0 3 (2 * (k' : ℤ) + 3) := by
      simp only [mem_rect]; omega
    -- Get the tiles covering each corner
    rw [← hv.covers, SetTileSet.coveredCells, Set.mem_iUnion] at h00_in h20_in
    obtain ⟨i, hi⟩ := h00_in
    obtain ⟨j, hj⟩ := h20_in
    -- Express tiles as lPlacedCopy
    let dxi := (t.tiles i).translation.1
    let dyi := (t.tiles i).translation.2
    let ri  := (t.tiles i).rotation
    let dxj := (t.tiles j).translation.1
    let dyj := (t.tiles j).translation.2
    let rj  := (t.tiles j).rotation
    have hi_eq : t.cellsAt i = lPlacedCopy dxi dyi ri := by
      simp [SetTileSet.cellsAt, lPlacedCopy, dxi, dyi, ri]
    have hj_eq : t.cellsAt j = lPlacedCopy dxj dyj rj := by
      simp [SetTileSet.cellsAt, lPlacedCopy, dxj, dyj, rj]
    -- Use ▸ to transport membership through the cellsAt equations
    have hi' : ((0 : ℤ), (0 : ℤ)) ∈ lPlacedCopy dxi dyi ri := hi_eq ▸ hi
    have hj' : ((2 : ℤ), (0 : ℤ)) ∈ lPlacedCopy dxj dyj rj := hj_eq ▸ hj
    -- i ≠ j: one tile can't cover both corners (x-span ≤ 1)
    have hij : i ≠ j := by
      intro heq; subst heq
      -- After j := i, dxj/dyj/rj become dxi/dyi/ri (let-bindings)
      exact lPlacedCopy_not_cover_x02 dxi dyi ri hi' hj'
    -- Tiles i and j are disjoint (from validity)
    have hdisj : Disjoint (lPlacedCopy dxi dyi ri) (lPlacedCopy dxj dyj rj) := by
      rw [← hi_eq, ← hj_eq]; exact hv.disjoint i j hij
    -- Helper: any cell of tile i is in rect 0 0 3 (2k'+3)
    have hi_sub_full : ∀ q, q ∈ lPlacedCopy dxi dyi ri →
        q ∈ rect 0 0 3 (2 * (k' : ℤ) + 3) := by
      intro q hq
      have hcell : q ∈ t.cellsAt i := hi_eq ▸ hq
      have hmem : q ∈ SetTileSet.coveredCells t :=
        Set.mem_iUnion.mpr ⟨i, hcell⟩
      rwa [hv.covers] at hmem
    -- Helper: any cell of tile j is in rect 0 0 3 (2k'+3)
    have hj_sub_full : ∀ q, q ∈ lPlacedCopy dxj dyj rj →
        q ∈ rect 0 0 3 (2 * (k' : ℤ) + 3) := by
      intro q hq
      have hcell : q ∈ t.cellsAt j := hj_eq ▸ hq
      have hmem : q ∈ SetTileSet.coveredCells t :=
        Set.mem_iUnion.mpr ⟨j, hcell⟩
      rwa [hv.covers] at hmem
    -- Tile i ⊆ rect 0 0 3 2
    have hi_sub_3x2 : lPlacedCopy dxi dyi ri ⊆ rect 0 0 3 2 := by
      intro q hq
      have hfull := hi_sub_full q hq
      simp only [mem_rect] at hfull ⊢
      exact ⟨hfull.1, hfull.2.1, hfull.2.2.1,
        lPlacedCopy_ybnd_of_cover_00 dxi dyi ri hi' q hq hfull.2.2.1⟩
    -- Tile j ⊆ rect 0 0 3 2
    have hj_sub_3x2 : lPlacedCopy dxj dyj rj ⊆ rect 0 0 3 2 := by
      intro q hq
      have hfull := hj_sub_full q hq
      simp only [mem_rect] at hfull ⊢
      exact ⟨hfull.1, hfull.2.1, hfull.2.2.1,
        lPlacedCopy_ybnd_of_cover_20 dxj dyj rj hj' q hq hfull.2.2.1⟩
    -- The union of tiles i and j equals rect 0 0 3 2
    have hunion_eq : lPlacedCopy dxi dyi ri ∪ lPlacedCopy dxj dyj rj = rect 0 0 3 2 := by
      have h_union_card : (lPlacedCopy dxi dyi ri ∪ lPlacedCopy dxj dyj rj).ncard = 6 := by
        rw [Set.ncard_union_eq hdisj (lPlacedCopy_finite _ _ _) (lPlacedCopy_finite _ _ _),
            lPlacedCopy_ncard, lPlacedCopy_ncard]
      have h_rect_card : (rect 0 0 3 (2 : ℤ)).ncard = 6 := by simp [rect_ncard]
      -- eq_of_subset_of_ncard_le (h : s ⊆ t) : s = t; with s = union, t = rect → union = rect ✓
      exact Set.eq_of_subset_of_ncard_le (Set.union_subset hi_sub_3x2 hj_sub_3x2)
        (by linarith) (rect_finite _ _ _ _)
    -- The remaining region after removing tiles i and j is tileable
    have hS : t.cellsAt i ∪ t.cellsAt j = rect 0 0 3 2 := by
      rw [hi_eq, hj_eq]; exact hunion_eq
    have h_remain : SetTileable (rect 0 0 3 (2 * (k' : ℤ) + 3) \ rect 0 0 3 2) lProtoset :=
      SetTileable.remove_two t hv i j hij hS
    -- The remaining region equals translate 0 2 (rect 0 0 3 (2*k'+1))
    have h_diff_eq : rect 0 0 3 (2 * (k' : ℤ) + 3) \ rect 0 0 3 2 =
        translate 0 2 (rect 0 0 3 (2 * (k' : ℤ) + 1)) := by
      ext ⟨x, y⟩
      simp only [Set.mem_diff, mem_rect, mem_translate]
      constructor
      · rintro ⟨⟨hx1, hx2, hy1, hy2⟩, hnotmem⟩
        push_neg at hnotmem
        -- hnotmem : 0 ≤ x → x < 3 → 0 ≤ y → 2 ≤ y
        have hy2' : 2 ≤ y := hnotmem hx1 hx2 hy1
        simp only [sub_zero]
        exact ⟨hx1, hx2, by linarith, by linarith⟩
      · rintro ⟨hx1, hx2, hy1, hy2⟩
        simp only [sub_zero] at *
        refine ⟨⟨hx1, hx2, by linarith, by linarith⟩, ?_⟩
        simp only [not_and, not_lt]
        intro _ _ _; linarith
    rw [h_diff_eq] at h_remain
    -- Translate back to get SetTileable (rect 0 0 3 (2*k'+1))
    have h_back : SetTileable (rect 0 0 3 (2 * (k' : ℤ) + 1)) lProtoset := by
      have h := h_remain.translate 0 (-2)
      have h_eq : translate 0 (-2) (translate 0 2 (rect 0 0 3 (2 * (k' : ℤ) + 1))) =
          rect 0 0 3 (2 * (k' : ℤ) + 1) := by
        ext ⟨x, y⟩; simp only [mem_translate, mem_rect]; omega
      rwa [h_eq] at h
    -- Contradict the IH (cast: 2 * ↑k' + 1 = 2 * (k':ℤ) + 1 definitionally)
    exact ih h_back

-- ============================================================
-- 2×n biconditional
-- ============================================================

/-- 2×n is L-tileable iff 3 ∣ n -/
theorem setTileable_2xn_iff (n : ℕ) : SetTileable (rect 0 0 2 n) lProtoset ↔ 3 ∣ n := by
  constructor
  · intro h
    have hdvd := setTileable_rect_area_dvd 2 n h
    rcases hdvd with ⟨k, hk⟩
    exact ⟨n - k, by omega⟩
  · rintro ⟨k, hk⟩
    subst hk
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp only [Nat.mul_zero, Nat.cast_zero]
      rw [rect_empty_of_eq]
      exact SetTileable.empty lProtoset
    · exact setTileable_2x_mult3 k hk_pos

-- ============================================================
-- General 2D families via refine
-- ============================================================

/-- Any (3a) × (2b) rectangle is L-tileable (a, b ≥ 1) -/
theorem setTileable_mult3_mult2 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    SetTileable (rect 0 0 (3 * a) (2 * b)) lProtoset := by
  have h := setTileable_3x2.scale_rect (by norm_num) (by norm_num) a b ha hb
  convert h using 2 <;> push_cast <;> ring

/-- Any (2a) × (3b) rectangle is L-tileable (a, b ≥ 1) -/
theorem setTileable_mult2_mult3 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    SetTileable (rect 0 0 (2 * a) (3 * b)) lProtoset := by
  have h := setTileable_swap (setTileable_mult3_mult2 b a hb ha)
  have heq : Set.swapRegion (rect 0 0 (3 * b) (2 * a)) = rect 0 0 (2 * a) (3 * b) := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rwa [heq] at h

-- ============================================================
-- New families: odd × 6k
-- ============================================================

/-- n×6 is L-tileable for all odd n ≥ 3 -/
theorem setTileable_odd_x_6 (n : ℕ) (hn_odd : n % 2 = 1) (hn_ge : 3 ≤ n) :
    SetTileable (rect 0 0 n 6) lProtoset := by
  induction' n using Nat.strong_induction_on with n ih
  rcases Nat.eq_or_lt_of_le hn_ge with rfl | hn_gt
  · exact setTileable_3x6
  · have ih2 : SetTileable (rect 0 0 (n - 2 : Nat) 6) lProtoset :=
      ih (n - 2) (by omega) (by omega) (by omega)
    have h_cast : ((n - 2 : Nat) : ℤ) = (n : ℤ) - 2 := by omega
    have ih2' : SetTileable (rect 0 0 ((n : ℤ) - 2) 6) lProtoset := h_cast ▸ ih2
    have h_sum : (n : ℤ) - 2 + 2 = (n : ℤ) := by omega
    rw [← h_sum]
    apply SetTileable.horizontal_union (by omega) (by omega) ih2'
    have h_trans : rect ((n : ℤ) - 2) 0 ((n : ℤ) - 2 + 2) 6 =
        translate ((n : ℤ) - 2) 0 (rect 0 0 2 6) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_2x6 ((n : ℤ) - 2) 0

/-- 6×n is L-tileable for all odd n ≥ 3 (by swap) -/
theorem setTileable_6x_odd (n : ℕ) (hn_odd : n % 2 = 1) (hn_ge : 3 ≤ n) :
    SetTileable (rect 0 0 6 n) lProtoset := by
  have h := setTileable_swap (setTileable_odd_x_6 n hn_odd hn_ge)
  have h_eq : Set.swapRegion (rect 0 0 (n : ℤ) 6) = rect 0 0 6 (n : ℤ) := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rwa [h_eq] at h

/-- n × (6k) is L-tileable for odd n ≥ 3 and k ≥ 1 -/
theorem setTileable_odd_x_mult6 (n k : ℕ) (hn_odd : n % 2 = 1) (hn_ge : 3 ≤ n) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 n (6 * k)) lProtoset := by
  have hn_pos : (0:ℤ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := (setTileable_odd_x_6 n hn_odd hn_ge).scale_rect hn_pos (by norm_num) 1 k (by omega) hk
  convert h using 2 <;> push_cast <;> ring
