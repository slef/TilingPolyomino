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
  have _ := hk
  apply SetTileable.refine_partition
    (pieces := fun (i : Fin k) => rect 0 (3 * (i.val : ℤ)) 2 (3 * (i.val + 1 : ℤ)))
  · ext ⟨x, y⟩
    simp only [Set.mem_iUnion, mem_rect]
    constructor
    · rintro ⟨i, hx1, hx2, hy1, hy2⟩
      have hi : (i.val : ℤ) < (k : ℤ) := Nat.cast_lt (α := ℤ).mpr i.isLt
      exact ⟨hx1, hx2, by omega, by omega⟩
    · rintro ⟨hx1, hx2, hy1, hy2⟩
      have hk_pos : 0 < (k : ℤ) := by omega
      let q := y / 3
      have hq_pos : 0 ≤ q := by omega
      have hq_lt : q < (k : ℤ) := by omega
      have h1 : q.toNat < k := by
        apply Nat.cast_lt (α := ℤ).mp
        rw [Int.toNat_of_nonneg hq_pos]
        exact hq_lt
      use ⟨q.toNat, h1⟩
      have h_q_val : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq_pos
      refine ⟨hx1, hx2, ?_, ?_⟩
      · rw [h_q_val]
        omega
      · rw [h_q_val]
        omega
  · intro i j hij
    dsimp [Function.onFun]
    rw [Set.disjoint_iff_inter_eq_empty]
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, mem_rect, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, _, hy1, hy2⟩, ⟨_, _, hy3, hy4⟩⟩
    have h_neq : (i.val : ℤ) ≠ (j.val : ℤ) := by
      intro h
      apply hij
      ext
      exact Nat.cast_inj.mp h
    omega
  · intro i
    have h_trans : rect 0 (3 * (i.val : ℤ)) 2 (3 * (i.val + 1 : ℤ)) =
        translate 0 (3 * (i.val : ℤ)) (rect 0 0 2 3) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_2x3 0 (3 * i.val)

theorem setTileable_3x_even (k : ℕ) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 3 (2 * k)) lProtoset := by
  have _ := hk
  apply SetTileable.refine_partition
    (pieces := fun (i : Fin k) => rect 0 (2 * (i.val : ℤ)) 3 (2 * (i.val + 1 : ℤ)))
  · ext ⟨x, y⟩
    simp only [Set.mem_iUnion, mem_rect]
    constructor
    · rintro ⟨i, hx1, hx2, hy1, hy2⟩
      have hi : (i.val : ℤ) < (k : ℤ) := Nat.cast_lt (α := ℤ).mpr i.isLt
      exact ⟨hx1, hx2, by omega, by omega⟩
    · rintro ⟨hx1, hx2, hy1, hy2⟩
      have hk_pos : 0 < (k : ℤ) := by omega
      let q := y / 2
      have hq_pos : 0 ≤ q := by omega
      have hq_lt : q < (k : ℤ) := by omega
      have h1 : q.toNat < k := by
        apply Nat.cast_lt (α := ℤ).mp
        rw [Int.toNat_of_nonneg hq_pos]
        exact hq_lt
      use ⟨q.toNat, h1⟩
      have h_q_val : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq_pos
      refine ⟨hx1, hx2, ?_, ?_⟩
      · rw [h_q_val]
        omega
      · rw [h_q_val]
        omega
  · intro i j hij
    dsimp [Function.onFun]
    rw [Set.disjoint_iff_inter_eq_empty]
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, mem_rect, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, _, hy1, hy2⟩, ⟨_, _, hy3, hy4⟩⟩
    have h_neq : (i.val : ℤ) ≠ (j.val : ℤ) := by
      intro h
      apply hij
      ext
      exact Nat.cast_inj.mp h
    omega
  · intro i
    have h_trans : rect 0 (2 * (i.val : ℤ)) 3 (2 * (i.val + 1 : ℤ)) =
        translate 0 (2 * (i.val : ℤ)) (rect 0 0 3 2) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_3x2 0 (2 * i.val)

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
  apply SetTileable.refine_partition
    (pieces := fun (p : Fin a × Fin b) =>
      rect (3 * p.1.val) (2 * p.2.val) (3 * (p.1.val + 1)) (2 * (p.2.val + 1)))
  · ext ⟨x, y⟩
    simp only [Set.mem_iUnion, mem_rect]
    constructor
    · rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hx1, hx2, hy1, hy2⟩
      refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast at * <;> omega
    · rintro ⟨hx1, hx2, hy1, hy2⟩
      have hxq_lt : (x / 3).toNat < a := by
        apply Nat.cast_lt (α := ℤ).mp
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      have hyq_lt : (y / 2).toNat < b := by
        apply Nat.cast_lt (α := ℤ).mp
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      refine ⟨⟨⟨(x / 3).toNat, hxq_lt⟩, ⟨(y / 2).toNat, hyq_lt⟩⟩, ?_, ?_, ?_, ?_⟩ <;>
        rw [Int.toNat_of_nonneg (by omega)] <;> push_cast <;> omega
  · intro ⟨⟨i₁, _⟩, ⟨j₁, _⟩⟩ ⟨⟨i₂, _⟩, ⟨j₂, _⟩⟩ hne
    simp only [Function.onFun, Set.disjoint_iff_inter_eq_empty]
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, mem_rect, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hx1, hx2, hy1, hy2⟩, hx1', hx2', hy1', hy2'⟩
    push_cast at *
    have heqi : i₁ = i₂ := by omega
    have heqj : j₁ = j₂ := by omega
    exact hne (Prod.ext (Fin.ext heqi) (Fin.ext heqj))
  · intro ⟨⟨i, _⟩, ⟨j, _⟩⟩
    have heq : rect (3 * (i : ℤ)) (2 * j) (3 * (i + 1)) (2 * (j + 1))
             = translate (3 * i) (2 * j) (rect 0 0 3 2) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      push_cast
      omega
    rw [heq]
    exact setTileable_translate setTileable_3x2 _ _

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
  apply SetTileable.refine_partition
    (pieces := fun (i : Fin k) => rect 0 (6 * (i.val : ℤ)) (n : ℤ) (6 * (i.val + 1 : ℤ)))
  · ext ⟨x, y⟩
    simp only [Set.mem_iUnion, mem_rect]
    constructor
    · rintro ⟨i, hx1, hx2, hy1, hy2⟩
      have hi : (i.val : ℤ) < (k : ℤ) := Nat.cast_lt (α := ℤ).mpr i.isLt
      exact ⟨hx1, hx2, by omega, by omega⟩
    · rintro ⟨hx1, hx2, hy1, hy2⟩
      let q := y / 6
      have hq_pos : 0 ≤ q := Int.ediv_nonneg (by omega) (by omega)
      have hq_lt : q < (k : ℤ) := by
        simp only [show q = y / 6 from rfl]
        omega
      have h_qnat_lt : q.toNat < k := by
        apply Nat.cast_lt (α := ℤ).mp
        rw [Int.toNat_of_nonneg hq_pos]
        exact hq_lt
      have h_q_val : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq_pos
      refine ⟨⟨q.toNat, h_qnat_lt⟩, hx1, hx2, ?_, ?_⟩
      · rw [h_q_val]
        linarith [Int.mul_ediv_add_emod y 6, Int.emod_nonneg y (show (6 : ℤ) ≠ 0 by omega)]
      · rw [h_q_val]
        linarith [Int.mul_ediv_add_emod y 6, Int.emod_lt_of_pos y (show (0 : ℤ) < 6 by omega)]
  · intro i j hij
    dsimp [Function.onFun]
    rw [Set.disjoint_iff_inter_eq_empty]
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, mem_rect, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, _, hy1, hy2⟩, ⟨_, _, hy3, hy4⟩⟩
    have h_neq : (i.val : ℤ) ≠ (j.val : ℤ) := by
      intro h
      apply hij
      ext
      exact Nat.cast_inj.mp h
    omega
  · intro i
    have h_trans : rect 0 (6 * (i.val : ℤ)) (n : ℤ) (6 * (i.val + 1 : ℤ)) =
        translate 0 (6 * (i.val : ℤ)) (rect 0 0 n 6) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate (setTileable_odd_x_6 n hn_odd hn_ge) 0 _
