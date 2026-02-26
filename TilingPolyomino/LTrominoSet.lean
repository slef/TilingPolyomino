import Mathlib.Tactic
import TilingPolyomino.TilingSet

open Set Function

-- ============================================================
-- L-tromino shape definitions
-- ============================================================

/-- The L-tromino shape (standard orientation): {(0,0),(0,1),(1,0)} -/
def lShape_cells : Set Cell := {(0,0), (0,1), (1,0)}

def lShape : Shape := ⟨
  lShape_cells,
  by simp [Set.finite_insert, lShape_cells],
  ⟨(0,0), by simp [lShape_cells]⟩
⟩

theorem lShape_eq_rects : lShape.cells = rect 0 0 1 2 ∪ rect 1 0 2 1 := by
  ext ⟨x, y⟩
  simp [lShape, lShape_cells]
  omega

theorem lShape_cells_ncard : lShape.cells.ncard = 3 := by
  dsimp [lShape, lShape_cells]
  rw [Set.ncard_insert_of_notMem]
  · rw [Set.ncard_insert_of_notMem]
    · rw [Set.ncard_singleton]
    · simp
  · simp

-- ============================================================
-- Swap rotation: swapRegion commutes with lShape placed copies
-- ============================================================

def swapRot : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | 3 => 1

theorem swapRegion_placedCopy (dx dy : ℤ) (r : Fin 4) :
    Set.swapRegion (placedCopy lShape dx dy r) = placedCopy lShape dy dx (swapRot r) := by
  dsimp [placedCopy]
  rw [lShape_eq_rects]
  fin_cases r
  · dsimp [swapRot]; rect_omega
  · dsimp [swapRot]; rect_omega
  · dsimp [swapRot]; rect_omega
  · dsimp [swapRot]; rect_omega

theorem setTileable_swap {R : Set Cell} (h : SetTileable R lShape) :
    SetTileable (Set.swapRegion R) lShape := by
  rcases h with ⟨t⟩
  apply Nonempty.intro
  refine {
    ι := t.ι
    tile := fun i => Set.swapRegion (t.tile i)
    covers := by
      ext ⟨x, y⟩
      have h_cov := t.covers
      have h1 : (x, y) ∈ ⋃ i, Set.swapRegion (t.tile i) ↔ ∃ i, (y, x) ∈ t.tile i := by
        simp only [mem_swapRegion, Set.mem_iUnion]
      have h2 : (∃ i, (y, x) ∈ t.tile i) ↔ (y, x) ∈ ⋃ i, t.tile i := by
        simp only [Set.mem_iUnion]
      have h3 : (y, x) ∈ ⋃ i, t.tile i ↔ (y, x) ∈ R := by rw [h_cov]
      rw [h1, h2, h3, mem_swapRegion]
    disjoint := by
      intro i j hij
      have hd := t.disjoint i j hij
      rw [Set.disjoint_iff_inter_eq_empty] at hd ⊢
      ext ⟨x, y⟩
      simp only [mem_swapRegion, Set.mem_inter_iff, Set.mem_empty_iff_false]
      have := Set.ext_iff.mp hd (y, x)
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false] at this
      exact this
    is_placed := by
      intro i
      rcases t.is_placed i with ⟨dx, dy, r, hr⟩
      use dy, dx, swapRot r
      rw [hr]
      exact swapRegion_placedCopy dx dy r
  }

-- ============================================================
-- Base cases
-- ============================================================

theorem setTileable_2x3 : SetTileable (rect 0 0 2 3) lShape := by
  apply Nonempty.intro
  refine Tiling.of_two _ lShape 0 0 0 1 2 2 ?_ ?_
  · dsimp [placedCopy]
    rw [lShape_eq_rects]
    rect_omega
  · dsimp [placedCopy]
    rw [lShape_eq_rects, Set.disjoint_iff_inter_eq_empty]
    rect_omega

theorem setTileable_3x2 : SetTileable (rect 0 0 3 2) lShape := by
  apply Nonempty.intro
  refine Tiling.of_two _ lShape 0 0 0 2 1 2 ?_ ?_
  · dsimp [placedCopy]
    rw [lShape_eq_rects]
    rect_omega
  · dsimp [placedCopy]
    rw [lShape_eq_rects, Set.disjoint_iff_inter_eq_empty]
    rect_omega

theorem setTileable_2x2_minus : SetTileable (rect 0 0 2 2 \ {(1,1)}) lShape := by
  apply Nonempty.intro
  refine Tiling.of_one _ lShape 0 0 0 ?_
  have h_sing : ({(1,1)} : Set Cell) = rect 1 1 2 2 := by
    ext ⟨x, y⟩
    simp
    omega
  dsimp [placedCopy]
  rw [lShape_eq_rects, h_sing]
  rect_omega

-- ============================================================
-- Inductive rectangle families
-- ============================================================

theorem setTileable_2x6 : SetTileable (rect 0 0 2 6) lShape := by
  have ha : SetTileable (rect 0 0 2 3) lShape := setTileable_2x3
  have hb : SetTileable (rect 0 3 2 6) lShape := by
    have h_trans : rect 0 3 2 6 = translate 0 3 (rect 0 0 2 3) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_2x3 0 3
  exact @SetTileable.vertical_union lShape 2 3 3 (by omega) (by omega) ha hb

theorem setTileable_6x2 : SetTileable (rect 0 0 6 2) lShape := by
  have h := setTileable_swap setTileable_2x6
  have h_eq : Set.swapRegion (rect 0 0 2 6) = rect 0 0 6 2 := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rw [h_eq] at h
  exact h

theorem setTileable_3x4 : SetTileable (rect 0 0 3 4) lShape := by
  have ha : SetTileable (rect 0 0 3 2) lShape := setTileable_3x2
  have hb : SetTileable (rect 0 2 3 4) lShape := by
    have h_trans : rect 0 2 3 4 = translate 0 2 (rect 0 0 3 2) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_3x2 0 2
  exact @SetTileable.vertical_union lShape 3 2 2 (by omega) (by omega) ha hb

theorem setTileable_3x6 : SetTileable (rect 0 0 3 6) lShape := by
  have ha : SetTileable (rect 0 0 3 2) lShape := setTileable_3x2
  have hb : SetTileable (rect 0 2 3 6) lShape := by
    have h_trans : rect 0 2 3 6 = translate 0 2 (rect 0 0 3 4) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_3x4 0 2
  exact @SetTileable.vertical_union lShape 3 2 4 (by omega) (by omega) ha hb

theorem setTileable_6x3 : SetTileable (rect 0 0 6 3) lShape := by
  have h := setTileable_swap setTileable_3x6
  have h_eq : Set.swapRegion (rect 0 0 3 6) = rect 0 0 6 3 := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rw [h_eq] at h
  exact h

theorem setTileable_6x6 : SetTileable (rect 0 0 6 6) lShape := by
  have ha : SetTileable (rect 0 0 6 3) lShape := setTileable_6x3
  have hb : SetTileable (rect 0 3 6 6) lShape := by
    have h_trans : rect 0 3 6 6 = translate 0 3 (rect 0 0 6 3) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_6x3 0 3
  exact @SetTileable.vertical_union lShape 6 3 3 (by omega) (by omega) ha hb

theorem setTileable_2x_mult3 (k : ℕ) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 2 (3*k)) lShape := by
  have _ := hk
  apply SetTileable.refine (fun (i : Fin k) => rect 0 (3 * (i.val : ℤ)) 2 (3 * (i.val + 1 : ℤ)))
  · ext ⟨x, y⟩
    simp only [Set.mem_iUnion, mem_rect]
    constructor
    · rintro ⟨i, hx1, hx2, hy1, hy2⟩
      have hi : (i.val : ℤ) < (k : ℤ) := Nat.cast_lt (α := ℤ).mpr i.isLt
      exact ⟨hx1, hx2, by omega, by omega⟩
    · rintro ⟨hx1, hx2, hy1, hy2⟩
      have hk_pos : 0 < (k : ℤ) := by omega
      have hy_pos : 0 ≤ y := hy1
      have hy_lt : y < 3 * (k : ℤ) := hy2
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
      · rw [h_q_val]; omega
      · rw [h_q_val]; omega
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
    exact rect_finite _ _ _ _
  · intro i
    have h_trans : rect 0 (3 * (i.val : ℤ)) 2 (3 * (i.val + 1 : ℤ)) =
        translate 0 (3 * (i.val : ℤ)) (rect 0 0 2 3) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_2x3 0 (3 * i.val)

theorem setTileable_3x_even (k : ℕ) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 3 (2*k)) lShape := by
  have _ := hk
  apply SetTileable.refine (fun (i : Fin k) => rect 0 (2 * (i.val : ℤ)) 3 (2 * (i.val + 1 : ℤ)))
  · ext ⟨x, y⟩
    simp only [Set.mem_iUnion, mem_rect]
    constructor
    · rintro ⟨i, hx1, hx2, hy1, hy2⟩
      have hi : (i.val : ℤ) < (k : ℤ) := Nat.cast_lt (α := ℤ).mpr i.isLt
      exact ⟨hx1, hx2, by omega, by omega⟩
    · rintro ⟨hx1, hx2, hy1, hy2⟩
      have hk_pos : 0 < (k : ℤ) := by omega
      have hy_pos : 0 ≤ y := hy1
      have hy_lt : y < 2 * (k : ℤ) := hy2
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
      · rw [h_q_val]; omega
      · rw [h_q_val]; omega
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
    exact rect_finite _ _ _ _
  · intro i
    have h_trans : rect 0 (2 * (i.val : ℤ)) 3 (2 * (i.val + 1 : ℤ)) =
        translate 0 (2 * (i.val : ℤ)) (rect 0 0 3 2) := by
      ext ⟨x, y⟩
      simp only [mem_rect, mem_translate]
      omega
    rw [h_trans]
    exact setTileable_translate setTileable_3x2 0 (2 * i.val)

theorem setTileable_mult3_x_2 (k : Nat) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 (3*k) 2) lShape := by
  have h := setTileable_swap (setTileable_2x_mult3 k hk)
  have h_eq : Set.swapRegion (rect 0 0 2 (3*k)) = rect 0 0 (3*k) 2 := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rw [h_eq] at h
  exact h

theorem setTileable_even_x_3 (k : Nat) (hk : 1 <= k) :
    SetTileable (rect 0 0 (2*k) 3) lShape := by
  have h := setTileable_swap (setTileable_3x_even k hk)
  have h_eq : Set.swapRegion (rect 0 0 3 (2*k)) = rect 0 0 (2*k) 3 := by
    ext ⟨x, y⟩
    simp only [mem_swapRegion, mem_rect]
    omega
  rw [h_eq] at h
  exact h

theorem setTileable_6x_of_ge2 (k : Nat) (hk : 2 ≤ k) :
    SetTileable (rect 0 0 6 k) lShape := by
  induction' k using Nat.strong_induction_on with n ih
  rcases eq_or_lt_of_le hk with rfl | hn2
  · exact setTileable_6x2
  · rcases eq_or_lt_of_le (show 3 ≤ n from hn2) with rfl | hn3
    · exact setTileable_6x3
    · have hn_ge_4 : 4 ≤ n := hn3
      have h_prev_nat : SetTileable (rect 0 0 6 (n - 2 : Nat)) lShape :=
        ih (n - 2) (by omega) (by omega)
      have h_prev : SetTileable (rect 0 0 6 (n - 2 : ℤ)) lShape := by
        have h_eq : ((n - 2 : Nat) : ℤ) = (n : ℤ) - 2 := by omega
        exact h_eq ▸ h_prev_nat
      have h_2 : SetTileable (rect 0 (n - 2 : ℤ) 6 n) lShape := by
        have h_trans : rect 0 (n - 2 : ℤ) 6 n = translate 0 (n - 2 : ℤ) (rect 0 0 6 2) := by
          ext ⟨x, y⟩
          simp only [mem_rect, mem_translate]
          omega
        rw [h_trans]
        exact setTileable_translate setTileable_6x2 0 (n - 2 : ℤ)
      have h_union := @SetTileable.vertical_union lShape 6 (n - 2 : ℤ) 2 (by omega) (by omega)
        h_prev (by
          have h_eq : (n - 2 : ℤ) + 2 = (n : ℤ) := by omega
          exact h_eq.symm ▸ h_2)
      have h_eq : (n - 2 : ℤ) + 2 = n := by omega
      rw [h_eq] at h_union
      exact h_union

theorem setTileable_kx6_of_ge2 (k : Nat) (hk : 2 <= k) :
    SetTileable (rect 0 0 k 6) lShape := by
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

theorem setTileable_rect_area_dvd (m n : Nat) (h : SetTileable (rect 0 0 m n) lShape) :
    3 ∣ m * n := by
  have h1 := SetTileable.ncard_dvd (rect_finite 0 0 m n) h
  have h2 : lShape.cells.ncard = 3 := lShape_cells_ncard
  have h3 : (rect 0 0 (m : ℤ) (n : ℤ)).ncard = m * n := by
    rw [rect_ncard]
    simp
  rw [h2, h3] at h1
  exact h1

-- ============================================================
-- Impossibility theorems
-- ============================================================

-- Helper: every placed copy of lShape contains a cell at (dx, dy)
private lemma placedCopy_contains_origin_offset (dx dy : ℤ) (r : Fin 4) :
    (dx, dy) ∈ placedCopy lShape dx dy r := by
  fin_cases r <;>
    simp [placedCopy, mem_translate, mem_rotate, lShape, lShape_cells, inverseRot,
          rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
          Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]

-- Helper: every placed copy spans ≥ 2 distinct x-values
private lemma placedCopy_x_span (dx dy : ℤ) (r : Fin 4) :
    (dx + 1, dy) ∈ placedCopy lShape dx dy r ∨ (dx - 1, dy) ∈ placedCopy lShape dx dy r := by
  fin_cases r <;>
    simp [placedCopy, mem_translate, mem_rotate, lShape, lShape_cells, inverseRot,
          rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3,
          Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] <;>
    omega

/-- No 1×n strip (n ≥ 1) is L-tileable: placed copies always span ≥ 2 x-values -/
theorem not_setTileable_1xn (n : ℕ) (hn : 1 ≤ n) : ¬ SetTileable (rect 0 0 1 n) lShape := by
  intro ⟨t⟩
  have hcell : ((0 : ℤ), (0 : ℤ)) ∈ rect 0 0 1 (n : ℤ) := by
    simp only [mem_rect]
    exact ⟨le_refl _, by norm_num, le_refl _, by exact_mod_cast hn⟩
  rw [← t.covers, Set.mem_iUnion] at hcell
  obtain ⟨i, hi⟩ := hcell
  obtain ⟨dx, dy, r, hrep⟩ := t.is_placed i
  have h_sub : ∀ q, q ∈ t.tile i → 0 ≤ q.1 ∧ q.1 < 1 := by
    intro q hq
    have hmem : q ∈ rect 0 0 1 (n : ℤ) := by
      have : q ∈ ⋃ j, t.tile j := Set.mem_iUnion.mpr ⟨i, hq⟩
      rwa [t.covers] at this
    simp only [mem_rect] at hmem
    exact ⟨hmem.1, hmem.2.1⟩
  rw [hrep] at h_sub
  have h_base : (dx, dy) ∈ placedCopy lShape dx dy r :=
    placedCopy_contains_origin_offset dx dy r
  have hbase := h_sub _ h_base
  rcases placedCopy_x_span dx dy r with h2 | h2
  · have := (h_sub _ h2).2; omega
  · have := (h_sub _ h2).1; omega

/-- Same result for the transposed strip (n×1) -/
theorem not_setTileable_nx1 (n : ℕ) (hn : 1 ≤ n) : ¬ SetTileable (rect 0 0 n 1) lShape := by
  intro h
  have hswap : SetTileable (Set.swapRegion (rect 0 0 n 1)) lShape :=
    setTileable_swap h
  have heq : Set.swapRegion (rect 0 0 (n : ℤ) 1) = rect 0 0 1 n := by
    ext ⟨x, y⟩; simp only [mem_swapRegion, mem_rect]; omega
  rw [heq] at hswap
  exact not_setTileable_1xn n hn hswap

-- ============================================================
-- 2×n biconditional
-- ============================================================

/-- 2×n is L-tileable iff 3 ∣ n -/
theorem setTileable_2xn_iff (n : ℕ) : SetTileable (rect 0 0 2 n) lShape ↔ 3 ∣ n := by
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
      exact SetTileable.empty lShape
    · exact setTileable_2x_mult3 k hk_pos

-- ============================================================
-- General 2D families via refine
-- ============================================================

/-- Any (3a) × (2b) rectangle is L-tileable (a, b ≥ 1) -/
theorem setTileable_mult3_mult2 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    SetTileable (rect 0 0 (3 * a) (2 * b)) lShape := by
  apply SetTileable.refine
    (pieces := fun (p : Fin a × Fin b) =>
      rect (3 * p.1.val) (2 * p.2.val) (3 * (p.1.val + 1)) (2 * (p.2.val + 1)))
  · ext ⟨x, y⟩
    simp only [Set.mem_iUnion, mem_rect]
    constructor
    · rintro ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hx1, hx2, hy1, hy2⟩
      refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast at * <;> omega
    · rintro ⟨hx1, hx2, hy1, hy2⟩
      have hx_nn : 0 ≤ x := by linarith
      have hy_nn : 0 ≤ y := by linarith
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
  · intro p; exact rect_finite _ _ _ _
  · intro ⟨⟨i, _⟩, ⟨j, _⟩⟩
    have heq : rect (3 * (i : ℤ)) (2 * j) (3 * (i + 1)) (2 * (j + 1))
             = translate (3 * i) (2 * j) (rect 0 0 3 2) := by
      ext ⟨x, y⟩; simp only [mem_rect, mem_translate]; push_cast; omega
    rw [heq]
    exact setTileable_translate setTileable_3x2 _ _

/-- Any (2a) × (3b) rectangle is L-tileable (a, b ≥ 1) -/
theorem setTileable_mult2_mult3 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    SetTileable (rect 0 0 (2 * a) (3 * b)) lShape := by
  have h := setTileable_swap (setTileable_mult3_mult2 b a hb ha)
  have heq : Set.swapRegion (rect 0 0 (3 * b) (2 * a)) = rect 0 0 (2 * a) (3 * b) := by
    ext ⟨x, y⟩; simp only [mem_swapRegion, mem_rect]; omega
  rwa [heq] at h

-- ============================================================
-- New families: odd × 6k
-- ============================================================

/-- n×6 is L-tileable for all odd n ≥ 3 -/
theorem setTileable_odd_x_6 (n : ℕ) (hn_odd : n % 2 = 1) (hn_ge : 3 ≤ n) :
    SetTileable (rect 0 0 n 6) lShape := by
  induction' n using Nat.strong_induction_on with n ih
  rcases Nat.eq_or_lt_of_le hn_ge with rfl | hn_gt
  · exact setTileable_3x6
  · have hn_ge5 : 5 ≤ n := by omega
    have ih2 : SetTileable (rect 0 0 (n - 2 : Nat) 6) lShape :=
      ih (n - 2) (by omega) (by omega) (by omega)
    have h_cast : ((n - 2 : Nat) : ℤ) = (n : ℤ) - 2 := by omega
    have ih2' : SetTileable (rect 0 0 ((n : ℤ) - 2) 6) lShape := h_cast ▸ ih2
    have h_sum : (n : ℤ) - 2 + 2 = (n : ℤ) := by omega
    rw [← h_sum]
    apply SetTileable.horizontal_union (by omega) (by omega) ih2'
    have h_trans : rect ((n : ℤ) - 2) 0 ((n : ℤ) - 2 + 2) 6 =
        translate ((n : ℤ) - 2) 0 (rect 0 0 2 6) := by
      ext ⟨x, y⟩; simp only [mem_rect, mem_translate]; omega
    rw [h_trans]
    exact setTileable_translate setTileable_2x6 ((n : ℤ) - 2) 0

/-- 6×n is L-tileable for all odd n ≥ 3 (by swap) -/
theorem setTileable_6x_odd (n : ℕ) (hn_odd : n % 2 = 1) (hn_ge : 3 ≤ n) :
    SetTileable (rect 0 0 6 n) lShape := by
  have h := setTileable_swap (setTileable_odd_x_6 n hn_odd hn_ge)
  have h_eq : Set.swapRegion (rect 0 0 (↑n : ℤ) 6) = rect 0 0 6 (↑n : ℤ) := by
    ext ⟨x, y⟩; simp only [mem_swapRegion, mem_rect]; omega
  rwa [h_eq] at h

/-- n × (6k) is L-tileable for odd n ≥ 3 and k ≥ 1 -/
theorem setTileable_odd_x_mult6 (n k : ℕ) (hn_odd : n % 2 = 1) (hn_ge : 3 ≤ n) (hk : 1 ≤ k) :
    SetTileable (rect 0 0 n (6 * k)) lShape := by
  apply SetTileable.refine
    (pieces := fun (i : Fin k) => rect 0 (6 * (i.val : ℤ)) (↑n : ℤ) (6 * (↑i.val + 1)))
  · ext ⟨x, y⟩
    simp only [Set.mem_iUnion, mem_rect]
    constructor
    · rintro ⟨i, hx1, hx2, hy1, hy2⟩
      have hi : (i.val : ℤ) < (k : ℤ) := Nat.cast_lt (α := ℤ).mpr i.isLt
      exact ⟨hx1, hx2, by omega, by push_cast; omega⟩
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
      have hq_eq : q = y / 6 := rfl
      refine ⟨⟨q.toNat, h_qnat_lt⟩, hx1, hx2, ?_, ?_⟩
      · rw [h_q_val, hq_eq]
        linarith [Int.mul_ediv_add_emod y 6, Int.emod_nonneg y (show (6:ℤ) ≠ 0 by omega)]
      · rw [h_q_val, hq_eq]
        linarith [Int.mul_ediv_add_emod y 6, Int.emod_lt_of_pos y (show (0:ℤ) < 6 by omega)]
  · intro i j hij
    dsimp [Function.onFun]
    rw [Set.disjoint_iff_inter_eq_empty]
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, mem_rect, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, _, hy1, hy2⟩, ⟨_, _, hy3, hy4⟩⟩
    have h_neq : (i.val : ℤ) ≠ (j.val : ℤ) := by
      intro h; apply hij; ext; exact Nat.cast_inj.mp h
    omega
  · intro i; exact rect_finite _ _ _ _
  · intro i
    have h_trans : rect 0 (6 * (i.val : ℤ)) (↑n : ℤ) (6 * (↑i.val + 1)) =
        translate 0 (6 * (i.val : ℤ)) (rect 0 0 n 6) := by
      ext ⟨x, y⟩; simp only [mem_rect, mem_translate]; push_cast; omega
    rw [h_trans]
    exact setTileable_translate (setTileable_odd_x_6 n hn_odd hn_ge) 0 _

-- ============================================================
-- Impossibility: 3 × (2k+1) is not L-tileable
-- ============================================================

/-- 3 × (2k+1) is never L-tileable by L-trominoes -/
theorem not_setTileable_3x_odd : ∀ k : ℕ, ¬ SetTileable (rect 0 0 3 (2*k+1)) lShape
  | 0 => by exact not_setTileable_nx1 3 (by omega)
  | (k+1) => by
      intro ⟨t⟩
      have ih := not_setTileable_3x_odd k
      -- The height of our region: 2*(k+1)+1 = 2k+3
      have h_height : (2 * (↑(k+1) : ℤ) + 1) = 2 * (↑k : ℤ) + 3 := by push_cast; ring
      -- Cell (0,0) must be in the region and hence covered by some tile
      have hkpos : (0:ℤ) < ↑(k+1) := by exact_mod_cast Nat.succ_pos k
      have hcell : ((0:ℤ),(0:ℤ)) ∈ rect 0 0 3 (2*(↑(k+1):ℤ)+1) := by
        simp only [mem_rect]
        refine ⟨le_refl _, by norm_num, le_refl _, ?_⟩
        linarith
      rw [← t.covers] at hcell
      obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp hcell
      obtain ⟨dx₀, dy₀, r₀, hrep₀⟩ := t.is_placed i₀
      -- Cell (2,0) must also be in the region and covered by some tile
      have hcell2 : ((2:ℤ),(0:ℤ)) ∈ rect 0 0 3 (2*(↑(k+1):ℤ)+1) := by
        simp only [mem_rect]
        refine ⟨by norm_num, by norm_num, le_refl _, ?_⟩
        linarith
      rw [← t.covers] at hcell2
      obtain ⟨i₁, hi₁⟩ := Set.mem_iUnion.mp hcell2
      obtain ⟨dx₁, dy₁, r₁, hrep₁⟩ := t.is_placed i₁
      -- All cells of each tile must be within the region
      have h_sub₀ : ∀ p, p ∈ t.tile i₀ → p ∈ rect 0 0 3 (2*(↑(k+1):ℤ)+1) := by
        intro p hp
        have : p ∈ ⋃ j, t.tile j := Set.mem_iUnion.mpr ⟨i₀, hp⟩
        rwa [t.covers] at this
      have h_sub₁ : ∀ p, p ∈ t.tile i₁ → p ∈ rect 0 0 3 (2*(↑(k+1):ℤ)+1) := by
        intro p hp
        have : p ∈ ⋃ j, t.tile j := Set.mem_iUnion.mpr ⟨i₁, hp⟩
        rwa [t.covers] at this
      rw [hrep₀] at hi₀ h_sub₀
      rw [hrep₁] at hi₁ h_sub₁
      -- From (0,0) ∈ placedCopy lShape dx₀ dy₀ r₀ and all cells in [0,3)×[0,2k+3),
      -- determine what the tile covering (0,0) looks like.
      -- For each rotation, the possible placements are determined by omega constraints.
      -- We'll show that in every case the first tile (covering (0,0)) has dy₀=0, dy₀=-1 etc.,
      -- then similarly for (2,0), and ultimately derive a sub-tiling of 3×(2k+1).
      -- This proof uses decide for the finite case analysis + structural IH.
      -- For now we extract the key contradiction via the area argument on the remaining region.
      -- (A complete structural proof follows below via omega case analysis.)
      -- Area argument: area of 3×(2k+3) = 9+6k, which is 3*(2k+3), 3 | it.
      -- After removing 2 tiles (covering (0,0) and (2,0)) the remaining region has area 9+6k-6 = 3+6k = 3*(1+2k).
      -- The remaining region must equal translate 0 2 (rect 0 0 3 (2k+1)) [if the bottom strip is exactly the 2 tiles].
      -- We need to show this rigorously.
      --
      -- The detailed Lean proof of this induction step requires significant case analysis on
      -- the rotations that can cover corners (0,0) and (2,0) within [0,3)×[0,∞).
      -- We defer it here with sorry and will complete it in a follow-up.
      sorry
