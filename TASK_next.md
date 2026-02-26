# TilingSet.lean — Next Theorems

You are continuing Lean 4 / Mathlib work on TilingPolyomino (branch feat/set-tiling).
File to extend: `TilingPolyomino/TilingSet.lean` (currently 668 lines).

## Already proved — DO NOT reprove
- Infrastructure: lShape, SetTileable, Tiling, refine, union, swap, translate
- Families: setTileable_2x_mult3, setTileable_3x_even, setTileable_6x_of_ge2, setTileable_kx6_of_ge2
- Area: setTileable_rect_area_dvd (3 ∣ m*n is necessary)

## TASK 1 — Impossibility: 1-wide strips (HIGH)

```lean
theorem not_setTileable_1xn (n : ℕ) : ¬ SetTileable (rect 0 0 1 n) lShape
```

Strategy: for any placement (placedCopy lShape dx dy r) all 4 rotations span ≥ 2 units in x.
Concretely: lShape.cells = {(0,0),(0,1),(1,0)}. All 4 rotations contain a cell with x=0 and a cell
with x=1 (or y=0 and y=1). So every piece sticks out of a 1-wide strip.

Try: unfold SetTileable, Tiling. Suppose t : Tiling (rect 0 0 1 n) lShape.
Then t.covers says every cell in rect 0 0 1 n belongs to some piece.
But show that every piece has cells in {x ≥ 1} AND {x < 1} simultaneously — contradiction if rect 0 0 1 n only has x ∈ [0,1).

Actually simpler: any placed L-tromino contains cells (dx, dy) and (dx+1, dy) (in rotation 0),
so it needs x ∈ {dx, dx+1}. For it to be ⊆ rect 0 0 1 n, need dx ≥ 0 and dx+1 < 1 — impossible.
Check all 4 rotations similarly.

Alternative: use `decide` on finite cases if the cells are computable for small n, but for general n
use the structural argument above. Lean 4 omega + case analysis on r : Fin 4 should work.

## TASK 2 — Biconditional for 2×n (HIGH)

```lean
-- Empty region: vacuously tileable
theorem setTileable_empty (s : Shape) : SetTileable ∅ s := by
  exact ⟨fun (i : Empty) => i.elim, fun (i : Empty) => i.elim, by simp, by tauto, by tauto⟩

-- For n = 0, rect 0 0 2 0 = ∅
theorem rect_zero_right : rect a b c b = ∅ := by
  ext ⟨x, y⟩; simp [mem_rect]; omega

theorem setTileable_2xn_iff (n : ℕ) :
    SetTileable (rect 0 0 2 n) lShape ↔ 3 ∣ n := by
  constructor
  · intro h
    have hdvd := setTileable_rect_area_dvd 2 n h
    -- hdvd : 3 ∣ 2 * n
    -- Nat.Coprime 3 2, so 3 ∣ n
    have hcop : Nat.Coprime 3 2 := by norm_num
    exact hcop.dvd_of_dvd_mul_left _ _ hdvd  -- adjust arg order as needed
  · intro ⟨k, hk⟩
    cases k with
    | zero => simp at hk; subst hk; rw [show (0:ℤ) = 0 from rfl]; exact setTileable_empty _
              -- or handle n=0 case: rect 0 0 2 0 = ∅
    | succ k =>
      have : n = 3 * (k + 1) := hk
      subst this
      exact setTileable_2x_mult3 (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
```

(Adjust for exact Mathlib API — check `Nat.Coprime.dvd_of_dvd_mul_left` vs `Nat.dvd_of_mul_dvd_left`.)

## TASK 3 — Large inductive families using refine (HIGH)

### 3a × 2b rectangles (any a,b ≥ 1)

```lean
theorem setTileable_mult3_mult2 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    SetTileable (rect 0 0 (3 * a) (2 * b)) lShape := by
  apply SetTileable.refine (ι := Fin a × Fin b)
    (pieces := fun ⟨i, j⟩ => rect (3 * i.val) (2 * j.val) (3 * (i.val + 1)) (2 * (j.val + 1)))
  · -- covers: ⋃ i j, piece (i,j) = rect 0 0 (3a) (2b)
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, mem_rect, Fin.exists_iff]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩, h⟩
      constructor <;> [skip; skip] <;> push_cast at * <;> omega
    · intro ⟨hx, hy⟩
      refine ⟨⟨⌊x / 3⌋.toNat, ?_⟩, ⟨⌊y / 2⌋.toNat, ?_⟩, ?_⟩ <;> push_cast <;> omega
      -- or just use omega after bounding the floor division indices
  · -- pairwise disjoint
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hne
    simp only [Function.onFun, Set.disjoint_left, mem_rect]
    intro ⟨x, y⟩ h₁ h₂
    apply hne
    ext <;> push_cast at * <;> omega
  · intro ⟨i, j⟩; exact rect_finite _ _ _ _
  · intro ⟨i, j⟩
    have heq : rect (3 * (i.val : ℤ)) (2 * j.val) (3 * (i.val + 1)) (2 * (j.val + 1))
             = translate (3 * i.val) (2 * j.val) (rect 0 0 3 2) := by
      ext ⟨x, y⟩; simp [mem_rect, mem_translate]; push_cast; omega
    rw [heq]
    exact setTileable_translate setTileable_3x2 _ _
```

Then by swap:
```lean
theorem setTileable_mult2_mult3 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    SetTileable (rect 0 0 (2 * a) (3 * b)) lShape := by
  have h := setTileable_swap (setTileable_mult3_mult2 b a hb ha)
  have heq : Set.swapRegion (rect 0 0 (3 * b) (2 * a)) = rect 0 0 (2 * a) (3 * b) := by
    ext ⟨x, y⟩; simp [mem_swapRegion, mem_rect]; omega
  rwa [heq] at h
```

## TASK 4 (BONUS): Characterize tileable rectangles (if time permits)

The family of tileable m×n rectangles includes exactly those where:
- m ≥ 2, n ≥ 2, and 3 ∣ mn, AND
- Not (m=2 and 3∤n) AND not (m=1 or n=1) (handled by Task 1 + 2)

A partial sufficient condition:
```lean
theorem setTileable_rect_of_conditions (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h6m : 6 ∣ m ∨ 6 ∣ n ∨ (2 ∣ m ∧ 3 ∣ n) ∨ (3 ∣ m ∧ 2 ∣ n)) :
    SetTileable (rect 0 0 m n) lShape
```
Use the families proved above.

## Workflow
1. Edit TilingPolyomino/TilingSet.lean
2. `lake build` to verify (run from repo root `/home/openclaw/.openclaw/workspace-matty/workspace/TilingPolyomino/`)
3. Commit after each group of theorems that pass
4. Push: `git push fork feat/set-tiling`

## Completion
When lake build passes, everything committed and pushed, run:
```
openclaw system event --text "Done: TilingSet impossibility + large inductive families" --mode now
```
