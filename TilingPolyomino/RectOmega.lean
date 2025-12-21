/-
# Rectangle Sets with Omega Automation

This file provides a minimal framework for reasoning about sets of grid cells
defined by Boolean combinations of axis-aligned half-open rectangles on ℤ × ℤ,
with an automation tactic `rect_omega` that proves set equalities by reducing
to Presburger arithmetic.

## Usage

The tactic `rect_omega` can prove goals of the form `A = B` where `A` and `B`
are `Set Cell` expressions built from:
- `rect x0 y0 x1 y1` (half-open rectangles)
- `∪` (union), `∩` (intersection), `\` (set difference)
- `translate dx dy s` (translation)

Example:
```lean
theorem example (n m : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m) :
  (rect 0 0 n (2*m) ∪ rect n 0 (2*n) (2*m)) =
  (rect 0 0 (2*n) m ∪ rect 0 m (2*n) (2*m)) := by
  rect_omega
```
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/- ## Basic Definitions -/

/-- A grid cell is a pair of integers -/
def Cell := ℤ × ℤ

/-- Half-open rectangle: `rect x0 y0 x1 y1` contains all cells `(x, y)` such that
    `x0 ≤ x < x1` and `y0 ≤ y < y1`. -/
def rect (x0 y0 x1 y1 : ℤ) : Set Cell :=
  {p : Cell | x0 ≤ p.1 ∧ p.1 < x1 ∧ y0 ≤ p.2 ∧ p.2 < y1}

/-- Translation of a set of cells by `(dx, dy)` -/
def translate (dx dy : ℤ) (s : Set Cell) : Set Cell :=
  {p : Cell | (p.1 - dx, p.2 - dy) ∈ s}

/- ## Simplification Lemmas -/

@[simp] theorem mem_rect (x0 y0 x1 y1 : ℤ) (p : Cell) :
  p ∈ rect x0 y0 x1 y1 ↔ x0 ≤ p.1 ∧ p.1 < x1 ∧ y0 ≤ p.2 ∧ p.2 < y1 := by
  rfl

@[simp] theorem mem_translate (dx dy : ℤ) (s : Set Cell) (p : Cell) :
  p ∈ translate dx dy s ↔ (p.1 - dx, p.2 - dy) ∈ s := by
  rfl

/- ## Automation Tactic -/

/-- Tactic to prove set equalities involving rectangles and Boolean operations.

    Strategy:
    1. Apply set extensionality (`ext p`)
    2. Simplify membership conditions (`simp`)
    3. Use `aesop` to handle propositional structure, with `omega` for arithmetic
-/
macro "rect_omega" : tactic => `(tactic| (
  ext p
  simp only [Set.mem_union, Set.mem_inter, Set.mem_diff, Set.mem_empty_iff_false,
    mem_rect, mem_translate]
  aesop (add 50% tactic Lean.Elab.Tactic.Omega.omegaDefault)
))

/- ## Demo Theorems -/

/-- Vertical split: splitting a (2n)×(2m) rectangle vertically vs horizontally.

    Left side: `rect 0 0 n (2*m) ∪ rect n 0 (2*n) (2*m)`
    Right side: `rect 0 0 (2*n) m ∪ rect 0 m (2*n) (2*m)`

    Both represent the same set: the full rectangle `rect 0 0 (2*n) (2*m)`.
-/
example (n m : ℤ) (hm : 0 ≤ m) :
  (rect 0 0 n (2*m) ∪ rect n 0 (2*n) (2*m)) =
  (rect 0 0 (2*n) m ∪ rect 0 m (2*n) (2*m)) := by
  rect_omega

/-- Disjointness: the left and right halves of a rectangle are disjoint
    when split at the midpoint (assuming the split point is valid). -/
theorem rect_left_right_disjoint (x0 y0 x1 y1 mid : ℤ) :
  rect x0 y0 mid y1 ∩ rect mid y0 x1 y1 = ∅ := by
  rect_omega

/-- Translation preserves rectangles (up to shifting bounds). -/
theorem translate_rect (x0 y0 x1 y1 dx dy : ℤ) :
  translate dx dy (rect x0 y0 x1 y1) = rect (x0 + dx) (y0 + dy) (x1 + dx) (y1 + dy) := by
  ext p
  simp only [mem_translate, mem_rect]
  constructor
  · intro ⟨hx0, hx1, hy0, hy1⟩
    constructor <;> omega
  · intro ⟨hx0, hx1, hy0, hy1⟩
    constructor <;> omega
