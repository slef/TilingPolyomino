import Mathlib.Data.Set.Basic

/-!
# The integer grid: cells, corners, rectangles

The shared vocabulary of the whole development, below everything else.
This file imports only Mathlib, so that the pure polyomino theory
(`Polyomino/`) — a candidate for extraction as a standalone library —
need not import any tiling file.

* `Cell` — a cell of the integer grid.
* `Corner` — the four corners of a rectangle.
* `rect` — the half-open rectangle `[x0, x1) × [y0, y1)`.
-/

/-- A cell on the integer grid -/
abbrev Cell := ℤ × ℤ

/-- The four corners of a rectangle. -/
inductive Corner
  | BL
  | BR
  | TL
  | TR
  deriving DecidableEq

/-- Half-open rectangle: `rect x0 y0 x1 y1` contains all cells `(x, y)` such that
    `x0 ≤ x < x1` and `y0 ≤ y < y1`. -/
def rect (x0 y0 x1 y1 : ℤ) : Set Cell :=
  {p : Cell | x0 ≤ p.1 ∧ p.1 < x1 ∧ y0 ≤ p.2 ∧ p.2 < y1}

@[simp] theorem mem_rect (x0 y0 x1 y1 : ℤ) (p : Cell) :
  p ∈ rect x0 y0 x1 y1 ↔ x0 ≤ p.1 ∧ p.1 < x1 ∧ y0 ≤ p.2 ∧ p.2 < y1 := by
  rfl
