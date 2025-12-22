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
import TilingPolyomino.Tiling

/- ## Basic Definitions -/

-- Cell is already defined in TilingPolyomino.Tiling

/-- Half-open rectangle: `rect x0 y0 x1 y1` contains all cells `(x, y)` such that
    `x0 ≤ x < x1` and `y0 ≤ y < y1`. -/
def rect (x0 y0 x1 y1 : ℤ) : Set Cell :=
  {p : Cell | x0 ≤ p.1 ∧ p.1 < x1 ∧ y0 ≤ p.2 ∧ p.2 < y1}

/-- Translation of a set of cells by `(dx, dy)` -/
def translate (dx dy : ℤ) (s : Set Cell) : Set Cell :=
  {p : Cell | (p.1 - dx, p.2 - dy) ∈ s}

/-- Inverse rotation: rotating by `r` then by `inverseRot r` gives identity. -/
@[simp] def inverseRot (r : Fin 4) : Fin 4 :=
  match r with
  | 0 => 0
  | 1 => 3
  | 2 => 2
  | 3 => 1

/-- Rotation of a set of cells by a multiple of 90° counterclockwise around the origin.
    `r : Fin 4` represents rotation by `r * 90°` (0°, 90°, 180°, or 270°). -/
def rotate (r : Fin 4) (s : Set Cell) : Set Cell :=
  {p : Cell | rotateCell p (inverseRot r) ∈ s}

/-- Reflection of a set of cells: swaps x and y coordinates (reflection across line y=x). -/
def reflect (s : Set Cell) : Set Cell :=
  {p : Cell | swapCell p ∈ s}

/- ## Simplification Lemmas -/

@[simp] theorem mem_rect (x0 y0 x1 y1 : ℤ) (p : Cell) :
  p ∈ rect x0 y0 x1 y1 ↔ x0 ≤ p.1 ∧ p.1 < x1 ∧ y0 ≤ p.2 ∧ p.2 < y1 := by
  rfl

@[simp] theorem mem_translate (dx dy : ℤ) (s : Set Cell) (p : Cell) :
  p ∈ translate dx dy s ↔ (p.1 - dx, p.2 - dy) ∈ s := by
  rfl

@[simp] theorem mem_rotate (r : Fin 4) (s : Set Cell) (p : Cell) :
  p ∈ rotate r s ↔ rotateCell p (inverseRot r) ∈ s := by
  rfl

@[simp] theorem mem_reflect (s : Set Cell) (p : Cell) :
  p ∈ reflect s ↔ swapCell p ∈ s := by
  rfl

/-- Simplification lemma for swapCell. Not marked @[simp] to avoid breaking other proofs. -/
theorem swapCell_def (p : Cell) : swapCell p = (p.2, p.1) := rfl

/-- Simplification lemmas for rotateCell. Omega needs concrete arithmetic expressions,
    so we provide explicit lemmas for each rotation amount. -/
@[simp] theorem rotateCell_0 (p : Cell) : rotateCell p 0 = p := rfl
@[simp] theorem rotateCell_1 (p : Cell) : rotateCell p 1 = (-p.2, p.1) := rfl
@[simp] theorem rotateCell_2 (p : Cell) : rotateCell p 2 = (-p.1, -p.2) := by
  simp only [rotateCell, rotateCell90]
@[simp] theorem rotateCell_3 (p : Cell) : rotateCell p 3 = (p.2, -p.1) := by
  simp only [rotateCell, rotateCell90]
  ring_nf

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
    mem_rect, mem_translate, mem_rotate, mem_reflect, inverseRot, rotateCell_0, rotateCell_1,
    rotateCell_2, rotateCell_3, swapCell_def]
  aesop (add 50% tactic Lean.Elab.Tactic.Omega.omegaDefault)
))

/- ## Rectangle Expression DSL -/

/-- Rectangle expression AST for building polyomino-like regions as Boolean
    expressions over half-open rectangles on ℤ×ℤ, plus translation, rotation, and reflection. -/
inductive RExp
  | empty : RExp
  | rect : (x0 y0 x1 y1 : ℤ) → RExp
  | union : RExp → RExp → RExp
  | inter : RExp → RExp → RExp
  | diff : RExp → RExp → RExp
  | shift : (dx dy : ℤ) → RExp → RExp
  | rotate : (r : Fin 4) → RExp → RExp
  | reflect : RExp → RExp
  deriving Repr, DecidableEq

/-- Semantics: evaluate a rectangle expression to a set of cells. -/
def RExp.eval : RExp → Set Cell
  | .empty => ∅
  | .rect x0 y0 x1 y1 => _root_.rect x0 y0 x1 y1
  | .union a b => eval a ∪ eval b
  | .inter a b => eval a ∩ eval b
  | .diff a b => eval a \ eval b
  | .shift dx dy e => translate dx dy (eval e)
  | .rotate r e => _root_.rotate r (eval e)
  | .reflect e => _root_.reflect (eval e)

/-- Convenient constructor for rectangles. -/
def RExp.r (x0 y0 x1 y1 : ℤ) : RExp := RExp.rect x0 y0 x1 y1

/-- Notation for union. -/
infixl:65 " ⊔ " => RExp.union

/-- Notation for intersection. -/
infixl:70 " ⊓ " => RExp.inter

/-- Notation for set difference. -/
infixl:70 " ⊖ " => RExp.diff

/-- Notation for translation/shift. -/
notation "⇑[" dx "," dy "]" e => RExp.shift dx dy e

/-- Notation for rotation. `↻[r] e` rotates expression `e` by `r * 90°` counterclockwise. -/
notation "↻[" r "]" e => RExp.rotate r e

/-- Notation for reflection. `↔ e` reflects expression `e` across the line y=x (swaps x and y). -/
notation "↔" e => RExp.reflect e

/- ## RExp Simplification Lemmas -/

@[simp] theorem RExp.r_eq (x0 y0 x1 y1 : ℤ) :
  RExp.r x0 y0 x1 y1 = RExp.rect x0 y0 x1 y1 := rfl

@[simp] theorem RExp.eval_r (x0 y0 x1 y1 : ℤ) :
  RExp.eval (RExp.r x0 y0 x1 y1) = _root_.rect x0 y0 x1 y1 := rfl

@[simp] theorem RExp.eval_empty : RExp.eval RExp.empty = (∅ : Set Cell) := rfl

@[simp] theorem RExp.eval_rect (x0 y0 x1 y1 : ℤ) :
  RExp.eval (RExp.rect x0 y0 x1 y1) = _root_.rect x0 y0 x1 y1 := rfl

@[simp] theorem RExp.eval_union (a b : RExp) :
  RExp.eval (RExp.union a b) = RExp.eval a ∪ RExp.eval b := rfl

@[simp] theorem RExp.eval_inter (a b : RExp) :
  RExp.eval (RExp.inter a b) = RExp.eval a ∩ RExp.eval b := rfl

@[simp] theorem RExp.eval_diff (a b : RExp) :
  RExp.eval (RExp.diff a b) = RExp.eval a \ RExp.eval b := rfl

@[simp] theorem RExp.eval_shift (dx dy : ℤ) (e : RExp) :
  RExp.eval (RExp.shift dx dy e) = translate dx dy (RExp.eval e) := rfl

@[simp] theorem RExp.eval_rotate (r : Fin 4) (e : RExp) :
  RExp.eval (RExp.rotate r e) = _root_.rotate r (RExp.eval e) := rfl

@[simp] theorem RExp.eval_reflect (e : RExp) :
  RExp.eval (RExp.reflect e) = _root_.reflect (RExp.eval e) := rfl

/- ## RExp Automation Tactic -/

/-- More efficient variant of `rect_omega` that avoids `aesop`'s exponential search.
    Uses omega directly without aesop's exponential case exploration. -/
macro "rect_omega_direct" : tactic => `(tactic| (
  ext p
  simp only [Set.mem_union, Set.mem_inter, Set.mem_diff, Set.mem_empty_iff_false,
    mem_rect, mem_translate, mem_rotate, mem_reflect, inverseRot, rotateCell_0, rotateCell_1,
    rotateCell_2, rotateCell_3, swapCell_def]
  omega
))

/-- Tactic to prove equalities of `RExp.eval` expressions.
    Simplifies `RExp.eval` to `Set Cell` expressions, then calls `rect_omega`. -/
macro "rexp_omega" : tactic => `(tactic| (
  simp only [RExp.eval_empty, RExp.eval_rect, RExp.eval_r, RExp.eval_union, RExp.eval_inter,
    RExp.eval_diff, RExp.eval_shift, RExp.eval_rotate, RExp.eval_reflect]
  rect_omega
))

/-- More efficient variant of `rexp_omega` that uses `rect_omega_direct` instead. -/
macro "rexp_omega_direct" : tactic => `(tactic| (
  simp only [RExp.eval_empty, RExp.eval_rect, RExp.eval_r, RExp.eval_union, RExp.eval_inter,
    RExp.eval_diff, RExp.eval_shift, RExp.eval_rotate, RExp.eval_reflect]
  rect_omega_direct
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

/- ## RExp Example Theorems -/

/-- Example (A): Vertical split identity expressed with RExp.
    Splitting a (2n)×(2m) rectangle vertically vs horizontally. -/
example (n m : ℤ) (hm : 0 ≤ m) :
  RExp.eval (RExp.r 0 0 n (2*m) ⊔ RExp.r n 0 (2*n) (2*m)) =
  RExp.eval (RExp.r 0 0 (2*n) m ⊔ RExp.r 0 m (2*n) (2*m)) := by
  rexp_omega

/-- Example (B): A hole/subtraction example.
    A 4×4 rectangle with a 2×2 hole in the middle equals the union of four rectangles
    forming a frame around the hole. -/
example :
  RExp.eval (RExp.r 0 0 4 4 ⊖ RExp.r 1 1 3 3) =
  RExp.eval ((RExp.r 0 0 4 1 ⊔ RExp.r 0 1 1 3) ⊔ (RExp.r 3 1 4 3 ⊔ RExp.r 0 3 4 4)) := by
  rexp_omega

/-- Example (C): Translation example.
    Translating a rectangle shifts its bounds by the translation vector. -/
example (x0 y0 x1 y1 dx dy : ℤ) :
  RExp.eval (⇑[dx, dy] (RExp.r x0 y0 x1 y1)) =
    _root_.rect (x0 + dx) (y0 + dy) (x1 + dx) (y1 + dy) := by
  simp only [RExp.eval_shift, RExp.eval_r]
  exact translate_rect x0 y0 x1 y1 dx dy

/-- Example (D): Test case with nested set differences and arithmetic.
    Tests that the tactic can handle expressions like `3 * j + 2`, `3 * k - 1` without timing out.
    This tests the same complexity as `rectangleMinus2Corner_decomp_rexp`:
    - Nested set differences (A ⊖ B ⊖ C)
    - Arithmetic expressions with multiplication and addition/subtraction
    - Unions of multiple RExp expressions
    - Translation operations

    This example shows that a rectangle minus two corners can be expressed as
    the union of a smaller rectangle-minus-corner, a translated rectangle, and an L-tromino.
    (This is similar in structure to the actual decomposition theorem.) -/
example (j k : ℕ) (hj : j ≥ 1) (hk : k ≥ 1) :
  -- Test the complexity: nested differences with arithmetic
  RExp.eval (RExp.r 0 0 (3 * j + 2) (3 * k + 1) ⊖
           RExp.r (3 * j + 1) (3 * k) (3 * j + 2) (3 * k + 1) ⊖
           RExp.r (3 * j) (3 * k) (3 * j + 1) (3 * k + 1)) =
  -- Decomposed into: rectangle-minus-corner ∪ translated rectangle ∪ L-tromino
  RExp.eval (RExp.r 0 0 (3 * j + 2) (3 * k - 1) ⊖
           RExp.r (3 * j + 1) (3 * k - 2) (3 * j + 2) (3 * k - 1)) ∪
  RExp.eval (⇑[0, 3 * k - 1] (RExp.r 0 0 (3 * j) 2)) ∪
  RExp.eval (RExp.r (3 * j) (3 * k - 2) (3 * j + 2) (3 * k) ⊖
           RExp.r (3 * j) (3 * k - 2) (3 * j + 1) (3 * k - 1)) := by
  -- To test the tactic: replace `sorry` with `rexp_omega_direct`
  -- This will test if the tactic can handle the complexity without timing out
  -- (The equality may or may not be true - this is primarily for performance testing)
  rexp_omega_direct

/-- Example (E): Rotation example.
    Rotating a rectangle by 180°.
    A 2×3 rectangle `rect 0 0 2 3` rotated by 180° becomes `rect (-1) (-2) 1 1`.

    The original rectangle contains cells with x ∈ {0, 1} and y ∈ {0, 1, 2}.
    After 180° rotation (x, y) → (-x, -y), we get cells with x ∈ {-1, 0} and y ∈ {-2, -1, 0},
    which is exactly `rect (-1) (-2) 1 1` (half-open: -1 ≤ x < 1, -2 ≤ y < 1).

    This example shows that rotation works with `rexp_omega`, proving that
    a rotated rectangle equals the expected set of cells using the automation tactic. -/
example :
  RExp.eval (↻[2] (RExp.r 0 0 2 3)) =
    _root_.rect (-1) (-2) 1 1 := by
  rexp_omega_direct

/-- Example (F): Reflection example.
    Reflecting a rectangle across the line y=x swaps its dimensions.
    A 2×3 rectangle `rect 0 0 2 3` reflected becomes `rect 0 0 3 2`.

    The original rectangle contains cells with x ∈ {0, 1} and y ∈ {0, 1, 2}.
    After reflection (x, y) → (y, x), we get cells with x ∈ {0, 1, 2} and y ∈ {0, 1},
    which is exactly `rect 0 0 3 2` (half-open: 0 ≤ x < 3, 0 ≤ y < 2).

    This example shows that reflection works with `rexp_omega`, proving that
    a reflected rectangle equals the expected set of cells using the automation tactic. -/
example :
  RExp.eval (↔ (RExp.r 0 0 2 3)) =
    _root_.rect 0 0 3 2 := by
  rexp_omega_direct
