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
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Interval
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

/- ## Finite Boxes -/

/-- Finite set representation of a half-open rectangle using `Finset.Ico`.
    Enumerates exactly the cells in `[x0, x1) × [y0, y1)`. -/
def boxFinset (x0 y0 x1 y1 : ℤ) : Finset Cell :=
  (Finset.Ico x0 x1).product (Finset.Ico y0 y1)

/-- Membership in `boxFinset` matches the `rect` definition. -/
@[simp] lemma mem_boxFinset (x0 y0 x1 y1 : ℤ) (p : Cell) :
  p ∈ boxFinset x0 y0 x1 y1 ↔
    x0 ≤ p.1 ∧ p.1 < x1 ∧ y0 ≤ p.2 ∧ p.2 < y1 := by
  simp only [boxFinset]
  -- Use simp to handle the .product to ×ˢ conversion and apply mem_product
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    exact ⟨hx0, hx1, hy0, hy1⟩
  · rintro ⟨hx0, hx1, hy0, hy1⟩
    exact ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩



/-- Cardinality of `boxFinset`. -/
theorem card_boxFinset (x0 y0 x1 y1 : ℤ) :
  (boxFinset x0 y0 x1 y1).card =
    ((x1 - x0).toNat) * ((y1 - y0).toNat) := by
  simp only [boxFinset]
  simp

/-- Example: cardinality of box starting at origin. -/
example (n m : ℤ) :
  (boxFinset 0 0 n m).card = n.toNat * m.toNat := by
  simp [card_boxFinset]

/-- Example: 4×4 box has 16 cells. -/
example :
  (boxFinset 0 0 4 4).card = 16 := by
  simp [card_boxFinset]

theorem rect_eq_boxFinset_coe (x0 y0 x1 y1 : ℤ) :
    rect x0 y0 x1 y1 = (boxFinset x0 y0 x1 y1 : Set Cell) := by
  ext p
  simp [boxFinset, rect]
  tauto

def rectFinset (x0 y0 x1 y1 : ℤ) : Finset Cell :=
  boxFinset x0 y0 x1 y1

theorem card_rectFinset (x0 y0 x1 y1 : ℤ) :
  (rectFinset x0 y0 x1 y1).card =
    ((x1 - x0).toNat) * ((y1 - y0).toNat) :=
by simpa [rectFinset] using card_boxFinset x0 y0 x1 y1


/- ## Cardinality Lemmas -/

theorem rect_encard (x0 y0 x1 y1 : ℤ) :
  (rect x0 y0 x1 y1).encard = (boxFinset x0 y0 x1 y1).card := by
  simp [rect_eq_boxFinset_coe]

theorem rect_encard_formula (x0 y0 x1 y1 : ℤ) :
  (rect x0 y0 x1 y1).encard =
    ((x1 - x0).toNat : ℕ∞) * ((y1 - y0).toNat : ℕ∞) := by
  simp [rect_encard]
  simp [card_boxFinset]

/-- Rectangles are finite sets. -/
theorem rect_finite (x0 y0 x1 y1 : ℤ) : Set.Finite (rect x0 y0 x1 y1) := by
  simp [rect_eq_boxFinset_coe]

/-- Cardinality of a half-open rectangle.
    For a rectangle `rect x0 y0 x1 y1`, the cardinality is `(x1 - x0).natAbs * (y1 - y0).natAbs`
    when `x0 < x1` and `y0 < y1`, and `0` otherwise. -/
theorem rect_ncard (x0 y0 x1 y1 : ℤ) :
  (rect x0 y0 x1 y1).ncard =
     (x1 - x0).toNat * (y1 - y0).toNat := by
  simp [rect_eq_boxFinset_coe]
  simp [card_boxFinset]

/-- Cardinality of empty set. -/
@[simp] theorem empty_ncard : (∅ : Set Cell).ncard = 0 := by
simp

/-- Cardinality of a union using inclusion-exclusion.
    `(A ∪ B).ncard = A.ncard + B.ncard - (A ∩ B).ncard` -/
theorem union_ncard (A B : Set Cell) (hA : Set.Finite A) (hB : Set.Finite B) :
  (A ∪ B).ncard = A.ncard + B.ncard - (A ∩ B).ncard := by
  -- Define finiteness proofs for the union and intersection
  have hAB : (A ∪ B).Finite := hA.union hB
  have hAiB : (A ∩ B).Finite := hA.inter_of_left B
  -- Convert ncard to toFinset.card
  rw [Set.ncard_eq_toFinset_card A hA, Set.ncard_eq_toFinset_card B hB,
      Set.ncard_eq_toFinset_card (A ∪ B) hAB, Set.ncard_eq_toFinset_card (A ∩ B) hAiB]
  -- Connect set operations with finset operations
  rw [Set.Finite.toFinset_union hA hB hAB, Set.Finite.toFinset_inter hA hB hAiB]
  -- Apply Finset.card_union_add_card_inter: (A ∪ B).card + (A ∩ B).card = A.card + B.card
  have h := Finset.card_union_add_card_inter hA.toFinset hB.toFinset
  omega

/-- Cardinality of a union of disjoint sets.
    When `A ∩ B = ∅`, we have `(A ∪ B).ncard = A.ncard + B.ncard`. -/
theorem union_ncard_disjoint (A B : Set Cell) (hA : Set.Finite A) (hB : Set.Finite B)
    (h : Disjoint A B) :
  (A ∪ B).ncard = A.ncard + B.ncard := by
  -- Use the general inclusion-exclusion formula
  rw [union_ncard A B hA hB]
  -- Show that disjoint sets have empty intersection
  have h_empty : A ∩ B = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty] at h
    exact h
  -- The empty set has cardinality 0
  have h_ncard : (A ∩ B).ncard = 0 := by
    rw [h_empty]
    exact empty_ncard
  -- Simplify: subtract 0 from the sum
  rw [h_ncard]
  omega

/-- Cardinality of set difference.
    `(A \ B).ncard = A.ncard - (A ∩ B).ncard` when `A` is finite. -/
theorem diff_ncard (A B : Set Cell) (hA : Set.Finite A) :
  (A \ B).ncard = A.ncard - (A ∩ B).ncard := by
  -- First, show that A = (A \ B) ∪ (A ∩ B)
  have h_union : A = (A \ B) ∪ (A ∩ B) := by
    ext p
    simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    constructor
    · intro hA_p
      -- If p ∈ A, then either p ∉ B (so p ∈ A \ B) or p ∈ B (so p ∈ A ∩ B)
      by_cases hB_p : p ∈ B
      · right
        exact ⟨hA_p, hB_p⟩
      · left
        exact ⟨hA_p, hB_p⟩
    · intro h
      -- If p ∈ (A \ B) ∪ (A ∩ B), then p ∈ A
      cases h with
      | inl h_diff => exact h_diff.1
      | inr h_inter => exact h_inter.1
  -- Show that (A \ B) and (A ∩ B) are disjoint
  have h_disjoint : Disjoint (A \ B) (A ∩ B) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false]
    tauto
  -- Establish finiteness of the components
  -- A \ B is a subset of A, so it's finite
  have h_diff_subset : A \ B ⊆ A := by
    intro p h
    exact h.1
  have h_diff_finite : Set.Finite (A \ B) := Set.Finite.subset hA h_diff_subset
  have h_inter_finite : Set.Finite (A ∩ B) := hA.inter_of_left B
  -- Use union_ncard_disjoint to get A.ncard = (A \ B).ncard + (A ∩ B).ncard
  have h_card : A.ncard = (A \ B).ncard + (A ∩ B).ncard := by
    have h_union_card : ((A \ B) ∪ (A ∩ B)).ncard = (A \ B).ncard + (A ∩ B).ncard :=
      union_ncard_disjoint (A \ B) (A ∩ B) h_diff_finite h_inter_finite h_disjoint
    rw [← h_union] at h_union_card
    exact h_union_card
  -- Rearrange to get the desired result
  omega

/-- Cardinality of set difference when the subtracted set is disjoint.
    When `A ∩ B = ∅`, we have `(A \ B).ncard = A.ncard`. -/
theorem diff_ncard_disjoint (A B : Set Cell) (hA : Set.Finite A) (h : Disjoint A B) :
  (A \ B).ncard = A.ncard := by
  -- Use diff_ncard to get (A \ B).ncard = A.ncard - (A ∩ B).ncard
  rw [diff_ncard A B hA]
  -- Show that disjoint sets have empty intersection
  have h_empty : A ∩ B = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty] at h
    exact h
  -- The empty set has cardinality 0
  have h_ncard : (A ∩ B).ncard = 0 := by
    rw [h_empty]
    exact empty_ncard
  -- Simplify: subtract 0 from A.ncard
  rw [h_ncard]
  omega

/-- Translation preserves cardinality (translation is a bijection). -/
theorem translate_ncard (dx dy : ℤ) (s : Set Cell) (h : Set.Finite s) :
  (translate dx dy s).ncard = s.ncard := by
  -- Show that translate is equivalent to image of s under translateCell
  have h_eq : translate dx dy s = (s.image (fun p => translateCell p (dx, dy))) := by
    ext p
    simp only [Set.mem_image, mem_translate, translateCell]
    constructor
    · intro h
      use (p.1 - dx, p.2 - dy)
      constructor
      · exact h
      · ring_nf
    · rintro ⟨q, hq, rfl⟩
      simp only
      convert hq using 1
      ring_nf
  rw [h_eq]
  -- Use Set.ncard_image_of_injective with translateCell_injective
  -- The image is finite because s is finite and translation is a bijection
  have h_image_finite : Set.Finite (s.image (fun p => translateCell p (dx, dy))) :=
    Set.Finite.image _ h
  exact Set.ncard_image_of_injective s (translateCell_injective (dx, dy))

/-- Rotation preserves cardinality (rotation is a bijection). -/
theorem rotate_ncard (r : Fin 4) (s : Set Cell) (h : Set.Finite s) :
  (rotate r s).ncard = s.ncard := by
  -- Show that rotate is equivalent to image of s under rotation function
  have h_eq : rotate r s = (s.image (fun p => rotateCell p r)) := by
    ext p
    simp only [Set.mem_image, mem_rotate]
    constructor
    · intro h
      -- p ∈ rotate r s means rotateCell p (inverseRot r) ∈ s
      -- We want to show p = rotateCell q r for some q ∈ s
      use rotateCell p (inverseRot r)
      constructor
      · exact h
      · -- Show: rotateCell (rotateCell p (inverseRot r)) r = p
        -- Prove by case analysis on r
        fin_cases r
        · -- r = 0, inverseRot 0 = 0
          simp [rotateCell_0, inverseRot]
        · -- r = 1, inverseRot 1 = 3
          simp only [rotateCell_3, inverseRot]
          -- Need: rotateCell (rotateCell p 3) 1 = p
          -- rotateCell p 3 = (p.2, -p.1)
          -- rotateCell (p.2, -p.1) 1 = (-(-p.1), p.2) = (p.1, p.2) = p
          ext <;> simp [rotateCell_1]
        · -- r = 2, inverseRot 2 = 2
          simp only [rotateCell_2, inverseRot]
          -- Need: rotateCell (rotateCell p 2) 2 = p
          -- rotateCell p 2 = (-p.1, -p.2)
          -- rotateCell (-p.1, -p.2) 2 = (-(-p.1), -(-p.2)) = (p.1, p.2) = p
          ext <;> simp [rotateCell_2]
        · -- r = 3, inverseRot 3 = 1
          simp only [rotateCell_1, inverseRot]
          -- Need: rotateCell (rotateCell p 1) 3 = p
          -- rotateCell p 1 = (-p.2, p.1)
          -- rotateCell (-p.2, p.1) 3 = (p.1, -(-p.2)) = (p.1, p.2) = p
          ext <;> simp [rotateCell_3]
    · rintro ⟨q, hq, rfl⟩
      -- Need to show: rotateCell (rotateCell q r) (inverseRot r) ∈ s
      -- This should be q, which is in s by hq
      -- Prove by case analysis
      fin_cases r
      · -- r = 0, inverseRot 0 = 0
        simp only [rotateCell_0, inverseRot] at hq ⊢
        exact hq
      · -- r = 1, inverseRot 1 = 3
        simp only [rotateCell_3, inverseRot] at hq ⊢
        -- Need: rotateCell (rotateCell q 1) 3 ∈ s, which is q ∈ s
        -- rotateCell q 1 = (-q.2, q.1)
        -- rotateCell (-q.2, q.1) 3 = (q.1, -(-q.2)) = (q.1, q.2) = q
        simp only [Fin.mk_one, Fin.isValue, rotateCell_1, neg_neg, Prod.mk.eta]
        exact hq
      · -- r = 2, inverseRot 2 = 2
        simp only [rotateCell_2, inverseRot] at hq ⊢
        -- rotateCell (rotateCell q 2) 2 = rotateCell (-q.1, -q.2) 2 = (q.1, q.2) = q
        simp only [Fin.reduceFinMk, rotateCell_2, neg_neg, Prod.mk.eta]
        exact hq
      · -- r = 3, inverseRot 3 = 1
        simp only [rotateCell_1, inverseRot] at hq ⊢
        simp only [Fin.reduceFinMk, rotateCell_3, neg_neg, Prod.mk.eta]
        exact hq
  rw [h_eq]
  -- Use Set.ncard_image_of_injective
  -- The image is finite because s is finite and rotation is a bijection
  have h_image_finite : Set.Finite (s.image (fun p => rotateCell p r)) :=
    Set.Finite.image _ h
  exact Set.ncard_image_of_injective s (rotateCell_injective r)

/-- Reflection preserves cardinality (reflection is a bijection). -/
theorem reflect_ncard (s : Set Cell) (h : Set.Finite s) :
  (reflect s).ncard = s.ncard := by
  -- Show that reflect is equivalent to image of s under swapCell
  have h_eq : reflect s = (s.image swapCell) := by
    ext p
    simp only [Set.mem_image, mem_reflect]
    constructor
    · intro h
      -- p ∈ reflect s means swapCell p ∈ s
      -- We want to show p = swapCell q for some q ∈ s
      use swapCell p
      constructor
      · exact h
      · -- Show: swapCell (swapCell p) = p
        -- This follows from swapCell being an involution
        exact swapCell_involutive p
    · rintro ⟨q, hq, rfl⟩
      -- Need to show: swapCell (swapCell q) ∈ s
      -- This is q, which is in s by hq
      rw [swapCell_involutive]
      exact hq
  rw [h_eq]
  -- Use Set.ncard_image_of_injective
  -- The image is finite because s is finite and reflection is a bijection
  have h_image_finite : Set.Finite (s.image swapCell) :=
    Set.Finite.image _ h
  exact Set.ncard_image_of_injective s swapCell_injective

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

/- ## RExp Cardinality Lemmas -/

/-- Cardinality of an empty RExp. -/
@[simp] theorem RExp.ncard_empty :
  (RExp.eval RExp.empty).ncard = 0 := by
  simp only [RExp.eval_empty, empty_ncard]

/-- Cardinality of a rectangle RExp. -/
theorem RExp.ncard_rect (x0 y0 x1 y1 : ℤ) :
  (RExp.eval (RExp.rect x0 y0 x1 y1)).ncard =
     (x1 - x0).toNat * (y1 - y0).toNat := by
  simp only [RExp.eval_rect]
  exact rect_ncard x0 y0 x1 y1

/-- Cardinality of a union RExp using inclusion-exclusion.
    Requires finiteness assumptions. -/
theorem RExp.ncard_union (a b : RExp) (ha : Set.Finite (RExp.eval a))
    (hb : Set.Finite (RExp.eval b)) :
  (RExp.eval (RExp.union a b)).ncard =
    (RExp.eval a).ncard + (RExp.eval b).ncard - (RExp.eval a ∩ RExp.eval b).ncard := by
  simp only [RExp.eval_union]
  exact union_ncard (RExp.eval a) (RExp.eval b) ha hb

/-- Cardinality of a union of disjoint RExp expressions. -/
theorem RExp.ncard_union_disjoint (a b : RExp) (ha : Set.Finite (RExp.eval a))
    (hb : Set.Finite (RExp.eval b)) (h : Disjoint (RExp.eval a) (RExp.eval b)) :
  (RExp.eval (RExp.union a b)).ncard = (RExp.eval a).ncard + (RExp.eval b).ncard := by
  simp only [RExp.eval_union]
  exact union_ncard_disjoint (RExp.eval a) (RExp.eval b) ha hb h

/-- Cardinality of an intersection RExp. -/
theorem RExp.ncard_inter (a b : RExp) :
  (RExp.eval (RExp.inter a b)).ncard = (RExp.eval a ∩ RExp.eval b).ncard := by
  simp only [RExp.eval_inter]

/-- Cardinality of a difference RExp. -/
theorem RExp.ncard_diff (a b : RExp) (ha : Set.Finite (RExp.eval a)) :
  (RExp.eval (RExp.diff a b)).ncard = (RExp.eval a).ncard - (RExp.eval a ∩ RExp.eval b).ncard := by
  simp only [RExp.eval_diff]
  exact diff_ncard (RExp.eval a) (RExp.eval b) ha

/-- Cardinality of a difference RExp when sets are disjoint. -/
theorem RExp.ncard_diff_disjoint (a b : RExp) (ha : Set.Finite (RExp.eval a))
    (h : Disjoint (RExp.eval a) (RExp.eval b)) :
  (RExp.eval (RExp.diff a b)).ncard = (RExp.eval a).ncard := by
  simp only [RExp.eval_diff]
  exact diff_ncard_disjoint (RExp.eval a) (RExp.eval b) ha h

/-- Translation preserves cardinality of RExp. -/
theorem RExp.ncard_shift (dx dy : ℤ) (e : RExp) (h : Set.Finite (RExp.eval e)) :
  (RExp.eval (RExp.shift dx dy e)).ncard = (RExp.eval e).ncard := by
  simp only [RExp.eval_shift]
  exact translate_ncard dx dy (RExp.eval e) h

/-- Rotation preserves cardinality of RExp. -/
theorem RExp.ncard_rotate (r : Fin 4) (e : RExp) (h : Set.Finite (RExp.eval e)) :
  (RExp.eval (RExp.rotate r e)).ncard = (RExp.eval e).ncard := by
  simp only [RExp.eval_rotate]
  exact rotate_ncard r (RExp.eval e) h

/-- Reflection preserves cardinality of RExp. -/
theorem RExp.ncard_reflect (e : RExp) (h : Set.Finite (RExp.eval e)) :
  (RExp.eval (RExp.reflect e)).ncard = (RExp.eval e).ncard := by
  simp only [RExp.eval_reflect]
  exact reflect_ncard (RExp.eval e) h

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

/- ## RExp Cardinality Automation Tactic -/

/-- Tactic to prove cardinality equalities for RExp expressions.

    This tactic:
    1. Simplifies `RExp.eval` expressions
    2. Applies cardinality lemmas (rect_ncard, union_ncard, etc.)
    3. Attempts to prove finiteness using `Set.toFinite`
    4. Uses `omega` for arithmetic simplifications

    Example:
    ```lean
    example (n m : ℤ) (hn : 0 ≤ n) (hm : 0 ≤ m) :
      (RExp.eval (RExp.r 0 0 n m)).ncard = n.natAbs * m.natAbs := by
      rexp_ncard
    ```
-/
macro "rexp_ncard" : tactic => `(tactic| (
  simp only [RExp.eval_empty, RExp.eval_rect, RExp.eval_r, RExp.eval_union, RExp.eval_inter,
    RExp.eval_diff, RExp.eval_shift, RExp.eval_rotate, RExp.eval_reflect,
    RExp.ncard_empty, RExp.ncard_rect, RExp.ncard_union, RExp.ncard_inter, RExp.ncard_diff,
    RExp.ncard_shift, RExp.ncard_rotate, RExp.ncard_reflect,
    rect_ncard, union_ncard, diff_ncard, empty_ncard]
  try (apply rect_finite)
  omega
))

/-- More aggressive variant that also handles disjointness automatically. -/
macro "rexp_ncard_auto" : tactic => `(tactic| (
  simp only [RExp.eval_empty, RExp.eval_rect, RExp.eval_r, RExp.eval_union, RExp.eval_inter,
    RExp.eval_diff, RExp.eval_shift, RExp.eval_rotate, RExp.eval_reflect,
    RExp.ncard_empty, RExp.ncard_rect, RExp.ncard_union, RExp.ncard_union_disjoint,
    RExp.ncard_inter, RExp.ncard_diff, RExp.ncard_diff_disjoint,
    RExp.ncard_shift, RExp.ncard_rotate, RExp.ncard_reflect,
    rect_ncard, union_ncard, union_ncard_disjoint, diff_ncard, diff_ncard_disjoint, empty_ncard]
  try (apply rect_finite)
  try (rw [Set.disjoint_iff_inter_eq_empty]; try rect_omega_direct)
  omega
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

/- ## Cardinality Example Theorems -/

/-- Example (G): Basic rectangle cardinality.
    A 3×4 rectangle has cardinality 12. -/
example : (RExp.eval (RExp.r 0 0 3 4)).ncard = 12 := by
  simp [rect_ncard]

/-- Example (H): Empty set has cardinality 0. -/
example : (RExp.eval RExp.empty).ncard = 0 := by
  simp

/-- Example (I): Translation preserves cardinality.
    Translating a 2×3 rectangle doesn't change its cardinality. -/
example (dx dy : ℤ) :
  (RExp.eval (⇑[dx, dy] (RExp.r 0 0 2 3))).ncard = 6 := by
  rw [RExp.ncard_shift]
  · simp [rect_ncard]
  · simp [rect_finite]

/-- Example (J): Rotation preserves cardinality.
    Rotating a 2×3 rectangle doesn't change its cardinality. -/
example (r : Fin 4) :
  (RExp.eval (↻[r] (RExp.r 0 0 2 3))).ncard = 6 := by
  rw [RExp.ncard_rotate]
  · simp [rect_ncard]
  · simp [rect_finite]

/-- Example (K): Reflection preserves cardinality.
    Reflecting a 2×3 rectangle doesn't change its cardinality. -/
example :
  (RExp.eval (↔ (RExp.r 0 0 2 3))).ncard = 6 := by
  rw [RExp.ncard_reflect]
  · simp [rect_ncard]
  · simp [rect_finite]
