import TilingPolyomino.AbstractBridge

/-!
# Abstract layer — reader-facing statements

This file is the **reader's contract** for the TilingPolyomino project.  It
states the project's headline theorems using only elementary definitions,
given from scratch below: cells are pairs of integers, an L-tromino is an
explicit three-cell set, and a tiling is a finite family of pairwise disjoint
tiles covering the region.

A reader who wants to verify what this project proves only needs to:

1. read the elementary definitions in §1 and accept them as faithful to the
   intended mathematics,
2. read the theorem statements in §2 and accept them as the intended claims,
3. check that this file compiles with no `sorry`.

Each theorem is proved by a one-line delegation to `AbstractBridge.lean`,
which restates these definitions verbatim and carries the machinery
connecting them to the general layer (`TilingPolyomino/`).  The delegation
type-checks by definitional equality, so what is proved there is *exactly*
what is stated here; none of the proofs need to be read.

## Headline theorems

* `Abstract.LTileable_rectangle_iff` — the classical characterization of the
  rectangles tileable by L-trominoes.
* `Abstract.LTileable_dogEaredRectangle_iff` — Ash & Golomb's dog-eared
  rectangle theorem: an `n × m` rectangle minus a corner cell is tileable iff
  `3 ∣ n·m − 1` (for `n, m ≥ 2`).
* `Abstract.LTileable_cornerDomino_iff` — an `n × m` rectangle minus a domino
  at a corner is tileable iff `3 ∣ n·m − 2` (for `n, m ≥ 3`).
* `Abstract.LTileable_twoCornerDefects_iff` — the two-corner defect theorem
  (MIT-ULB CompGeom Group): for `n, m ≥ 6`, a rectangle with a defect of size
  1 or 2 at each of two distinct corners is tileable iff its area is
  divisible by 3.

## Sources and attribution

* J. Marshall Ash and Solomon W. Golomb, *Tiling deficient rectangles with
  trominoes*, Mathematics Magazine **77** (2004), no. 1, 46–55
  ([doi:10.2307/3219230](https://dx.doi.org/10.2307/3219230)).
  `LTileable_dogEaredRectangle_iff` is their dog-eared rectangle theorem;
  `LTileable_rectangle_iff` (the classical characterization of L-tromino
  tileable rectangles) and `LTileable_cornerDomino_iff` belong to the same
  circle of results — see the paper and the references therein.
* `LTileable_twoCornerDefects_iff` is a new result (2026) due to the
  **MIT-ULB CompGeom Group**; this file and the general layer contain its
  first proof and formalization.
* The elementary formulations stated in this file are this project's own
  restatements of the above.
-/

namespace Abstract

/-! ## §1 Elementary definitions -/

/-- A set of cells is an **L-tromino** if it is one of the four rotations of
    the L-shape `{(0,0), (0,1), (1,0)}`, translated anywhere in the plane —
    equivalently, three cells of a 2×2 square. -/
def IsLTromino (T : Set (ℤ × ℤ)) : Prop :=
  ∃ x y : ℤ,
    T = {(x, y), (x, y + 1), (x + 1, y)} ∨
    T = {(x, y), (x + 1, y), (x + 1, y + 1)} ∨
    T = {(x, y + 1), (x + 1, y), (x + 1, y + 1)} ∨
    T = {(x, y), (x, y + 1), (x + 1, y + 1)}

/-- A region is **L-tileable** if it is the union of finitely many pairwise
    disjoint L-trominoes. -/
def LTileable (R : Set (ℤ × ℤ)) : Prop :=
  ∃ (k : ℕ) (t : Fin k → Set (ℤ × ℤ)),
    (∀ i, IsLTromino (t i)) ∧
    (∀ i j, i ≠ j → Disjoint (t i) (t j)) ∧
    (⋃ i, t i) = R

/-- The `n × m` rectangle `[0, n) × [0, m)` of cells. -/
def rectangle (n m : ℤ) : Set (ℤ × ℤ) :=
  {p | 0 ≤ p.1 ∧ p.1 < n ∧ 0 ≤ p.2 ∧ p.2 < m}

/-- `D` is a **corner defect** of the rectangle `[0, n) × [0, m)` anchored at
    the corner cell `p`: either the corner cell alone, or the corner cell
    together with one of its two neighbours along the boundary. -/
def IsCornerDefect (n m : ℤ) (p : ℤ × ℤ) (D : Set (ℤ × ℤ)) : Prop :=
  (p = (0, 0) ∧
    (D = {(0, 0)} ∨ D = {(0, 0), (1, 0)} ∨ D = {(0, 0), (0, 1)})) ∨
  (p = (n - 1, 0) ∧
    (D = {(n - 1, 0)} ∨ D = {(n - 1, 0), (n - 2, 0)} ∨
     D = {(n - 1, 0), (n - 1, 1)})) ∨
  (p = (0, m - 1) ∧
    (D = {(0, m - 1)} ∨ D = {(0, m - 1), (1, m - 1)} ∨
     D = {(0, m - 1), (0, m - 2)})) ∨
  (p = (n - 1, m - 1) ∧
    (D = {(n - 1, m - 1)} ∨ D = {(n - 1, m - 1), (n - 2, m - 1)} ∨
     D = {(n - 1, m - 1), (n - 1, m - 2)}))

/-! ## §2 Headline theorems -/

/-- **The rectangle theorem.** An `n × m` rectangle is L-tileable iff it is
    empty, or its area is divisible by 3, neither side is 1, and it is not a
    `3 × odd` (or `odd × 3`) rectangle. -/
theorem LTileable_rectangle_iff (n m : ℕ) :
    LTileable (rectangle n m) ↔
      n = 0 ∨ m = 0 ∨
        (3 ∣ n * m ∧ n ≥ 2 ∧ m ≥ 2 ∧ ¬(n = 3 ∧ Odd m) ∧ ¬(Odd n ∧ m = 3)) :=
  AbstractBridge.LTileable_rectangle_iff n m

/-- **Ash–Golomb's dog-eared rectangle theorem.** For `n, m ≥ 2`, the `n × m`
    rectangle with the corner cell `(0, 0)` removed is L-tileable iff
    `3 ∣ n·m − 1`. -/
theorem LTileable_dogEaredRectangle_iff (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2) :
    LTileable (rectangle n m \ {(0, 0)}) ↔ 3 ∣ (n * m - 1) :=
  AbstractBridge.LTileable_dogEaredRectangle_iff n m hn hm

/-- **The corner-domino theorem.** For `n, m ≥ 3`, the `n × m` rectangle with
    the two adjacent corner cells `(0, 0)` and `(1, 0)` removed is L-tileable
    iff `3 ∣ n·m − 2`. -/
theorem LTileable_cornerDomino_iff (n m : ℕ) (hn : n ≥ 3) (hm : m ≥ 3) :
    LTileable (rectangle n m \ {(0, 0), (1, 0)}) ↔ 3 ∣ (n * m - 2) :=
  AbstractBridge.LTileable_cornerDomino_iff n m hn hm

/-- **The two-corner defect theorem** (MIT-ULB CompGeom Group). For
    `n, m ≥ 6`, an `n × m` rectangle with a corner defect of size 1 or 2 at
    each of two *distinct* corners is L-tileable iff its number of cells is
    divisible by 3. -/
theorem LTileable_twoCornerDefects_iff (n m : ℤ) (hn : n ≥ 6) (hm : m ≥ 6)
    {p₁ p₂ : ℤ × ℤ} {D₁ D₂ : Set (ℤ × ℤ)}
    (h₁ : IsCornerDefect n m p₁ D₁) (h₂ : IsCornerDefect n m p₂ D₂)
    (hp : p₁ ≠ p₂) :
    LTileable (rectangle n m \ (D₁ ∪ D₂)) ↔
      3 ∣ (rectangle n m \ (D₁ ∪ D₂)).ncard :=
  AbstractBridge.LTileable_twoCornerDefects_iff n m hn hm h₁ h₂ hp

end Abstract
