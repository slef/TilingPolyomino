/-
# Polyomino Tiling Proofs (L-tromino specialization)

This file develops the theory of tilings by L-trominoes on rectangles
and deficient rectangles, building on the general framework in
`TilingPolyomino.Tiling`.

Main results include:
- `rect_tileable_iff`: characterization of L-tileable rectangles.
- `rectMinusCorner_tileable_iff`: Ash–Golomb's "dog-eared rectangle" theorem.
-/

import TilingPolyomino.Tiling
import TilingPolyomino.RectOmega
import Mathlib.Tactic


/- ## L-Tromino Protoset

The L-tromino is a single prototile that looks like:
```
  □
  □ □   (cells: (0,0), (0,1), (1,0))
```
-/

/-- The L-tromino shape, anchored at origin -/
def LTromino : Prototile := ⟨[(0, 0), (0, 1), (1, 0)], by decide⟩

/-- A protoset containing just the L-tromino -/
def LTrominoSet : Protoset Unit := ⟨fun _ => LTromino⟩

/- ## Existential Tileability -/

/-- A region is tileable by L-trominoes if there exists a valid tiling -/
def LTileable (r : Region) : Prop := Tileable LTrominoSet r

/-- Explicit tiling of the 5×9 rectangle with 15 L-trominoes.
This is a special base case that needs an irregular tiling.
The key insight is that 5×9 cannot be decomposed into rectangular pieces
that are all individually L-tileable. We need tiles that cross boundaries. -/
def tiling_5x9 : TileSet LTrominoSet (Fin 15) := ⟨![
  ⟨(), (1, 0), 1⟩,   -- Tile 0: covers (0,0), (1,0), (1,1)
  ⟨(), (0, 2), 3⟩,   -- Tile 1: covers (0,1), (0,2), (1,2)
  ⟨(), (0, 4), 3⟩,   -- Tile 2: covers (0,3), (0,4), (1,4)
  ⟨(), (2, 3), 2⟩,   -- Tile 3: covers (1,3), (2,2), (2,3)
  ⟨(), (0, 6), 3⟩,   -- Tile 4: covers (0,5), (0,6), (1,6)
  ⟨(), (2, 5), 2⟩,   -- Tile 5: covers (1,5), (2,4), (2,5)
  ⟨(), (0, 8), 3⟩,   -- Tile 6: covers (0,7), (0,8), (1,8)
  ⟨(), (2, 7), 1⟩,   -- Tile 7: covers (1,7), (2,7), (2,8)
  ⟨(), (3, 6), 1⟩,   -- Tile 8: covers (2,6), (3,6), (3,7)
  ⟨(), (4, 8), 2⟩,   -- Tile 9: covers (3,8), (4,7), (4,8)
  ⟨(), (4, 5), 1⟩,   -- Tile 10: covers (3,5), (4,5), (4,6)
  ⟨(), (2, 1), 3⟩,   -- Tile 11: covers (2,0), (2,1), (3,1)
  ⟨(), (4, 0), 1⟩,   -- Tile 12: covers (3,0), (4,0), (4,1)
  ⟨(), (4, 2), 1⟩,   -- Tile 13: covers (3,2), (4,2), (4,3)
  ⟨(), (3, 4), 3⟩    -- Tile 14: covers (3,3), (3,4), (4,4)
]⟩

theorem tiling_5x9_valid : tiling_5x9.Valid (rectangle 5 9) := by decide

theorem tileable_5x9 : LTileable (rectangle 5 9) :=
  ⟨Fin 15, inferInstance, inferInstance, tiling_5x9, tiling_5x9_valid⟩

/- ## Deficient Rectangles (Three-Cornered) -/

/-- The top-right corner cell of an `n × m` rectangle (0-based coordinates). -/
def cornerTR (n m : ℕ) : Cell :=
  (Int.ofNat (n - 1), Int.ofNat (m - 1))

/-- The cell immediately to the left of the top-right corner of an `n × m`
rectangle (0-based coordinates).

In coordinates: `(n-2, m-1)`.  This is only meaningful when `n ≥ 2`. -/
def cornerTR2 (n m : ℕ) : Cell :=
  (Int.ofNat (n - 2), Int.ofNat (m - 1))

/-- A three-cornered `n × m` rectangle: `rectangle n m` with its top-right corner removed.

We implement this as `erase` of the top-right corner from the full rectangle, so
cardinality lemmas are immediate from `Finset.card_erase`. -/
def rectangleMinusCorner (n m : ℕ) : Region :=
  (rectangle n m).erase (cornerTR n m)

/-- A rectangle `n × m` with both the top-right corner and the square
immediately to its left removed. -/
def rectangleMinus2Corner (n m : ℕ) : Region :=
  ((rectangle n m).erase (cornerTR n m)).erase (cornerTR2 n m)

/-- A tiling of the 2×2 rectangle with its top-right corner removed. -/
def tiling_2x2_minus : TileSet LTrominoSet Unit :=
  mkTileSet LTrominoSet Unit (fun _ => mkPlacedTile () 0 0 0)

theorem tiling_2x2_minus_valid :
    tiling_2x2_minus.Valid (rectangleMinusCorner 2 2) := by
  decide

/-- The 2×2 rectangle with a missing top-right corner is L-tileable. -/
theorem tileable_2x2_minus : LTileable (rectangleMinusCorner 2 2) :=
  ⟨Unit, inferInstance, inferInstance, tiling_2x2_minus, tiling_2x2_minus_valid⟩

/-- Explicit tiling of the 5×2 rectangle with its top-right corner removed.

In 0-based `(x,y)` coordinates (with `0 ≤ x ≤ 4`, `0 ≤ y ≤ 1`, missing `(4,1)`), the three
L-trominoes are:

- `T₁ = {(0,0),(0,1),(1,0)}`
- `T₂ = {(2,0),(1,1),(2,1)}`
- `T₃ = {(3,0),(3,1),(4,0)}`
-/
def tiling_5x2_minus : TileSet LTrominoSet (Fin 3) := ⟨![
  ⟨(), (0, 0), 0⟩,  -- T₁ at the left
  ⟨(), (2, 1), 2⟩,  -- T₂ covering the remaining part of the 3×2 block
  ⟨(), (3, 0), 0⟩   -- T₃ to the right, under the missing corner
]⟩

theorem tiling_5x2_minus_valid :
    tiling_5x2_minus.Valid (rectangleMinusCorner 5 2) := by
  decide

/-- The 5×2 rectangle with a missing top-right corner is L-tileable. -/
theorem tileable_5x2_minus : LTileable (rectangleMinusCorner 5 2) :=
  ⟨Fin 3, inferInstance, inferInstance, tiling_5x2_minus, tiling_5x2_minus_valid⟩

/-- Explicit tiling of the 4×4 rectangle with its top-right corner removed.
This is the `2² × 2²` deficiency-1 square used in Ash–Golomb's Theorem 2. -/
def tiling_4x4_minus : TileSet LTrominoSet (Fin 5) := ⟨![
  ⟨(), (0, 0), 0⟩,  -- bottom-left quadrant
  ⟨(), (3, 0), 1⟩,  -- bottom-right quadrant
  ⟨(), (0, 3), 3⟩,  -- top-left quadrant
  ⟨(), (2, 2), 0⟩,  -- top-right quadrant (except the missing corner)
  ⟨(), (1, 1), 0⟩   -- central tromino
]⟩

theorem tiling_4x4_minus_valid :
    tiling_4x4_minus.Valid (rectangleMinusCorner 4 4) := by
  decide

/-- The 4×4 rectangle with a missing top-right corner is L-tileable. -/
theorem tileable_4x4_minus : LTileable (rectangleMinusCorner 4 4) :=
  ⟨Fin 5, inferInstance, inferInstance, tiling_4x4_minus, tiling_4x4_minus_valid⟩

/-- Explicit tiling of the 5×5 rectangle with its top-right corner removed.

We follow the Ash–Golomb decomposition:
- a 2×3 rectangle `A` at the bottom-left,
- a 3×2 rectangle `B` at the bottom-right,
- and four L-trominoes near the top boundary.

The eight tiles (0–7) are:
- tiles 0–1: a copy of `tiling_2x3` covering `A = {(x,y) | x ∈ {0,1}, y ∈ {0,1,2}}`,
- tiles 2–3: a tiling of `B = {(x,y) | x ∈ {2,3,4}, y ∈ {0,1}}`,
- tiles 4–7: the four L-trominoes:
  - `T₁ = {(0,3),(0,4),(1,4)}`,
  - `T₂ = {(1,3),(2,3),(2,2)}`,
  - `T₃ = {(2,4),(3,4),(3,3)}`,
  - `T₄ = {(3,2),(4,2),(4,3)}`.
-/
def tiling_5x5_minus : TileSet LTrominoSet (Fin 8) := ⟨![
  -- A: 2×3 rectangle at bottom-left (copy of tiling_2x3)
  ⟨(), (0, 0), 0⟩,
  ⟨(), (1, 2), 2⟩,
  -- B: 3×2 rectangle at bottom-right
  ⟨(), (2, 0), 0⟩,
  ⟨(), (4, 1), 2⟩,
  -- T₁: {(0,3),(0,4),(1,4)}
  ⟨(), (0, 4), 3⟩,
  -- T₂: {(1,3),(2,3),(2,2)}
  ⟨(), (2, 3), 2⟩,
  -- T₃: {(2,4),(3,4),(3,3)}
  ⟨(), (3, 4), 2⟩,
  -- T₄: {(3,2),(4,2),(4,3)}
  ⟨(), (4, 2), 1⟩
]⟩

theorem tiling_5x5_minus_valid :
    tiling_5x5_minus.Valid (rectangleMinusCorner 5 5) := by
  decide

/-- The 5×5 rectangle with a missing top-right corner is L-tileable. -/
theorem tileable_5x5_minus : LTileable (rectangleMinusCorner 5 5) :=
  ⟨Fin 8, inferInstance, inferInstance, tiling_5x5_minus, tiling_5x5_minus_valid⟩

/-- Explicit tiling of the 7×7 rectangle with its top-right corner removed.

We use the user-specified partition of `R(7,7)⁻` into 16 disjoint L-trominoes,
converted to 0-based coordinates.

In 0-based `(x,y)` coordinates (with `0 ≤ x,y ≤ 6`, missing `(6,6)`), the 16
L-trominoes are:
- `T₁  = {(0,0),(0,1),(1,1)}`
- `T₂  = {(1,0),(2,0),(2,1)}`
- `T₃  = {(0,2),(0,3),(1,3)}`
- `T₄  = {(1,2),(2,2),(2,3)}`
- `T₅  = {(0,4),(1,4),(1,5)}`
- `T₆  = {(0,5),(0,6),(1,6)}`
- `T₇  = {(2,6),(3,5),(3,6)}`
- `T₈  = {(2,4),(2,5),(3,4)}`
- `T₉  = {(3,0),(4,0),(4,1)}`
- `T₁₀ = {(3,1),(3,2),(4,2)}`
- `T₁₁ = {(3,3),(4,3),(4,4)}`
- `T₁₂ = {(4,5),(4,6),(5,6)}`
- `T₁₃ = {(5,0),(6,0),(6,1)}`
- `T₁₄ = {(5,1),(5,2),(6,2)}`
- `T₁₅ = {(5,3),(6,3),(6,4)}`
- `T₁₆ = {(5,4),(5,5),(6,5)}`.
-/
def tiling_7x7_minus : TileSet LTrominoSet (Fin 16) := ⟨![
  -- T₁
  ⟨(), (0, 1), 3⟩,
  -- T₂
  ⟨(), (2, 0), 1⟩,
  -- T₃
  ⟨(), (0, 3), 3⟩,
  -- T₄
  ⟨(), (2, 2), 1⟩,
  -- T₅
  ⟨(), (1, 4), 1⟩,
  -- T₆
  ⟨(), (0, 6), 3⟩,
  -- T₇
  ⟨(), (3, 6), 2⟩,
  -- T₈
  ⟨(), (2, 4), 0⟩,
  -- T₉
  ⟨(), (4, 0), 1⟩,
  -- T₁₀
  ⟨(), (3, 2), 3⟩,
  -- T₁₁
  ⟨(), (4, 3), 1⟩,
  -- T₁₂
  ⟨(), (4, 6), 3⟩,
  -- T₁₃
  ⟨(), (6, 0), 1⟩,
  -- T₁₄
  ⟨(), (5, 2), 3⟩,
  -- T₁₅
  ⟨(), (6, 3), 1⟩,
  -- T₁₆
  ⟨(), (5, 5), 3⟩
]⟩

theorem tiling_7x7_minus_valid :
    tiling_7x7_minus.Valid (rectangleMinusCorner 7 7) := by
  decide

/-- The 7×7 rectangle with a missing top-right corner is L-tileable. -/
theorem tileable_7x7_minus : LTileable (rectangleMinusCorner 7 7) :=
  ⟨Fin 16, inferInstance, inferInstance, tiling_7x7_minus, tiling_7x7_minus_valid⟩


def tiling_piece2_base : TileSet LTrominoSet (Fin 5) := ⟨![
  ⟨(), (0, 0), 0⟩,
  ⟨(), (1, 2), 1⟩,
  ⟨(), (2, 1), 1⟩,
  ⟨(), (3, 0), 1⟩,
  ⟨(), (3, 3), 2⟩
]⟩

theorem tiling_piece2_base_valid : tiling_piece2_base.Valid (rectangle 4 4 \ {(0, 3)}) := by decide

theorem tileable_piece2_base : LTileable (rectangle 4 4 \ {(0, 3)}) :=
  ⟨Fin 5, inferInstance, inferInstance, tiling_piece2_base, tiling_piece2_base_valid⟩
