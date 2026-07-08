import TilingPolyomino.Grid
import Mathlib.Tactic

/-!
# Polyominoes: adjacency, connectivity, vertices, alignment

The basic vocabulary of polyominoes as subsets of the integer grid:

* `CellAdj` — edge-adjacency of cells.
* `CellConnected` — connectivity through paths of edge-adjacent cells.
* `IsVertex` — the grid points where the boundary of a polyomino turns.
* `VertexAligned` — all vertices on the pitch-`f` grid `fℤ × fℤ`.

This file (like all of `Polyomino/`) is tiling-free: it imports only
`TilingPolyomino.Grid` and Mathlib.
-/

open Set

-- ============================================================
-- §1 Polyominoes: adjacency, connectivity, vertices, alignment
-- ============================================================

/-- Two cells are **edge-adjacent**: they share a unit edge. -/
def CellAdj (p q : Cell) : Prop :=
  (p.1 = q.1 ∧ (q.2 = p.2 + 1 ∨ p.2 = q.2 + 1)) ∨
  (p.2 = q.2 ∧ (q.1 = p.1 + 1 ∨ p.1 = q.1 + 1))

lemma CellAdj.symm {p q : Cell} (h : CellAdj p q) : CellAdj q p := by
  unfold CellAdj at h ⊢
  omega

/-- A set of cells is **connected** if any two of its cells are joined by a
    path of edge-adjacent cells staying in the set.  (Named `CellConnected`
    to avoid Mathlib's topological `IsConnected`.) -/
def CellConnected (P : Set Cell) : Prop :=
  ∀ ⦃p⦄, p ∈ P → ∀ ⦃q⦄, q ∈ P →
    Relation.ReflTransGen (fun a b => b ∈ P ∧ CellAdj a b) p q

/-- The grid point `v = (x, y)` — the lattice point at the lower-left corner
    of cell `(x, y)` — is a **vertex** of `P` if the boundary of `P` turns
    at `v`.  The four cells incident to `v` are
    SW `(x−1, y−1)`, SE `(x, y−1)`, NW `(x−1, y)`, NE `(x, y)`;
    `v` is a vertex iff the 2×2 membership pattern around `v` is constant
    neither row-wise (which would make the local boundary horizontal or
    empty) nor column-wise (vertical or empty).  Equivalently: exactly 1 or
    3 of the four incident cells lie in `P`, or exactly 2 that are
    diagonally opposite. -/
def IsVertex (P : Set Cell) (v : Cell) : Prop :=
  ¬(((v.1 - 1, v.2 - 1) ∈ P ↔ (v.1, v.2 - 1) ∈ P) ∧
    ((v.1 - 1, v.2) ∈ P ↔ (v.1, v.2) ∈ P)) ∧
  ¬(((v.1 - 1, v.2 - 1) ∈ P ↔ (v.1 - 1, v.2) ∈ P) ∧
    ((v.1, v.2 - 1) ∈ P ↔ (v.1, v.2) ∈ P))

/-- Sanity check for `IsVertex`: the vertices of a (nondegenerate) rectangle
    are exactly its four corners. -/
example (x0 y0 x1 y1 : ℤ) (hx : x0 < x1) (hy : y0 < y1) (v : Cell) :
    IsVertex (rect x0 y0 x1 y1) v ↔
      v = (x0, y0) ∨ v = (x1, y0) ∨ v = (x0, y1) ∨ v = (x1, y1) := by
  obtain ⟨x, y⟩ := v
  simp only [IsVertex, mem_rect, Prod.mk.injEq]
  omega

/-- `P` is **`f`-aligned**: every vertex of `P` lies on the pitch-`f` grid
    `fℤ × fℤ`.  This is the provisional stand-in for fatness: it forces all
    boundary features of `P` to be at distance ≥ `f` from each other. -/
def VertexAligned (f : ℤ) (P : Set Cell) : Prop :=
  ∀ v : Cell, IsVertex P v → f ∣ v.1 ∧ f ∣ v.2

/-- A finite set of cells fits in a box. -/
lemma exists_bound (P : Set Cell) (hfin : P.Finite) :
    ∃ B : ℤ, ∀ p ∈ P, p.1 < B ∧ p.2 < B ∧ -B < p.1 ∧ -B < p.2 := by
  obtain ⟨M₁, hM₁⟩ := (hfin.image Prod.fst).bddAbove
  obtain ⟨M₂, hM₂⟩ := (hfin.image Prod.snd).bddAbove
  obtain ⟨m₁, hm₁⟩ := (hfin.image Prod.fst).bddBelow
  obtain ⟨m₂, hm₂⟩ := (hfin.image Prod.snd).bddBelow
  refine ⟨|M₁| + |M₂| + |m₁| + |m₂| + 1, fun p hp => ?_⟩
  have h1 : p.1 ≤ M₁ := hM₁ (Set.mem_image_of_mem _ hp)
  have h2 : p.2 ≤ M₂ := hM₂ (Set.mem_image_of_mem _ hp)
  have h3 : m₁ ≤ p.1 := hm₁ (Set.mem_image_of_mem _ hp)
  have h4 : m₂ ≤ p.2 := hm₂ (Set.mem_image_of_mem _ hp)
  have := le_abs_self M₁
  have := le_abs_self M₂
  have := neg_abs_le m₁
  have := neg_abs_le m₂
  have := abs_nonneg M₁
  have := abs_nonneg M₂
  have := abs_nonneg m₁
  have := abs_nonneg m₂
  omega
