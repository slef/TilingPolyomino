import TilingPolyomino.Polyomino.Basic
import Mathlib.Data.Int.LeastGreatest

/-!
# The boundary of a polyomino: edges and the boundary walk

* `IsCutLine` — a vertical grid line carrying a vertex of `P`.
* The **boundary walk** (`isCutLine_of_horiz_discont`,
  `exists_vertex_row_of_vert_discont`): a membership discontinuity between
  two adjacent cells lies on a boundary edge of `P`; walking along that
  edge to its (finite) end produces a turn of the boundary, i.e. a vertex.
  This gives vertices — hence cut lines — wherever we need them.
-/

open Set

-- ============================================================
-- §1 Cut lines and the boundary walk
-- ============================================================

/-- `x` is a **cut line** of `P`: some vertex of `P` lies on the vertical
    grid line at abscissa `x`. -/
def IsCutLine (P : Set Cell) (x : ℤ) : Prop := ∃ y : ℤ, IsVertex P (x, y)

/-- **Boundary walk, vertical edge.**  If two horizontally adjacent cells
    disagree about membership in `P`, the grid line between them carries a
    vertex: walk up the vertical boundary edge separating the two columns;
    at the first height where the columns agree again, the boundary turns. -/
theorem isCutLine_of_horiz_discont (P : Set Cell) (hfin : P.Finite)
    {x y : ℤ} (h : ¬((x, y) ∈ P ↔ (x + 1, y) ∈ P)) :
    IsCutLine P (x + 1) := by
  classical
  obtain ⟨B, hB⟩ := exists_bound P hfin
  have hinh : ∃ t : ℤ, y < t ∧ ((x, t) ∈ P ↔ (x + 1, t) ∈ P) := by
    have hmax := le_max_right (y + 1) B
    refine ⟨max (y + 1) B, by omega, ?_⟩
    have h1 : (x, max (y + 1) B) ∉ P := fun hm => by
      have h1' : max (y + 1) B < B := (hB _ hm).2.1
      omega
    have h2 : (x + 1, max (y + 1) B) ∉ P := fun hm => by
      have h2' : max (y + 1) B < B := (hB _ hm).2.1
      omega
    simp [h1, h2]
  obtain ⟨t₁, ⟨ht₁y, ht₁⟩, hleast⟩ :=
    Int.exists_least_of_bdd
      (P := fun t => y < t ∧ ((x, t) ∈ P ↔ (x + 1, t) ∈ P))
      ⟨y + 1, fun _ hz => by omega⟩ hinh
  have hprev : ¬(((x, t₁ - 1) ∈ P) ↔ ((x + 1, t₁ - 1) ∈ P)) := by
    rcases eq_or_lt_of_le (by omega : y ≤ t₁ - 1) with heq | hlt
    · rw [← heq]; exact h
    · intro hiff
      exact absurd (hleast (t₁ - 1) ⟨hlt, hiff⟩) (by omega)
  refine ⟨t₁, ?_⟩
  have hxx : (x + 1 : ℤ) - 1 = x := by ring
  simp only [IsVertex, hxx]
  constructor
  · exact fun hc => hprev hc.1
  · intro hc
    exact hprev (hc.1.trans (ht₁.trans hc.2.symm))

/-- **Boundary walk, horizontal edge.**  If two vertically adjacent cells
    disagree about membership in `P`, the grid row between them carries a
    vertex: walk right along the horizontal boundary edge; at the first
    abscissa where the rows agree again, the boundary turns. -/
theorem exists_vertex_row_of_vert_discont (P : Set Cell) (hfin : P.Finite)
    {x y : ℤ} (h : ¬((x, y) ∈ P ↔ (x, y + 1) ∈ P)) :
    ∃ u : ℤ, IsVertex P (u, y + 1) := by
  classical
  obtain ⟨B, hB⟩ := exists_bound P hfin
  have hinh : ∃ u : ℤ, x < u ∧ ((u, y) ∈ P ↔ (u, y + 1) ∈ P) := by
    have hmax := le_max_right (x + 1) B
    refine ⟨max (x + 1) B, by omega, ?_⟩
    have h1 : (max (x + 1) B, y) ∉ P := fun hm => by
      have h1' : max (x + 1) B < B := (hB _ hm).1
      omega
    have h2 : (max (x + 1) B, y + 1) ∉ P := fun hm => by
      have h2' : max (x + 1) B < B := (hB _ hm).1
      omega
    simp [h1, h2]
  obtain ⟨u₁, ⟨hu₁x, hu₁⟩, hleast⟩ :=
    Int.exists_least_of_bdd
      (P := fun u => x < u ∧ ((u, y) ∈ P ↔ (u, y + 1) ∈ P))
      ⟨x + 1, fun _ hz => by omega⟩ hinh
  have hprev : ¬(((u₁ - 1, y) ∈ P) ↔ ((u₁ - 1, y + 1) ∈ P)) := by
    rcases eq_or_lt_of_le (by omega : x ≤ u₁ - 1) with heq | hlt
    · rw [← heq]; exact h
    · intro hiff
      exact absurd (hleast (u₁ - 1) ⟨hlt, hiff⟩) (by omega)
  refine ⟨u₁, ?_⟩
  have hyy : (y + 1 : ℤ) - 1 = y := by ring
  simp only [IsVertex, hyy]
  constructor
  · intro hc
    exact hprev (hc.1.trans (hu₁.trans hc.2.symm))
  · exact fun hc => hprev hc.1
