import TilingPolyomino.FatPolyomino
import Mathlib.Data.Int.LeastGreatest

/-!
# Vertical decomposition of a polyomino

First stage of the proof of `exists_cornerChain` (see `FatPolyomino.lean`):
cutting the polyomino `P` vertically through every vertex decomposes it into
rectangles (**pieces**, `VPiece`).  Plan (SL, 2026-07-05):

1. *(§1–§4, §6 — proved)* The **vertical decomposition**: the pieces are
   rectangles contained in `P`, pairwise disjoint, with union exactly `P`
   (`vDecomp_isDecomposition`), and there are finitely many
   (`vDecomp_finite`).  For an `f`-aligned polyomino all piece coordinates
   are multiples of `f`, so sides are ≥ `f` and for `f = 20` each piece is
   a `RectPiece` of the corner-chain layer (`VPiece.toRectPiece`).
2. *(§5 — proved)* **Doors** between horizontally adjacent pieces; the door
   graph is connected because `P` is (`vPiece_reachable`).
3. *(§7 — statement)* **Spanning tree** of the door graph (`PieceTree`,
   `exists_spanning_pieceTree`).
4. *(next)* Root the tree at a leaf; subdivide each piece by a vertical
   split line and horizontal cuts at door midpoints; walk the sub-pieces of
   each piece clockwise, recursing through each tree door — this produces
   the `IsCornerChain` demanded by `exists_cornerChain`.

The workhorse here is the **boundary walk** (`isCutLine_of_horiz_discont`,
`exists_vertex_row_of_vert_discont`): a membership discontinuity between two
adjacent cells lies on a boundary edge of `P`; walking along that edge to
its (finite) end produces a turn of the boundary, i.e. a vertex.  This gives
vertices — hence cut lines — wherever we need them.
-/

open Set

-- ============================================================
-- §1 Cut lines and the boundary walk
-- ============================================================

/-- `x` is a **cut line** of `P`: some vertex of `P` lies on the vertical
    grid line at abscissa `x`. -/
def IsCutLine (P : Set Cell) (x : ℤ) : Prop := ∃ y : ℤ, IsVertex P (x, y)

/-- A finite set of cells fits in a box. -/
private lemma exists_bound (P : Set Cell) (hfin : P.Finite) :
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

-- ============================================================
-- §2 VPieces: the pieces of the vertical decomposition
-- ============================================================

/-- One rectangle `[a, b) × [y0, y1)` of the vertical decomposition. -/
@[ext] structure VPiece where
  a : ℤ
  y0 : ℤ
  b : ℤ
  y1 : ℤ

namespace VPiece

/-- The cells of a piece. -/
def cells (s : VPiece) : Set Cell := rect s.a s.y0 s.b s.y1

/-- `s` is a **piece** of the vertical decomposition of `P`: it spans the strip
    between two *consecutive* cut lines, and a maximal vertical run of cells
    of `P` within that strip. -/
structure IsPieceOf (s : VPiece) (P : Set Cell) : Prop where
  lt_x : s.a < s.b
  lt_y : s.y0 < s.y1
  subset : s.cells ⊆ P
  cut_left : IsCutLine P s.a
  cut_right : IsCutLine P s.b
  no_cut : ∀ x, s.a < x → x < s.b → ¬IsCutLine P x
  floor : ∀ x, s.a ≤ x → x < s.b → (x, s.y0 - 1) ∉ P
  ceil : ∀ x, s.a ≤ x → x < s.b → (x, s.y1) ∉ P

/-- Two pieces of the decomposition sharing a cell are equal.  The strips
    agree because each strip runs between consecutive cut lines; the runs
    agree because both are vertically maximal in the same column. -/
theorem IsPieceOf.eq_of_mem {P : Set Cell} {s t : VPiece}
    (hs : s.IsPieceOf P) (ht : t.IsPieceOf P) {p : Cell}
    (hps : p ∈ s.cells) (hpt : p ∈ t.cells) : s = t := by
  obtain ⟨x, y⟩ := p
  simp only [cells, mem_rect] at hps hpt
  -- the strips coincide
  have ha : s.a = t.a := by
    rcases lt_trichotomy s.a t.a with hlt | heq | hgt
    · exact absurd ht.cut_left (hs.no_cut t.a hlt (by omega))
    · exact heq
    · exact absurd hs.cut_left (ht.no_cut s.a hgt (by omega))
  have hb : s.b = t.b := by
    rcases lt_trichotomy s.b t.b with hlt | heq | hgt
    · exact absurd hs.cut_right (ht.no_cut s.b (by omega) hlt)
    · exact heq
    · exact absurd ht.cut_right (hs.no_cut t.b (by omega) hgt)
  -- the runs coincide
  have hy0 : s.y0 = t.y0 := by
    rcases lt_trichotomy s.y0 t.y0 with hlt | heq | hgt
    · exact absurd (hs.subset (by simp only [cells, mem_rect]; omega :
        (x, t.y0 - 1) ∈ s.cells)) (ht.floor x (by omega) (by omega))
    · exact heq
    · exact absurd (ht.subset (by simp only [cells, mem_rect]; omega :
        (x, s.y0 - 1) ∈ t.cells)) (hs.floor x (by omega) (by omega))
  have hy1 : s.y1 = t.y1 := by
    rcases lt_trichotomy s.y1 t.y1 with hlt | heq | hgt
    · exact absurd (ht.subset (by simp only [cells, mem_rect]; omega :
        (x, s.y1) ∈ t.cells)) (hs.ceil x (by omega) (by omega))
    · exact heq
    · exact absurd (hs.subset (by simp only [cells, mem_rect]; omega :
        (x, t.y1) ∈ s.cells)) (ht.ceil x (by omega) (by omega))
  ext <;> assumption

/-- Distinct pieces of the decomposition are disjoint. -/
theorem IsPieceOf.disjoint {P : Set Cell} {s t : VPiece}
    (hs : s.IsPieceOf P) (ht : t.IsPieceOf P) (hne : s ≠ t) :
    Disjoint s.cells t.cells := by
  rw [Set.disjoint_left]
  intro p hps hpt
  exact hne (hs.eq_of_mem ht hps hpt)

end VPiece

-- ============================================================
-- §3 Cover: every cell lies in a piece
-- ============================================================

/-- Columns of `P` agree across a stretch containing no cut line: a
    disagreement between adjacent columns would put a vertex on the line
    between them (`isCutLine_of_horiz_discont`). -/
lemma mem_iff_of_no_cut (P : Set Cell) (hfin : P.Finite) {x x' : ℤ}
    (hle : x ≤ x') (hno : ∀ u, x < u → u ≤ x' → ¬IsCutLine P u) (y : ℤ) :
    ((x, y) ∈ P ↔ (x', y) ∈ P) := by
  revert hno
  induction x', hle using Int.le_induction with
  | base => exact fun _ => Iff.rfl
  | succ n hn ih =>
    intro hno
    have hstep : ((n, y) ∈ P ↔ (n + 1, y) ∈ P) := by
      by_contra hdis
      exact hno (n + 1) (by omega) (by omega)
        (isCutLine_of_horiz_discont P hfin hdis)
    exact (ih (fun u hu1 hu2 => hno u hu1 (by omega))).trans hstep

/-- The maximal vertical run of `P` through a cell. -/
private lemma exists_run (P : Set Cell) (hfin : P.Finite) {x y : ℤ}
    (hp : (x, y) ∈ P) :
    ∃ y0 y1 : ℤ, y0 ≤ y ∧ y < y1 ∧
      (∀ t, y0 ≤ t → t < y1 → (x, t) ∈ P) ∧
      (x, y0 - 1) ∉ P ∧ (x, y1) ∉ P := by
  classical
  obtain ⟨B, hB⟩ := exists_bound P hfin
  obtain ⟨y1, ⟨hy1gt, hy1notin⟩, hy1least⟩ :=
    Int.exists_least_of_bdd (P := fun t => y < t ∧ (x, t) ∉ P)
      ⟨y + 1, fun _ hz => by omega⟩
      ⟨max (y + 1) B, by
        have := le_max_right (y + 1) B
        refine ⟨by omega, fun hm => ?_⟩
        have h' : max (y + 1) B < B := (hB _ hm).2.1
        omega⟩
  obtain ⟨y0', ⟨hy0lt, hy0notin⟩, hy0greatest⟩ :=
    Int.exists_greatest_of_bdd (P := fun t => t < y ∧ (x, t) ∉ P)
      ⟨y - 1, fun _ hz => by omega⟩
      ⟨min (y - 1) (-B), by
        have := min_le_right (y - 1) (-B)
        refine ⟨by omega, fun hm => ?_⟩
        have h' : -B < min (y - 1) (-B) := (hB _ hm).2.2.2
        omega⟩
  refine ⟨y0' + 1, y1, by omega, by omega, ?_, ?_, hy1notin⟩
  · intro t ht0 ht1
    by_contra htn
    rcases lt_trichotomy t y with hlt | heq | hgt
    · exact absurd (hy0greatest t ⟨hlt, htn⟩) (by omega)
    · exact htn (heq ▸ hp)
    · exact absurd (hy1least t ⟨hgt, htn⟩) (by omega)
  · rw [show (y0' + 1 - 1 : ℤ) = y0' from by ring]
    exact hy0notin

/-- The strip around a cell: two consecutive cut lines bracketing it.  Their
    existence comes from walking the row through the cell to its two ends,
    where the boundary of `P` provides vertices. -/
private lemma exists_strip (P : Set Cell) (hfin : P.Finite) {x y : ℤ}
    (hp : (x, y) ∈ P) :
    ∃ a b : ℤ, a ≤ x ∧ x < b ∧ IsCutLine P a ∧ IsCutLine P b ∧
      ∀ u, a < u → u < b → ¬IsCutLine P u := by
  classical
  obtain ⟨B, hB⟩ := exists_bound P hfin
  -- a cut line at or left of `x`
  have hcutL : ∃ a₀ : ℤ, a₀ ≤ x ∧ IsCutLine P a₀ := by
    obtain ⟨a₀, ⟨ha₀le, ha₀run⟩, ha₀least⟩ :=
      Int.exists_least_of_bdd
        (P := fun u => u ≤ x ∧ ∀ t, u ≤ t → t ≤ x → (t, y) ∈ P)
        ⟨-B, fun z hz => by
          have h' : -B < z := (hB _ (hz.2 z le_rfl hz.1)).2.2.1
          omega⟩
        ⟨x, le_rfl, fun t h1 h2 => by
          have : t = x := le_antisymm h2 h1
          rwa [this]⟩
    have hnotpred : ¬(a₀ - 1 ≤ x ∧ ∀ t, a₀ - 1 ≤ t → t ≤ x → (t, y) ∈ P) := by
      intro hpred
      exact absurd (ha₀least _ hpred) (by omega)
    push_neg at hnotpred
    obtain ⟨t, ht1, ht2, htn⟩ := hnotpred (by omega)
    have ht : t = a₀ - 1 := by
      by_contra hne
      exact htn (ha₀run t (by omega) ht2)
    subst ht
    have hdis : ¬(((a₀ - 1, y) ∈ P) ↔ ((a₀ - 1 + 1, y) ∈ P)) := by
      rw [show (a₀ - 1 + 1 : ℤ) = a₀ from by ring]
      simp [htn, ha₀run a₀ le_rfl ha₀le]
    have hcut := isCutLine_of_horiz_discont P hfin hdis
    rw [show (a₀ - 1 + 1 : ℤ) = a₀ from by ring] at hcut
    exact ⟨a₀, ha₀le, hcut⟩
  -- a cut line strictly right of `x`
  have hcutR : ∃ b₀ : ℤ, x < b₀ ∧ IsCutLine P b₀ := by
    obtain ⟨b₀, ⟨hb₀ge, hb₀run⟩, hb₀greatest⟩ :=
      Int.exists_greatest_of_bdd
        (P := fun u => x ≤ u ∧ ∀ t, x ≤ t → t ≤ u → (t, y) ∈ P)
        ⟨B, fun z hz => by
          have h' : z < B := (hB _ (hz.2 z hz.1 le_rfl)).1
          omega⟩
        ⟨x, le_rfl, fun t h1 h2 => by
          have : t = x := le_antisymm h2 h1
          rwa [this]⟩
    have hnotsucc : ¬(x ≤ b₀ + 1 ∧ ∀ t, x ≤ t → t ≤ b₀ + 1 → (t, y) ∈ P) := by
      intro hsucc
      exact absurd (hb₀greatest _ hsucc) (by omega)
    push_neg at hnotsucc
    obtain ⟨t, ht1, ht2, htn⟩ := hnotsucc (by omega)
    have ht : t = b₀ + 1 := by
      by_contra hne
      exact htn (hb₀run t ht1 (by omega))
    subst ht
    have hdis : ¬(((b₀, y) ∈ P) ↔ ((b₀ + 1, y) ∈ P)) := by
      simp [htn, hb₀run b₀ hb₀ge le_rfl]
    exact ⟨b₀ + 1, by omega, isCutLine_of_horiz_discont P hfin hdis⟩
  obtain ⟨a₀, ha₀x, ha₀cut⟩ := hcutL
  obtain ⟨b₀, hb₀x, hb₀cut⟩ := hcutR
  obtain ⟨a, ⟨hacut, hax⟩, hagreatest⟩ :=
    Int.exists_greatest_of_bdd (P := fun u => IsCutLine P u ∧ u ≤ x)
      ⟨x, fun _ hz => hz.2⟩ ⟨a₀, ha₀cut, ha₀x⟩
  obtain ⟨b, ⟨hbcut, hbx⟩, hbleast⟩ :=
    Int.exists_least_of_bdd (P := fun u => IsCutLine P u ∧ x < u)
      ⟨x + 1, fun _ hz => by omega⟩ ⟨b₀, hb₀cut, hb₀x⟩
  refine ⟨a, b, hax, hbx, hacut, hbcut, fun u hu1 hu2 hcut => ?_⟩
  rcases (by omega : u ≤ x ∨ x < u) with h | h
  · exact absurd (hagreatest u ⟨hcut, h⟩) (by omega)
  · exact absurd (hbleast u ⟨hcut, h⟩) (by omega)

/-- **Cover.**  Every cell of a finite polyomino lies in a piece of the
    vertical decomposition. -/
theorem exists_vPiece_mem (P : Set Cell) (hfin : P.Finite) {p : Cell}
    (hp : p ∈ P) : ∃ s : VPiece, s.IsPieceOf P ∧ p ∈ s.cells := by
  obtain ⟨x, y⟩ := p
  obtain ⟨a, b, hax, hxb, hacut, hbcut, hno⟩ := exists_strip P hfin hp
  obtain ⟨y0, y1, hy0, hy1, hrun, hfloor, hceil⟩ := exists_run P hfin hp
  -- all columns of the strip agree with the column through `p`
  have htrans : ∀ x', a ≤ x' → x' < b → ∀ t, ((x', t) ∈ P ↔ (x, t) ∈ P) := by
    intro x' hax' hx'b t
    rcases (by omega : x' ≤ x ∨ x < x') with h | h
    · exact mem_iff_of_no_cut P hfin h
        (fun u hu1 hu2 => hno u (by omega) (by omega)) t
    · exact (mem_iff_of_no_cut P hfin (le_of_lt h)
        (fun u hu1 hu2 => hno u (by omega) (by omega)) t).symm
  refine ⟨⟨a, y0, b, y1⟩, ⟨?_, ?_, ?_, hacut, hbcut, hno, ?_, ?_⟩, ?_⟩
  · change a < b
    omega
  · change y0 < y1
    omega
  · rintro ⟨x', t⟩ hmem
    simp only [VPiece.cells, mem_rect] at hmem
    exact (htrans x' (by omega) (by omega) t).mpr (hrun t (by omega) (by omega))
  · intro x' h1 h2 hmem
    exact hfloor ((htrans x' h1 h2 _).mp hmem)
  · intro x' h1 h2 hmem
    exact hceil ((htrans x' h1 h2 _).mp hmem)
  · simp only [VPiece.cells, mem_rect]
    omega

-- ============================================================
-- §4 Alignment: piece coordinates of an aligned polyomino
-- ============================================================

namespace VPiece

/-- For an `f`-aligned polyomino, all four coordinates of every piece are
    multiples of `f`: the strip boundaries are cut lines, which carry
    vertices, and the run boundaries lie on horizontal boundary edges whose
    turning points are vertices at the same height. -/
theorem IsPieceOf.aligned {P : Set Cell} (hfin : P.Finite) {f : ℤ}
    (hal : VertexAligned f P) {s : VPiece} (hs : s.IsPieceOf P) :
    f ∣ s.a ∧ f ∣ s.y0 ∧ f ∣ s.b ∧ f ∣ s.y1 := by
  obtain ⟨ya, hva⟩ := hs.cut_left
  obtain ⟨yb, hvb⟩ := hs.cut_right
  have hx := hs.lt_x
  have hy := hs.lt_y
  refine ⟨(hal _ hva).1, ?_, (hal _ hvb).1, ?_⟩
  · -- bottom edge: membership flips between heights `y0 - 1` and `y0`
    have hin : (s.a, s.y0) ∈ P :=
      hs.subset (by simp only [cells, mem_rect]; omega)
    have hout : (s.a, s.y0 - 1) ∉ P := hs.floor s.a le_rfl hx
    obtain ⟨u, hv⟩ := exists_vertex_row_of_vert_discont P hfin
      (by simp [hin, hout] : ¬(((s.a, s.y0 - 1) ∈ P) ↔ ((s.a, s.y0 - 1 + 1) ∈ P)))
    have hdvd : f ∣ s.y0 - 1 + 1 := (hal _ hv).2
    rwa [show s.y0 - 1 + 1 = s.y0 from by ring] at hdvd
  · -- top edge: membership flips between heights `y1 - 1` and `y1`
    have hin : (s.a, s.y1 - 1) ∈ P :=
      hs.subset (by simp only [cells, mem_rect]; omega)
    have hout : (s.a, s.y1) ∉ P := hs.ceil s.a le_rfl hx
    obtain ⟨u, hv⟩ := exists_vertex_row_of_vert_discont P hfin
      (by simp [hin, hout] : ¬(((s.a, s.y1 - 1) ∈ P) ↔ ((s.a, s.y1 - 1 + 1) ∈ P)))
    have hdvd : f ∣ s.y1 - 1 + 1 := (hal _ hv).2
    rwa [show s.y1 - 1 + 1 = s.y1 from by ring] at hdvd

/-- VPieces of an `f`-aligned polyomino have both sides of length at least
    `f`. -/
theorem IsPieceOf.side_ge {P : Set Cell} (hfin : P.Finite) {f : ℤ}
    (hal : VertexAligned f P) {s : VPiece} (hs : s.IsPieceOf P) :
    s.a + f ≤ s.b ∧ s.y0 + f ≤ s.y1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hs.aligned hfin hal
  have hab : f ≤ s.b - s.a :=
    Int.le_of_dvd (by have := hs.lt_x; omega) (dvd_sub h3 h1)
  have hy : f ≤ s.y1 - s.y0 :=
    Int.le_of_dvd (by have := hs.lt_y; omega) (dvd_sub h4 h2)
  omega

end VPiece

-- ============================================================
-- §5 Doors and the adjacency graph
-- ============================================================

/-- A **door** joins piece `s` to a piece `t` on its right: they share the
    vertical line `x = s.b = t.a` along a nonempty interval of heights
    (their runs overlap).  Two given pieces share at most one door. -/
def DoorBetween (s t : VPiece) : Prop :=
  s.b = t.a ∧ max s.y0 t.y0 < min s.y1 t.y1

/-- Two pieces are **adjacent** when a door joins them, either way. -/
def VPiece.Adj (s t : VPiece) : Prop := DoorBetween s t ∨ DoorBetween t s

lemma VPiece.Adj.symm {s t : VPiece} (h : s.Adj t) : t.Adj s :=
  h.elim Or.inr Or.inl

/-- A cell of `P` adjacent to a cell of a piece lies in the same piece or
    in an adjacent one: vertical neighbours share the (maximal) run, and a
    horizontal neighbour outside the strip is seen through a door. -/
theorem VPiece.IsPieceOf.eq_or_adj_of_cellAdj {P : Set Cell} {u : VPiece}
    (hu : u.IsPieceOf P) {b c : Cell} (hb : b ∈ u.cells) (hcP : c ∈ P)
    (hadj : CellAdj b c) {t : VPiece} (ht : t.IsPieceOf P) (hct : c ∈ t.cells) :
    u = t ∨ u.Adj t := by
  by_cases hcu : c ∈ u.cells
  · exact Or.inl (hu.eq_of_mem ht hcu hct)
  right
  obtain ⟨b1, b2⟩ := b
  obtain ⟨c1, c2⟩ := c
  simp only [VPiece.cells, mem_rect] at hb hcu hct
  rcases hadj with ⟨heq, hor⟩ | ⟨heq, hor⟩
  · -- vertically adjacent cells always share the piece (runs are maximal)
    exfalso
    rcases hor with h | h
    · have hc2 : c2 = u.y1 := by omega
      exact hu.ceil c1 (by omega) (by omega) (by rwa [hc2] at hcP)
    · have hc2 : c2 = u.y0 - 1 := by omega
      exact hu.floor c1 (by omega) (by omega) (by rwa [hc2] at hcP)
  · rcases hor with h | h
    · -- `c` is just right of the strip: door from `u` to `t`
      left
      have hta : t.a = u.b := by
        rcases lt_trichotomy t.a u.b with hlt | heqq | hgt
        · exact absurd hu.cut_right (ht.no_cut u.b hlt (by omega))
        · exact heqq
        · omega
      exact ⟨hta.symm, by omega⟩
    · -- `c` is just left of the strip: door from `t` to `u`
      right
      have htb : t.b = u.a := by
        rcases lt_trichotomy t.b u.a with hlt | heqq | hgt
        · omega
        · exact heqq
        · exact absurd hu.cut_left (ht.no_cut u.a (by omega) hgt)
      exact ⟨htb, by omega⟩

private lemma mem_of_path {P : Set Cell} {p q : Cell} (hp : p ∈ P)
    (h : Relation.ReflTransGen (fun a b => b ∈ P ∧ CellAdj a b) p q) :
    q ∈ P := by
  induction h with
  | refl => exact hp
  | tail _ hbc _ => exact hbc.1

/-- **Connectivity of the door graph.**  Any two pieces of a finite connected
    polyomino are joined by a path of doors: follow a cell path between
    them and record the piece changes, which happen only at doors. -/
theorem vPiece_reachable (P : Set Cell) (hfin : P.Finite)
    (hconn : CellConnected P) {s t : VPiece}
    (hs : s.IsPieceOf P) (ht : t.IsPieceOf P) :
    Relation.ReflTransGen
      (fun u v : VPiece => u.IsPieceOf P ∧ v.IsPieceOf P ∧ u.Adj v) s t := by
  have hx := hs.lt_x
  have hy := hs.lt_y
  have hp : (s.a, s.y0) ∈ s.cells := by simp only [VPiece.cells, mem_rect]; omega
  have hqt : (t.a, t.y0) ∈ t.cells := by
    have := ht.lt_x
    have := ht.lt_y
    simp only [VPiece.cells, mem_rect]
    omega
  have hpP : (s.a, s.y0) ∈ P := hs.subset hp
  have hqP : (t.a, t.y0) ∈ P := ht.subset hqt
  have hpath := hconn hpP hqP
  suffices H : ∀ q, Relation.ReflTransGen (fun a b => b ∈ P ∧ CellAdj a b)
      (s.a, s.y0) q →
      ∀ t' : VPiece, t'.IsPieceOf P → q ∈ t'.cells →
      Relation.ReflTransGen
        (fun u v : VPiece => u.IsPieceOf P ∧ v.IsPieceOf P ∧ u.Adj v) s t' by
    exact H _ hpath t ht hqt
  intro q hq
  induction hq with
  | refl =>
    intro t' ht' hqt'
    rw [hs.eq_of_mem ht' hp hqt']
  | @tail b c hpb hbc ih =>
    intro t' ht' hct'
    have hbP : b ∈ P := mem_of_path hpP hpb
    obtain ⟨u, hu, hbu⟩ := exists_vPiece_mem P hfin hbP
    have hreach := ih u hu hbu
    rcases hu.eq_or_adj_of_cellAdj hbu hbc.1 hbc.2 ht' hct' with heq | hadj
    · rwa [heq] at hreach
    · exact hreach.tail ⟨hu, ht', hadj⟩

-- ============================================================
-- §6 The decomposition, packaged
-- ============================================================

/-- **The vertical decomposition** of `P`: the set of all its pieces. -/
def vDecomp (P : Set Cell) : Set VPiece := {s | s.IsPieceOf P}

@[simp] lemma mem_vDecomp {P : Set Cell} {s : VPiece} :
    s ∈ vDecomp P ↔ s.IsPieceOf P := Iff.rfl

/-- **The vertical decomposition theorem.**  The pieces of the decomposition
    are rectangles contained in `P`, pairwise disjoint, and their union is
    exactly `P`. -/
theorem vDecomp_isDecomposition (P : Set Cell) (hfin : P.Finite) :
    (∀ s ∈ vDecomp P, s.cells ⊆ P) ∧
    (vDecomp P).Pairwise (fun s t => Disjoint s.cells t.cells) ∧
    (⋃ s ∈ vDecomp P, s.cells) = P := by
  refine ⟨fun s hs => hs.subset, fun s hs t ht hne => hs.disjoint ht hne, ?_⟩
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun s hs => hs.subset
  · intro p hp
    obtain ⟨s, hs, hps⟩ := exists_vPiece_mem P hfin hp
    exact Set.mem_biUnion hs hps

/-- A finite polyomino has finitely many pieces (each piece is determined by
    its bottom-left cell, which lies in `P`). -/
theorem vDecomp_finite (P : Set Cell) (hfin : P.Finite) :
    (vDecomp P).Finite := by
  have hmem : ∀ s ∈ vDecomp P, (s.a, s.y0) ∈ s.cells := by
    intro s hs
    have h1 := hs.lt_x
    have h2 := hs.lt_y
    simp only [VPiece.cells, mem_rect]
    omega
  apply Set.Finite.of_finite_image (f := fun s : VPiece => (s.a, s.y0))
  · exact hfin.subset (by
      rintro q ⟨s, hs, rfl⟩
      exact hs.subset (hmem s hs))
  · intro s hs t ht heq
    have heq' : (s.a, s.y0) = (t.a, t.y0) := heq
    exact VPiece.IsPieceOf.eq_of_mem hs ht (hmem s hs)
      (by rw [heq']; exact hmem t ht)

/-- For a `20`-aligned polyomino, a piece of the vertical decomposition
    qualifies as a `RectPiece` of the corner-chain layer: its sides are
    ≥ 20 ≥ 6. -/
def VPiece.toRectPiece (s : VPiece) {P : Set Cell} (hfin : P.Finite)
    (hal : VertexAligned 20 P) (hs : s.IsPieceOf P) : RectPiece where
  x0 := s.a
  y0 := s.y0
  x1 := s.b
  y1 := s.y1
  wide := by have := hs.side_ge hfin hal; omega
  tall := by have := hs.side_ge hfin hal; omega

@[simp] lemma VPiece.toRectPiece_cells (s : VPiece) {P : Set Cell}
    (hfin : P.Finite) (hal : VertexAligned 20 P) (hs : s.IsPieceOf P) :
    (s.toRectPiece hfin hal hs).cells = s.cells := rfl

-- ============================================================
-- §7 Spanning trees of the door graph
-- ============================================================

/-- A rooted tree of decomposition pieces — the combinatorial object
    produced by choosing a spanning tree of the door graph and a root.
    The Euler tour of the corner-chain construction will recurse on it. -/
inductive PieceTree where
  | node (piece : VPiece) (children : List PieceTree)

namespace PieceTree

/-- The root piece. -/
def root : PieceTree → VPiece
  | node s _ => s

@[simp] lemma root_node (s : VPiece) (children : List PieceTree) :
    (node s children).root = s := rfl

mutual
  /-- All pieces of the tree, in preorder. -/
  def pieces : PieceTree → List VPiece
    | node s children => s :: piecesList children

  /-- All pieces of a forest, in preorder. -/
  def piecesList : List PieceTree → List VPiece
    | [] => []
    | c :: cs => c.pieces ++ piecesList cs
end

@[simp] lemma pieces_node (s : VPiece) (children : List PieceTree) :
    (node s children).pieces = s :: piecesList children := rfl

@[simp] lemma piecesList_nil : piecesList [] = [] := rfl

@[simp] lemma piecesList_cons (c : PieceTree) (cs : List PieceTree) :
    piecesList (c :: cs) = c.pieces ++ piecesList cs := rfl

mutual
  /-- Well-formedness over `P`: every node is a piece of the decomposition
      of `P`, and each child's root shares a door with its parent. -/
  def WF (P : Set Cell) : PieceTree → Prop
    | node s children => s.IsPieceOf P ∧ WFChildren P s children

  /-- The children of a node with piece `parent` are well-formed and hang
      off doors of `parent`. -/
  def WFChildren (P : Set Cell) (parent : VPiece) : List PieceTree → Prop
    | [] => True
    | c :: cs => parent.Adj c.root ∧ c.WF P ∧ WFChildren P parent cs
end

@[simp] lemma wf_node {P : Set Cell} (s : VPiece) (children : List PieceTree) :
    (node s children).WF P ↔ s.IsPieceOf P ∧ WFChildren P s children :=
  Iff.rfl

@[simp] lemma wfChildren_nil {P : Set Cell} (parent : VPiece) :
    WFChildren P parent [] := trivial

@[simp] lemma wfChildren_cons {P : Set Cell} (parent : VPiece)
    (c : PieceTree) (cs : List PieceTree) :
    WFChildren P parent (c :: cs) ↔
      parent.Adj c.root ∧ c.WF P ∧ WFChildren P parent cs :=
  Iff.rfl

/-- `T` is a **spanning tree** of the vertical decomposition of `P`: it is
    well-formed and its nodes are exactly the pieces, each occurring once. -/
structure IsSpanningTree (T : PieceTree) (P : Set Cell) : Prop where
  wf : T.WF P
  nodup : T.pieces.Nodup
  complete : ∀ s : VPiece, s.IsPieceOf P → s ∈ T.pieces

end PieceTree

/-- Reachability inside a set `S` of pieces, moving only through doors. -/
private def ReachIn (S : Set VPiece) : VPiece → VPiece → Prop :=
  Relation.ReflTransGen fun u v => u ∈ S ∧ v ∈ S ∧ u.Adj v

private lemma reachIn_mem {S : Set VPiece} {u v : VPiece} (hu : u ∈ S)
    (h : ReachIn S u v) : v ∈ S := by
  induction h with
  | refl => exact hu
  | tail _ hstep _ => exact hstep.2.1

private lemma reachIn_symm {S : Set VPiece} {u v : VPiece}
    (h : ReachIn S u v) : ReachIn S v u := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.head ⟨hstep.2.1, hstep.1, hstep.2.2.symm⟩ ih

/-- A door path in `S` starting at `u` is in fact a path *within* the
    door-component of `u` in `S`. -/
private lemma reachIn_component {S : Set VPiece} {u b : VPiece}
    (h : ReachIn S u b) :
    ReachIn {v | v ∈ S ∧ ReachIn S u v} u b := by
  induction h with
  | refl => exact .refl
  | @tail b' c hpath hstep ih =>
    exact ih.tail ⟨⟨hstep.1, hpath⟩, ⟨hstep.2.1, hpath.tail hstep⟩, hstep.2.2⟩

/-- Walking to `r` from elsewhere, one can stop just before `r`: some piece
    avoiding `r` throughout is reachable and door-adjacent to `r`. -/
private lemma exists_attach {S : Set VPiece} {u r : VPiece}
    (h : ReachIn S u r) :
    u ≠ r → ∃ w, ReachIn (S \ {r}) u w ∧ w.Adj r := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun h => absurd rfl h
  | @head a c hstep hrest ih =>
    intro hne
    by_cases hcr : c = r
    · subst hcr
      exact ⟨a, .refl, hstep.2.2⟩
    · obtain ⟨w, hw1, hw2⟩ := ih hcr
      exact ⟨w, Relation.ReflTransGen.head
        ⟨⟨hstep.1, by simpa using hne⟩, ⟨hstep.2.1, by simpa using hcr⟩,
          hstep.2.2⟩ hw1, hw2⟩

/-- Children construction: split a set `U` of pieces — closed under
    door-reachability in `S'` and with every piece linked to `r` through a
    door — into components, and build one subtree per component, each
    hanging off a door of `r`. -/
private theorem exists_children_aux (P : Set Cell) (r : VPiece)
    (S' : Set VPiece) (hS'fin : S'.Finite)
    (IH : ∀ C : Set VPiece, C ⊆ S' →
      (∀ a ∈ C, ∀ b ∈ C, ReachIn C a b) →
      ∀ w ∈ C, ∃ T : PieceTree, T.root = w ∧ T.WF P ∧ T.pieces.Nodup ∧
        ∀ s : VPiece, s ∈ T.pieces ↔ s ∈ C) :
    ∀ m : ℕ, ∀ U : Set VPiece, U ⊆ S' → U.ncard ≤ m →
      (∀ u ∈ U, ∀ v, ReachIn S' u v → v ∈ U) →
      (∀ u ∈ U, ∃ w, ReachIn S' u w ∧ w.Adj r) →
      ∃ L : List PieceTree, PieceTree.WFChildren P r L ∧
        (PieceTree.piecesList L).Nodup ∧
        ∀ s : VPiece, s ∈ PieceTree.piecesList L ↔ s ∈ U := by
  intro m
  induction m with
  | zero =>
    intro U hUsub hUcard _ _
    have hUfin : U.Finite := hS'fin.subset hUsub
    obtain rfl : U = ∅ := (Set.ncard_eq_zero hUfin).mp (by omega)
    exact ⟨[], PieceTree.wfChildren_nil r, List.nodup_nil, by simp⟩
  | succ m IHm =>
    intro U hUsub hUcard hUclosed hUattach
    rcases U.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · exact ⟨[], PieceTree.wfChildren_nil r, List.nodup_nil, by simp⟩
    have hUfin : U.Finite := hS'fin.subset hUsub
    have huS' : u ∈ S' := hUsub hu
    -- the component of `u`, and its attach point next to `r`
    set C := {v | v ∈ S' ∧ ReachIn S' u v} with hCdef
    have huC : u ∈ C := ⟨huS', .refl⟩
    have hCsub : C ⊆ S' := fun v hv => hv.1
    have hCU : C ⊆ U := fun v hv => hUclosed u hu v hv.2
    have hCconn : ∀ a ∈ C, ∀ b ∈ C, ReachIn C a b := fun a ha b hb =>
      (reachIn_symm (reachIn_component ha.2)).trans (reachIn_component hb.2)
    obtain ⟨w, hw_reach, hw_adj⟩ := hUattach u hu
    have hwC : w ∈ C := ⟨reachIn_mem huS' hw_reach, hw_reach⟩
    obtain ⟨T, hTroot, hTwf, hTnodup, hTmem⟩ := IH C hCsub hCconn w hwC
    -- recurse on what is left of `U`
    have hU'sub : U \ C ⊆ S' := fun v hv => hUsub hv.1
    have hU'card : (U \ C).ncard ≤ m := by
      have h1 : U \ C ⊆ U \ {u} :=
        Set.diff_subset_diff_right (Set.singleton_subset_iff.mpr huC)
      have h2 : (U \ C).ncard ≤ (U \ {u}).ncard :=
        Set.ncard_le_ncard h1 hUfin.diff
      have h3 : (U \ {u}).ncard = U.ncard - 1 :=
        Set.ncard_diff_singleton_of_mem hu
      have h4 : 0 < U.ncard := (Set.ncard_pos hUfin).mpr ⟨u, hu⟩
      omega
    have hU'closed : ∀ a ∈ U \ C, ∀ v, ReachIn S' a v → v ∈ U \ C := by
      rintro a ⟨haU, haC⟩ v hav
      refine ⟨hUclosed a haU v hav, fun hvC => haC ?_⟩
      exact ⟨hUsub haU, hvC.2.trans (reachIn_symm hav)⟩
    have hU'attach : ∀ a ∈ U \ C, ∃ w', ReachIn S' a w' ∧ w'.Adj r :=
      fun a ha => hUattach a ha.1
    obtain ⟨L', hL'wf, hL'nodup, hL'mem⟩ :=
      IHm (U \ C) hU'sub hU'card hU'closed hU'attach
    refine ⟨T :: L', ⟨by rw [hTroot]; exact hw_adj.symm, hTwf, hL'wf⟩, ?_, ?_⟩
    · simp only [PieceTree.piecesList_cons]
      exact hTnodup.append hL'nodup fun s hsT hsL' =>
        ((hL'mem s).mp hsL').2 ((hTmem s).mp hsT)
    · intro s
      simp only [PieceTree.piecesList_cons, List.mem_append, hTmem, hL'mem]
      constructor
      · rintro (h | h)
        · exact hCU h
        · exact h.1
      · intro hs
        by_cases hsC : s ∈ C
        · exact Or.inl hsC
        · exact Or.inr ⟨hs, hsC⟩

/-- Any internally door-connected finite set of decomposition pieces
    carries a spanning tree with prescribed root: remove the root, split
    the rest into components, attach each component at a piece adjacent to
    the root. -/
private theorem exists_rooted_tree_aux (P : Set Cell) :
    ∀ n : ℕ, ∀ S : Set VPiece, S.Finite → S.ncard ≤ n →
      (∀ s ∈ S, s.IsPieceOf P) →
      (∀ a ∈ S, ∀ b ∈ S, ReachIn S a b) →
      ∀ r ∈ S,
      ∃ T : PieceTree, T.root = r ∧ T.WF P ∧ T.pieces.Nodup ∧
        ∀ s : VPiece, s ∈ T.pieces ↔ s ∈ S := by
  intro n
  induction n with
  | zero =>
    intro S hSfin hScard _ _ r hr
    obtain rfl : S = ∅ := (Set.ncard_eq_zero hSfin).mp (by omega)
    simp at hr
  | succ n IHn =>
    intro S hSfin hScard hSpieces hSconn r hr
    have hS'fin : (S \ {r}).Finite := hSfin.diff
    have hS'card : (S \ {r}).ncard ≤ n := by
      have h3 : (S \ {r}).ncard = S.ncard - 1 :=
        Set.ncard_diff_singleton_of_mem hr
      have h4 : 0 < S.ncard := (Set.ncard_pos hSfin).mpr ⟨r, hr⟩
      omega
    have IH : ∀ C : Set VPiece, C ⊆ S \ {r} →
        (∀ a ∈ C, ∀ b ∈ C, ReachIn C a b) →
        ∀ w ∈ C, ∃ T : PieceTree, T.root = w ∧ T.WF P ∧ T.pieces.Nodup ∧
          ∀ s : VPiece, s ∈ T.pieces ↔ s ∈ C := by
      intro C hCsub hCconn w hw
      refine IHn C (hS'fin.subset hCsub) ?_
        (fun s hs => hSpieces s (hCsub hs).1) hCconn w hw
      calc C.ncard ≤ (S \ {r}).ncard := Set.ncard_le_ncard hCsub hS'fin
        _ ≤ n := hS'card
    have hclosed : ∀ u ∈ S \ {r}, ∀ v, ReachIn (S \ {r}) u v → v ∈ S \ {r} :=
      fun u hu v hv => reachIn_mem hu hv
    have hattach : ∀ u ∈ S \ {r}, ∃ w, ReachIn (S \ {r}) u w ∧ w.Adj r := by
      rintro u ⟨huS, hur⟩
      exact exists_attach (hSconn u huS r hr) (by simpa using hur)
    obtain ⟨L, hLwf, hLnodup, hLmem⟩ :=
      exists_children_aux P r (S \ {r}) hS'fin IH
        (S \ {r}).ncard (S \ {r}) subset_rfl le_rfl hclosed hattach
    refine ⟨.node r L, rfl, ⟨hSpieces r hr, hLwf⟩, ?_, ?_⟩
    · rw [PieceTree.pieces_node, List.nodup_cons]
      exact ⟨fun h => ((hLmem r).mp h).2 rfl, hLnodup⟩
    · intro s
      rw [PieceTree.pieces_node, List.mem_cons, hLmem s]
      constructor
      · rintro (rfl | h)
        · exact hr
        · exact h.1
      · intro hs
        by_cases hsr : s = r
        · exact Or.inl hsr
        · exact Or.inr ⟨hs, by simpa using hsr⟩

/-- **Spanning-tree existence.**  The door graph of a nonempty finite
    connected polyomino carries a spanning tree: pick any root, split the
    remaining pieces into door-components, attach each component at a piece
    adjacent to the root, and recurse. -/
theorem exists_spanning_pieceTree (P : Set Cell) (hfin : P.Finite)
    (hne : P.Nonempty) (hconn : CellConnected P) :
    ∃ T : PieceTree, T.IsSpanningTree P := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨r, hr, -⟩ := exists_vPiece_mem P hfin hp
  have hconn' : ∀ a ∈ vDecomp P, ∀ b ∈ vDecomp P, ReachIn (vDecomp P) a b :=
    fun a ha b hb => vPiece_reachable P hfin hconn ha hb
  obtain ⟨T, -, hwf, hnodup, hmem⟩ :=
    exists_rooted_tree_aux P (vDecomp P).ncard (vDecomp P)
      (vDecomp_finite P hfin) le_rfl (fun _ hs => hs) hconn' r hr
  exact ⟨T, hwf, hnodup, fun s hs => (hmem s).mpr hs⟩
