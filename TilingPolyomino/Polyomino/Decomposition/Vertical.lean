import TilingPolyomino.Polyomino.Boundary
import Mathlib.Data.Int.LeastGreatest

/-!
# Vertical decomposition of a polyomino

Cutting a finite polyomino `P` vertically through every vertex decomposes
it into rectangles (**pieces**, `VPiece`): each piece spans the strip
between two consecutive cut lines and a maximal vertical run of cells of
`P` within it.

* §1–§2 pieces are well-defined and pairwise disjoint;
* §3 every cell lies in a piece (`exists_vPiece_mem`), via the boundary
  walk of `Polyomino.Boundary`;
* §4 for an `f`-aligned polyomino all piece coordinates are multiples of
  `f`, so sides are ≥ `f`;
* §5 **doors** between horizontally adjacent pieces; the door graph is
  connected because `P` is (`vPiece_reachable`);
* §6 the decomposition packaged (`vDecomp_isDecomposition`,
  `vDecomp_finite`).
-/

open Set

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
