import TilingPolyomino.Polyomino.Basic

/-!
# Fat polyominoes

`Fat l P`: around every vertex `v` — throughout the square of `L∞`-radius
`l` centered at `v` — the polyomino coincides with a quarter plane cornered
at `v` (a *convex* corner) or with the complement of one (a *reflex*
corner).  This is the formal rendering of "every vertex is at `L∞`-distance
≥ `l` from every non-incident edge"; it rules out *diagonal* vertices.

Besides the definition, this file proves the local consequences used by the
boundary-walk and boundary-cycle theory: the pointwise membership criterion
(`Fat.mem_iff`), no diagonal vertices (`Fat.not_diagonal`), monotonicity of
membership along rows and columns of the box (`Fat.column_no_dip` …
`Fat.row_no_bump`), and isolation of vertices (`Fat.vertex_isolated`).
-/

open Set

-- ============================================================
-- §1 Fatness
-- ============================================================

/-- The quarter plane having the grid point `v` as its corner `c`:
    `quadrant v .BL` extends up and to the right of `v` (so `v` is its
    bottom-left corner), and so on. -/
def quadrant (v : Cell) : Corner → Set Cell
  | .BL => {p | v.1 ≤ p.1 ∧ v.2 ≤ p.2}
  | .BR => {p | p.1 < v.1 ∧ v.2 ≤ p.2}
  | .TL => {p | v.1 ≤ p.1 ∧ p.2 < v.2}
  | .TR => {p | p.1 < v.1 ∧ p.2 < v.2}

/-- The square of cells of `L∞`-radius `l` around the grid point `v`. -/
def box (v : Cell) (l : ℤ) : Set Cell :=
  rect (v.1 - l) (v.2 - l) (v.1 + l) (v.2 + l)

/-- `P` is **`l`-fat**: around every vertex `v` — throughout the square of
    `L∞`-radius `l` centered at `v` — the polyomino coincides with a
    quarter plane cornered at `v` (a *convex* corner of `P`) or with the
    complement of one (a *reflex* corner).

    This is the formal rendering of "every vertex is at `L∞`-distance
    ≥ `l` from every non-incident edge": if no foreign edge comes within
    `l` of `v`, the only boundary inside the square consists of the two
    edges incident to `v`, which run straight through it, so `P` is a
    quadrant there; conversely a quadrant's square contains no boundary
    besides the two incident edges.  Note this rules out *diagonal*
    vertices (two cells of `P` meeting diagonally at `v`): no quadrant has
    that 2×2 pattern at its corner. -/
def Fat (l : ℤ) (P : Set Cell) : Prop :=
  ∀ v : Cell, IsVertex P v →
    ∃ c : Corner,
      P ∩ box v l = quadrant v c ∩ box v l ∨
      P ∩ box v l = (quadrant v c)ᶜ ∩ box v l

/-- Fatness is monotone: an `l`-fat polyomino is `l'`-fat for `l' ≤ l`. -/
lemma Fat.mono {l l' : ℤ} {P : Set Cell} (h : Fat l P) (hle : l' ≤ l) :
    Fat l' P := by
  intro v hv
  obtain ⟨c, hc⟩ := h v hv
  have hsub : box v l' ⊆ box v l := by
    rintro ⟨x, y⟩ hp
    simp only [box, mem_rect] at hp ⊢
    omega
  have hBB : box v l ∩ box v l' = box v l' :=
    Set.inter_eq_self_of_subset_right hsub
  have key : ∀ Q : Set Cell, P ∩ box v l = Q ∩ box v l →
      P ∩ box v l' = Q ∩ box v l' := fun Q hQ =>
    calc P ∩ box v l' = (P ∩ box v l) ∩ box v l' := by
          rw [Set.inter_assoc, hBB]
      _ = (Q ∩ box v l) ∩ box v l' := by rw [hQ]
      _ = Q ∩ box v l' := by rw [Set.inter_assoc, hBB]
  exact ⟨c, hc.imp (key _) (key _)⟩

/-- Sanity check for `Fat`: a rectangle with both sides ≥ `l` is `l`-fat
    (all four corners are convex). -/
example (l n m : ℤ) (hl : 0 < l) (hn : l ≤ n) (hm : l ≤ m) :
    Fat l (rect 0 0 n m) := by
  rintro ⟨a, b⟩ hv
  simp only [IsVertex, mem_rect] at hv
  have hc : (a = 0 ∨ a = n) ∧ (b = 0 ∨ b = m) := by omega
  obtain ⟨rfl | rfl, rfl | rfl⟩ := hc
  · exact ⟨.BL, .inl (by
      ext ⟨x, y⟩
      simp only [box, quadrant, Set.mem_inter_iff, mem_rect, Set.mem_setOf_eq]
      omega)⟩
  · exact ⟨.TL, .inl (by
      ext ⟨x, y⟩
      simp only [box, quadrant, Set.mem_inter_iff, mem_rect, Set.mem_setOf_eq]
      omega)⟩
  · exact ⟨.BR, .inl (by
      ext ⟨x, y⟩
      simp only [box, quadrant, Set.mem_inter_iff, mem_rect, Set.mem_setOf_eq]
      omega)⟩
  · exact ⟨.TR, .inl (by
      ext ⟨x, y⟩
      simp only [box, quadrant, Set.mem_inter_iff, mem_rect, Set.mem_setOf_eq]
      omega)⟩


/-- Pointwise form of fatness: membership in the box around a vertex is
    decided by the quadrant. -/
lemma Fat.mem_iff {l : ℤ} {P : Set Cell} (hfat : Fat l P) {v : Cell}
    (hv : IsVertex P v) :
    ∃ c : Corner,
      (∀ p ∈ box v l, (p ∈ P ↔ p ∈ quadrant v c)) ∨
      (∀ p ∈ box v l, (p ∈ P ↔ p ∉ quadrant v c)) := by
  obtain ⟨c, hc | hc⟩ := hfat v hv
  · refine ⟨c, Or.inl fun p hp => ?_⟩
    have h := Set.ext_iff.mp hc p
    simp only [Set.mem_inter_iff, hp, and_true] at h
    exact h
  · refine ⟨c, Or.inr fun p hp => ?_⟩
    have h := Set.ext_iff.mp hc p
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, hp, and_true] at h
    exact h

/-- At a vertex of a fat polyomino the 2×2 pattern is never the diagonal
    one (two cells of `P` meeting diagonally): no quadrant looks like that
    at its corner. -/
lemma Fat.not_diagonal {l : ℤ} {P : Set Cell} (hl : 1 ≤ l) (hfat : Fat l P)
    {v : Cell} (hv : IsVertex P v) :
    ¬(((v.1 - 1, v.2 - 1) ∈ P ↔ (v.1, v.2) ∈ P) ∧
      ((v.1 - 1, v.2) ∈ P ↔ (v.1, v.2 - 1) ∈ P)) := by
  obtain ⟨a, b⟩ := v
  rintro ⟨hd1, hd2⟩
  obtain ⟨c, hc | hc⟩ := hfat.mem_iff hv
  · cases c with
    | BL =>
      have hNE : ((a, b) : Cell) ∈ P :=
        (hc (a, b) (by simp only [box, mem_rect]; omega)).mpr
          (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      have hSW := (hc (a - 1, b - 1) (by simp only [box, mem_rect]; omega)).mp
        (hd1.mpr hNE)
      simp only [quadrant, Set.mem_setOf_eq] at hSW
      omega
    | BR =>
      have hNW : ((a - 1, b) : Cell) ∈ P :=
        (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mpr
          (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      have hSE := (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mp
        (hd2.mp hNW)
      simp only [quadrant, Set.mem_setOf_eq] at hSE
      omega
    | TL =>
      have hSE : ((a, b - 1) : Cell) ∈ P :=
        (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mpr
          (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      have hNW := (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mp
        (hd2.mpr hSE)
      simp only [quadrant, Set.mem_setOf_eq] at hNW
      omega
    | TR =>
      have hSW : ((a - 1, b - 1) : Cell) ∈ P :=
        (hc (a - 1, b - 1) (by simp only [box, mem_rect]; omega)).mpr
          (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      have hNE := (hc (a, b) (by simp only [box, mem_rect]; omega)).mp
        (hd1.mp hSW)
      simp only [quadrant, Set.mem_setOf_eq] at hNE
      omega
  · cases c with
    | BL =>
      have hSW : ((a - 1, b - 1) : Cell) ∈ P :=
        (hc (a - 1, b - 1) (by simp only [box, mem_rect]; omega)).mpr
          (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      exact (hc (a, b) (by simp only [box, mem_rect]; omega)).mp (hd1.mp hSW)
        (by simp only [quadrant, Set.mem_setOf_eq]; omega)
    | BR =>
      have hSE : ((a, b - 1) : Cell) ∈ P :=
        (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mpr
          (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      exact (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mp (hd2.mpr hSE)
        (by simp only [quadrant, Set.mem_setOf_eq]; omega)
    | TL =>
      have hNW : ((a - 1, b) : Cell) ∈ P :=
        (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mpr
          (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      exact (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mp (hd2.mp hNW)
        (by simp only [quadrant, Set.mem_setOf_eq]; omega)
    | TR =>
      have hNE : ((a, b) : Cell) ∈ P :=
        (hc (a, b) (by simp only [box, mem_rect]; omega)).mpr
          (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      exact (hc (a - 1, b - 1) (by simp only [box, mem_rect]; omega)).mp
        (hd1.mpr hNE)
        (by simp only [quadrant, Set.mem_setOf_eq]; omega)



-- ------------------------------------------------------------
-- Monotonicity of the quadrant picture: inside the box around a
-- vertex, membership along any fixed column (or row) changes at most
-- once, so the patterns ∈,∉,∈ and ∉,∈,∉ are impossible.
-- ------------------------------------------------------------

/-- No column dips out of `P` and back inside the box of a vertex. -/
lemma Fat.column_no_dip {l : ℤ} {P : Set Cell} (hfat : Fat l P) {v : Cell}
    (hv : IsVertex P v) {x ya yb yc : ℤ}
    (hx1 : v.1 - l ≤ x) (hx2 : x < v.1 + l)
    (hy1 : v.2 - l ≤ ya) (hy2 : yc < v.2 + l)
    (hab : ya < yb) (hbc : yb < yc)
    (ha : (x, ya) ∈ P) (hb : (x, yb) ∉ P) (hc : (x, yc) ∈ P) : False := by
  obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff hv
  · have Ha := (hcc (x, ya) (by simp only [box, mem_rect]; omega)).mp ha
    have Hc := (hcc (x, yc) (by simp only [box, mem_rect]; omega)).mp hc
    have Hb : (x, yb) ∉ quadrant v c := fun hq =>
      hb ((hcc (x, yb) (by simp only [box, mem_rect]; omega)).mpr hq)
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at Ha Hb Hc <;> omega
  · have Ha : (x, ya) ∉ quadrant v c :=
      (hcc (x, ya) (by simp only [box, mem_rect]; omega)).mp ha
    have Hc : (x, yc) ∉ quadrant v c :=
      (hcc (x, yc) (by simp only [box, mem_rect]; omega)).mp hc
    have Hb : (x, yb) ∈ quadrant v c := by
      by_contra hq
      exact hb ((hcc (x, yb) (by simp only [box, mem_rect]; omega)).mpr hq)
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at Ha Hb Hc <;> omega

/-- No column bumps into `P` and back out inside the box of a vertex. -/
lemma Fat.column_no_bump {l : ℤ} {P : Set Cell} (hfat : Fat l P) {v : Cell}
    (hv : IsVertex P v) {x ya yb yc : ℤ}
    (hx1 : v.1 - l ≤ x) (hx2 : x < v.1 + l)
    (hy1 : v.2 - l ≤ ya) (hy2 : yc < v.2 + l)
    (hab : ya < yb) (hbc : yb < yc)
    (ha : (x, ya) ∉ P) (hb : (x, yb) ∈ P) (hc : (x, yc) ∉ P) : False := by
  obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff hv
  · have Hb := (hcc (x, yb) (by simp only [box, mem_rect]; omega)).mp hb
    have Ha : (x, ya) ∉ quadrant v c := fun hq =>
      ha ((hcc (x, ya) (by simp only [box, mem_rect]; omega)).mpr hq)
    have Hc : (x, yc) ∉ quadrant v c := fun hq =>
      hc ((hcc (x, yc) (by simp only [box, mem_rect]; omega)).mpr hq)
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at Ha Hb Hc <;> omega
  · have Hb : (x, yb) ∉ quadrant v c :=
      (hcc (x, yb) (by simp only [box, mem_rect]; omega)).mp hb
    have Ha : (x, ya) ∈ quadrant v c := by
      by_contra hq
      exact ha ((hcc (x, ya) (by simp only [box, mem_rect]; omega)).mpr hq)
    have Hc : (x, yc) ∈ quadrant v c := by
      by_contra hq
      exact hc ((hcc (x, yc) (by simp only [box, mem_rect]; omega)).mpr hq)
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at Ha Hb Hc <;> omega

/-- No row dips out of `P` and back inside the box of a vertex. -/
lemma Fat.row_no_dip {l : ℤ} {P : Set Cell} (hfat : Fat l P) {v : Cell}
    (hv : IsVertex P v) {y xa xb xc : ℤ}
    (hy1 : v.2 - l ≤ y) (hy2 : y < v.2 + l)
    (hx1 : v.1 - l ≤ xa) (hx2 : xc < v.1 + l)
    (hab : xa < xb) (hbc : xb < xc)
    (ha : (xa, y) ∈ P) (hb : (xb, y) ∉ P) (hc : (xc, y) ∈ P) : False := by
  obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff hv
  · have Ha := (hcc (xa, y) (by simp only [box, mem_rect]; omega)).mp ha
    have Hc := (hcc (xc, y) (by simp only [box, mem_rect]; omega)).mp hc
    have Hb : (xb, y) ∉ quadrant v c := fun hq =>
      hb ((hcc (xb, y) (by simp only [box, mem_rect]; omega)).mpr hq)
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at Ha Hb Hc <;> omega
  · have Ha : (xa, y) ∉ quadrant v c :=
      (hcc (xa, y) (by simp only [box, mem_rect]; omega)).mp ha
    have Hc : (xc, y) ∉ quadrant v c :=
      (hcc (xc, y) (by simp only [box, mem_rect]; omega)).mp hc
    have Hb : (xb, y) ∈ quadrant v c := by
      by_contra hq
      exact hb ((hcc (xb, y) (by simp only [box, mem_rect]; omega)).mpr hq)
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at Ha Hb Hc <;> omega

/-- No row bumps into `P` and back out inside the box of a vertex. -/
lemma Fat.row_no_bump {l : ℤ} {P : Set Cell} (hfat : Fat l P) {v : Cell}
    (hv : IsVertex P v) {y xa xb xc : ℤ}
    (hy1 : v.2 - l ≤ y) (hy2 : y < v.2 + l)
    (hx1 : v.1 - l ≤ xa) (hx2 : xc < v.1 + l)
    (hab : xa < xb) (hbc : xb < xc)
    (ha : (xa, y) ∉ P) (hb : (xb, y) ∈ P) (hc : (xc, y) ∉ P) : False := by
  obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff hv
  · have Hb := (hcc (xb, y) (by simp only [box, mem_rect]; omega)).mp hb
    have Ha : (xa, y) ∉ quadrant v c := fun hq =>
      ha ((hcc (xa, y) (by simp only [box, mem_rect]; omega)).mpr hq)
    have Hc : (xc, y) ∉ quadrant v c := fun hq =>
      hc ((hcc (xc, y) (by simp only [box, mem_rect]; omega)).mpr hq)
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at Ha Hb Hc <;> omega
  · have Hb : (xb, y) ∉ quadrant v c :=
      (hcc (xb, y) (by simp only [box, mem_rect]; omega)).mp hb
    have Ha : (xa, y) ∈ quadrant v c := by
      by_contra hq
      exact ha ((hcc (xa, y) (by simp only [box, mem_rect]; omega)).mpr hq)
    have Hc : (xc, y) ∈ quadrant v c := by
      by_contra hq
      exact hc ((hcc (xc, y) (by simp only [box, mem_rect]; omega)).mpr hq)
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at Ha Hb Hc <;> omega

/-- **Vertices are isolated**: inside the box of a vertex there is no
    other vertex — off the corner, the quadrant's 2×2 patterns are row- or
    column-constant. -/
lemma Fat.vertex_isolated {l : ℤ} {P : Set Cell} (hfat : Fat l P)
    {v v' : Cell} (hv : IsVertex P v) (hv' : IsVertex P v') (hne : v' ≠ v)
    (h1 : v.1 - l < v'.1) (h2 : v'.1 < v.1 + l)
    (h3 : v.2 - l < v'.2) (h4 : v'.2 < v.2 + l) : False := by
  obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff hv
  · by_cases hx : v'.1 = v.1
    · have hy : v'.2 ≠ v.2 := fun h => hne (Prod.ext hx h)
      have hQ : ∀ x' : ℤ,
          ((x', v'.2 - 1) ∈ quadrant v c ↔ (x', v'.2) ∈ quadrant v c) := by
        intro x'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      exact hv'.2
        ⟨((hcc (v'.1 - 1, v'.2 - 1) (by simp only [box, mem_rect]; omega)).trans
            (hQ (v'.1 - 1))).trans
            (hcc (v'.1 - 1, v'.2) (by simp only [box, mem_rect]; omega)).symm,
          ((hcc (v'.1, v'.2 - 1) (by simp only [box, mem_rect]; omega)).trans
            (hQ v'.1)).trans
            (hcc (v'.1, v'.2) (by simp only [box, mem_rect]; omega)).symm⟩
    · have hQ : ∀ y' : ℤ,
          ((v'.1 - 1, y') ∈ quadrant v c ↔ (v'.1, y') ∈ quadrant v c) := by
        intro y'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      exact hv'.1
        ⟨((hcc (v'.1 - 1, v'.2 - 1) (by simp only [box, mem_rect]; omega)).trans
            (hQ (v'.2 - 1))).trans
            (hcc (v'.1, v'.2 - 1) (by simp only [box, mem_rect]; omega)).symm,
          ((hcc (v'.1 - 1, v'.2) (by simp only [box, mem_rect]; omega)).trans
            (hQ v'.2)).trans
            (hcc (v'.1, v'.2) (by simp only [box, mem_rect]; omega)).symm⟩
  · by_cases hx : v'.1 = v.1
    · have hy : v'.2 ≠ v.2 := fun h => hne (Prod.ext hx h)
      have hQ : ∀ x' : ℤ,
          ((x', v'.2 - 1) ∈ quadrant v c ↔ (x', v'.2) ∈ quadrant v c) := by
        intro x'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      exact hv'.2
        ⟨((hcc (v'.1 - 1, v'.2 - 1) (by simp only [box, mem_rect]; omega)).trans
            (not_congr (hQ (v'.1 - 1)))).trans
            (hcc (v'.1 - 1, v'.2) (by simp only [box, mem_rect]; omega)).symm,
          ((hcc (v'.1, v'.2 - 1) (by simp only [box, mem_rect]; omega)).trans
            (not_congr (hQ v'.1))).trans
            (hcc (v'.1, v'.2) (by simp only [box, mem_rect]; omega)).symm⟩
    · have hQ : ∀ y' : ℤ,
          ((v'.1 - 1, y') ∈ quadrant v c ↔ (v'.1, y') ∈ quadrant v c) := by
        intro y'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      exact hv'.1
        ⟨((hcc (v'.1 - 1, v'.2 - 1) (by simp only [box, mem_rect]; omega)).trans
            (not_congr (hQ (v'.2 - 1)))).trans
            (hcc (v'.1, v'.2 - 1) (by simp only [box, mem_rect]; omega)).symm,
          ((hcc (v'.1 - 1, v'.2) (by simp only [box, mem_rect]; omega)).trans
            (not_congr (hQ v'.2))).trans
            (hcc (v'.1, v'.2) (by simp only [box, mem_rect]; omega)).symm⟩

