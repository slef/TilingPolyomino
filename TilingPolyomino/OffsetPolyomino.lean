import TilingPolyomino.AlignedPolyomino
import TilingPolyomino.EulerTour
import Mathlib.Tactic

/-!
# Fat polyominoes are L-tileable (via the inward offset)

Target (SL, 2026-07-07): **every fat, connected, simply connected
polyomino whose area is a multiple of 3 is L-tileable**, where *`l`-fat*
means every vertex of the boundary is at `L∞`-distance ≥ `l` from every
non-incident boundary edge — a purely *local* condition, unlike the global
grid alignment of `LTileable_of_vertexAligned`.

## Proof sketch (SL)

1. **Offset.**  Push every edge of `P` inwards by at least 6 and then
   further until it snaps onto the 3×2 grid.  Formally `offsetCore P` is
   the union of the complete 3×2 grid cells whose 6-neighbourhood
   (`offBox`) lies inside `P`.  The offset polyomino automatically has all
   its vertices on the 3×2 grid — for *any* `P` — so it is L-tileable by
   `LTileable_of_vertexOnGrid3x2`, with no connectivity or area
   hypothesis.
2. **Corridor.**  `corridor P = P \ offsetCore P` is the moat between the
   boundary of `P` and the offset polyomino, of thickness 6–8.  Its area
   is `≡ |P| (mod 3)` because the offset area is a multiple of 6.
3. **Corridor chain.**  Decompose the corridor into one rectangle per
   boundary edge of `P`, following the boundary cycle (single, since `P`
   is connected and has no holes): walking the cycle, at each convex
   vertex `uᵢ` of `P` cut forward from the offset vertex `vᵢ` to the
   boundary of `P`, at each reflex vertex cut forward from `uᵢ` to the
   offset boundary.  Each rectangle is (6–8) × (≥ 8) — both sides ≥ 6 —
   and consecutive rectangles meet corner-to-corner (`PushAdj`) at the
   endpoints of the cuts.  This is `exists_corridorChain`.
4. **Assembly.**  Tile the corridor by defect pushing
   (`IsCornerChain.tileable`), the offset core by step 1, and glue.

The constant: `Fat 16`.  16 = 2·8 is what keeps two offset edges from
crossing (touching is fine — `offsetCore` may degenerate or disconnect,
which step 1 tolerates), and edges of length ≥ 16 lose at most 8 to a cut,
leaving rectangles of length ≥ 8 ≥ 6.  See
`docs/offset-polyomino-argument.md` for the full accounting and the
scoping decisions (no holes for now; diagonal vertices excluded by
fatness).
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

-- ============================================================
-- §2 The offset polyomino
-- ============================================================

/-- The **safety box** of the 3×2 grid cell with corner `c`: the grid cell
    inflated by 6 in every direction (a 15 × 14 box). -/
def offBox (c : Cell) : Set Cell :=
  rect (c.1 - 6) (c.2 - 6) (c.1 + 9) (c.2 + 8)

/-- The **offset polyomino**: the union of the complete 3×2 grid cells
    whose safety box lies inside `P`.  This realizes "offset every edge of
    `P` inwards by at least 6, then snap onto the 3×2 grid": along a
    boundary edge of a fat polyomino, the offset boundary runs on the
    first grid line at distance ≥ 6 inside `P`, i.e. at distance 6–8. -/
def offsetCore (P : Set Cell) : Set Cell := {p | offBox (cornerOf p) ⊆ P}

lemma mem_offsetCore {P : Set Cell} {p : Cell} :
    p ∈ offsetCore P ↔ offBox (cornerOf p) ⊆ P := Iff.rfl

/-- Membership in the offset polyomino depends only on the grid cell. -/
lemma offsetCore_congr (P : Set Cell) {p q : Cell}
    (h : cornerOf p = cornerOf q) :
    (p ∈ offsetCore P ↔ q ∈ offsetCore P) := by
  simp only [mem_offsetCore, h]

lemma offsetCore_subset (P : Set Cell) : offsetCore P ⊆ P := by
  rintro ⟨a, b⟩ hp
  exact hp (by simp only [offBox, cornerOf, mem_rect]; omega)

lemma offsetCore_finite {P : Set Cell} (hfin : P.Finite) :
    (offsetCore P).Finite :=
  hfin.subset (offsetCore_subset P)

/-- The offset polyomino has **all vertices on the 3×2 grid** — with no
    hypothesis on `P` at all: membership is constant on grid cells, so the
    boundary of `offsetCore P` can only turn at grid points. -/
theorem vertexOnGrid_offsetCore (P : Set Cell) :
    VertexOnGrid 3 2 (offsetCore P) := by
  rintro ⟨a, b⟩ hv
  refine ⟨?_, ?_⟩
  · change (3 : ℤ) ∣ a
    by_contra h3
    exact hv.1
      ⟨offsetCore_congr P
        (by simp only [cornerOf, Prod.mk.injEq, and_true]; omega),
       offsetCore_congr P
        (by simp only [cornerOf, Prod.mk.injEq, and_true]; omega)⟩
  · change (2 : ℤ) ∣ b
    by_contra h2
    exact hv.2
      ⟨offsetCore_congr P
        (by simp only [cornerOf, Prod.mk.injEq, true_and]; omega),
       offsetCore_congr P
        (by simp only [cornerOf, Prod.mk.injEq, true_and]; omega)⟩

/-- The offset polyomino is L-tileable — with no connectivity or area
    hypothesis: it is a disjoint union of 3×2 blocks. -/
theorem LTileable_offsetCore {P : Set Cell} (hfin : P.Finite) :
    LTileable (offsetCore P) :=
  LTileable_of_vertexOnGrid3x2 _ (offsetCore_finite hfin)
    (vertexOnGrid_offsetCore P)

-- ============================================================
-- §3 Area of the offset polyomino
-- ============================================================

/-- A finite disjoint union of sets of size divisible by `k` has size
    divisible by `k`. -/
private lemma dvd_ncard_biUnion {ι : Type*} {k : ℕ} {s : Set ι}
    (hs : s.Finite) (f : ι → Set Cell) (hfin : ∀ i ∈ s, (f i).Finite)
    (hcard : ∀ i ∈ s, k ∣ (f i).ncard) (hd : s.PairwiseDisjoint f) :
    k ∣ (⋃ i ∈ s, f i).ncard := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | @insert a t ha htfin ih =>
    rw [Set.biUnion_insert]
    have hdisj : Disjoint (f a) (⋃ i ∈ t, f i) := by
      rw [Set.disjoint_iUnion₂_right]
      intro i hi
      exact hd (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hi)
        (by rintro rfl; exact ha hi)
    rw [Set.ncard_union_eq hdisj (hfin a (Set.mem_insert _ _))
      (htfin.biUnion fun i hi => hfin i (Set.mem_insert_of_mem _ hi))]
    exact Nat.dvd_add (hcard a (Set.mem_insert _ _))
      (ih (fun i hi => hfin i (Set.mem_insert_of_mem _ hi))
        (fun i hi => hcard i (Set.mem_insert_of_mem _ hi))
        (hd.subset (Set.subset_insert _ _)))

/-- The area of the offset polyomino is a multiple of 6: it is a finite
    disjoint union of full 3×2 grid cells. -/
theorem dvd_ncard_offsetCore {P : Set Cell} (hfin : P.Finite) :
    6 ∣ (offsetCore P).ncard := by
  set C : Set Cell := cornerOf '' offsetCore P with hC
  have hCfin : C.Finite := (offsetCore_finite hfin).image _
  have hCdvd : ∀ c ∈ C, 3 ∣ c.1 ∧ 2 ∣ c.2 := by
    rintro c ⟨p, _, rfl⟩
    simp only [cornerOf]
    omega
  have hcover : offsetCore P = ⋃ c ∈ C, gridCell c := by
    ext q
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hq
      exact ⟨cornerOf q, ⟨q, hq, rfl⟩, mem_gridCell_cornerOf q⟩
    · rintro ⟨c, hcC, hqc⟩
      obtain ⟨h1, h2⟩ := hCdvd c hcC
      obtain ⟨p, hp, rfl⟩ := hcC
      exact (offsetCore_congr P (cornerOf_of_mem_gridCell h1 h2 hqc)).mpr hp
  have hdisj : C.PairwiseDisjoint gridCell := by
    intro c hc c' hc' hne
    rw [Function.onFun, Set.disjoint_left]
    intro q hqc hqc'
    obtain ⟨h1, h2⟩ := hCdvd c hc
    obtain ⟨h1', h2'⟩ := hCdvd c' hc'
    exact hne ((cornerOf_of_mem_gridCell h1 h2 hqc).symm.trans
      (cornerOf_of_mem_gridCell h1' h2' hqc'))
  have hcell : ∀ c ∈ C, (6 : ℕ) ∣ (gridCell c).ncard := by
    intro c _
    have e1 : c.1 + 3 - c.1 = 3 := by ring
    have e2 : c.2 + 2 - c.2 = 2 := by ring
    rw [gridCell, rect_ncard, e1, e2]
    decide
  rw [hcover]
  exact dvd_ncard_biUnion hCfin gridCell (fun c _ => rect_finite _ _ _ _)
    hcell hdisj

-- ============================================================
-- §4 The corridor
-- ============================================================

/-- The **corridor**: the moat of `P` between its boundary and the offset
    polyomino, of thickness 6–8. -/
def corridor (P : Set Cell) : Set Cell := P \ offsetCore P

lemma offsetCore_union_corridor (P : Set Cell) :
    offsetCore P ∪ corridor P = P :=
  Set.union_diff_cancel (offsetCore_subset P)

lemma disjoint_offsetCore_corridor (P : Set Cell) :
    Disjoint (offsetCore P) (corridor P) :=
  Set.disjoint_sdiff_right

/-- The corridor inherits the area divisibility of `P` (the offset area is
    a multiple of 6). -/
lemma dvd_ncard_corridor {P : Set Cell} (hfin : P.Finite)
    (harea : 3 ∣ P.ncard) : 3 ∣ (corridor P).ncard := by
  have h6 := dvd_ncard_offsetCore hfin
  have hd : (corridor P).ncard = P.ncard - (offsetCore P).ncard :=
    Set.ncard_diff (offsetCore_subset P) (offsetCore_finite hfin)
  have hle : (offsetCore P).ncard ≤ P.ncard :=
    Set.ncard_le_ncard (offsetCore_subset P) hfin
  omega

/-- A nonempty polyomino has a nonempty corridor: a cell of maximal
    abscissa in `P` sees the complement inside its safety box. -/
lemma corridor_nonempty {P : Set Cell} (hfin : P.Finite) (hne : P.Nonempty) :
    (corridor P).Nonempty := by
  obtain ⟨⟨a, b⟩, hpP, hmax⟩ := Set.exists_max_image P Prod.fst hfin hne
  refine ⟨(a, b), hpP, fun hcore => ?_⟩
  have hsub : offBox (cornerOf (a, b)) ⊆ P := hcore
  have hmem : (a + 1, b) ∈ P :=
    hsub (by simp only [offBox, cornerOf, mem_rect]; omega)
  have h1 : a + 1 ≤ a := hmax (a + 1, b) hmem
  omega

-- ============================================================
-- §5 The boundary walk: straight runs and the successor vertex
-- ============================================================
--
-- The boundary of `P` is walked with the interior on the left.  A vertex
-- of a fat polyomino has exactly one outgoing arm in that orientation
-- (the quadrant picture decides which); following it to its first turn
-- yields the *successor* vertex.  This section proves existence and
-- uniqueness of the successor; the next sessions build the orbit
-- machinery (single boundary cycle via ray-crossing parity) and the
-- corridor rectangles on top of it.

/-- A straight horizontal piece of the boundary of `P` on the grid line
    at height `y`, columns `[x0, x1)`, with the **interior above**;
    walked eastward it has the interior on the left. -/
def HRunAbove (P : Set Cell) (y x0 x1 : ℤ) : Prop :=
  ∀ x, x0 ≤ x → x < x1 → (x, y) ∈ P ∧ (x, y - 1) ∉ P

/-- Interior below; walked westward it has the interior on the left. -/
def HRunBelow (P : Set Cell) (y x0 x1 : ℤ) : Prop :=
  ∀ x, x0 ≤ x → x < x1 → (x, y - 1) ∈ P ∧ (x, y) ∉ P

/-- A straight vertical piece of the boundary of `P` on the grid line at
    abscissa `x`, rows `[y0, y1)`, with the **interior to the west**;
    walked northward it has the interior on the left. -/
def VRunLeft (P : Set Cell) (x y0 y1 : ℤ) : Prop :=
  ∀ y, y0 ≤ y → y < y1 → (x - 1, y) ∈ P ∧ (x, y) ∉ P

/-- Interior to the east; walked southward it has the interior on the
    left. -/
def VRunRight (P : Set Cell) (x y0 y1 : ℤ) : Prop :=
  ∀ y, y0 ≤ y → y < y1 → (x, y) ∈ P ∧ (x - 1, y) ∉ P

/-- `w` is the **successor** of the vertex `u` on the boundary walk of
    `P` with the interior on the left: the straight boundary run leaving
    `u` in the walking direction ends at the vertex `w`.  The four
    disjuncts are the four walking directions E, W, N, S. -/
def NextVtx (P : Set Cell) (u w : Cell) : Prop :=
  IsVertex P u ∧ IsVertex P w ∧
    ((u.2 = w.2 ∧ u.1 < w.1 ∧ HRunAbove P u.2 u.1 w.1) ∨
     (u.2 = w.2 ∧ w.1 < u.1 ∧ HRunBelow P u.2 w.1 u.1) ∨
     (u.1 = w.1 ∧ u.2 < w.2 ∧ VRunLeft P u.1 u.2 w.2) ∨
     (u.1 = w.1 ∧ w.2 < u.2 ∧ VRunRight P u.1 w.2 u.2))

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

-- No interior point of a straight run is a vertex: the 2×2 pattern there
-- is row- (resp. column-) constant.

private lemma hrunAbove_not_vertex {P : Set Cell} {y x0 x1 : ℤ}
    (h : HRunAbove P y x0 x1) :
    ∀ x, x0 < x → x < x1 → ¬IsVertex P (x, y) := by
  intro x h1 h2 hv
  have ha := h (x - 1) (by omega) (by omega)
  have hb := h x (by omega) h2
  exact hv.1 ⟨iff_of_false ha.2 hb.2, iff_of_true ha.1 hb.1⟩

private lemma hrunBelow_not_vertex {P : Set Cell} {y x0 x1 : ℤ}
    (h : HRunBelow P y x0 x1) :
    ∀ x, x0 < x → x < x1 → ¬IsVertex P (x, y) := by
  intro x h1 h2 hv
  have ha := h (x - 1) (by omega) (by omega)
  have hb := h x (by omega) h2
  exact hv.1 ⟨iff_of_true ha.1 hb.1, iff_of_false ha.2 hb.2⟩

private lemma vrunLeft_not_vertex {P : Set Cell} {x y0 y1 : ℤ}
    (h : VRunLeft P x y0 y1) :
    ∀ y, y0 < y → y < y1 → ¬IsVertex P (x, y) := by
  intro y h1 h2 hv
  have ha := h (y - 1) (by omega) (by omega)
  have hb := h y (by omega) h2
  exact hv.2 ⟨iff_of_true ha.1 hb.1, iff_of_false ha.2 hb.2⟩

private lemma vrunRight_not_vertex {P : Set Cell} {x y0 y1 : ℤ}
    (h : VRunRight P x y0 y1) :
    ∀ y, y0 < y → y < y1 → ¬IsVertex P (x, y) := by
  intro y h1 h2 hv
  have ha := h (y - 1) (by omega) (by omega)
  have hb := h y (by omega) h2
  exact hv.2 ⟨iff_of_false ha.2 hb.2, iff_of_true ha.1 hb.1⟩

-- The four walk lemmas: a straight run that starts (for ≥ 16 steps)
-- continues to its first turn, which is a vertex.

private lemma walk_east {P : Set Cell} (hfin : P.Finite) {y x0 : ℤ}
    (hcell : (x0, y) ∈ P ∧ (x0, y - 1) ∉ P) :
    ∃ x1, x0 < x1 ∧ HRunAbove P y x0 x1 ∧ IsVertex P (x1, y) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.fst).bddAbove
  have hbound : ∀ p ∈ P, p.1 ≤ B := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ x, x0 ≤ x ∧ ¬((x, y) ∈ P ∧ (x, y - 1) ∉ P) := by
    refine ⟨max x0 (B + 1), le_max_left _ _, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : max x0 (B + 1) ≤ B := hbound _ hmem
    have := le_max_right x0 (B + 1)
    omega
  obtain ⟨x1, ⟨hx1ge, hx1fail⟩, hleast⟩ :=
    Int.exists_least_of_bdd
      (P := fun x => x0 ≤ x ∧ ¬((x, y) ∈ P ∧ (x, y - 1) ∉ P))
      ⟨x0, fun _ hz => hz.1⟩ hinh
  have hrun' : HRunAbove P y x0 x1 := by
    intro x h1 h2
    by_contra hx
    exact absurd (hleast x ⟨h1, hx⟩) (by omega)
  have hgt : x0 < x1 := by
    rcases eq_or_lt_of_le hx1ge with heq | h
    · exact absurd (heq ▸ hcell) hx1fail
    · exact h
  have hprev := hrun' (x1 - 1) (by omega) (by omega)
  refine ⟨x1, hgt, hrun', ?_, ?_⟩
  · exact fun ⟨h1, h2⟩ =>
      hx1fail ⟨h2.mp hprev.1, fun hSE => hprev.2 (h1.mpr hSE)⟩
  · exact fun ⟨h1, _⟩ => hprev.2 (h1.mpr hprev.1)

private lemma walk_west {P : Set Cell} (hfin : P.Finite) {y x0 : ℤ}
    (hcell : (x0 - 1, y - 1) ∈ P ∧ (x0 - 1, y) ∉ P) :
    ∃ x1, x1 < x0 ∧ HRunBelow P y x1 x0 ∧ IsVertex P (x1, y) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.fst).bddBelow
  have hbound : ∀ p ∈ P, B ≤ p.1 := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ x, x < x0 ∧ ¬((x, y - 1) ∈ P ∧ (x, y) ∉ P) := by
    refine ⟨min (x0 - 1) (B - 1),
      by have := min_le_left (x0 - 1) (B - 1); omega, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : B ≤ min (x0 - 1) (B - 1) := hbound _ hmem
    have := min_le_right (x0 - 1) (B - 1)
    omega
  obtain ⟨xf, ⟨hxflt, hxffail⟩, hgreatest⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun x => x < x0 ∧ ¬((x, y - 1) ∈ P ∧ (x, y) ∉ P))
      ⟨x0, fun _ hz => le_of_lt hz.1⟩ hinh
  have hrun' : HRunBelow P y (xf + 1) x0 := by
    intro x h1 h2
    by_contra hx
    exact absurd (hgreatest x ⟨h2, hx⟩) (by omega)
  have hlt : xf + 1 < x0 := by
    rcases eq_or_lt_of_le (show xf ≤ x0 - 1 by omega) with heq | h
    · subst heq
      exact absurd hcell hxffail
    · omega
  have hcur := hrun' (xf + 1) le_rfl (by omega)
  have hfail' : ¬((xf + 1 - 1, y - 1) ∈ P ∧ (xf + 1 - 1, y) ∉ P) := by
    rw [show xf + 1 - 1 = xf from by ring]
    exact hxffail
  refine ⟨xf + 1, hlt, hrun', ?_, ?_⟩
  · exact fun ⟨h1, h2⟩ =>
      hfail' ⟨h1.mpr hcur.1, fun hNW => hcur.2 (h2.mp hNW)⟩
  · exact fun ⟨_, h2⟩ => hcur.2 (h2.mp hcur.1)

private lemma walk_north {P : Set Cell} (hfin : P.Finite) {x y0 : ℤ}
    (hcell : (x - 1, y0) ∈ P ∧ (x, y0) ∉ P) :
    ∃ y1, y0 < y1 ∧ VRunLeft P x y0 y1 ∧ IsVertex P (x, y1) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddAbove
  have hbound : ∀ p ∈ P, p.2 ≤ B := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ y, y0 ≤ y ∧ ¬((x - 1, y) ∈ P ∧ (x, y) ∉ P) := by
    refine ⟨max y0 (B + 1), le_max_left _ _, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : max y0 (B + 1) ≤ B := hbound _ hmem
    have := le_max_right y0 (B + 1)
    omega
  obtain ⟨y1, ⟨hy1ge, hy1fail⟩, hleast⟩ :=
    Int.exists_least_of_bdd
      (P := fun y => y0 ≤ y ∧ ¬((x - 1, y) ∈ P ∧ (x, y) ∉ P))
      ⟨y0, fun _ hz => hz.1⟩ hinh
  have hrun' : VRunLeft P x y0 y1 := by
    intro y h1 h2
    by_contra hy
    exact absurd (hleast y ⟨h1, hy⟩) (by omega)
  have hgt : y0 < y1 := by
    rcases eq_or_lt_of_le hy1ge with heq | h
    · exact absurd (heq ▸ hcell) hy1fail
    · exact h
  have hprev := hrun' (y1 - 1) (by omega) (by omega)
  refine ⟨y1, hgt, hrun', ?_, ?_⟩
  · exact fun ⟨h1, _⟩ => hprev.2 (h1.mp hprev.1)
  · exact fun ⟨h1, h2⟩ =>
      hy1fail ⟨h1.mp hprev.1, fun hNE => hprev.2 (h2.mpr hNE)⟩

private lemma walk_south {P : Set Cell} (hfin : P.Finite) {x y0 : ℤ}
    (hcell : (x, y0 - 1) ∈ P ∧ (x - 1, y0 - 1) ∉ P) :
    ∃ y1, y1 < y0 ∧ VRunRight P x y1 y0 ∧ IsVertex P (x, y1) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddBelow
  have hbound : ∀ p ∈ P, B ≤ p.2 := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ y, y < y0 ∧ ¬((x, y) ∈ P ∧ (x - 1, y) ∉ P) := by
    refine ⟨min (y0 - 1) (B - 1),
      by have := min_le_left (y0 - 1) (B - 1); omega, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : B ≤ min (y0 - 1) (B - 1) := hbound _ hmem
    have := min_le_right (y0 - 1) (B - 1)
    omega
  obtain ⟨yf, ⟨hyflt, hyffail⟩, hgreatest⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun y => y < y0 ∧ ¬((x, y) ∈ P ∧ (x - 1, y) ∉ P))
      ⟨y0, fun _ hz => le_of_lt hz.1⟩ hinh
  have hrun' : VRunRight P x (yf + 1) y0 := by
    intro y h1 h2
    by_contra hy
    exact absurd (hgreatest y ⟨h2, hy⟩) (by omega)
  have hlt : yf + 1 < y0 := by
    rcases eq_or_lt_of_le (show yf ≤ y0 - 1 by omega) with heq | h
    · subst heq
      exact absurd hcell hyffail
    · omega
  have hcur := hrun' (yf + 1) le_rfl (by omega)
  have hfail' : ¬((x, yf + 1 - 1) ∈ P ∧ (x - 1, yf + 1 - 1) ∉ P) := by
    rw [show yf + 1 - 1 = yf from by ring]
    exact hyffail
  refine ⟨yf + 1, hlt, hrun', ?_, ?_⟩
  · exact fun ⟨_, h2⟩ => hcur.2 (h2.mpr hcur.1)
  · exact fun ⟨h1, h2⟩ =>
      hfail' ⟨h2.mpr hcur.1, fun hSW => hcur.2 (h1.mp hSW)⟩

-- The four *reverse-end* walk lemmas: the other end of each oriented run.

/-- The **west end** of a horizontal boundary run with the interior
    above. -/
private lemma walk_west' {P : Set Cell} (hfin : P.Finite) {y x0 : ℤ}
    (hcell : (x0, y) ∈ P ∧ (x0, y - 1) ∉ P) :
    ∃ x1, x1 ≤ x0 ∧ HRunAbove P y x1 (x0 + 1) ∧ IsVertex P (x1, y) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.fst).bddBelow
  have hbound : ∀ p ∈ P, B ≤ p.1 := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ x, x < x0 ∧ ¬((x, y) ∈ P ∧ (x, y - 1) ∉ P) := by
    refine ⟨min (x0 - 1) (B - 1),
      by have := min_le_left (x0 - 1) (B - 1); omega, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : B ≤ min (x0 - 1) (B - 1) := hbound _ hmem
    have := min_le_right (x0 - 1) (B - 1)
    omega
  obtain ⟨xf, ⟨hxflt, hxffail⟩, hgreatest⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun x => x < x0 ∧ ¬((x, y) ∈ P ∧ (x, y - 1) ∉ P))
      ⟨x0, fun _ hz => le_of_lt hz.1⟩ hinh
  have hrun' : HRunAbove P y (xf + 1) (x0 + 1) := by
    intro x h1 h2
    by_contra hx
    rcases eq_or_lt_of_le (show x ≤ x0 by omega) with heq | hlt
    · subst heq
      exact hx hcell
    · exact absurd (hgreatest x ⟨hlt, hx⟩) (by omega)
  have hcur := hrun' (xf + 1) le_rfl (by omega)
  have hfail' : ¬((xf + 1 - 1, y) ∈ P ∧ (xf + 1 - 1, y - 1) ∉ P) := by
    rw [show xf + 1 - 1 = xf from by ring]
    exact hxffail
  refine ⟨xf + 1, by omega, hrun', ?_, ?_⟩
  · exact fun ⟨h1, h2⟩ =>
      hfail' ⟨h2.mpr hcur.1, fun hSW => hcur.2 (h1.mp hSW)⟩
  · exact fun ⟨_, h2⟩ => hcur.2 (h2.mpr hcur.1)

/-- The **east end** of a horizontal boundary run with the interior
    below. -/
private lemma walk_east' {P : Set Cell} (hfin : P.Finite) {y x0 : ℤ}
    (hcell : (x0, y - 1) ∈ P ∧ (x0, y) ∉ P) :
    ∃ x1, x0 < x1 ∧ HRunBelow P y x0 x1 ∧ IsVertex P (x1, y) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.fst).bddAbove
  have hbound : ∀ p ∈ P, p.1 ≤ B := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ x, x0 ≤ x ∧ ¬((x, y - 1) ∈ P ∧ (x, y) ∉ P) := by
    refine ⟨max x0 (B + 1), le_max_left _ _, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : max x0 (B + 1) ≤ B := hbound _ hmem
    have := le_max_right x0 (B + 1)
    omega
  obtain ⟨x1, ⟨hx1ge, hx1fail⟩, hleast⟩ :=
    Int.exists_least_of_bdd
      (P := fun x => x0 ≤ x ∧ ¬((x, y - 1) ∈ P ∧ (x, y) ∉ P))
      ⟨x0, fun _ hz => hz.1⟩ hinh
  have hrun' : HRunBelow P y x0 x1 := by
    intro x h1 h2
    by_contra hx
    exact absurd (hleast x ⟨h1, hx⟩) (by omega)
  have hgt : x0 < x1 := by
    rcases eq_or_lt_of_le hx1ge with heq | h
    · exact absurd (heq ▸ hcell) hx1fail
    · exact h
  have hprev := hrun' (x1 - 1) (by omega) (by omega)
  refine ⟨x1, hgt, hrun', ?_, ?_⟩
  · exact fun ⟨h1, h2⟩ =>
      hx1fail ⟨h1.mp hprev.1, fun hNE => hprev.2 (h2.mpr hNE)⟩
  · exact fun ⟨h1, _⟩ => hprev.2 (h1.mp hprev.1)

/-- The **south end** of a vertical boundary run with the interior to the
    west. -/
private lemma walk_south' {P : Set Cell} (hfin : P.Finite) {x y0 : ℤ}
    (hcell : (x - 1, y0) ∈ P ∧ (x, y0) ∉ P) :
    ∃ y1, y1 ≤ y0 ∧ VRunLeft P x y1 (y0 + 1) ∧ IsVertex P (x, y1) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddBelow
  have hbound : ∀ p ∈ P, B ≤ p.2 := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ y, y < y0 ∧ ¬((x - 1, y) ∈ P ∧ (x, y) ∉ P) := by
    refine ⟨min (y0 - 1) (B - 1),
      by have := min_le_left (y0 - 1) (B - 1); omega, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : B ≤ min (y0 - 1) (B - 1) := hbound _ hmem
    have := min_le_right (y0 - 1) (B - 1)
    omega
  obtain ⟨yf, ⟨hyflt, hyffail⟩, hgreatest⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun y => y < y0 ∧ ¬((x - 1, y) ∈ P ∧ (x, y) ∉ P))
      ⟨y0, fun _ hz => le_of_lt hz.1⟩ hinh
  have hrun' : VRunLeft P x (yf + 1) (y0 + 1) := by
    intro y h1 h2
    by_contra hy
    rcases eq_or_lt_of_le (show y ≤ y0 by omega) with heq | hlt
    · subst heq
      exact hy hcell
    · exact absurd (hgreatest y ⟨hlt, hy⟩) (by omega)
  have hcur := hrun' (yf + 1) le_rfl (by omega)
  have hfail' : ¬((x - 1, yf + 1 - 1) ∈ P ∧ (x, yf + 1 - 1) ∉ P) := by
    rw [show yf + 1 - 1 = yf from by ring]
    exact hyffail
  refine ⟨yf + 1, by omega, hrun', ?_, ?_⟩
  · exact fun ⟨_, h2⟩ => hcur.2 (h2.mp hcur.1)
  · exact fun ⟨h1, h2⟩ =>
      hfail' ⟨h1.mpr hcur.1, fun hSE => hcur.2 (h2.mp hSE)⟩

/-- The **north end** of a vertical boundary run with the interior to the
    east. -/
private lemma walk_north' {P : Set Cell} (hfin : P.Finite) {x y0 : ℤ}
    (hcell : (x, y0) ∈ P ∧ (x - 1, y0) ∉ P) :
    ∃ y1, y0 < y1 ∧ VRunRight P x y0 y1 ∧ IsVertex P (x, y1) := by
  obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddAbove
  have hbound : ∀ p ∈ P, p.2 ≤ B := fun p hp => hB ⟨p, hp, rfl⟩
  have hinh : ∃ y, y0 ≤ y ∧ ¬((x, y) ∈ P ∧ (x - 1, y) ∉ P) := by
    refine ⟨max y0 (B + 1), le_max_left _ _, ?_⟩
    rintro ⟨hmem, -⟩
    have h' : max y0 (B + 1) ≤ B := hbound _ hmem
    have := le_max_right y0 (B + 1)
    omega
  obtain ⟨y1, ⟨hy1ge, hy1fail⟩, hleast⟩ :=
    Int.exists_least_of_bdd
      (P := fun y => y0 ≤ y ∧ ¬((x, y) ∈ P ∧ (x - 1, y) ∉ P))
      ⟨y0, fun _ hz => hz.1⟩ hinh
  have hrun' : VRunRight P x y0 y1 := by
    intro y h1 h2
    by_contra hy
    exact absurd (hleast y ⟨h1, hy⟩) (by omega)
  have hgt : y0 < y1 := by
    rcases eq_or_lt_of_le hy1ge with heq | h
    · exact absurd (heq ▸ hcell) hy1fail
    · exact h
  have hprev := hrun' (y1 - 1) (by omega) (by omega)
  refine ⟨y1, hgt, hrun', ?_, ?_⟩
  · exact fun ⟨h1, _⟩ => hprev.2 (h1.mpr hprev.1)
  · exact fun ⟨h1, h2⟩ =>
      hy1fail ⟨h2.mp hprev.1, fun hNW => hprev.2 (h1.mpr hNW)⟩

/-- **Existence of the successor.**  Every vertex of a fat polyomino has a
    successor on the interior-on-the-left boundary walk: the quadrant
    picture provides the first cell of the outgoing arm, and the walk
    lemmas extend it to the first turn. -/
theorem exists_nextVtx {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u : Cell} (hu : IsVertex P u) : ∃ w, NextVtx P u w := by
  obtain ⟨a, b⟩ := u
  obtain ⟨c, hc | hc⟩ := hfat.mem_iff hu
  -- convex corners
  · cases c with
    | BL =>
      -- interior up-right: walk east along the bottom arm
      have hcell : ((a, b) : Cell) ∈ P ∧ ((a, b - 1) : Cell) ∉ P := by
        constructor
        · exact (hc (a, b) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          have h' := (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mp hmem
          simp only [quadrant, Set.mem_setOf_eq] at h'
          omega
      obtain ⟨x1, hgt, hrun', hvtx⟩ := walk_east hfin hcell
      exact ⟨(x1, b), hu, hvtx, Or.inl ⟨rfl, hgt, hrun'⟩⟩
    | BR =>
      -- interior up-left: walk north along the east arm
      have hcell : ((a - 1, b) : Cell) ∈ P ∧ ((a, b) : Cell) ∉ P := by
        constructor
        · exact (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          have h' := (hc (a, b) (by simp only [box, mem_rect]; omega)).mp hmem
          simp only [quadrant, Set.mem_setOf_eq] at h'
          omega
      obtain ⟨y1, hgt, hrun', hvtx⟩ := walk_north hfin hcell
      exact ⟨(a, y1), hu, hvtx, Or.inr (Or.inr (Or.inl ⟨rfl, hgt, hrun'⟩))⟩
    | TL =>
      -- interior down-right: walk south along the east arm
      have hcell : ((a, b - 1) : Cell) ∈ P ∧ ((a - 1, b - 1) : Cell) ∉ P := by
        constructor
        · exact (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          have h' := (hc (a - 1, b - 1)
            (by simp only [box, mem_rect]; omega)).mp hmem
          simp only [quadrant, Set.mem_setOf_eq] at h'
          omega
      obtain ⟨y1, hlt, hrun', hvtx⟩ := walk_south hfin hcell
      exact ⟨(a, y1), hu, hvtx, Or.inr (Or.inr (Or.inr ⟨rfl, hlt, hrun'⟩))⟩
    | TR =>
      -- interior down-left: walk west along the top arm
      have hcell : ((a - 1, b - 1) : Cell) ∈ P ∧ ((a - 1, b) : Cell) ∉ P := by
        constructor
        · exact (hc (a - 1, b - 1) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          have h' := (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mp hmem
          simp only [quadrant, Set.mem_setOf_eq] at h'
          omega
      obtain ⟨x1, hlt, hrun', hvtx⟩ := walk_west hfin hcell
      exact ⟨(x1, b), hu, hvtx, Or.inr (Or.inl ⟨rfl, hlt, hrun'⟩)⟩
  -- reflex corners
  · cases c with
    | BL =>
      -- hole up-right: walk north along the east arm
      have hcell : ((a - 1, b) : Cell) ∈ P ∧ ((a, b) : Cell) ∉ P := by
        constructor
        · exact (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          exact (hc (a, b) (by simp only [box, mem_rect]; omega)).mp hmem
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      obtain ⟨y1, hgt, hrun', hvtx⟩ := walk_north hfin hcell
      exact ⟨(a, y1), hu, hvtx, Or.inr (Or.inr (Or.inl ⟨rfl, hgt, hrun'⟩))⟩
    | BR =>
      -- hole up-left: walk west along the top arm
      have hcell : ((a - 1, b - 1) : Cell) ∈ P ∧ ((a - 1, b) : Cell) ∉ P := by
        constructor
        · exact (hc (a - 1, b - 1) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          exact (hc (a - 1, b) (by simp only [box, mem_rect]; omega)).mp hmem
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      obtain ⟨x1, hlt, hrun', hvtx⟩ := walk_west hfin hcell
      exact ⟨(x1, b), hu, hvtx, Or.inr (Or.inl ⟨rfl, hlt, hrun'⟩)⟩
    | TL =>
      -- hole down-right: walk east along the bottom arm
      have hcell : ((a, b) : Cell) ∈ P ∧ ((a, b - 1) : Cell) ∉ P := by
        constructor
        · exact (hc (a, b) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          exact (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mp hmem
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      obtain ⟨x1, hgt, hrun', hvtx⟩ := walk_east hfin hcell
      exact ⟨(x1, b), hu, hvtx, Or.inl ⟨rfl, hgt, hrun'⟩⟩
    | TR =>
      -- hole down-left: walk south along the east arm
      have hcell : ((a, b - 1) : Cell) ∈ P ∧ ((a - 1, b - 1) : Cell) ∉ P := by
        constructor
        · exact (hc (a, b - 1) (by simp only [box, mem_rect]; omega)).mpr
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
        · intro hmem
          exact (hc (a - 1, b - 1) (by simp only [box, mem_rect]; omega)).mp hmem
            (by simp only [quadrant, Set.mem_setOf_eq]; omega)
      obtain ⟨y1, hlt, hrun', hvtx⟩ := walk_south hfin hcell
      exact ⟨(a, y1), hu, hvtx, Or.inr (Or.inr (Or.inr ⟨rfl, hlt, hrun'⟩))⟩

/-- **Uniqueness of the successor.**  Two outgoing arms in the same
    direction end at the same first turn; two different directions
    contradict each other on the first step or force the (excluded)
    diagonal pattern at `u`. -/
theorem NextVtx.unique {P : Set Cell} (hfat : Fat 16 P) {u w w' : Cell}
    (h : NextVtx P u w) (h' : NextVtx P u w') : w = w' := by
  obtain ⟨hu, hw, hcase⟩ := h
  obtain ⟨-, hw', hcase'⟩ := h'
  have hdiag := hfat.not_diagonal (by norm_num) hu
  rcases hcase with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ <;>
    rcases hcase' with ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩
  -- E, E
  · have hww : IsVertex P (w.1, u.2) := by
      rwa [show ((w.1, u.2) : Cell) = w from Prod.ext rfl e1]
    have hww' : IsVertex P (w'.1, u.2) := by
      rwa [show ((w'.1, u.2) : Cell) = w' from Prod.ext rfl f1]
    rcases lt_trichotomy w.1 w'.1 with hlt | heq | hgt
    · exact absurd hww (hrunAbove_not_vertex hr' w.1 e2 hlt)
    · exact Prod.ext heq (e1.symm.trans f1)
    · exact absurd hww' (hrunAbove_not_vertex hr w'.1 f2 hgt)
  -- E, W: diagonal at u
  · have hE := hr u.1 le_rfl e2
    have hW := hr' (u.1 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_true hW.1 hE.1, iff_of_false hW.2 hE.2⟩ hdiag
  -- E, N: first cells clash
  · exact absurd (hr u.1 le_rfl e2).1 (hr' u.2 le_rfl f2).2
  -- E, S
  · exact absurd (hr' (u.2 - 1) (by omega) (by omega)).1 (hr u.1 le_rfl e2).2
  -- W, E: diagonal at u
  · have hE := hr' u.1 le_rfl f2
    have hW := hr (u.1 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_true hW.1 hE.1, iff_of_false hW.2 hE.2⟩ hdiag
  -- W, W
  · have hww : IsVertex P (w.1, u.2) := by
      rwa [show ((w.1, u.2) : Cell) = w from Prod.ext rfl e1]
    have hww' : IsVertex P (w'.1, u.2) := by
      rwa [show ((w'.1, u.2) : Cell) = w' from Prod.ext rfl f1]
    rcases lt_trichotomy w.1 w'.1 with hlt | heq | hgt
    · exact absurd hww' (hrunBelow_not_vertex hr w'.1 hlt f2)
    · exact Prod.ext heq (e1.symm.trans f1)
    · exact absurd hww (hrunBelow_not_vertex hr' w.1 hgt e2)
  -- W, N
  · exact absurd (hr' u.2 le_rfl f2).1 (hr (u.1 - 1) (by omega) (by omega)).2
  -- W, S
  · exact absurd (hr (u.1 - 1) (by omega) (by omega)).1
      (hr' (u.2 - 1) (by omega) (by omega)).2
  -- N, E
  · exact absurd (hr' u.1 le_rfl f2).1 (hr u.2 le_rfl e2).2
  -- N, W
  · exact absurd (hr u.2 le_rfl e2).1 (hr' (u.1 - 1) (by omega) (by omega)).2
  -- N, N
  · have hww : IsVertex P (u.1, w.2) := by
      rwa [show ((u.1, w.2) : Cell) = w from Prod.ext e1 rfl]
    have hww' : IsVertex P (u.1, w'.2) := by
      rwa [show ((u.1, w'.2) : Cell) = w' from Prod.ext f1 rfl]
    rcases lt_trichotomy w.2 w'.2 with hlt | heq | hgt
    · exact absurd hww (vrunLeft_not_vertex hr' w.2 e2 hlt)
    · exact Prod.ext (e1.symm.trans f1) heq
    · exact absurd hww' (vrunLeft_not_vertex hr w'.2 f2 hgt)
  -- N, S: diagonal at u
  · have hN := hr u.2 le_rfl e2
    have hS := hr' (u.2 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_false hS.2 hN.2, iff_of_true hN.1 hS.1⟩ hdiag
  -- S, E
  · exact absurd (hr (u.2 - 1) (by omega) (by omega)).1 (hr' u.1 le_rfl f2).2
  -- S, W
  · exact absurd (hr' (u.1 - 1) (by omega) (by omega)).1
      (hr (u.2 - 1) (by omega) (by omega)).2
  -- S, N: diagonal at u
  · have hN := hr' u.2 le_rfl f2
    have hS := hr (u.2 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_false hS.2 hN.2, iff_of_true hN.1 hS.1⟩ hdiag
  -- S, S
  · have hww : IsVertex P (u.1, w.2) := by
      rwa [show ((u.1, w.2) : Cell) = w from Prod.ext e1 rfl]
    have hww' : IsVertex P (u.1, w'.2) := by
      rwa [show ((u.1, w'.2) : Cell) = w' from Prod.ext f1 rfl]
    rcases lt_trichotomy w.2 w'.2 with hlt | heq | hgt
    · exact absurd hww' (vrunRight_not_vertex hr w'.2 hlt f2)
    · exact Prod.ext (e1.symm.trans f1) heq
    · exact absurd hww (vrunRight_not_vertex hr' w.2 hgt e2)

/-- **Injectivity of the successor**: the incoming arm at a vertex is
    unique as well.  Mirror image of `NextVtx.unique`, with the last step
    of the run playing the role of the first. -/
theorem NextVtx.pred_unique {P : Set Cell} (hfat : Fat 16 P) {u u' w : Cell}
    (h : NextVtx P u w) (h' : NextVtx P u' w) : u = u' := by
  obtain ⟨hu, hw, hcase⟩ := h
  obtain ⟨hu', -, hcase'⟩ := h'
  have hdiagw := hfat.not_diagonal (by norm_num) hw
  rcases hcase with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ <;>
    rcases hcase' with ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ <;>
    [rw [e1] at hr; rw [e1] at hr; rw [e1] at hr; rw [e1] at hr;
     rw [e1] at hr; rw [e1] at hr; rw [e1] at hr; rw [e1] at hr;
     rw [e1] at hr; rw [e1] at hr; rw [e1] at hr; rw [e1] at hr;
     rw [e1] at hr; rw [e1] at hr; rw [e1] at hr; rw [e1] at hr] <;>
    [rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr';
     rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr';
     rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr';
     rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr'; rw [f1] at hr']
  -- E, E
  · have hvu : IsVertex P (u.1, w.2) := by
      rwa [show ((u.1, w.2) : Cell) = u from Prod.ext rfl e1.symm]
    have hvu' : IsVertex P (u'.1, w.2) := by
      rwa [show ((u'.1, w.2) : Cell) = u' from Prod.ext rfl f1.symm]
    rcases lt_trichotomy u.1 u'.1 with hlt | heq | hgt
    · exact absurd hvu' (hrunAbove_not_vertex hr u'.1 hlt f2)
    · exact Prod.ext heq (e1.trans f1.symm)
    · exact absurd hvu (hrunAbove_not_vertex hr' u.1 hgt e2)
  -- E, W: diagonal at w
  · have hE := hr (w.1 - 1) (by omega) (by omega)
    have hW := hr' w.1 le_rfl f2
    exact absurd ⟨iff_of_false hE.2 hW.2, iff_of_true hE.1 hW.1⟩ hdiagw
  -- E, N
  · have hE := hr (w.1 - 1) (by omega) (by omega)
    have hN := hr' (w.2 - 1) (by omega) (by omega)
    exact absurd hN.1 hE.2
  -- E, S
  · have hE := hr (w.1 - 1) (by omega) (by omega)
    have hS := hr' w.2 le_rfl f2
    exact absurd hE.1 hS.2
  -- W, E: diagonal at w
  · have hW := hr w.1 le_rfl e2
    have hE := hr' (w.1 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_false hE.2 hW.2, iff_of_true hE.1 hW.1⟩ hdiagw
  -- W, W
  · have hvu : IsVertex P (u.1, w.2) := by
      rwa [show ((u.1, w.2) : Cell) = u from Prod.ext rfl e1.symm]
    have hvu' : IsVertex P (u'.1, w.2) := by
      rwa [show ((u'.1, w.2) : Cell) = u' from Prod.ext rfl f1.symm]
    rcases lt_trichotomy u.1 u'.1 with hlt | heq | hgt
    · exact absurd hvu (hrunBelow_not_vertex hr' u.1 e2 hlt)
    · exact Prod.ext heq (e1.trans f1.symm)
    · exact absurd hvu' (hrunBelow_not_vertex hr u'.1 f2 hgt)
  -- W, N
  · have hW := hr w.1 le_rfl e2
    have hN := hr' (w.2 - 1) (by omega) (by omega)
    exact absurd hW.1 hN.2
  -- W, S
  · have hW := hr w.1 le_rfl e2
    have hS := hr' w.2 le_rfl f2
    exact absurd hS.1 hW.2
  -- N, E
  · have hN := hr (w.2 - 1) (by omega) (by omega)
    have hE := hr' (w.1 - 1) (by omega) (by omega)
    exact absurd hN.1 hE.2
  -- N, W
  · have hN := hr (w.2 - 1) (by omega) (by omega)
    have hW := hr' w.1 le_rfl f2
    exact absurd hW.1 hN.2
  -- N, N
  · have hvu : IsVertex P (w.1, u.2) := by
      rwa [show ((w.1, u.2) : Cell) = u from Prod.ext e1.symm rfl]
    have hvu' : IsVertex P (w.1, u'.2) := by
      rwa [show ((w.1, u'.2) : Cell) = u' from Prod.ext f1.symm rfl]
    rcases lt_trichotomy u.2 u'.2 with hlt | heq | hgt
    · exact absurd hvu' (vrunLeft_not_vertex hr u'.2 hlt f2)
    · exact Prod.ext (e1.trans f1.symm) heq
    · exact absurd hvu (vrunLeft_not_vertex hr' u.2 hgt e2)
  -- N, S: diagonal at w
  · have hN := hr (w.2 - 1) (by omega) (by omega)
    have hS := hr' w.2 le_rfl f2
    exact absurd ⟨iff_of_true hN.1 hS.1, iff_of_false hS.2 hN.2⟩ hdiagw
  -- S, E
  · have hS := hr w.2 le_rfl e2
    have hE := hr' (w.1 - 1) (by omega) (by omega)
    exact absurd hE.1 hS.2
  -- S, W
  · have hS := hr w.2 le_rfl e2
    have hW := hr' w.1 le_rfl f2
    exact absurd hS.1 hW.2
  -- S, N: diagonal at w
  · have hS := hr w.2 le_rfl e2
    have hN := hr' (w.2 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_true hN.1 hS.1, iff_of_false hS.2 hN.2⟩ hdiagw
  -- S, S
  · have hvu : IsVertex P (w.1, u.2) := by
      rwa [show ((w.1, u.2) : Cell) = u from Prod.ext e1.symm rfl]
    have hvu' : IsVertex P (w.1, u'.2) := by
      rwa [show ((w.1, u'.2) : Cell) = u' from Prod.ext f1.symm rfl]
    rcases lt_trichotomy u.2 u'.2 with hlt | heq | hgt
    · exact absurd hvu (vrunRight_not_vertex hr' u.2 e2 hlt)
    · exact Prod.ext (e1.trans f1.symm) heq
    · exact absurd hvu' (vrunRight_not_vertex hr u'.2 f2 hgt)

/-- A finite polyomino has finitely many vertices: every vertex has one of
    its four incident cells in `P`. -/
lemma vertexSet_finite {P : Set Cell} (hfin : P.Finite) :
    {v : Cell | IsVertex P v}.Finite := by
  apply Set.Finite.subset
    (((hfin.union (hfin.image fun p => (p.1 + 1, p.2))).union
      (hfin.image fun p => (p.1, p.2 + 1))).union
      (hfin.image fun p => (p.1 + 1, p.2 + 1)))
  intro v hv
  by_cases hNE : (v.1, v.2) ∈ P
  · exact Or.inl (Or.inl (Or.inl (by rwa [show ((v.1, v.2) : Cell) = v from
      Prod.ext rfl rfl] at hNE)))
  by_cases hNW : (v.1 - 1, v.2) ∈ P
  · exact Or.inl (Or.inl (Or.inr ⟨_, hNW,
      Prod.ext (show v.1 - 1 + 1 = v.1 by ring) rfl⟩))
  by_cases hSE : (v.1, v.2 - 1) ∈ P
  · exact Or.inl (Or.inr ⟨_, hSE,
      Prod.ext rfl (show v.2 - 1 + 1 = v.2 by ring)⟩)
  by_cases hSW : (v.1 - 1, v.2 - 1) ∈ P
  · exact Or.inr ⟨_, hSW,
      Prod.ext (show v.1 - 1 + 1 = v.1 by ring)
        (show v.2 - 1 + 1 = v.2 by ring)⟩
  exact absurd ⟨iff_of_false hSW hSE, iff_of_false hNW hNE⟩ hv.1

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

/-- **Edges are long**: an edge of a 16-fat polyomino has length at least
    16 — a turn any earlier would put a vertex inside the box of `u`,
    where both cell columns (rows) beside the would-be turn lie on the
    same side of the quadrant and so carry identical membership. -/
theorem NextVtx.far {P : Set Cell} (hfat : Fat 16 P) {u w : Cell}
    (h : NextVtx P u w) :
    (u.2 = w.2 ∧ u.1 + 16 ≤ w.1 ∧ HRunAbove P u.2 u.1 w.1) ∨
    (u.2 = w.2 ∧ w.1 + 16 ≤ u.1 ∧ HRunBelow P u.2 w.1 u.1) ∨
    (u.1 = w.1 ∧ u.2 + 16 ≤ w.2 ∧ VRunLeft P u.1 u.2 w.2) ∨
    (u.1 = w.1 ∧ w.2 + 16 ≤ u.2 ∧ VRunRight P u.1 w.2 u.2) := by
  rcases h.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
  · refine Or.inl ⟨e1, ?_, hr⟩
    by_contra hlt
    push_neg at hlt
    obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h.1
    · have hQ : ∀ y' : ℤ,
          ((w.1 - 1, y') ∈ quadrant u c ↔ (w.1, y') ∈ quadrant u c) := by
        intro y'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).trans
          (hQ w.2)).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1, w.2 - 1) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ (w.2 - 1))).trans
          (hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.1 ⟨hr2, hr1⟩
    · have hQ : ∀ y' : ℤ,
          ((w.1 - 1, y') ∈ quadrant u c ↔ (w.1, y') ∈ quadrant u c) := by
        intro y'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ w.2))).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1, w.2 - 1) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ (w.2 - 1)))).trans
          (hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.1 ⟨hr2, hr1⟩
  · refine Or.inr (Or.inl ⟨e1, ?_, hr⟩)
    by_contra hlt
    push_neg at hlt
    obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h.1
    · have hQ : ∀ y' : ℤ,
          ((w.1 - 1, y') ∈ quadrant u c ↔ (w.1, y') ∈ quadrant u c) := by
        intro y'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).trans
          (hQ w.2)).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1, w.2 - 1) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ (w.2 - 1))).trans
          (hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.1 ⟨hr2, hr1⟩
    · have hQ : ∀ y' : ℤ,
          ((w.1 - 1, y') ∈ quadrant u c ↔ (w.1, y') ∈ quadrant u c) := by
        intro y'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ w.2))).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1, w.2 - 1) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ (w.2 - 1)))).trans
          (hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.1 ⟨hr2, hr1⟩
  · refine Or.inr (Or.inr (Or.inl ⟨e1, ?_, hr⟩))
    by_contra hlt
    push_neg at hlt
    obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h.1
    · have hQ : ∀ x' : ℤ,
          ((x', w.2 - 1) ∈ quadrant u c ↔ (x', w.2) ∈ quadrant u c) := by
        intro x'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1 - 1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ (w.1 - 1))).trans
          (hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1, w.2 - 1) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ w.1)).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.2 ⟨hr1, hr2⟩
    · have hQ : ∀ x' : ℤ,
          ((x', w.2 - 1) ∈ quadrant u c ↔ (x', w.2) ∈ quadrant u c) := by
        intro x'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1 - 1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ (w.1 - 1)))).trans
          (hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1, w.2 - 1) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ w.1))).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.2 ⟨hr1, hr2⟩
  · refine Or.inr (Or.inr (Or.inr ⟨e1, ?_, hr⟩))
    by_contra hlt
    push_neg at hlt
    obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h.1
    · have hQ : ∀ x' : ℤ,
          ((x', w.2 - 1) ∈ quadrant u c ↔ (x', w.2) ∈ quadrant u c) := by
        intro x'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1 - 1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ (w.1 - 1))).trans
          (hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1, w.2 - 1) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (hQ w.1)).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.2 ⟨hr1, hr2⟩
    · have hQ : ∀ x' : ℤ,
          ((x', w.2 - 1) ∈ quadrant u c ↔ (x', w.2) ∈ quadrant u c) := by
        intro x'
        cases c <;> simp only [quadrant, Set.mem_setOf_eq] <;> omega
      have hr1 : ((w.1 - 1, w.2 - 1) ∈ P ↔ (w.1 - 1, w.2) ∈ P) :=
        ((hcc (w.1 - 1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ (w.1 - 1)))).trans
          (hcc (w.1 - 1, w.2) (by simp only [box, mem_rect]; omega)).symm
      have hr2 : ((w.1, w.2 - 1) ∈ P ↔ (w.1, w.2) ∈ P) :=
        ((hcc (w.1, w.2 - 1) (by simp only [box, mem_rect]; omega)).trans
          (not_congr (hQ w.1))).trans
          (hcc (w.1, w.2) (by simp only [box, mem_rect]; omega)).symm
      exact h.2.1.2 ⟨hr1, hr2⟩

-- ------------------------------------------------------------
-- Boundary segments of `P`, as curve data for the parity toolkit
-- ------------------------------------------------------------

/-- The vertical boundary segments of `P`: `(x, y) ∈ bndV P` iff the unit
    segment on the grid line `x` between the cells `(x-1, y)` and `(x, y)`
    separates `P` from its complement. -/
def bndV (P : Set Cell) : Set (ℤ × ℤ) :=
  {t | ¬((t.1 - 1, t.2) ∈ P ↔ (t.1, t.2) ∈ P)}

/-- The horizontal boundary segments of `P`: `(x, y) ∈ bndH P` iff the
    unit segment on the grid row `y` between the cells `(x, y-1)` and
    `(x, y)` separates `P` from its complement. -/
def bndH (P : Set Cell) : Set (ℤ × ℤ) :=
  {t | ¬((t.1, t.2 - 1) ∈ P ↔ (t.1, t.2) ∈ P)}

lemma bndV_finite {P : Set Cell} (hfin : P.Finite) : (bndV P).Finite := by
  apply Set.Finite.subset (hfin.union (hfin.image fun p => (p.1 + 1, p.2)))
  intro t ht
  by_cases h : (t.1, t.2) ∈ P
  · exact Or.inl (by rwa [show ((t.1, t.2) : Cell) = t from Prod.ext rfl rfl]
      at h)
  · have h' : (t.1 - 1, t.2) ∈ P := by
      by_contra h''
      exact ht (iff_of_false h'' h)
    exact Or.inr ⟨_, h', Prod.ext (show t.1 - 1 + 1 = t.1 by ring) rfl⟩

lemma bndH_finite {P : Set Cell} (hfin : P.Finite) : (bndH P).Finite := by
  apply Set.Finite.subset (hfin.union (hfin.image fun p => (p.1, p.2 + 1)))
  intro t ht
  by_cases h : (t.1, t.2) ∈ P
  · exact Or.inl (by rwa [show ((t.1, t.2) : Cell) = t from Prod.ext rfl rfl]
      at h)
  · have h' : (t.1, t.2 - 1) ∈ P := by
      by_contra h''
      exact ht (iff_of_false h'' h)
    exact Or.inr ⟨_, h', Prod.ext rfl (show t.2 - 1 + 1 = t.2 by ring)⟩

/-- **The full boundary has even degree at every grid point** — a free
    mod-2 identity of the 2×2 membership pattern, with no hypothesis on
    `P` whatsoever. -/
lemma bnd_degree (P : Set Cell) (x y : ℤ) :
    (((x, y) ∈ bndV P) ↔ ((x, y - 1) ∈ bndV P)) ↔
      (((x, y) ∈ bndH P) ↔ ((x - 1, y) ∈ bndH P)) := by
  simp only [bndV, bndH, Set.mem_setOf_eq]
  tauto

-- ============================================================
-- §6 Ray-crossing parity: the abstract toolkit
-- ============================================================
--
-- For the single-boundary-cycle theorem.  A *curve* is presented by two
-- sets of unit segments: `V ⊆ ℤ × ℤ` (the pair `(x, y)` denotes the
-- vertical segment on the grid line `x` between the cells `(x-1, y)` and
-- `(x, y)`) and `H` (the pair `(x, y)` denotes the horizontal segment on
-- the grid row `y` between the cells `(x, y-1)` and `(x, y)`).  The only
-- global hypothesis is the **even-degree identity** at every grid point.
-- The parity of the number of crossings of the rightward ray from a cell
-- then changes exactly when the cell moves across a segment of the curve.

/-- The crossings of the rightward ray from the cell `(a, b)` with the
    vertical segments `V`: the abscissas `x > a` with `(x, b) ∈ V`. -/
def rayCross (V : Set (ℤ × ℤ)) (a b : ℤ) : Set ℤ :=
  {x : ℤ | a < x ∧ (x, b) ∈ V}

lemma rayCross_finite {V : Set (ℤ × ℤ)} (hV : V.Finite) (a b : ℤ) :
    (rayCross V a b).Finite := by
  apply Set.Finite.subset ((hV.inter_of_left {t | t.2 = b}).image Prod.fst)
  rintro x ⟨h1, h2⟩
  exact ⟨(x, b), ⟨h2, rfl⟩, rfl⟩

/-- The crossings within the window `(a, t]`. -/
private def raySeg (V : Set (ℤ × ℤ)) (a t r : ℤ) : Set ℤ :=
  {x : ℤ | a < x ∧ x ≤ t ∧ (x, r) ∈ V}

private lemma raySeg_finite (V : Set (ℤ × ℤ)) (a t r : ℤ) :
    (raySeg V a t r).Finite := by
  apply (Set.finite_Icc (a + 1) t).subset
  rintro x ⟨h1, h2, -⟩
  exact Set.mem_Icc.mpr ⟨by omega, h2⟩

private lemma raySeg_base (V : Set (ℤ × ℤ)) (a r : ℤ) :
    raySeg V a a r = ∅ := by
  ext x
  simp only [raySeg, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2, -⟩
  omega

private lemma raySeg_succ_mem {V : Set (ℤ × ℤ)} {a t r : ℤ} (hat : a ≤ t)
    (h : (t + 1, r) ∈ V) :
    (raySeg V a (t + 1) r).ncard = (raySeg V a t r).ncard + 1 := by
  have heq : raySeg V a (t + 1) r = insert (t + 1) (raySeg V a t r) := by
    ext x
    simp only [raySeg, Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hx : x = t + 1
      · exact Or.inl hx
      · exact Or.inr ⟨h1, by omega, h3⟩
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨by omega, le_rfl, h⟩
      · exact ⟨h1, by omega, h3⟩
  rw [heq, Set.ncard_insert_of_notMem
    (fun hx => by simp only [raySeg, Set.mem_setOf_eq] at hx; omega)
    (raySeg_finite _ _ _ _)]

private lemma raySeg_succ_not_mem {V : Set (ℤ × ℤ)} {a t r : ℤ}
    (h : (t + 1, r) ∉ V) :
    raySeg V a (t + 1) r = raySeg V a t r := by
  ext x
  simp only [raySeg, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    by_cases hx : x = t + 1
    · subst hx
      exact absurd h3 h
    · omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by omega, h3⟩

private lemma rayCross_eq_raySeg {V : Set (ℤ × ℤ)} {a b M : ℤ}
    (hM : ∀ t ∈ V, t.1 ≤ M) :
    rayCross V a b = raySeg V a M b := by
  ext x
  simp only [rayCross, raySeg, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, hM _ h2, h2⟩
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩

/-- **Horizontal parity step.**  The crossing counts of two horizontally
    adjacent cells have even sum iff the vertical segment between the two
    cells is not on the curve. -/
lemma even_rayCross_add_right {V : Set (ℤ × ℤ)} (hV : V.Finite) (a b : ℤ) :
    (Even ((rayCross V a b).ncard + (rayCross V (a + 1) b).ncard)) ↔
      (a + 1, b) ∉ V := by
  by_cases h : (a + 1, b) ∈ V
  · have heq : rayCross V a b = insert (a + 1) (rayCross V (a + 1) b) := by
      ext x
      simp only [rayCross, Set.mem_setOf_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hx : x = a + 1
        · exact Or.inl hx
        · exact Or.inr ⟨by omega, h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨by omega, h⟩
        · exact ⟨by omega, h2⟩
    refine iff_of_false (fun hev => ?_) (not_not_intro h)
    rw [heq, Set.ncard_insert_of_notMem
      (fun hx => by simp only [rayCross, Set.mem_setOf_eq] at hx; omega)
      (rayCross_finite hV _ _)] at hev
    rw [Nat.even_iff] at hev
    omega
  · have heq : rayCross V a b = rayCross V (a + 1) b := by
      ext x
      simp only [rayCross, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        by_cases hx : x = a + 1
        · subst hx
          exact absurd h2 h
        · omega
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    refine iff_of_true ?_ h
    rw [heq]
    exact ⟨(rayCross V (a + 1) b).ncard, rfl⟩

/-- **Vertical parity step.**  Under the even-degree identity, the
    crossing counts of two vertically adjacent cells have even sum iff the
    horizontal segment between the two cells is not on the curve.  Proved
    by telescoping the even-degree identity along the row. -/
lemma even_rayCross_add_up {V H : Set (ℤ × ℤ)} (hV : V.Finite) (hH : H.Finite)
    (hdeg : ∀ x y : ℤ, (((x, y) ∈ V) ↔ ((x, y - 1) ∈ V)) ↔
      (((x, y) ∈ H) ↔ ((x - 1, y) ∈ H)))
    (a b : ℤ) :
    (Even ((rayCross V a b).ncard + (rayCross V a (b + 1)).ncard)) ↔
      (a, b + 1) ∉ H := by
  obtain ⟨M0, hM0⟩ := ((hV.union hH).image Prod.fst).bddAbove
  have hMV : ∀ t ∈ V, t.1 ≤ max a M0 + 1 := fun t ht => by
    have h' : t.1 ≤ M0 := hM0 ⟨t, Or.inl ht, rfl⟩
    omega
  have hMnotH : (max a M0 + 1, b + 1) ∉ H := fun hmem => by
    have h' : max a M0 + 1 ≤ M0 := hM0 ⟨_, Or.inr hmem, rfl⟩
    omega
  -- the invariant, telescoped from `a` to the end of the support
  have key : ∀ t, a ≤ t →
      ((Even ((raySeg V a t b).ncard + (raySeg V a t (b + 1)).ncard)) ↔
        (((a, b + 1) ∈ H) ↔ ((t, b + 1) ∈ H))) := by
    intro t ht
    induction t, ht using Int.le_induction with
    | base =>
      rw [raySeg_base, raySeg_base]
      simp
    | succ n hn ih =>
      have hdeg' := hdeg (n + 1) (b + 1)
      rw [show b + 1 - 1 = b from by ring,
        show n + 1 - 1 = n from by ring] at hdeg'
      by_cases h1 : (n + 1, b) ∈ V <;> by_cases h2 : (n + 1, b + 1) ∈ V
      · have hHiff : ((n + 1, b + 1) ∈ H ↔ (n, b + 1) ∈ H) :=
          hdeg'.mp (iff_of_true h2 h1)
        have hpar : Even ((raySeg V a (n + 1) b).ncard +
              (raySeg V a (n + 1) (b + 1)).ncard) ↔
            Even ((raySeg V a n b).ncard + (raySeg V a n (b + 1)).ncard) := by
          rw [raySeg_succ_mem hn h1, raySeg_succ_mem hn h2,
            Nat.even_iff, Nat.even_iff]
          omega
        rw [hpar, ih]
        clear hpar ih
        tauto
      · have hHiff : ¬((n + 1, b + 1) ∈ H ↔ (n, b + 1) ∈ H) :=
          fun hiff => h2 ((hdeg'.mpr hiff).mpr h1)
        have hpar : Even ((raySeg V a (n + 1) b).ncard +
              (raySeg V a (n + 1) (b + 1)).ncard) ↔
            ¬Even ((raySeg V a n b).ncard + (raySeg V a n (b + 1)).ncard) := by
          rw [raySeg_succ_mem hn h1, raySeg_succ_not_mem h2,
            Nat.even_iff, Nat.even_iff]
          omega
        rw [hpar, ih]
        clear hpar ih
        tauto
      · have hHiff : ¬((n + 1, b + 1) ∈ H ↔ (n, b + 1) ∈ H) :=
          fun hiff => h1 ((hdeg'.mpr hiff).mp h2)
        have hpar : Even ((raySeg V a (n + 1) b).ncard +
              (raySeg V a (n + 1) (b + 1)).ncard) ↔
            ¬Even ((raySeg V a n b).ncard + (raySeg V a n (b + 1)).ncard) := by
          rw [raySeg_succ_not_mem h1, raySeg_succ_mem hn h2,
            Nat.even_iff, Nat.even_iff]
          omega
        rw [hpar, ih]
        clear hpar ih
        tauto
      · have hHiff : ((n + 1, b + 1) ∈ H ↔ (n, b + 1) ∈ H) :=
          hdeg'.mp (iff_of_false h2 h1)
        have hpar : Even ((raySeg V a (n + 1) b).ncard +
              (raySeg V a (n + 1) (b + 1)).ncard) ↔
            Even ((raySeg V a n b).ncard + (raySeg V a n (b + 1)).ncard) := by
          rw [raySeg_succ_not_mem h1, raySeg_succ_not_mem h2]
        rw [hpar, ih]
        clear hpar ih
        tauto
  have hfin := key (max a M0 + 1) (by have := le_max_left a M0; omega)
  rw [rayCross_eq_raySeg hMV, rayCross_eq_raySeg hMV, hfin]
  exact ⟨fun hiff hmem => hMnotH (hiff.mp hmem),
    fun hn => iff_of_false hn hMnotH⟩

-- ============================================================
-- §7 The curve of a closed vertex family; the boundary is one cycle
-- ============================================================
--
-- A family `S` of vertices that is closed under the successor and the
-- predecessor spans a *curve*: the segments of the edges `(u, next u)`
-- for `u ∈ S`.  The curve is contained in the boundary; the key locality
-- lemma says that at every grid point it is either absent or agrees with
-- the *whole* boundary — which gives it the even-degree property, so the
-- ray-crossing parity toolkit applies.  Parity is constant on `P` and on
-- `Pᶜ` (steps inside either never cross the boundary), flips across
-- curve segments and is preserved across boundary segments *not* on the
-- curve; connectivity of `P` and `Pᶜ` then forces every boundary segment
-- onto the curve, and every vertex into `S`: the boundary is one cycle.

/-- The vertical segments of the curve spanned by `S`: those on a
    (necessarily vertical) edge `(u, next u)` with `u ∈ S`.  For a
    horizontal edge `u.2 = w.2` makes both intervals empty. -/
def curveV (P : Set Cell) (S : Set Cell) : Set (ℤ × ℤ) :=
  {t | ∃ u ∈ S, ∃ w, NextVtx P u w ∧ t.1 = u.1 ∧
    ((u.2 ≤ t.2 ∧ t.2 < w.2) ∨ (w.2 ≤ t.2 ∧ t.2 < u.2))}

/-- The horizontal segments of the curve spanned by `S`. -/
def curveH (P : Set Cell) (S : Set Cell) : Set (ℤ × ℤ) :=
  {t | ∃ u ∈ S, ∃ w, NextVtx P u w ∧ t.2 = u.2 ∧
    ((u.1 ≤ t.1 ∧ t.1 < w.1) ∨ (w.1 ≤ t.1 ∧ t.1 < u.1))}

/-- Curve segments are boundary segments. -/
lemma curveV_subset_bndV (P : Set Cell) (S : Set Cell) :
    curveV P S ⊆ bndV P := by
  rintro ⟨sx, sy⟩ ⟨u, huS, w, hnw, hcoord, hint⟩
  obtain ⟨-, -, hcase⟩ := hnw
  have hc : sx = u.1 := hcoord
  subst hc
  rcases hcase with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
  · exact absurd hint (by omega)
  · exact absurd hint (by omega)
  · have hy : u.2 ≤ sy ∧ sy < w.2 := by
      rcases hint with h | h
      · exact h
      · omega
    have hval := hr sy hy.1 hy.2
    exact fun hiff => hval.2 (hiff.mp hval.1)
  · have hy : w.2 ≤ sy ∧ sy < u.2 := by
      rcases hint with h | h
      · omega
      · exact h
    have hval := hr sy hy.1 hy.2
    exact fun hiff => hval.2 (hiff.mpr hval.1)

/-- Curve segments are boundary segments. -/
lemma curveH_subset_bndH (P : Set Cell) (S : Set Cell) :
    curveH P S ⊆ bndH P := by
  rintro ⟨sx, sy⟩ ⟨u, huS, w, hnw, hcoord, hint⟩
  obtain ⟨-, -, hcase⟩ := hnw
  have hc : sy = u.2 := hcoord
  subst hc
  rcases hcase with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
  · have hx : u.1 ≤ sx ∧ sx < w.1 := by
      rcases hint with h | h
      · exact h
      · omega
    have hval := hr sx hx.1 hx.2
    exact fun hiff => hval.2 (hiff.mpr hval.1)
  · have hx : w.1 ≤ sx ∧ sx < u.1 := by
      rcases hint with h | h
      · omega
      · exact h
    have hval := hr sx hx.1 hx.2
    exact fun hiff => hval.2 (hiff.mp hval.1)
  · exact absurd hint (by omega)
  · exact absurd hint (by omega)

lemma curveV_finite {P : Set Cell} (hfin : P.Finite) (S : Set Cell) :
    (curveV P S).Finite :=
  (bndV_finite hfin).subset (curveV_subset_bndV P S)

lemma curveH_finite {P : Set Cell} (hfin : P.Finite) (S : Set Cell) :
    (curveH P S).Finite :=
  (bndH_finite hfin).subset (curveH_subset_bndH P S)

/-- **Governing edge, vertical.**  Every vertical boundary segment lies on
    an edge of the boundary walk: walk to both ends of its straight run. -/
lemma govern_V {P : Set Cell} (hfin : P.Finite) {x y : ℤ}
    (hbnd : (x, y) ∈ bndV P) :
    ∃ u w : Cell, NextVtx P u w ∧ u.1 = x ∧
      ((u.2 ≤ y ∧ y < w.2) ∨ (w.2 ≤ y ∧ y < u.2)) := by
  by_cases h : (x, y) ∈ P
  · -- interior to the east: the edge is walked south
    have h' : (x - 1, y) ∉ P := fun hm => hbnd (iff_of_true hm h)
    obtain ⟨yn, hgt, hrunN, hvtxN⟩ := walk_north' hfin ⟨h, h'⟩
    have hcell : (x, y + 1 - 1) ∈ P ∧ (x - 1, y + 1 - 1) ∉ P := by
      rw [show y + 1 - 1 = y from by ring]
      exact ⟨h, h'⟩
    obtain ⟨ys, hlt, hrunS, hvtxS⟩ := walk_south hfin hcell
    have hrun : VRunRight P x ys yn := by
      intro y' h1 h2
      rcases (by omega : y' ≤ y ∨ y < y') with hc | hc
      · exact hrunS y' h1 (by omega)
      · exact hrunN y' (by omega) h2
    exact ⟨(x, yn), (x, ys), ⟨hvtxN, hvtxS,
      Or.inr (Or.inr (Or.inr ⟨rfl, show ys < yn by omega, hrun⟩))⟩, rfl,
      Or.inr ⟨show ys ≤ y by omega, hgt⟩⟩
  · -- interior to the west: the edge is walked north
    have h' : (x - 1, y) ∈ P := by
      by_contra h''
      exact hbnd (iff_of_false h'' h)
    obtain ⟨ys, hle, hrunS, hvtxS⟩ := walk_south' hfin ⟨h', h⟩
    obtain ⟨yn, hgt, hrunN, hvtxN⟩ := walk_north hfin ⟨h', h⟩
    have hrun : VRunLeft P x ys yn := by
      intro y' h1 h2
      rcases (by omega : y' ≤ y ∨ y < y') with hc | hc
      · exact hrunS y' h1 (by omega)
      · exact hrunN y' (by omega) h2
    exact ⟨(x, ys), (x, yn), ⟨hvtxS, hvtxN,
      Or.inr (Or.inr (Or.inl ⟨rfl, show ys < yn by omega, hrun⟩))⟩, rfl,
      Or.inl ⟨hle, hgt⟩⟩

/-- **Governing edge, horizontal.** -/
lemma govern_H {P : Set Cell} (hfin : P.Finite) {x y : ℤ}
    (hbnd : (x, y) ∈ bndH P) :
    ∃ u w : Cell, NextVtx P u w ∧ u.2 = y ∧
      ((u.1 ≤ x ∧ x < w.1) ∨ (w.1 ≤ x ∧ x < u.1)) := by
  by_cases h : (x, y) ∈ P
  · -- interior above: the edge is walked east
    have h' : (x, y - 1) ∉ P := fun hm => hbnd (iff_of_true hm h)
    obtain ⟨xw, hle, hrunW, hvtxW⟩ := walk_west' hfin ⟨h, h'⟩
    obtain ⟨xe, hgt, hrunE, hvtxE⟩ := walk_east hfin ⟨h, h'⟩
    have hrun : HRunAbove P y xw xe := by
      intro x' h1 h2
      rcases (by omega : x' ≤ x ∨ x < x') with hc | hc
      · exact hrunW x' h1 (by omega)
      · exact hrunE x' (by omega) h2
    exact ⟨(xw, y), (xe, y), ⟨hvtxW, hvtxE,
      Or.inl ⟨rfl, show xw < xe by omega, hrun⟩⟩, rfl,
      Or.inl ⟨hle, hgt⟩⟩
  · -- interior below: the edge is walked west
    have h' : (x, y - 1) ∈ P := by
      by_contra h''
      exact hbnd (iff_of_false h'' h)
    obtain ⟨xe, hgt, hrunE, hvtxE⟩ := walk_east' hfin ⟨h', h⟩
    have hcell : (x + 1 - 1, y - 1) ∈ P ∧ (x + 1 - 1, y) ∉ P := by
      rw [show x + 1 - 1 = x from by ring]
      exact ⟨h', h⟩
    obtain ⟨xw, hlt, hrunW, hvtxW⟩ := walk_west hfin hcell
    have hrun : HRunBelow P y xw xe := by
      intro x' h1 h2
      rcases (by omega : x' ≤ x ∨ x < x') with hc | hc
      · exact hrunW x' h1 (by omega)
      · exact hrunE x' (by omega) h2
    exact ⟨(xe, y), (xw, y), ⟨hvtxE, hvtxW,
      Or.inr (Or.inl ⟨rfl, show xw < xe by omega, hrun⟩)⟩, rfl,
      Or.inr ⟨show xw ≤ x by omega, hgt⟩⟩

-- Oriented governing edges: like `govern_V`/`govern_H`, but keyed to the
-- side of the interior, returning the run and both endpoint coordinates.

/-- The maximal edge through a horizontal boundary segment with the
    interior above (an east edge). -/
lemma govern_H_above {P : Set Cell} (hfin : P.Finite) {x y : ℤ}
    (h1 : (x, y) ∈ P) (h2 : (x, y - 1) ∉ P) :
    ∃ u w : Cell, NextVtx P u w ∧ u.2 = y ∧ w.2 = y ∧
      u.1 ≤ x ∧ x < w.1 ∧ HRunAbove P y u.1 w.1 := by
  obtain ⟨xw, hle, hrunW, hvtxW⟩ := walk_west' hfin ⟨h1, h2⟩
  obtain ⟨xe, hgt, hrunE, hvtxE⟩ := walk_east hfin ⟨h1, h2⟩
  have hrun : HRunAbove P y xw xe := by
    intro x' hx1 hx2
    rcases (by omega : x' ≤ x ∨ x < x') with hc | hc
    · exact hrunW x' hx1 (by omega)
    · exact hrunE x' (by omega) hx2
  exact ⟨(xw, y), (xe, y), ⟨hvtxW, hvtxE,
    Or.inl ⟨rfl, show xw < xe by omega, hrun⟩⟩, rfl, rfl, hle, hgt, hrun⟩

/-- The maximal edge through a horizontal boundary segment with the
    interior below (a west edge). -/
lemma govern_H_below {P : Set Cell} (hfin : P.Finite) {x y : ℤ}
    (h1 : (x, y - 1) ∈ P) (h2 : (x, y) ∉ P) :
    ∃ u w : Cell, NextVtx P u w ∧ u.2 = y ∧ w.2 = y ∧
      w.1 ≤ x ∧ x < u.1 ∧ HRunBelow P y w.1 u.1 := by
  obtain ⟨xe, hgt, hrunE, hvtxE⟩ := walk_east' hfin ⟨h1, h2⟩
  have hcell : (x + 1 - 1, y - 1) ∈ P ∧ (x + 1 - 1, y) ∉ P := by
    rw [show x + 1 - 1 = x from by ring]
    exact ⟨h1, h2⟩
  obtain ⟨xw, hlt, hrunW, hvtxW⟩ := walk_west hfin hcell
  have hrun : HRunBelow P y xw xe := by
    intro x' hx1 hx2
    rcases (by omega : x' ≤ x ∨ x < x') with hc | hc
    · exact hrunW x' hx1 (by omega)
    · exact hrunE x' (by omega) hx2
  exact ⟨(xe, y), (xw, y), ⟨hvtxE, hvtxW,
    Or.inr (Or.inl ⟨rfl, show xw < xe by omega, hrun⟩)⟩, rfl, rfl,
    show xw ≤ x by omega, hgt, hrun⟩

/-- The maximal edge through a vertical boundary segment with the interior
    to the west (a north edge). -/
lemma govern_V_left {P : Set Cell} (hfin : P.Finite) {x y : ℤ}
    (h1 : (x - 1, y) ∈ P) (h2 : (x, y) ∉ P) :
    ∃ u w : Cell, NextVtx P u w ∧ u.1 = x ∧ w.1 = x ∧
      u.2 ≤ y ∧ y < w.2 ∧ VRunLeft P x u.2 w.2 := by
  obtain ⟨ys, hle, hrunS, hvtxS⟩ := walk_south' hfin ⟨h1, h2⟩
  obtain ⟨yn, hgt, hrunN, hvtxN⟩ := walk_north hfin ⟨h1, h2⟩
  have hrun : VRunLeft P x ys yn := by
    intro y' hy1 hy2
    rcases (by omega : y' ≤ y ∨ y < y') with hc | hc
    · exact hrunS y' hy1 (by omega)
    · exact hrunN y' (by omega) hy2
  exact ⟨(x, ys), (x, yn), ⟨hvtxS, hvtxN,
    Or.inr (Or.inr (Or.inl ⟨rfl, show ys < yn by omega, hrun⟩))⟩, rfl, rfl,
    hle, hgt, hrun⟩

/-- The maximal edge through a vertical boundary segment with the interior
    to the east (a south edge). -/
lemma govern_V_right {P : Set Cell} (hfin : P.Finite) {x y : ℤ}
    (h1 : (x, y) ∈ P) (h2 : (x - 1, y) ∉ P) :
    ∃ u w : Cell, NextVtx P u w ∧ u.1 = x ∧ w.1 = x ∧
      w.2 ≤ y ∧ y < u.2 ∧ VRunRight P x w.2 u.2 := by
  obtain ⟨yn, hgt, hrunN, hvtxN⟩ := walk_north' hfin ⟨h1, h2⟩
  have hcell : (x, y + 1 - 1) ∈ P ∧ (x - 1, y + 1 - 1) ∉ P := by
    rw [show y + 1 - 1 = y from by ring]
    exact ⟨h1, h2⟩
  obtain ⟨ys, hlt, hrunS, hvtxS⟩ := walk_south hfin hcell
  have hrun : VRunRight P x ys yn := by
    intro y' hy1 hy2
    rcases (by omega : y' ≤ y ∨ y < y') with hc | hc
    · exact hrunS y' hy1 (by omega)
    · exact hrunN y' (by omega) hy2
  exact ⟨(x, yn), (x, ys), ⟨hvtxN, hvtxS,
    Or.inr (Or.inr (Or.inr ⟨rfl, show ys < yn by omega, hrun⟩))⟩, rfl, rfl,
    show ys ≤ y by omega, hgt, hrun⟩

-- ------------------------------------------------------------
-- The bands along an edge: the interior side is full for 15 rows,
-- the exterior side empty for 15 rows.  Fatness enters through the
-- column/row monotonicity at the edge's own vertices or at the
-- vertices of the offending governing edge.
-- ------------------------------------------------------------

/-- The 15 rows above an east edge lie in `P`. -/
lemma band_in_east {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (h : NextVtx P u w) (he : u.2 = w.2) (hlt : u.1 < w.1) :
    ∀ x k : ℤ, u.1 ≤ x → x < w.1 → 0 ≤ k → k < 15 → (x, u.2 + k) ∈ P := by
  have hr : HRunAbove P u.2 u.1 w.1 := by
    rcases h.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
    · exact hr
    · omega
    · omega
    · omega
  intro x k hx1 hx2 hk0 hk15
  by_contra hnot
  obtain ⟨k', ⟨hk'0, hk'not⟩, hleast⟩ :=
    Int.exists_least_of_bdd (P := fun j => 0 ≤ j ∧ (x, u.2 + j) ∉ P)
      ⟨0, fun _ hz => hz.1⟩ ⟨k, hk0, hnot⟩
  have hk'k : k' ≤ k := hleast k ⟨hk0, hnot⟩
  have hk'1 : 1 ≤ k' := by
    rcases eq_or_lt_of_le hk'0 with heq | hpos
    · rw [← heq, add_zero] at hk'not
      exact absurd (hr x hx1 hx2).1 hk'not
    · omega
  have hprev : (x, u.2 + k' - 1) ∈ P := by
    by_contra hp
    have := hleast (k' - 1) ⟨by omega, by
      rw [show u.2 + (k' - 1) = u.2 + k' - 1 from by ring]
      exact hp⟩
    omega
  obtain ⟨u', w', hnw', hu2', hw2', hwx', hux', hr'⟩ :=
    govern_H_below hfin hprev hk'not
  rcases (by omega : w'.1 ≤ u.1 ∨ u.1 < w'.1) with hcase | hcase
  · have hup := hr' u.1 hcase (by omega)
    have hlo := hr u.1 le_rfl hlt
    exact hfat.column_no_bump h.1 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hlo.2 hlo.1 hup.2
  · have hup := hr' w'.1 le_rfl (by omega)
    have hlo := hr w'.1 (by omega) (by omega)
    exact hfat.column_no_bump hnw'.2.1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hlo.2 hlo.1 hup.2

/-- The 15 rows below an east edge avoid `P`. -/
lemma band_out_east {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (h : NextVtx P u w) (he : u.2 = w.2) (hlt : u.1 < w.1) :
    ∀ x k : ℤ, u.1 ≤ x → x < w.1 → 0 ≤ k → k < 15 →
      (x, u.2 - 1 - k) ∉ P := by
  have hr : HRunAbove P u.2 u.1 w.1 := by
    rcases h.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
    · exact hr
    · omega
    · omega
    · omega
  intro x k hx1 hx2 hk0 hk15 hmem
  obtain ⟨k', ⟨hk'0, hk'mem⟩, hleast⟩ :=
    Int.exists_least_of_bdd (P := fun j => 0 ≤ j ∧ (x, u.2 - 1 - j) ∈ P)
      ⟨0, fun _ hz => hz.1⟩ ⟨k, hk0, hmem⟩
  have hk'k : k' ≤ k := hleast k ⟨hk0, hmem⟩
  have hk'1 : 1 ≤ k' := by
    rcases eq_or_lt_of_le hk'0 with heq | hpos
    · rw [← heq, sub_zero] at hk'mem
      exact absurd hk'mem (hr x hx1 hx2).2
    · omega
  have h1' : (x, u.2 - k' - 1) ∈ P := by
    rw [show u.2 - k' - 1 = u.2 - 1 - k' from by ring]
    exact hk'mem
  have h2' : (x, u.2 - k') ∉ P := by
    intro hp
    have := hleast (k' - 1) ⟨by omega, by
      rw [show u.2 - 1 - (k' - 1) = u.2 - k' from by ring]
      exact hp⟩
    omega
  obtain ⟨u', w', hnw', hu2', hw2', hwx', hux', hr'⟩ :=
    govern_H_below hfin h1' h2'
  rcases (by omega : w'.1 ≤ u.1 ∨ u.1 < w'.1) with hcase | hcase
  · have hup := hr' u.1 hcase (by omega)
    have hlo := hr u.1 le_rfl hlt
    exact hfat.column_no_dip h.1 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hup.1 hup.2 hlo.1
  · have hup := hr' w'.1 le_rfl (by omega)
    have hlo := hr w'.1 (by omega) (by omega)
    exact hfat.column_no_dip hnw'.2.1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hup.1 hup.2 hlo.1

/-- The 15 rows below a west edge lie in `P`. -/
lemma band_in_west {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (h : NextVtx P u w) (he : u.2 = w.2) (hlt : w.1 < u.1) :
    ∀ x k : ℤ, w.1 ≤ x → x < u.1 → 0 ≤ k → k < 15 →
      (x, u.2 - 1 - k) ∈ P := by
  have hr : HRunBelow P u.2 w.1 u.1 := by
    rcases h.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
    · omega
    · exact hr
    · omega
    · omega
  intro x k hx1 hx2 hk0 hk15
  by_contra hnot
  obtain ⟨k', ⟨hk'0, hk'not⟩, hleast⟩ :=
    Int.exists_least_of_bdd (P := fun j => 0 ≤ j ∧ (x, u.2 - 1 - j) ∉ P)
      ⟨0, fun _ hz => hz.1⟩ ⟨k, hk0, hnot⟩
  have hk'k : k' ≤ k := hleast k ⟨hk0, hnot⟩
  have hk'1 : 1 ≤ k' := by
    rcases eq_or_lt_of_le hk'0 with heq | hpos
    · rw [← heq, sub_zero] at hk'not
      exact absurd (hr x hx1 hx2).1 hk'not
    · omega
  have h1' : (x, u.2 - k') ∈ P := by
    have hp : ¬(x, u.2 - 1 - (k' - 1)) ∉ P := fun hp =>
      absurd (hleast (k' - 1) ⟨by omega, hp⟩) (by omega)
    rw [not_not] at hp
    rwa [show u.2 - 1 - (k' - 1) = u.2 - k' from by ring] at hp
  have h2' : (x, u.2 - k' - 1) ∉ P := by
    rw [show u.2 - k' - 1 = u.2 - 1 - k' from by ring]
    exact hk'not
  obtain ⟨u', w', hnw', hu2', hw2', hux', hwx', hr'⟩ :=
    govern_H_above hfin h1' h2'
  rcases (by omega : u'.1 ≤ w.1 ∨ w.1 < u'.1) with hcase | hcase
  · have hup := hr' w.1 hcase (by omega)
    have hlo := hr w.1 le_rfl hlt
    exact hfat.column_no_bump h.2.1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hup.2 hlo.1 hlo.2
  · have hup := hr' u'.1 le_rfl (by omega)
    have hlo := hr u'.1 (by omega) (by omega)
    exact hfat.column_no_bump hnw'.1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hup.2 hlo.1 hlo.2

/-- The 15 rows above a west edge avoid `P`. -/
lemma band_out_west {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (h : NextVtx P u w) (he : u.2 = w.2) (hlt : w.1 < u.1) :
    ∀ x k : ℤ, w.1 ≤ x → x < u.1 → 0 ≤ k → k < 15 → (x, u.2 + k) ∉ P := by
  have hr : HRunBelow P u.2 w.1 u.1 := by
    rcases h.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
    · omega
    · exact hr
    · omega
    · omega
  intro x k hx1 hx2 hk0 hk15 hmem
  obtain ⟨k', ⟨hk'0, hk'mem⟩, hleast⟩ :=
    Int.exists_least_of_bdd (P := fun j => 0 ≤ j ∧ (x, u.2 + j) ∈ P)
      ⟨0, fun _ hz => hz.1⟩ ⟨k, hk0, hmem⟩
  have hk'k : k' ≤ k := hleast k ⟨hk0, hmem⟩
  have hk'1 : 1 ≤ k' := by
    rcases eq_or_lt_of_le hk'0 with heq | hpos
    · rw [← heq, add_zero] at hk'mem
      exact absurd hk'mem (hr x hx1 hx2).2
    · omega
  have h2' : (x, u.2 + k' - 1) ∉ P := by
    intro hp
    have := hleast (k' - 1) ⟨by omega, by
      rw [show u.2 + (k' - 1) = u.2 + k' - 1 from by ring]
      exact hp⟩
    omega
  obtain ⟨u', w', hnw', hu2', hw2', hux', hwx', hr'⟩ :=
    govern_H_above hfin hk'mem h2'
  rcases (by omega : u'.1 ≤ w.1 ∨ w.1 < u'.1) with hcase | hcase
  · have hup := hr' w.1 hcase (by omega)
    have hlo := hr w.1 le_rfl hlt
    exact hfat.column_no_dip h.2.1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hlo.1 hlo.2 hup.1
  · have hup := hr' u'.1 le_rfl (by omega)
    have hlo := hr u'.1 (by omega) (by omega)
    exact hfat.column_no_dip hnw'.1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hlo.1 hlo.2 hup.1

/-- The 15 columns west of a north edge lie in `P`. -/
lemma band_in_north {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (h : NextVtx P u w) (hveq : u.1 = w.1) (hlt : u.2 < w.2) :
    ∀ y k : ℤ, u.2 ≤ y → y < w.2 → 0 ≤ k → k < 15 →
      (u.1 - 1 - k, y) ∈ P := by
  have hr : VRunLeft P u.1 u.2 w.2 := by
    rcases h.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
    · omega
    · omega
    · exact hr
    · omega
  intro y k hy1 hy2 hk0 hk15
  by_contra hnot
  obtain ⟨k', ⟨hk'0, hk'not⟩, hleast⟩ :=
    Int.exists_least_of_bdd (P := fun j => 0 ≤ j ∧ (u.1 - 1 - j, y) ∉ P)
      ⟨0, fun _ hz => hz.1⟩ ⟨k, hk0, hnot⟩
  have hk'k : k' ≤ k := hleast k ⟨hk0, hnot⟩
  have hk'1 : 1 ≤ k' := by
    rcases eq_or_lt_of_le hk'0 with heq | hpos
    · rw [← heq, sub_zero] at hk'not
      exact absurd (hr y hy1 hy2).1 hk'not
    · omega
  have h1' : (u.1 - k', y) ∈ P := by
    have hp : ¬(u.1 - 1 - (k' - 1), y) ∉ P := fun hp =>
      absurd (hleast (k' - 1) ⟨by omega, hp⟩) (by omega)
    rw [not_not] at hp
    rwa [show u.1 - 1 - (k' - 1) = u.1 - k' from by ring] at hp
  have h2' : (u.1 - k' - 1, y) ∉ P := by
    rw [show u.1 - k' - 1 = u.1 - 1 - k' from by ring]
    exact hk'not
  obtain ⟨u', w', hnw', hu1', hw1', hwy', huy', hr'⟩ :=
    govern_V_right hfin h1' h2'
  rcases (by omega : w'.2 ≤ u.2 ∨ u.2 < w'.2) with hcase | hcase
  · have hup := hr' u.2 hcase (by omega)
    have hlo := hr u.2 le_rfl hlt
    exact hfat.row_no_bump h.1 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hup.2 hlo.1 hlo.2
  · have hup := hr' w'.2 le_rfl (by omega)
    have hlo := hr w'.2 (by omega) (by omega)
    exact hfat.row_no_bump hnw'.2.1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hup.2 hlo.1 hlo.2

/-- The 15 columns east of a north edge avoid `P`. -/
lemma band_out_north {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (h : NextVtx P u w) (hveq : u.1 = w.1) (hlt : u.2 < w.2) :
    ∀ y k : ℤ, u.2 ≤ y → y < w.2 → 0 ≤ k → k < 15 → (u.1 + k, y) ∉ P := by
  have hr : VRunLeft P u.1 u.2 w.2 := by
    rcases h.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
    · omega
    · omega
    · exact hr
    · omega
  intro y k hy1 hy2 hk0 hk15 hmem
  obtain ⟨k', ⟨hk'0, hk'mem⟩, hleast⟩ :=
    Int.exists_least_of_bdd (P := fun j => 0 ≤ j ∧ (u.1 + j, y) ∈ P)
      ⟨0, fun _ hz => hz.1⟩ ⟨k, hk0, hmem⟩
  have hk'k : k' ≤ k := hleast k ⟨hk0, hmem⟩
  have hk'1 : 1 ≤ k' := by
    rcases eq_or_lt_of_le hk'0 with heq | hpos
    · rw [← heq, add_zero] at hk'mem
      exact absurd hk'mem (hr y hy1 hy2).2
    · omega
  have h2' : (u.1 + k' - 1, y) ∉ P := by
    intro hp
    have := hleast (k' - 1) ⟨by omega, by
      rw [show u.1 + (k' - 1) = u.1 + k' - 1 from by ring]
      exact hp⟩
    omega
  obtain ⟨u', w', hnw', hu1', hw1', hwy', huy', hr'⟩ :=
    govern_V_right hfin hk'mem h2'
  rcases (by omega : w'.2 ≤ u.2 ∨ u.2 < w'.2) with hcase | hcase
  · have hup := hr' u.2 hcase (by omega)
    have hlo := hr u.2 le_rfl hlt
    exact hfat.row_no_dip h.1 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hlo.1 hlo.2 hup.1
  · have hup := hr' w'.2 le_rfl (by omega)
    have hlo := hr w'.2 (by omega) (by omega)
    exact hfat.row_no_dip hnw'.2.1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hlo.1 hlo.2 hup.1

/-- The 15 columns east of a south edge lie in `P`. -/
lemma band_in_south {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (h : NextVtx P u w) (hveq : u.1 = w.1) (hlt : w.2 < u.2) :
    ∀ y k : ℤ, w.2 ≤ y → y < u.2 → 0 ≤ k → k < 15 →
      (u.1 + k, y) ∈ P := by
  have hr : VRunRight P u.1 w.2 u.2 := by
    rcases h.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
    · omega
    · omega
    · omega
    · exact hr
  intro y k hy1 hy2 hk0 hk15
  by_contra hnot
  obtain ⟨k', ⟨hk'0, hk'not⟩, hleast⟩ :=
    Int.exists_least_of_bdd (P := fun j => 0 ≤ j ∧ (u.1 + j, y) ∉ P)
      ⟨0, fun _ hz => hz.1⟩ ⟨k, hk0, hnot⟩
  have hk'k : k' ≤ k := hleast k ⟨hk0, hnot⟩
  have hk'1 : 1 ≤ k' := by
    rcases eq_or_lt_of_le hk'0 with heq | hpos
    · rw [← heq, add_zero] at hk'not
      exact absurd (hr y hy1 hy2).1 hk'not
    · omega
  have h1' : (u.1 + k' - 1, y) ∈ P := by
    have hp : ¬(u.1 + (k' - 1), y) ∉ P := fun hp =>
      absurd (hleast (k' - 1) ⟨by omega, hp⟩) (by omega)
    rw [not_not] at hp
    rwa [show u.1 + (k' - 1) = u.1 + k' - 1 from by ring] at hp
  obtain ⟨u', w', hnw', hu1', hw1', huy', hwy', hr'⟩ :=
    govern_V_left hfin h1' hk'not
  rcases (by omega : u'.2 ≤ w.2 ∨ w.2 < u'.2) with hcase | hcase
  · have hup := hr' w.2 hcase (by omega)
    have hlo := hr w.2 le_rfl hlt
    exact hfat.row_no_bump h.2.1 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hlo.2 hlo.1 hup.2
  · have hup := hr' u'.2 le_rfl (by omega)
    have hlo := hr u'.2 (by omega) (by omega)
    exact hfat.row_no_bump hnw'.1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hlo.2 hlo.1 hup.2

/-- The 15 columns west of a south edge avoid `P`. -/
lemma band_out_south {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (h : NextVtx P u w) (hveq : u.1 = w.1) (hlt : w.2 < u.2) :
    ∀ y k : ℤ, w.2 ≤ y → y < u.2 → 0 ≤ k → k < 15 →
      (u.1 - 1 - k, y) ∉ P := by
  have hr : VRunRight P u.1 w.2 u.2 := by
    rcases h.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
    · omega
    · omega
    · omega
    · exact hr
  intro y k hy1 hy2 hk0 hk15 hmem
  obtain ⟨k', ⟨hk'0, hk'mem⟩, hleast⟩ :=
    Int.exists_least_of_bdd (P := fun j => 0 ≤ j ∧ (u.1 - 1 - j, y) ∈ P)
      ⟨0, fun _ hz => hz.1⟩ ⟨k, hk0, hmem⟩
  have hk'k : k' ≤ k := hleast k ⟨hk0, hmem⟩
  have hk'1 : 1 ≤ k' := by
    rcases eq_or_lt_of_le hk'0 with heq | hpos
    · rw [← heq, sub_zero] at hk'mem
      exact absurd hk'mem (hr y hy1 hy2).2
    · omega
  have h1' : (u.1 - k' - 1, y) ∈ P := by
    rw [show u.1 - k' - 1 = u.1 - 1 - k' from by ring]
    exact hk'mem
  have h2' : (u.1 - k', y) ∉ P := by
    intro hp
    have := hleast (k' - 1) ⟨by omega, by
      rw [show u.1 - 1 - (k' - 1) = u.1 - k' from by ring]
      exact hp⟩
    omega
  obtain ⟨u', w', hnw', hu1', hw1', huy', hwy', hr'⟩ :=
    govern_V_left hfin h1' h2'
  rcases (by omega : u'.2 ≤ w.2 ∨ w.2 < u'.2) with hcase | hcase
  · have hup := hr' w.2 hcase (by omega)
    have hlo := hr w.2 le_rfl hlt
    exact hfat.row_no_dip h.2.1 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hup.1 hlo.2 hlo.1
  · have hup := hr' u'.2 le_rfl (by omega)
    have hlo := hr u'.2 (by omega) (by omega)
    exact hfat.row_no_dip hnw'.1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hup.1 hlo.2 hlo.1

/-- A vertex on the closed span of an edge is one of its two endpoints:
    edge interiors carry no vertex. -/
lemma endpoint_of_vertexV {P : Set Cell} {u w : Cell} (hnw : NextVtx P u w)
    {g : Cell} (hgv : IsVertex P g) (hg1 : g.1 = u.1)
    (hg2 : (u.2 ≤ g.2 ∧ g.2 ≤ w.2) ∨ (w.2 ≤ g.2 ∧ g.2 ≤ u.2)) :
    g = u ∨ g = w := by
  rcases hnw.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
  · exact Or.inl (Prod.ext hg1 (by omega))
  · exact Or.inl (Prod.ext hg1 (by omega))
  · rcases (by omega : g.2 = u.2 ∨ g.2 = w.2 ∨ (u.2 < g.2 ∧ g.2 < w.2))
      with h | h | h
    · exact Or.inl (Prod.ext hg1 h)
    · exact Or.inr (Prod.ext (hg1.trans e1) h)
    · exact absurd (show IsVertex P (u.1, g.2) by
        rwa [show ((u.1, g.2) : Cell) = g from Prod.ext hg1.symm rfl])
        (vrunLeft_not_vertex hr g.2 h.1 h.2)
  · rcases (by omega : g.2 = u.2 ∨ g.2 = w.2 ∨ (w.2 < g.2 ∧ g.2 < u.2))
      with h | h | h
    · exact Or.inl (Prod.ext hg1 h)
    · exact Or.inr (Prod.ext (hg1.trans e1) h)
    · exact absurd (show IsVertex P (u.1, g.2) by
        rwa [show ((u.1, g.2) : Cell) = g from Prod.ext hg1.symm rfl])
        (vrunRight_not_vertex hr g.2 h.1 h.2)

/-- A vertex on the closed span of an edge is one of its two endpoints. -/
lemma endpoint_of_vertexH {P : Set Cell} {u w : Cell} (hnw : NextVtx P u w)
    {g : Cell} (hgv : IsVertex P g) (hg2 : g.2 = u.2)
    (hg1 : (u.1 ≤ g.1 ∧ g.1 ≤ w.1) ∨ (w.1 ≤ g.1 ∧ g.1 ≤ u.1)) :
    g = u ∨ g = w := by
  rcases hnw.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩
  · rcases (by omega : g.1 = u.1 ∨ g.1 = w.1 ∨ (u.1 < g.1 ∧ g.1 < w.1))
      with h | h | h
    · exact Or.inl (Prod.ext h hg2)
    · exact Or.inr (Prod.ext h (hg2.trans e1))
    · exact absurd (show IsVertex P (g.1, u.2) by
        rwa [show ((g.1, u.2) : Cell) = g from Prod.ext rfl hg2.symm])
        (hrunAbove_not_vertex hr g.1 h.1 h.2)
  · rcases (by omega : g.1 = u.1 ∨ g.1 = w.1 ∨ (w.1 < g.1 ∧ g.1 < u.1))
      with h | h | h
    · exact Or.inl (Prod.ext h hg2)
    · exact Or.inr (Prod.ext h (hg2.trans e1))
    · exact absurd (show IsVertex P (g.1, u.2) by
        rwa [show ((g.1, u.2) : Cell) = g from Prod.ext rfl hg2.symm])
        (hrunBelow_not_vertex hr g.1 h.1 h.2)
  · exact Or.inl (Prod.ext (by omega) hg2)
  · exact Or.inl (Prod.ext (by omega) hg2)

/-- A vertex incident to a curve segment belongs to the (successor-closed)
    family. -/
lemma vertex_mem_S_of_curveV {P S : Set Cell}
    (hSn : ∀ u ∈ S, ∀ w, NextVtx P u w → w ∈ S)
    {t : ℤ × ℤ} (ht : t ∈ curveV P S) {g : Cell} (hgv : IsVertex P g)
    (hg1 : g.1 = t.1) (hg2 : g.2 = t.2 ∨ g.2 = t.2 + 1) : g ∈ S := by
  obtain ⟨u, huS, w, hnw, hcoord, hint⟩ := ht
  rcases endpoint_of_vertexV hnw hgv (hg1.trans hcoord)
      (show (u.2 ≤ g.2 ∧ g.2 ≤ w.2) ∨ (w.2 ≤ g.2 ∧ g.2 ≤ u.2) by omega)
    with rfl | rfl
  · exact huS
  · exact hSn u huS _ hnw

/-- A vertex incident to a curve segment belongs to the family. -/
lemma vertex_mem_S_of_curveH {P S : Set Cell}
    (hSn : ∀ u ∈ S, ∀ w, NextVtx P u w → w ∈ S)
    {t : ℤ × ℤ} (ht : t ∈ curveH P S) {g : Cell} (hgv : IsVertex P g)
    (hg2 : g.2 = t.2) (hg1 : g.1 = t.1 ∨ g.1 = t.1 + 1) : g ∈ S := by
  obtain ⟨u, huS, w, hnw, hcoord, hint⟩ := ht
  rcases endpoint_of_vertexH hnw hgv (hg2.trans hcoord)
      (show (u.1 ≤ g.1 ∧ g.1 ≤ w.1) ∨ (w.1 ≤ g.1 ∧ g.1 ≤ u.1) by omega)
    with rfl | rfl
  · exact huS
  · exact hSn u huS _ hnw

/-- **Locality of the curve.**  At a grid point touched by the curve, the
    curve agrees with the whole boundary: at a vertex the boundary
    segments there belong to the edges into and out of it (closure of `S`
    covers both), and elsewhere the incident edge runs straight through,
    supplying the two collinear segments and killing the perpendicular
    ones. -/
lemma curve_local {P S : Set Cell} (hfin : P.Finite)
    (hSn : ∀ u ∈ S, ∀ w, NextVtx P u w → w ∈ S)
    (hSp : ∀ u w, NextVtx P u w → w ∈ S → u ∈ S)
    (x y : ℤ)
    (hsome : (x, y) ∈ curveV P S ∨ (x, y - 1) ∈ curveV P S ∨
      (x, y) ∈ curveH P S ∨ (x - 1, y) ∈ curveH P S) :
    ((x, y) ∈ curveV P S ↔ (x, y) ∈ bndV P) ∧
    ((x, y - 1) ∈ curveV P S ↔ (x, y - 1) ∈ bndV P) ∧
    ((x, y) ∈ curveH P S ↔ (x, y) ∈ bndH P) ∧
    ((x - 1, y) ∈ curveH P S ↔ (x - 1, y) ∈ bndH P) := by
  by_cases hgv : IsVertex P (x, y)
  · -- the grid point is a vertex, and it belongs to `S`
    have hgS : ((x, y) : Cell) ∈ S := by
      rcases hsome with h | h | h | h
      · exact vertex_mem_S_of_curveV hSn h hgv rfl (Or.inl rfl)
      · exact vertex_mem_S_of_curveV hSn h hgv rfl
          (Or.inr (show y = y - 1 + 1 by omega))
      · exact vertex_mem_S_of_curveH hSn h hgv rfl (Or.inl rfl)
      · exact vertex_mem_S_of_curveH hSn h hgv rfl
          (Or.inr (show x = x - 1 + 1 by omega))
    -- every boundary segment at the vertex is on the curve: its governing
    -- edge cannot run through a vertex, so it starts or ends there
    have hVup : (x, y) ∈ bndV P → (x, y) ∈ curveV P S := by
      intro hb
      obtain ⟨u, w, hnw, hu1, hint⟩ := govern_V hfin hb
      have huS : u ∈ S := by
        rcases endpoint_of_vertexV hnw hgv hu1.symm
            (show (u.2 ≤ y ∧ y ≤ w.2) ∨ (w.2 ≤ y ∧ y ≤ u.2) by omega)
          with heq | heq
        · rwa [← heq]
        · exact hSp u w hnw (heq ▸ hgS)
      exact ⟨u, huS, w, hnw, hu1.symm, hint⟩
    have hVdn : (x, y - 1) ∈ bndV P → (x, y - 1) ∈ curveV P S := by
      intro hb
      obtain ⟨u, w, hnw, hu1, hint⟩ := govern_V hfin hb
      have huS : u ∈ S := by
        rcases endpoint_of_vertexV hnw hgv hu1.symm
            (show (u.2 ≤ y ∧ y ≤ w.2) ∨ (w.2 ≤ y ∧ y ≤ u.2) by omega)
          with heq | heq
        · rwa [← heq]
        · exact hSp u w hnw (heq ▸ hgS)
      exact ⟨u, huS, w, hnw, hu1.symm, hint⟩
    have hHrt : (x, y) ∈ bndH P → (x, y) ∈ curveH P S := by
      intro hb
      obtain ⟨u, w, hnw, hu2, hint⟩ := govern_H hfin hb
      have huS : u ∈ S := by
        rcases endpoint_of_vertexH hnw hgv hu2.symm
            (show (u.1 ≤ x ∧ x ≤ w.1) ∨ (w.1 ≤ x ∧ x ≤ u.1) by omega)
          with heq | heq
        · rwa [← heq]
        · exact hSp u w hnw (heq ▸ hgS)
      exact ⟨u, huS, w, hnw, hu2.symm, hint⟩
    have hHlf : (x - 1, y) ∈ bndH P → (x - 1, y) ∈ curveH P S := by
      intro hb
      obtain ⟨u, w, hnw, hu2, hint⟩ := govern_H hfin hb
      have huS : u ∈ S := by
        rcases endpoint_of_vertexH hnw hgv hu2.symm
            (show (u.1 ≤ x ∧ x ≤ w.1) ∨ (w.1 ≤ x ∧ x ≤ u.1) by omega)
          with heq | heq
        · rwa [← heq]
        · exact hSp u w hnw (heq ▸ hgS)
      exact ⟨u, huS, w, hnw, hu2.symm, hint⟩
    exact ⟨⟨fun h => curveV_subset_bndV P S h, hVup⟩,
      ⟨fun h => curveV_subset_bndV P S h, hVdn⟩,
      ⟨fun h => curveH_subset_bndH P S h, hHrt⟩,
      ⟨fun h => curveH_subset_bndH P S h, hHlf⟩⟩
  · -- not a vertex: the incident edge runs straight through the point
    rcases hsome with h | h | h | h
    · -- the segment above the point is on a vertical edge
      have hVup := h
      obtain ⟨u, huS, w, hnw, hcoord, hint⟩ := h
      have huv := hnw.1
      have hwv := hnw.2.1
      have hc : x = u.1 := hcoord
      subst hc
      rcases hnw.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ |
        ⟨e1, e2, hr⟩
      · exact absurd hint (by omega)
      · exact absurd hint (by omega)
      · -- north edge through (u.1, y)
        have hy : u.2 ≤ y ∧ y < w.2 := by
          rcases hint with hh | hh
          · exact hh
          · omega
        have hy1 : u.2 < y := by
          rcases eq_or_lt_of_le hy.1 with heq | h'
          · exact absurd (show IsVertex P (u.1, y) by
              rwa [show ((u.1, y) : Cell) = u from Prod.ext rfl heq.symm])
              hgv
          · exact h'
        have hVdn : ((u.1, y - 1) : ℤ × ℤ) ∈ curveV P S :=
          ⟨u, huS, w, hnw, rfl,
            Or.inl ⟨show u.2 ≤ y - 1 by omega, show y - 1 < w.2 by omega⟩⟩
        have hrt : ((u.1, y) : ℤ × ℤ) ∉ bndH P := fun hb =>
          hb (iff_of_false (hr (y - 1) (by omega) (by omega)).2
            (hr y (by omega) (by omega)).2)
        have hlf : ((u.1 - 1, y) : ℤ × ℤ) ∉ bndH P := fun hb =>
          hb (iff_of_true (hr (y - 1) (by omega) (by omega)).1
            (hr y (by omega) (by omega)).1)
        exact ⟨iff_of_true hVup (curveV_subset_bndV P S hVup),
          iff_of_true hVdn (curveV_subset_bndV P S hVdn),
          iff_of_false (fun hc => hrt (curveH_subset_bndH P S hc)) hrt,
          iff_of_false (fun hc => hlf (curveH_subset_bndH P S hc)) hlf⟩
      · -- south edge through (u.1, y)
        have hy : w.2 ≤ y ∧ y < u.2 := by
          rcases hint with hh | hh
          · omega
          · exact hh
        have hy1 : w.2 < y := by
          rcases eq_or_lt_of_le hy.1 with heq | h'
          · exact absurd (show IsVertex P (u.1, y) by
              rwa [show ((u.1, y) : Cell) = w from Prod.ext e1 heq.symm])
              hgv
          · exact h'
        have hVdn : ((u.1, y - 1) : ℤ × ℤ) ∈ curveV P S :=
          ⟨u, huS, w, hnw, rfl,
            Or.inr ⟨show w.2 ≤ y - 1 by omega, show y - 1 < u.2 by omega⟩⟩
        have hrt : ((u.1, y) : ℤ × ℤ) ∉ bndH P := fun hb =>
          hb (iff_of_true (hr (y - 1) (by omega) (by omega)).1
            (hr y (by omega) (by omega)).1)
        have hlf : ((u.1 - 1, y) : ℤ × ℤ) ∉ bndH P := fun hb =>
          hb (iff_of_false (hr (y - 1) (by omega) (by omega)).2
            (hr y (by omega) (by omega)).2)
        exact ⟨iff_of_true hVup (curveV_subset_bndV P S hVup),
          iff_of_true hVdn (curveV_subset_bndV P S hVdn),
          iff_of_false (fun hc => hrt (curveH_subset_bndH P S hc)) hrt,
          iff_of_false (fun hc => hlf (curveH_subset_bndH P S hc)) hlf⟩
    · -- the segment below the point is on a vertical edge
      have hVdn := h
      obtain ⟨u, huS, w, hnw, hcoord, hint⟩ := h
      have huv := hnw.1
      have hwv := hnw.2.1
      have hc : x = u.1 := hcoord
      subst hc
      rcases hnw.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ |
        ⟨e1, e2, hr⟩
      · exact absurd hint (by omega)
      · exact absurd hint (by omega)
      · -- north edge through (u.1, y)
        have hy : u.2 ≤ y - 1 ∧ y - 1 < w.2 := by
          rcases hint with hh | hh
          · exact hh
          · omega
        have hy1 : y < w.2 := by
          rcases eq_or_lt_of_le (show y ≤ w.2 by omega) with heq | h'
          · exact absurd (show IsVertex P (u.1, y) by
              rwa [show ((u.1, y) : Cell) = w from Prod.ext e1 heq]) hgv
          · exact h'
        have hVup : ((u.1, y) : ℤ × ℤ) ∈ curveV P S :=
          ⟨u, huS, w, hnw, rfl, Or.inl ⟨show u.2 ≤ y by omega, hy1⟩⟩
        have hrt : ((u.1, y) : ℤ × ℤ) ∉ bndH P := fun hb =>
          hb (iff_of_false (hr (y - 1) (by omega) (by omega)).2
            (hr y (by omega) (by omega)).2)
        have hlf : ((u.1 - 1, y) : ℤ × ℤ) ∉ bndH P := fun hb =>
          hb (iff_of_true (hr (y - 1) (by omega) (by omega)).1
            (hr y (by omega) (by omega)).1)
        exact ⟨iff_of_true hVup (curveV_subset_bndV P S hVup),
          iff_of_true hVdn (curveV_subset_bndV P S hVdn),
          iff_of_false (fun hc => hrt (curveH_subset_bndH P S hc)) hrt,
          iff_of_false (fun hc => hlf (curveH_subset_bndH P S hc)) hlf⟩
      · -- south edge through (u.1, y)
        have hy : w.2 ≤ y - 1 ∧ y - 1 < u.2 := by
          rcases hint with hh | hh
          · omega
          · exact hh
        have hy1 : y < u.2 := by
          rcases eq_or_lt_of_le (show y ≤ u.2 by omega) with heq | h'
          · exact absurd (show IsVertex P (u.1, y) by
              rwa [show ((u.1, y) : Cell) = u from Prod.ext rfl heq]) hgv
          · exact h'
        have hVup : ((u.1, y) : ℤ × ℤ) ∈ curveV P S :=
          ⟨u, huS, w, hnw, rfl, Or.inr ⟨show w.2 ≤ y by omega, hy1⟩⟩
        have hrt : ((u.1, y) : ℤ × ℤ) ∉ bndH P := fun hb =>
          hb (iff_of_true (hr (y - 1) (by omega) (by omega)).1
            (hr y (by omega) (by omega)).1)
        have hlf : ((u.1 - 1, y) : ℤ × ℤ) ∉ bndH P := fun hb =>
          hb (iff_of_false (hr (y - 1) (by omega) (by omega)).2
            (hr y (by omega) (by omega)).2)
        exact ⟨iff_of_true hVup (curveV_subset_bndV P S hVup),
          iff_of_true hVdn (curveV_subset_bndV P S hVdn),
          iff_of_false (fun hc => hrt (curveH_subset_bndH P S hc)) hrt,
          iff_of_false (fun hc => hlf (curveH_subset_bndH P S hc)) hlf⟩
    · -- the segment right of the point is on a horizontal edge
      have hHrt := h
      obtain ⟨u, huS, w, hnw, hcoord, hint⟩ := h
      have huv := hnw.1
      have hwv := hnw.2.1
      have hc : y = u.2 := hcoord
      subst hc
      rcases hnw.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ |
        ⟨e1, e2, hr⟩
      · -- east edge through (x, u.2)
        have hx : u.1 ≤ x ∧ x < w.1 := by
          rcases hint with hh | hh
          · exact hh
          · omega
        have hx1 : u.1 < x := by
          rcases eq_or_lt_of_le hx.1 with heq | h'
          · exact absurd (show IsVertex P (x, u.2) by
              rwa [show ((x, u.2) : Cell) = u from Prod.ext heq.symm rfl]) hgv
          · exact h'
        have hHlf : ((x - 1, u.2) : ℤ × ℤ) ∈ curveH P S :=
          ⟨u, huS, w, hnw, rfl,
            Or.inl ⟨show u.1 ≤ x - 1 by omega, show x - 1 < w.1 by omega⟩⟩
        have hup : ((x, u.2) : ℤ × ℤ) ∉ bndV P := fun hb =>
          hb (iff_of_true (hr (x - 1) (by omega) (by omega)).1
            (hr x (by omega) (by omega)).1)
        have hdn : ((x, u.2 - 1) : ℤ × ℤ) ∉ bndV P := fun hb =>
          hb (iff_of_false (hr (x - 1) (by omega) (by omega)).2
            (hr x (by omega) (by omega)).2)
        exact ⟨iff_of_false (fun hc => hup (curveV_subset_bndV P S hc)) hup,
          iff_of_false (fun hc => hdn (curveV_subset_bndV P S hc)) hdn,
          iff_of_true hHrt (curveH_subset_bndH P S hHrt),
          iff_of_true hHlf (curveH_subset_bndH P S hHlf)⟩
      · -- west edge through (x, u.2)
        have hx : w.1 ≤ x ∧ x < u.1 := by
          rcases hint with hh | hh
          · omega
          · exact hh
        have hx1 : w.1 < x := by
          rcases eq_or_lt_of_le hx.1 with heq | h'
          · exact absurd (show IsVertex P (x, u.2) by
              rwa [show ((x, u.2) : Cell) = w from Prod.ext heq.symm e1]) hgv
          · exact h'
        have hHlf : ((x - 1, u.2) : ℤ × ℤ) ∈ curveH P S :=
          ⟨u, huS, w, hnw, rfl,
            Or.inr ⟨show w.1 ≤ x - 1 by omega, show x - 1 < u.1 by omega⟩⟩
        have hup : ((x, u.2) : ℤ × ℤ) ∉ bndV P := fun hb =>
          hb (iff_of_false (hr (x - 1) (by omega) (by omega)).2
            (hr x (by omega) (by omega)).2)
        have hdn : ((x, u.2 - 1) : ℤ × ℤ) ∉ bndV P := fun hb =>
          hb (iff_of_true (hr (x - 1) (by omega) (by omega)).1
            (hr x (by omega) (by omega)).1)
        exact ⟨iff_of_false (fun hc => hup (curveV_subset_bndV P S hc)) hup,
          iff_of_false (fun hc => hdn (curveV_subset_bndV P S hc)) hdn,
          iff_of_true hHrt (curveH_subset_bndH P S hHrt),
          iff_of_true hHlf (curveH_subset_bndH P S hHlf)⟩
      · exact absurd hint (by omega)
      · exact absurd hint (by omega)
    · -- the segment left of the point is on a horizontal edge
      have hHlf := h
      obtain ⟨u, huS, w, hnw, hcoord, hint⟩ := h
      have huv := hnw.1
      have hwv := hnw.2.1
      have hc : y = u.2 := hcoord
      subst hc
      rcases hnw.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ |
        ⟨e1, e2, hr⟩
      · -- east edge through (x, u.2)
        have hx : u.1 ≤ x - 1 ∧ x - 1 < w.1 := by
          rcases hint with hh | hh
          · exact hh
          · omega
        have hx1 : x < w.1 := by
          rcases eq_or_lt_of_le (show x ≤ w.1 by omega) with heq | h'
          · exact absurd (show IsVertex P (x, u.2) by
              rwa [show ((x, u.2) : Cell) = w from Prod.ext heq e1]) hgv
          · exact h'
        have hHrt : ((x, u.2) : ℤ × ℤ) ∈ curveH P S :=
          ⟨u, huS, w, hnw, rfl, Or.inl ⟨show u.1 ≤ x by omega, hx1⟩⟩
        have hup : ((x, u.2) : ℤ × ℤ) ∉ bndV P := fun hb =>
          hb (iff_of_true (hr (x - 1) (by omega) (by omega)).1
            (hr x (by omega) (by omega)).1)
        have hdn : ((x, u.2 - 1) : ℤ × ℤ) ∉ bndV P := fun hb =>
          hb (iff_of_false (hr (x - 1) (by omega) (by omega)).2
            (hr x (by omega) (by omega)).2)
        exact ⟨iff_of_false (fun hc => hup (curveV_subset_bndV P S hc)) hup,
          iff_of_false (fun hc => hdn (curveV_subset_bndV P S hc)) hdn,
          iff_of_true hHrt (curveH_subset_bndH P S hHrt),
          iff_of_true hHlf (curveH_subset_bndH P S hHlf)⟩
      · -- west edge through (x, u.2)
        have hx : w.1 ≤ x - 1 ∧ x - 1 < u.1 := by
          rcases hint with hh | hh
          · omega
          · exact hh
        have hx1 : x < u.1 := by
          rcases eq_or_lt_of_le (show x ≤ u.1 by omega) with heq | h'
          · exact absurd (show IsVertex P (x, u.2) by
              rwa [show ((x, u.2) : Cell) = u from Prod.ext heq rfl]) hgv
          · exact h'
        have hHrt : ((x, u.2) : ℤ × ℤ) ∈ curveH P S :=
          ⟨u, huS, w, hnw, rfl, Or.inr ⟨show w.1 ≤ x by omega, hx1⟩⟩
        have hup : ((x, u.2) : ℤ × ℤ) ∉ bndV P := fun hb =>
          hb (iff_of_false (hr (x - 1) (by omega) (by omega)).2
            (hr x (by omega) (by omega)).2)
        have hdn : ((x, u.2 - 1) : ℤ × ℤ) ∉ bndV P := fun hb =>
          hb (iff_of_true (hr (x - 1) (by omega) (by omega)).1
            (hr x (by omega) (by omega)).1)
        exact ⟨iff_of_false (fun hc => hup (curveV_subset_bndV P S hc)) hup,
          iff_of_false (fun hc => hdn (curveV_subset_bndV P S hc)) hdn,
          iff_of_true hHrt (curveH_subset_bndH P S hHrt),
          iff_of_true hHlf (curveH_subset_bndH P S hHlf)⟩
      · exact absurd hint (by omega)
      · exact absurd hint (by omega)

/-- **Even degree of the curve** at every grid point: it is locally either
    absent or equal to the whole boundary, and the boundary satisfies the
    identity for free. -/
lemma curve_degree {P S : Set Cell} (hfin : P.Finite)
    (hSn : ∀ u ∈ S, ∀ w, NextVtx P u w → w ∈ S)
    (hSp : ∀ u w, NextVtx P u w → w ∈ S → u ∈ S) :
    ∀ x y : ℤ, (((x, y) ∈ curveV P S) ↔ ((x, y - 1) ∈ curveV P S)) ↔
      (((x, y) ∈ curveH P S) ↔ ((x - 1, y) ∈ curveH P S)) := by
  intro x y
  by_cases hsome : (x, y) ∈ curveV P S ∨ (x, y - 1) ∈ curveV P S ∨
      (x, y) ∈ curveH P S ∨ (x - 1, y) ∈ curveH P S
  · obtain ⟨h1, h2, h3, h4⟩ := curve_local hfin hSn hSp x y hsome
    rw [h1, h2, h3, h4]
    exact bnd_degree P x y
  · push_neg at hsome
    obtain ⟨h1, h2, h3, h4⟩ := hsome
    exact iff_of_true (iff_of_false h1 h2) (iff_of_false h3 h4)

private lemma mem_of_pathA {A : Set Cell} {p q : Cell} (hp : p ∈ A)
    (h : Relation.ReflTransGen (fun a b => b ∈ A ∧ CellAdj a b) p q) :
    q ∈ A := by
  induction h with
  | refl => exact hp
  | tail _ hbc _ => exact hbc.1

/-- **Parity is constant along paths that do not cross the boundary**: on
    any set `A` whose cells all agree about membership in `P` (so `A = P`
    or `A = Pᶜ`), the ray-crossing parity of the curve is invariant along
    cell paths in `A`. -/
lemma par_const_of_path {P S : Set Cell} (hfin : P.Finite)
    (hSn : ∀ u ∈ S, ∀ w, NextVtx P u w → w ∈ S)
    (hSp : ∀ u w, NextVtx P u w → w ∈ S → u ∈ S)
    {A : Set Cell} (hA : ∀ p ∈ A, ∀ q ∈ A, ((p : Cell) ∈ P ↔ q ∈ P))
    {p q : Cell} (hp : p ∈ A)
    (hpath : Relation.ReflTransGen (fun a b => b ∈ A ∧ CellAdj a b) p q) :
    (Even ((rayCross (curveV P S) p.1 p.2).ncard) ↔
      Even ((rayCross (curveV P S) q.1 q.2).ncard)) := by
  induction hpath with
  | refl => exact Iff.rfl
  | @tail b c hpb hbc ih =>
    have hbA : b ∈ A := mem_of_pathA hp hpb
    have hcA : c ∈ A := hbc.1
    have hPiff : (b ∈ P ↔ c ∈ P) := hA b hbA c hcA
    refine ih.trans ?_
    rcases hbc.2 with ⟨hx, hy | hy⟩ | ⟨hy, hx | hx⟩
    · -- step up
      have hseg : ((b.1, b.2 + 1) : ℤ × ℤ) ∉ curveH P S := by
        intro hcv
        refine curveH_subset_bndH P S hcv ?_
        change ((b.1, b.2 + 1 - 1) : Cell) ∈ P ↔ ((b.1, b.2 + 1) : Cell) ∈ P
        rw [show b.2 + 1 - 1 = b.2 from by ring,
          show ((b.1, b.2) : Cell) = b from Prod.ext rfl rfl,
          show ((b.1, b.2 + 1) : Cell) = c from Prod.ext hx hy.symm]
        exact hPiff
      have hstep := Nat.even_add.mp
        ((even_rayCross_add_up (curveV_finite hfin S) (curveH_finite hfin S)
          (curve_degree hfin hSn hSp) b.1 b.2).mpr hseg)
      have hc' : rayCross (curveV P S) c.1 c.2 =
          rayCross (curveV P S) b.1 (b.2 + 1) := by rw [hx, hy]
      rw [hc']
      exact hstep
    · -- step down
      have hseg : ((c.1, c.2 + 1) : ℤ × ℤ) ∉ curveH P S := by
        intro hcv
        refine curveH_subset_bndH P S hcv ?_
        change ((c.1, c.2 + 1 - 1) : Cell) ∈ P ↔ ((c.1, c.2 + 1) : Cell) ∈ P
        rw [show c.2 + 1 - 1 = c.2 from by ring,
          show ((c.1, c.2) : Cell) = c from Prod.ext rfl rfl,
          show ((c.1, c.2 + 1) : Cell) = b from Prod.ext hx.symm hy.symm]
        exact hPiff.symm
      have hstep := Nat.even_add.mp
        ((even_rayCross_add_up (curveV_finite hfin S) (curveH_finite hfin S)
          (curve_degree hfin hSn hSp) c.1 c.2).mpr hseg)
      have hb'' : rayCross (curveV P S) b.1 b.2 =
          rayCross (curveV P S) c.1 (c.2 + 1) := by rw [hx, hy]
      rw [hb'']
      exact hstep.symm
    · -- step right
      have hseg : ((b.1 + 1, b.2) : ℤ × ℤ) ∉ curveV P S := by
        intro hcv
        refine curveV_subset_bndV P S hcv ?_
        change ((b.1 + 1 - 1, b.2) : Cell) ∈ P ↔ ((b.1 + 1, b.2) : Cell) ∈ P
        rw [show b.1 + 1 - 1 = b.1 from by ring,
          show ((b.1, b.2) : Cell) = b from Prod.ext rfl rfl,
          show ((b.1 + 1, b.2) : Cell) = c from Prod.ext hx.symm hy]
        exact hPiff
      have hstep := Nat.even_add.mp
        ((even_rayCross_add_right (curveV_finite hfin S) b.1 b.2).mpr hseg)
      have hc' : rayCross (curveV P S) c.1 c.2 =
          rayCross (curveV P S) (b.1 + 1) b.2 := by rw [hx, hy]
      rw [hc']
      exact hstep
    · -- step left
      have hseg : ((c.1 + 1, c.2) : ℤ × ℤ) ∉ curveV P S := by
        intro hcv
        refine curveV_subset_bndV P S hcv ?_
        change ((c.1 + 1 - 1, c.2) : Cell) ∈ P ↔ ((c.1 + 1, c.2) : Cell) ∈ P
        rw [show c.1 + 1 - 1 = c.1 from by ring,
          show ((c.1, c.2) : Cell) = c from Prod.ext rfl rfl,
          show ((c.1 + 1, c.2) : Cell) = b from Prod.ext hx.symm hy.symm]
        exact hPiff.symm
      have hstep := Nat.even_add.mp
        ((even_rayCross_add_right (curveV_finite hfin S) c.1 c.2).mpr hseg)
      have hb'' : rayCross (curveV P S) b.1 b.2 =
          rayCross (curveV P S) (c.1 + 1) c.2 := by rw [hx, hy]
      rw [hb'']
      exact hstep.symm

/-- **The curve covers the whole boundary.**  Parity is constant on `P`
    and on `Pᶜ` by connectivity; it flips across curve segments and is
    preserved across boundary segments not on the curve — so a boundary
    segment off the curve would equate the two constants while any curve
    segment separates them. -/
theorem curve_covers {P S : Set Cell} (hfin : P.Finite)
    (hconn : CellConnected P) (hsimp : CellConnected Pᶜ) (hfat : Fat 16 P)
    (hSv : ∀ u ∈ S, IsVertex P u)
    (hSn : ∀ u ∈ S, ∀ w, NextVtx P u w → w ∈ S)
    (hSp : ∀ u w, NextVtx P u w → w ∈ S → u ∈ S)
    (hne : S.Nonempty) :
    bndV P ⊆ curveV P S ∧ bndH P ⊆ curveH P S := by
  classical
  obtain ⟨u0, hu0⟩ := hne
  obtain ⟨w0, hnw0⟩ := exists_nextVtx hfin hfat (hSv u0 hu0)
  -- reference flip: two adjacent cells across a curve segment, one inside
  -- and one outside `P`, with different parities
  have href : ∃ dP dO : Cell, dP ∈ P ∧ dO ∉ P ∧
      ¬(Even ((rayCross (curveV P S) dP.1 dP.2).ncard) ↔
        Even ((rayCross (curveV P S) dO.1 dO.2).ncard)) := by
    rcases hnw0.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ |
      ⟨e1, e2, hr⟩
    · -- east edge: flip across its first segment
      have hs0 : ((u0.1, u0.2) : ℤ × ℤ) ∈ curveH P S :=
        ⟨u0, hu0, w0, hnw0, rfl, Or.inl ⟨le_rfl, e2⟩⟩
      have hcells := hr u0.1 le_rfl e2
      refine ⟨(u0.1, u0.2), (u0.1, u0.2 - 1), hcells.1, hcells.2, fun hiff => ?_⟩
      have h := even_rayCross_add_up (curveV_finite hfin S)
        (curveH_finite hfin S) (curve_degree hfin hSn hSp) u0.1 (u0.2 - 1)
      rw [show u0.2 - 1 + 1 = u0.2 from by ring] at h
      exact (h.mp (Nat.even_add.mpr hiff.symm)) hs0
    · -- west edge
      have hs0 : ((u0.1 - 1, u0.2) : ℤ × ℤ) ∈ curveH P S :=
        ⟨u0, hu0, w0, hnw0, rfl,
          Or.inr ⟨show w0.1 ≤ u0.1 - 1 by omega, show u0.1 - 1 < u0.1 by omega⟩⟩
      have hcells := hr (u0.1 - 1) (by omega) (by omega)
      refine ⟨(u0.1 - 1, u0.2 - 1), (u0.1 - 1, u0.2), hcells.1, hcells.2,
        fun hiff => ?_⟩
      have h := even_rayCross_add_up (curveV_finite hfin S)
        (curveH_finite hfin S) (curve_degree hfin hSn hSp) (u0.1 - 1) (u0.2 - 1)
      rw [show u0.2 - 1 + 1 = u0.2 from by ring] at h
      exact (h.mp (Nat.even_add.mpr hiff)) hs0
    · -- north edge
      have hs0 : ((u0.1, u0.2) : ℤ × ℤ) ∈ curveV P S :=
        ⟨u0, hu0, w0, hnw0, rfl, Or.inl ⟨le_rfl, e2⟩⟩
      have hcells := hr u0.2 le_rfl e2
      refine ⟨(u0.1 - 1, u0.2), (u0.1, u0.2), hcells.1, hcells.2,
        fun hiff => ?_⟩
      have h := even_rayCross_add_right (curveV_finite hfin S) (u0.1 - 1) u0.2
      rw [show u0.1 - 1 + 1 = u0.1 from by ring] at h
      exact (h.mp (Nat.even_add.mpr hiff)) hs0
    · -- south edge
      have hs0 : ((u0.1, u0.2 - 1) : ℤ × ℤ) ∈ curveV P S :=
        ⟨u0, hu0, w0, hnw0, rfl,
          Or.inr ⟨show w0.2 ≤ u0.2 - 1 by omega, show u0.2 - 1 < u0.2 by omega⟩⟩
      have hcells := hr (u0.2 - 1) (by omega) (by omega)
      refine ⟨(u0.1, u0.2 - 1), (u0.1 - 1, u0.2 - 1), hcells.1, hcells.2,
        fun hiff => ?_⟩
      have h := even_rayCross_add_right (curveV_finite hfin S) (u0.1 - 1)
        (u0.2 - 1)
      rw [show u0.1 - 1 + 1 = u0.1 from by ring] at h
      exact (h.mp (Nat.even_add.mpr hiff.symm)) hs0
  obtain ⟨dP, dO, hdP, hdO, hflip⟩ := href
  -- transfer: equal parity across any boundary segment is contradictory
  have htrans : ∀ c1 c2 : Cell, c1 ∈ P → c2 ∉ P →
      (Even ((rayCross (curveV P S) c1.1 c1.2).ncard) ↔
        Even ((rayCross (curveV P S) c2.1 c2.2).ncard)) → False := by
    intro c1 c2 hc1 hc2 hiff
    have h1 := par_const_of_path hfin hSn hSp
      (A := P) (fun p hp q hq => iff_of_true hp hq) hc1 (hconn hc1 hdP)
    have h2 := par_const_of_path hfin hSn hSp
      (A := Pᶜ) (fun p hp q hq => iff_of_false hp hq) hc2 (hsimp hc2 hdO)
    exact hflip (h1.symm.trans (hiff.trans h2))
  constructor
  · rintro ⟨tx, ty⟩ hb
    by_contra hnc
    have h := even_rayCross_add_right (curveV_finite hfin S) (tx - 1) ty
    rw [show tx - 1 + 1 = tx from by ring] at h
    have heq := Nat.even_add.mp (h.mpr hnc)
    by_cases hcell : (tx, ty) ∈ P
    · have hcell' : ((tx - 1, ty) : Cell) ∉ P := fun hm =>
        hb (iff_of_true hm hcell)
      exact htrans (tx, ty) (tx - 1, ty) hcell hcell' heq.symm
    · have hcell' : ((tx - 1, ty) : Cell) ∈ P := by
        by_contra h''
        exact hb (iff_of_false h'' hcell)
      exact htrans (tx - 1, ty) (tx, ty) hcell' hcell heq
  · rintro ⟨tx, ty⟩ hb
    by_contra hnc
    have h := even_rayCross_add_up (curveV_finite hfin S)
      (curveH_finite hfin S) (curve_degree hfin hSn hSp) tx (ty - 1)
    rw [show ty - 1 + 1 = ty from by ring] at h
    have heq := Nat.even_add.mp (h.mpr hnc)
    by_cases hcell : (tx, ty) ∈ P
    · have hcell' : ((tx, ty - 1) : Cell) ∉ P := fun hm =>
        hb (iff_of_true hm hcell)
      exact htrans (tx, ty) (tx, ty - 1) hcell hcell' heq.symm
    · have hcell' : ((tx, ty - 1) : Cell) ∈ P := by
        by_contra h''
        exact hb (iff_of_false h'' hcell)
      exact htrans (tx, ty - 1) (tx, ty) hcell' hcell heq

/-- **The boundary is a single cycle**: a nonempty family of vertices
    closed under the successor and predecessor contains *every* vertex of
    a connected, simply connected fat polyomino. -/
theorem vertex_mem_of_closed {P S : Set Cell} (hfin : P.Finite)
    (hconn : CellConnected P) (hsimp : CellConnected Pᶜ) (hfat : Fat 16 P)
    (hSv : ∀ u ∈ S, IsVertex P u)
    (hSn : ∀ u ∈ S, ∀ w, NextVtx P u w → w ∈ S)
    (hSp : ∀ u w, NextVtx P u w → w ∈ S → u ∈ S)
    (hne : S.Nonempty) :
    ∀ v : Cell, IsVertex P v → v ∈ S := by
  intro v hv
  obtain ⟨hcovV, -⟩ := curve_covers hfin hconn hsimp hfat hSv hSn hSp hne
  rcases not_and_or.mp hv.1 with h | h
  · -- the segment below `v` is on the boundary, hence on the curve
    have hbv : ((v.1, v.2 - 1) : ℤ × ℤ) ∈ bndV P := h
    exact vertex_mem_S_of_curveV hSn (hcovV hbv) hv rfl
      (Or.inr (show v.2 = v.2 - 1 + 1 by omega))
  · -- the segment above `v` is on the boundary, hence on the curve
    have hbv : ((v.1, v.2) : ℤ × ℤ) ∈ bndV P := h
    exact vertex_mem_S_of_curveV hSn (hcovV hbv) hv rfl (Or.inl rfl)

-- ============================================================
-- §8 The corridor chain and the main theorem
-- ============================================================
--
-- The geometric core, still to be proved (see
-- `docs/offset-polyomino-argument.md` for the construction, SL
-- 2026-07-07): one corridor rectangle per boundary edge of `P`, following
-- the boundary cycle; forward cuts at each vertex (from the offset vertex
-- to `∂P` at convex corners, from the `P`-vertex to the offset boundary
-- at reflex corners) make consecutive rectangles meet corner-to-corner.
-- Connectivity of `P` and of `Pᶜ` make the boundary a *single* cycle
-- (via the ray-crossing parity argument); fatness 16 keeps every
-- rectangle ≥ 6 in both dimensions and offset edges from crossing.

/-- **Consecutive edges are perpendicular**: the incoming and outgoing
    arms of a vertex never share an axis (same axis would make the 2×2
    pattern at the vertex row- or column-constant). -/
lemma NextVtx.perp {P : Set Cell} {p u w : Cell}
    (h1 : NextVtx P p u) (h2 : NextVtx P u w) :
    (p.2 = u.2 ∧ u.1 = w.1) ∨ (p.1 = u.1 ∧ u.2 = w.2) := by
  have hu := h2.1
  rcases h1.2.2 with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ <;>
    rw [e1] at hr <;>
    rcases h2.2.2 with ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩ | ⟨f1, f2, hr'⟩
  -- in E
  · have ha := hr (u.1 - 1) (by omega) (by omega)
    have hb := hr' u.1 le_rfl f2
    exact absurd ⟨iff_of_false ha.2 hb.2, iff_of_true ha.1 hb.1⟩ hu.1
  · have ha := hr (u.1 - 1) (by omega) (by omega)
    have hb := hr' (u.1 - 1) (by omega) (by omega)
    exact absurd ha.1 hb.2
  · exact Or.inl ⟨e1, f1⟩
  · exact Or.inl ⟨e1, f1⟩
  -- in W
  · have ha := hr u.1 le_rfl e2
    have hb := hr' u.1 le_rfl f2
    exact absurd hb.1 ha.2
  · have ha := hr u.1 le_rfl e2
    have hb := hr' (u.1 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_true hb.1 ha.1, iff_of_false hb.2 ha.2⟩ hu.1
  · exact Or.inl ⟨e1, f1⟩
  · exact Or.inl ⟨e1, f1⟩
  -- in N
  · exact Or.inr ⟨e1, f1⟩
  · exact Or.inr ⟨e1, f1⟩
  · have ha := hr (u.2 - 1) (by omega) (by omega)
    have hb := hr' u.2 le_rfl f2
    exact absurd ⟨iff_of_true ha.1 hb.1, iff_of_false ha.2 hb.2⟩ hu.2
  · have ha := hr (u.2 - 1) (by omega) (by omega)
    have hb := hr' (u.2 - 1) (by omega) (by omega)
    exact absurd hb.1 ha.2
  -- in S
  · exact Or.inr ⟨e1, f1⟩
  · exact Or.inr ⟨e1, f1⟩
  · have ha := hr u.2 le_rfl e2
    have hb := hr' u.2 le_rfl f2
    exact absurd hb.1 ha.2
  · have ha := hr u.2 le_rfl e2
    have hb := hr' (u.2 - 1) (by omega) (by omega)
    exact absurd ⟨iff_of_false hb.2 ha.2, iff_of_true hb.1 ha.1⟩ hu.2

-- ------------------------------------------------------------
-- The snapped offset lines and the corridor rectangle of an edge
-- ------------------------------------------------------------

/-- The least multiple of 3 at distance ≥ 6 to the right of `x`. -/
def snapE (x : ℤ) : ℤ := x + 6 + (-(x + 6)) % 3

/-- The greatest multiple of 3 at distance ≥ 6 to the left of `x`. -/
def snapW (x : ℤ) : ℤ := x - 6 - (x - 6) % 3

/-- The least even number at distance ≥ 6 above `y`. -/
def snapN (y : ℤ) : ℤ := y + 6 + (-(y + 6)) % 2

/-- The greatest even number at distance ≥ 6 below `y`. -/
def snapS (y : ℤ) : ℤ := y - 6 - (y - 6) % 2

lemma snapE_spec (x : ℤ) :
    3 ∣ snapE x ∧ x + 6 ≤ snapE x ∧ snapE x ≤ x + 8 := by
  unfold snapE
  omega

lemma snapW_spec (x : ℤ) :
    3 ∣ snapW x ∧ x - 8 ≤ snapW x ∧ snapW x ≤ x - 6 := by
  unfold snapW
  omega

lemma snapN_spec (y : ℤ) :
    2 ∣ snapN y ∧ y + 6 ≤ snapN y ∧ snapN y ≤ y + 7 := by
  unfold snapN
  omega

lemma snapS_spec (y : ℤ) :
    2 ∣ snapS y ∧ y - 7 ≤ snapS y ∧ snapS y ≤ y - 6 := by
  unfold snapS
  omega

/-- Left edge of the corridor rectangle of the edge `u → w`, whose
    predecessor vertex is `p` and successor vertex is `z`.  Following SL's
    forward-cut rule: at a *convex* start the rectangle begins at the
    offset line of the incoming edge; at a *reflex* end it absorbs the
    corner block up to the offset line of the outgoing edge.  Convexity is
    read off the turn: left turns (S→E, E→N, N→W, W→S) are convex. -/
def eX0 (p u w z : Cell) : ℤ :=
  if u.2 = w.2 then
    if u.1 < w.1 then (if u.2 < p.2 then snapE u.1 else u.1)
    else (if w.2 < z.2 then snapW w.1 else w.1)
  else if u.2 < w.2 then snapW u.1
  else u.1

/-- Right edge of the corridor rectangle of `u → w`. -/
def eX1 (p u w z : Cell) : ℤ :=
  if u.2 = w.2 then
    if u.1 < w.1 then (if z.2 < w.2 then snapE w.1 else w.1)
    else (if u.2 < p.2 then u.1 else snapW u.1)
  else if u.2 < w.2 then u.1
  else snapE u.1

/-- Bottom edge of the corridor rectangle of `u → w`. -/
def eY0 (p u w z : Cell) : ℤ :=
  if u.1 = w.1 then
    if u.2 < w.2 then (if p.1 < u.1 then snapN u.2 else u.2)
    else (if z.1 < w.1 then snapS w.2 else w.2)
  else if u.1 < w.1 then u.2
  else snapS u.2

/-- Top edge of the corridor rectangle of `u → w`. -/
def eY1 (p u w z : Cell) : ℤ :=
  if u.1 = w.1 then
    if u.2 < w.2 then (if w.1 < z.1 then snapN w.2 else w.2)
    else (if u.1 < p.1 then snapS u.2 else u.2)
  else if u.1 < w.1 then snapN u.2
  else u.2

/-- Entry corner of the rectangle of `u → w` (where the chain comes in
    from the rectangle of `p → u`). -/
def eEntry (p u w : Cell) : Corner :=
  if u.2 = w.2 then
    if u.1 < w.1 then (if u.2 < p.2 then .BL else .TL)
    else (if u.2 < p.2 then .BR else .TR)
  else if u.2 < w.2 then (if p.1 < u.1 then .BR else .BL)
  else (if u.1 < p.1 then .TL else .TR)

/-- Exit corner of the rectangle of `u → w` (where the chain leaves into
    the rectangle of `w → z`). -/
def eExit (u w z : Cell) : Corner :=
  if u.2 = w.2 then
    if u.1 < w.1 then (if w.2 < z.2 then .TR else .BR)
    else (if w.2 < z.2 then .TL else .BL)
  else if u.2 < w.2 then (if w.1 < z.1 then .TR else .TL)
  else (if z.1 < w.1 then .BL else .BR)

/-- Entry and exit corners of a rectangle are always distinct: the entry
    lies on the start side of the edge, the exit on the end side. -/
lemma eEntry_ne_eExit (p u w z : Cell) : eEntry p u w ≠ eExit u w z := by
  unfold eEntry eExit
  split_ifs <;> decide

/-- The corridor rectangle of the edge `u → w`, as a `RectPiece` (the
    `max`es are collapsed by `edgePiece_x1`/`edgePiece_y1` for a genuine
    edge). -/
def edgePiece (p u w z : Cell) : RectPiece where
  x0 := eX0 p u w z
  y0 := eY0 p u w z
  x1 := max (eX1 p u w z) (eX0 p u w z + 6)
  y1 := max (eY1 p u w z) (eY0 p u w z + 6)
  wide := le_max_right _ _
  tall := le_max_right _ _

/-- For a genuine edge the rectangle's sides are at least 6. -/
lemma eBounds {P : Set Cell} (hfat : Fat 16 P) {u w : Cell}
    (h : NextVtx P u w) (p z : Cell) :
    eX0 p u w z + 6 ≤ eX1 p u w z ∧ eY0 p u w z + 6 ≤ eY1 p u w z := by
  have hEu := snapE_spec u.1
  have hEw := snapE_spec w.1
  have hWu := snapW_spec u.1
  have hWw := snapW_spec w.1
  have hNu := snapN_spec u.2
  have hNw := snapN_spec w.2
  have hSu := snapS_spec u.2
  have hSw := snapS_spec w.2
  rcases h.far hfat with ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ <;>
    constructor <;>
    · simp only [eX0, eX1, eY0, eY1]
      split_ifs <;> omega

@[simp] lemma edgePiece_x0 (p u w z : Cell) :
    (edgePiece p u w z).x0 = eX0 p u w z := rfl

@[simp] lemma edgePiece_y0 (p u w z : Cell) :
    (edgePiece p u w z).y0 = eY0 p u w z := rfl

lemma edgePiece_x1 {P : Set Cell} (hfat : Fat 16 P) {u w : Cell}
    (h : NextVtx P u w) (p z : Cell) :
    (edgePiece p u w z).x1 = eX1 p u w z := by
  have := (eBounds hfat h p z).1
  simp only [edgePiece]
  omega

lemma edgePiece_y1 {P : Set Cell} (hfat : Fat 16 P) {u w : Cell}
    (h : NextVtx P u w) (p z : Cell) :
    (edgePiece p u w z).y1 = eY1 p u w z := by
  have := (eBounds hfat h p z).2
  simp only [edgePiece]
  omega

set_option linter.unusedSimpArgs false in
/-- **Consecutive corridor rectangles meet at a pushing corner**: the
    exit corner of the rectangle of `u → w` coincides with the entry
    corner of the rectangle of `w → z`, with edge-adjacent corner cells —
    at the forward-cut endpoint of the shared vertex `w`.  (The uniform
    simp lists over the eight configurations trip the unused-argument
    linter; disabled locally.) -/
lemma edgePiece_pushAdj {P : Set Cell} (hfat : Fat 16 P) {p u w z z' : Cell}
    (h2 : NextVtx P u w) (h3 : NextVtx P w z) :
    PushAdj (edgePiece p u w z) (edgePiece u w z z')
      (eExit u w z) (eEntry u w z) := by
  rcases h2.far hfat with ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ <;>
    rcases h3.far hfat with ⟨f1, f2, -⟩ | ⟨f1, f2, -⟩ | ⟨f1, f2, -⟩ | ⟨f1, f2, -⟩
  -- E, E / E, W : impossible
  · rcases NextVtx.perp h2 h3 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
  · rcases NextVtx.perp h2 h3 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
  -- E → N (convex): exit TR, entry BR
  · have hlt : u.1 < w.1 := by omega
    have hzw : w.2 < z.2 := by omega
    have hexit : eExit u w z = Corner.TR := by
      unfold eExit
      rw [if_pos e1, if_pos hlt, if_pos hzw]
    have hentry : eEntry u w z = Corner.BR := by
      unfold eEntry
      rw [if_neg (by omega : ¬w.2 = z.2), if_pos hzw, if_pos hlt]
    have hx1 : eX1 p u w z = w.1 := by
      unfold eX1
      rw [if_pos e1, if_pos hlt, if_neg (by omega : ¬z.2 < w.2)]
    have hy1 : eY1 p u w z = snapN u.2 := by
      unfold eY1
      rw [if_neg (by omega : ¬u.1 = w.1), if_pos hlt]
    have hx1' : eX1 u w z z' = w.1 := by
      unfold eX1
      rw [if_neg (by omega : ¬w.2 = z.2), if_pos hzw]
    have hy0' : eY0 u w z z' = snapN w.2 := by
      unfold eY0
      rw [if_pos f1, if_pos hzw, if_pos hlt]
    have hsn : snapN u.2 = snapN w.2 := by rw [e1]
    rw [hexit, hentry]
    constructor
    · simp only [RectPiece.cornerPt, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx1, hy1, hx1', hy0', hsn]
    · simp only [RectPiece.cornerCell, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx1, hy1, hx1', hy0', CellAdj, true_and, and_true]
      omega
  -- E → S (reflex): exit BR, entry TR
  · have hlt : u.1 < w.1 := by omega
    have hzw : z.2 < w.2 := by omega
    have hexit : eExit u w z = Corner.BR := by
      unfold eExit
      rw [if_pos e1, if_pos hlt, if_neg (by omega : ¬w.2 < z.2)]
    have hentry : eEntry u w z = Corner.TR := by
      unfold eEntry
      rw [if_neg (by omega : ¬w.2 = z.2), if_neg (by omega : ¬w.2 < z.2),
        if_neg (by omega : ¬w.1 < u.1)]
    have hx1 : eX1 p u w z = snapE w.1 := by
      unfold eX1
      rw [if_pos e1, if_pos hlt, if_pos hzw]
    have hy0 : eY0 p u w z = u.2 := by
      unfold eY0
      rw [if_neg (by omega : ¬u.1 = w.1), if_pos hlt]
    have hx1' : eX1 u w z z' = snapE w.1 := by
      unfold eX1
      rw [if_neg (by omega : ¬w.2 = z.2), if_neg (by omega : ¬w.2 < z.2)]
    have hy1' : eY1 u w z z' = w.2 := by
      unfold eY1
      rw [if_pos f1, if_neg (by omega : ¬w.2 < z.2),
        if_neg (by omega : ¬w.1 < u.1)]
    have hse : u.2 = w.2 := e1
    rw [hexit, hentry]
    constructor
    · simp only [RectPiece.cornerPt, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx1, hy0, hx1', hy1', hse]
    · simp only [RectPiece.cornerCell, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx1, hy0, hx1', hy1', CellAdj, true_and, and_true]
      omega
  -- W, E / W, W : impossible
  · rcases NextVtx.perp h2 h3 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
  · rcases NextVtx.perp h2 h3 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
  -- W → N (reflex): exit TL, entry BL
  · have hlt : w.1 < u.1 := by omega
    have hzw : w.2 < z.2 := by omega
    have hexit : eExit u w z = Corner.TL := by
      unfold eExit
      rw [if_pos e1, if_neg (by omega : ¬u.1 < w.1), if_pos hzw]
    have hentry : eEntry u w z = Corner.BL := by
      unfold eEntry
      rw [if_neg (by omega : ¬w.2 = z.2), if_pos hzw,
        if_neg (by omega : ¬u.1 < w.1)]
    have hx0 : eX0 p u w z = snapW w.1 := by
      unfold eX0
      rw [if_pos e1, if_neg (by omega : ¬u.1 < w.1), if_pos hzw]
    have hy1 : eY1 p u w z = u.2 := by
      unfold eY1
      rw [if_neg (by omega : ¬u.1 = w.1), if_neg (by omega : ¬u.1 < w.1)]
    have hx0' : eX0 u w z z' = snapW w.1 := by
      unfold eX0
      rw [if_neg (by omega : ¬w.2 = z.2), if_pos hzw]
    have hy0' : eY0 u w z z' = w.2 := by
      unfold eY0
      rw [if_pos f1, if_pos hzw, if_neg (by omega : ¬u.1 < w.1)]
    have hse : u.2 = w.2 := e1
    rw [hexit, hentry]
    constructor
    · simp only [RectPiece.cornerPt, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx0, hy1, hx0', hy0', hse]
    · simp only [RectPiece.cornerCell, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx0, hy1, hx0', hy0', CellAdj, true_and, and_true]
      omega
  -- W → S (convex): exit BL, entry TL
  · have hlt : w.1 < u.1 := by omega
    have hzw : z.2 < w.2 := by omega
    have hexit : eExit u w z = Corner.BL := by
      unfold eExit
      rw [if_pos e1, if_neg (by omega : ¬u.1 < w.1),
        if_neg (by omega : ¬w.2 < z.2)]
    have hentry : eEntry u w z = Corner.TL := by
      unfold eEntry
      rw [if_neg (by omega : ¬w.2 = z.2), if_neg (by omega : ¬w.2 < z.2),
        if_pos hlt]
    have hx0 : eX0 p u w z = w.1 := by
      unfold eX0
      rw [if_pos e1, if_neg (by omega : ¬u.1 < w.1),
        if_neg (by omega : ¬w.2 < z.2)]
    have hy0 : eY0 p u w z = snapS u.2 := by
      unfold eY0
      rw [if_neg (by omega : ¬u.1 = w.1), if_neg (by omega : ¬u.1 < w.1)]
    have hx0' : eX0 u w z z' = w.1 := by
      unfold eX0
      rw [if_neg (by omega : ¬w.2 = z.2), if_neg (by omega : ¬w.2 < z.2)]
    have hy1' : eY1 u w z z' = snapS w.2 := by
      unfold eY1
      rw [if_pos f1, if_neg (by omega : ¬w.2 < z.2), if_pos hlt]
    have hss : snapS u.2 = snapS w.2 := by rw [e1]
    rw [hexit, hentry]
    constructor
    · simp only [RectPiece.cornerPt, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx0, hy0, hx0', hy1', hss]
    · simp only [RectPiece.cornerCell, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx0, hy0, hx0', hy1', CellAdj, true_and, and_true]
      omega
  -- N → E (reflex): exit TR, entry TL
  · have hlt : u.2 < w.2 := by omega
    have hzw : w.1 < z.1 := by omega
    have hexit : eExit u w z = Corner.TR := by
      unfold eExit
      rw [if_neg (by omega : ¬u.2 = w.2), if_pos hlt, if_pos hzw]
    have hentry : eEntry u w z = Corner.TL := by
      unfold eEntry
      rw [if_pos f1, if_pos hzw, if_neg (by omega : ¬w.2 < u.2)]
    have hx1 : eX1 p u w z = u.1 := by
      unfold eX1
      rw [if_neg (by omega : ¬u.2 = w.2), if_pos hlt]
    have hy1 : eY1 p u w z = snapN w.2 := by
      unfold eY1
      rw [if_pos e1, if_pos hlt, if_pos hzw]
    have hx0' : eX0 u w z z' = w.1 := by
      unfold eX0
      rw [if_pos f1, if_pos hzw, if_neg (by omega : ¬w.2 < u.2)]
    have hy1' : eY1 u w z z' = snapN w.2 := by
      unfold eY1
      rw [if_neg (by omega : ¬w.1 = z.1), if_pos hzw]
    have hse : u.1 = w.1 := e1
    rw [hexit, hentry]
    constructor
    · simp only [RectPiece.cornerPt, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx1, hy1, hx0', hy1', hse]
    · simp only [RectPiece.cornerCell, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx1, hy1, hx0', hy1', CellAdj, true_and, and_true]
      omega
  -- N → W (convex): exit TL, entry TR
  · have hlt : u.2 < w.2 := by omega
    have hzw : z.1 < w.1 := by omega
    have hexit : eExit u w z = Corner.TL := by
      unfold eExit
      rw [if_neg (by omega : ¬u.2 = w.2), if_pos hlt,
        if_neg (by omega : ¬w.1 < z.1)]
    have hentry : eEntry u w z = Corner.TR := by
      unfold eEntry
      rw [if_pos f1, if_neg (by omega : ¬w.1 < z.1),
        if_neg (by omega : ¬w.2 < u.2)]
    have hx0 : eX0 p u w z = snapW u.1 := by
      unfold eX0
      rw [if_neg (by omega : ¬u.2 = w.2), if_pos hlt]
    have hy1 : eY1 p u w z = w.2 := by
      unfold eY1
      rw [if_pos e1, if_pos hlt, if_neg (by omega : ¬w.1 < z.1)]
    have hx1' : eX1 u w z z' = snapW w.1 := by
      unfold eX1
      rw [if_pos f1, if_neg (by omega : ¬w.1 < z.1),
        if_neg (by omega : ¬w.2 < u.2)]
    have hy1' : eY1 u w z z' = w.2 := by
      unfold eY1
      rw [if_neg (by omega : ¬w.1 = z.1), if_neg (by omega : ¬w.1 < z.1)]
    have hsw : snapW u.1 = snapW w.1 := by rw [e1]
    rw [hexit, hentry]
    constructor
    · simp only [RectPiece.cornerPt, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx0, hy1, hx1', hy1', hsw]
    · simp only [RectPiece.cornerCell, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx0, hy1, hx1', hy1', CellAdj, true_and, and_true]
      omega
  -- N, N / N, S : impossible
  · rcases NextVtx.perp h2 h3 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
  · rcases NextVtx.perp h2 h3 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
  -- S → E (convex): exit BR, entry BL
  · have hlt : w.2 < u.2 := by omega
    have hzw : w.1 < z.1 := by omega
    have hexit : eExit u w z = Corner.BR := by
      unfold eExit
      rw [if_neg (by omega : ¬u.2 = w.2), if_neg (by omega : ¬u.2 < w.2),
        if_neg (by omega : ¬z.1 < w.1)]
    have hentry : eEntry u w z = Corner.BL := by
      unfold eEntry
      rw [if_pos f1, if_pos hzw, if_pos hlt]
    have hx1 : eX1 p u w z = snapE u.1 := by
      unfold eX1
      rw [if_neg (by omega : ¬u.2 = w.2), if_neg (by omega : ¬u.2 < w.2)]
    have hy0 : eY0 p u w z = w.2 := by
      unfold eY0
      rw [if_pos e1, if_neg (by omega : ¬u.2 < w.2),
        if_neg (by omega : ¬z.1 < w.1)]
    have hx0' : eX0 u w z z' = snapE w.1 := by
      unfold eX0
      rw [if_pos f1, if_pos hzw, if_pos hlt]
    have hy0' : eY0 u w z z' = w.2 := by
      unfold eY0
      rw [if_neg (by omega : ¬w.1 = z.1), if_pos hzw]
    have hse : snapE u.1 = snapE w.1 := by rw [e1]
    rw [hexit, hentry]
    constructor
    · simp only [RectPiece.cornerPt, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx1, hy0, hx0', hy0', hse]
    · simp only [RectPiece.cornerCell, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx1, hy0, hx0', hy0', CellAdj, true_and, and_true]
      omega
  -- S → W (reflex): exit BL, entry BR
  · have hlt : w.2 < u.2 := by omega
    have hzw : z.1 < w.1 := by omega
    have hexit : eExit u w z = Corner.BL := by
      unfold eExit
      rw [if_neg (by omega : ¬u.2 = w.2), if_neg (by omega : ¬u.2 < w.2),
        if_pos hzw]
    have hentry : eEntry u w z = Corner.BR := by
      unfold eEntry
      rw [if_pos f1, if_neg (by omega : ¬w.1 < z.1), if_pos hlt]
    have hx0 : eX0 p u w z = u.1 := by
      unfold eX0
      rw [if_neg (by omega : ¬u.2 = w.2), if_neg (by omega : ¬u.2 < w.2)]
    have hy0 : eY0 p u w z = snapS w.2 := by
      unfold eY0
      rw [if_pos e1, if_neg (by omega : ¬u.2 < w.2), if_pos hzw]
    have hx1' : eX1 u w z z' = w.1 := by
      unfold eX1
      rw [if_pos f1, if_neg (by omega : ¬w.1 < z.1), if_pos hlt]
    have hy0' : eY0 u w z z' = snapS w.2 := by
      unfold eY0
      rw [if_neg (by omega : ¬w.1 = z.1), if_neg (by omega : ¬w.1 < z.1)]
    have hse : u.1 = w.1 := e1
    rw [hexit, hentry]
    constructor
    · simp only [RectPiece.cornerPt, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx0, hy0, hx1', hy0', hse]
    · simp only [RectPiece.cornerCell, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat h2, edgePiece_y1 hfat h2, edgePiece_x1 hfat h3,
        edgePiece_y1 hfat h3, hx0, hy0, hx1', hy0', CellAdj, true_and, and_true]
      omega
  -- S, N / S, S : impossible
  · rcases NextVtx.perp h2 h3 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
  · rcases NextVtx.perp h2 h3 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega

open Set

set_option linter.unusedVariables false in
/-- **Corridor rectangles lie in the corridor.**  Membership in `P`: within
    the longitudinal span of the edge the interior band (`band_in_*`)
    applies directly; in the reflex-end extension past `w` (present only
    when the outgoing edge turns right) the cell lies in `box w 16` and the
    quadrant picture at `w` — pinned down by the last cells of the incoming
    run and the first cell of the outgoing run — forces the reflex corner
    whose complement contains the cell.  Exclusion from `offsetCore`: the
    safety box of every rectangle cell reaches a cell of the exterior band
    (`band_out_*` at depth 0), because the transverse side of the rectangle
    stops at the snapped offset line, at distance ≤ 8 from the edge.
    (`h1` is kept for signature parity with the corridor-chain assembly;
    the proof only needs the edge `h2` and its successor `h3`.) -/
theorem edgePiece_subset_corridor {P : Set Cell} (hfin : P.Finite)
    (hfat : Fat 16 P) {p u w z : Cell}
    (h1 : NextVtx P p u) (h2 : NextVtx P u w) (h3 : NextVtx P w z) :
    (edgePiece p u w z).cells ⊆ corridor P := by
  intro q hq
  simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
    edgePiece_x1 hfat h2 p z, edgePiece_y1 hfat h2 p z] at hq
  obtain ⟨hqx0, hqx1, hqy0, hqy1⟩ := hq
  change q ∈ P ∧ q ∉ offsetCore P
  rcases h2.far hfat with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ |
    ⟨e1, e2, hr⟩
  -- EAST edge: interior above, rows [u.2, snapN u.2)
  · have hlt : u.1 < w.1 := by omega
    have hne : ¬u.1 = w.1 := by omega
    have hy0 : eY0 p u w z = u.2 := by
      unfold eY0; rw [if_neg hne, if_pos hlt]
    have hy1 : eY1 p u w z = snapN u.2 := by
      unfold eY1; rw [if_neg hne, if_pos hlt]
    have hsN := snapN_spec u.2
    have hx0 : u.1 ≤ eX0 p u w z := by
      have hsEu := snapE_spec u.1
      unfold eX0; rw [if_pos e1, if_pos hlt]; split_ifs <;> omega
    rw [hy0] at hqy0
    rw [hy1] at hqy1
    have hqx : u.1 ≤ q.1 := by omega
    rcases (by omega : q.1 < w.1 ∨ w.1 ≤ q.1) with hql | hqg
    · -- within the edge span
      refine ⟨?_, ?_⟩
      · have hmem := band_in_east hfin hfat h2 e1 hlt q.1 (q.2 - u.2) hqx hql
          (by omega) (by omega)
        rw [show u.2 + (q.2 - u.2) = q.2 from by ring] at hmem
        exact hmem
      · intro hcore
        have hsub : offBox (cornerOf q) ⊆ P := hcore
        have hout := band_out_east hfin hfat h2 e1 hlt q.1 0 hqx hql le_rfl
          (by omega)
        rw [sub_zero] at hout
        exact hout (hsub (by simp only [offBox, cornerOf, mem_rect]; omega))
    · -- the reflex-end extension past `w`: the outgoing edge goes south
      have hz : z.2 < w.2 := by
        by_contra hz
        have hx1 : eX1 p u w z = w.1 := by
          unfold eX1; rw [if_pos e1, if_pos hlt, if_neg hz]
        omega
      have hx1 : eX1 p u w z = snapE w.1 := by
        unfold eX1; rw [if_pos e1, if_pos hlt, if_pos hz]
      rw [hx1] at hqx1
      have hsEw := snapE_spec w.1
      refine ⟨?_, ?_⟩
      · rcases h3.far hfat with ⟨f1, -, -⟩ | ⟨f1, -, -⟩ | ⟨-, f2, -⟩ |
          ⟨-, -, hr3⟩
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
        · have hA : ((w.1 - 1, w.2) : Cell) ∈ P := by
            have h' := (hr (w.1 - 1) (by omega) (by omega)).1
            rwa [e1] at h'
          have hB : ((w.1, w.2 - 1) : Cell) ∈ P :=
            (hr3 (w.2 - 1) (by omega) (by omega)).1
          have hC : ((w.1 - 1, w.2 - 1) : Cell) ∉ P :=
            (hr3 (w.2 - 1) (by omega) (by omega)).2
          obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h2.2.1
          · exfalso
            have hA' := (hcc (w.1 - 1, w.2)
              (by simp only [box, mem_rect]; omega)).mp hA
            have hB' := (hcc (w.1, w.2 - 1)
              (by simp only [box, mem_rect]; omega)).mp hB
            cases c <;> simp only [quadrant, Set.mem_setOf_eq] at hA' hB' <;>
              omega
          · have hC' : ((w.1 - 1, w.2 - 1) : Cell) ∈ quadrant w c := by
              by_contra hqd
              exact hC ((hcc (w.1 - 1, w.2 - 1)
                (by simp only [box, mem_rect]; omega)).mpr hqd)
            refine (hcc q (by simp only [box, mem_rect]; omega)).mpr ?_
            cases c <;> simp only [quadrant, Set.mem_setOf_eq] at hC' ⊢ <;>
              omega
      · intro hcore
        have hsub : offBox (cornerOf q) ⊆ P := hcore
        have hout := band_out_east hfin hfat h2 e1 hlt (w.1 - 1) 0 (by omega)
          (by omega) le_rfl (by omega)
        rw [sub_zero] at hout
        exact hout (hsub (by simp only [offBox, cornerOf, mem_rect]; omega))
  -- WEST edge: interior below, rows [snapS u.2, u.2)
  · have hlt : w.1 < u.1 := by omega
    have hne : ¬u.1 = w.1 := by omega
    have hnlt : ¬u.1 < w.1 := by omega
    have hy0 : eY0 p u w z = snapS u.2 := by
      unfold eY0; rw [if_neg hne, if_neg hnlt]
    have hy1 : eY1 p u w z = u.2 := by
      unfold eY1; rw [if_neg hne, if_neg hnlt]
    have hsS := snapS_spec u.2
    have hx1 : eX1 p u w z ≤ u.1 := by
      have hsWu := snapW_spec u.1
      unfold eX1; rw [if_pos e1, if_neg hnlt]; split_ifs <;> omega
    rw [hy0] at hqy0
    rw [hy1] at hqy1
    have hqx : q.1 < u.1 := by omega
    rcases (by omega : w.1 ≤ q.1 ∨ q.1 < w.1) with hql | hqg
    · -- within the edge span
      refine ⟨?_, ?_⟩
      · have hmem := band_in_west hfin hfat h2 e1 hlt q.1 (u.2 - 1 - q.2) hql
          hqx (by omega) (by omega)
        rw [show u.2 - 1 - (u.2 - 1 - q.2) = q.2 from by ring] at hmem
        exact hmem
      · intro hcore
        have hsub : offBox (cornerOf q) ⊆ P := hcore
        have hout := band_out_west hfin hfat h2 e1 hlt q.1 0 hql hqx le_rfl
          (by omega)
        rw [add_zero] at hout
        exact hout (hsub (by simp only [offBox, cornerOf, mem_rect]; omega))
    · -- the reflex-end extension past `w`: the outgoing edge goes north
      have hz : w.2 < z.2 := by
        by_contra hz
        have hx0 : eX0 p u w z = w.1 := by
          unfold eX0; rw [if_pos e1, if_neg hnlt, if_neg hz]
        omega
      have hx0 : eX0 p u w z = snapW w.1 := by
        unfold eX0; rw [if_pos e1, if_neg hnlt, if_pos hz]
      rw [hx0] at hqx0
      have hsWw := snapW_spec w.1
      refine ⟨?_, ?_⟩
      · rcases h3.far hfat with ⟨f1, -, -⟩ | ⟨f1, -, -⟩ | ⟨-, -, hr3⟩ |
          ⟨-, f2, -⟩
        · exfalso; omega
        · exfalso; omega
        · have hA : ((w.1, w.2 - 1) : Cell) ∈ P := by
            have h' := (hr w.1 le_rfl (by omega)).1
            rwa [e1] at h'
          have hB : ((w.1 - 1, w.2) : Cell) ∈ P :=
            (hr3 w.2 le_rfl (by omega)).1
          have hC : ((w.1, w.2) : Cell) ∉ P :=
            (hr3 w.2 le_rfl (by omega)).2
          obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h2.2.1
          · exfalso
            have hA' := (hcc (w.1, w.2 - 1)
              (by simp only [box, mem_rect]; omega)).mp hA
            have hB' := (hcc (w.1 - 1, w.2)
              (by simp only [box, mem_rect]; omega)).mp hB
            cases c <;> simp only [quadrant, Set.mem_setOf_eq] at hA' hB' <;>
              omega
          · have hC' : ((w.1, w.2) : Cell) ∈ quadrant w c := by
              by_contra hqd
              exact hC ((hcc (w.1, w.2)
                (by simp only [box, mem_rect]; omega)).mpr hqd)
            refine (hcc q (by simp only [box, mem_rect]; omega)).mpr ?_
            cases c <;> simp only [quadrant, Set.mem_setOf_eq] at hC' ⊢ <;>
              omega
        · exfalso; omega
      · intro hcore
        have hsub : offBox (cornerOf q) ⊆ P := hcore
        have hout := band_out_west hfin hfat h2 e1 hlt w.1 0 le_rfl (by omega)
          le_rfl (by omega)
        rw [add_zero] at hout
        exact hout (hsub (by simp only [offBox, cornerOf, mem_rect]; omega))
  -- NORTH edge: interior to the west, columns [snapW u.1, u.1)
  · have hlt : u.2 < w.2 := by omega
    have hne : ¬u.2 = w.2 := by omega
    have hx0 : eX0 p u w z = snapW u.1 := by
      unfold eX0; rw [if_neg hne, if_pos hlt]
    have hx1 : eX1 p u w z = u.1 := by
      unfold eX1; rw [if_neg hne, if_pos hlt]
    have hsW := snapW_spec u.1
    have hy0 : u.2 ≤ eY0 p u w z := by
      have hsNu := snapN_spec u.2
      unfold eY0; rw [if_pos e1, if_pos hlt]; split_ifs <;> omega
    rw [hx0] at hqx0
    rw [hx1] at hqx1
    have hqy : u.2 ≤ q.2 := by omega
    rcases (by omega : q.2 < w.2 ∨ w.2 ≤ q.2) with hql | hqg
    · -- within the edge span
      refine ⟨?_, ?_⟩
      · have hmem := band_in_north hfin hfat h2 e1 hlt q.2 (u.1 - 1 - q.1) hqy
          hql (by omega) (by omega)
        rw [show u.1 - 1 - (u.1 - 1 - q.1) = q.1 from by ring] at hmem
        exact hmem
      · intro hcore
        have hsub : offBox (cornerOf q) ⊆ P := hcore
        have hout := band_out_north hfin hfat h2 e1 hlt q.2 0 hqy hql le_rfl
          (by omega)
        rw [add_zero] at hout
        exact hout (hsub (by simp only [offBox, cornerOf, mem_rect]; omega))
    · -- the reflex-end extension past `w`: the outgoing edge goes east
      have hz : w.1 < z.1 := by
        by_contra hz
        have hy1 : eY1 p u w z = w.2 := by
          unfold eY1; rw [if_pos e1, if_pos hlt, if_neg hz]
        omega
      have hy1 : eY1 p u w z = snapN w.2 := by
        unfold eY1; rw [if_pos e1, if_pos hlt, if_pos hz]
      rw [hy1] at hqy1
      have hsNw := snapN_spec w.2
      refine ⟨?_, ?_⟩
      · rcases h3.far hfat with ⟨-, -, hr3⟩ | ⟨-, f2, -⟩ | ⟨f1, -, -⟩ |
          ⟨f1, -, -⟩
        · have hA : ((w.1 - 1, w.2 - 1) : Cell) ∈ P := by
            have h' := (hr (w.2 - 1) (by omega) (by omega)).1
            rwa [e1] at h'
          have hC : ((w.1, w.2 - 1) : Cell) ∉ P := by
            have h' := (hr (w.2 - 1) (by omega) (by omega)).2
            rwa [e1] at h'
          have hB : ((w.1, w.2) : Cell) ∈ P := (hr3 w.1 le_rfl (by omega)).1
          obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h2.2.1
          · exfalso
            have hA' := (hcc (w.1 - 1, w.2 - 1)
              (by simp only [box, mem_rect]; omega)).mp hA
            have hB' := (hcc (w.1, w.2)
              (by simp only [box, mem_rect]; omega)).mp hB
            cases c <;> simp only [quadrant, Set.mem_setOf_eq] at hA' hB' <;>
              omega
          · have hC' : ((w.1, w.2 - 1) : Cell) ∈ quadrant w c := by
              by_contra hqd
              exact hC ((hcc (w.1, w.2 - 1)
                (by simp only [box, mem_rect]; omega)).mpr hqd)
            refine (hcc q (by simp only [box, mem_rect]; omega)).mpr ?_
            cases c <;> simp only [quadrant, Set.mem_setOf_eq] at hC' ⊢ <;>
              omega
        · exfalso; omega
        · exfalso; omega
        · exfalso; omega
      · intro hcore
        have hsub : offBox (cornerOf q) ⊆ P := hcore
        have hout := band_out_north hfin hfat h2 e1 hlt (w.2 - 1) 0 (by omega)
          (by omega) le_rfl (by omega)
        rw [add_zero] at hout
        exact hout (hsub (by simp only [offBox, cornerOf, mem_rect]; omega))
  -- SOUTH edge: interior to the east, columns [u.1, snapE u.1)
  · have hlt : w.2 < u.2 := by omega
    have hne : ¬u.2 = w.2 := by omega
    have hnlt : ¬u.2 < w.2 := by omega
    have hx0 : eX0 p u w z = u.1 := by
      unfold eX0; rw [if_neg hne, if_neg hnlt]
    have hx1 : eX1 p u w z = snapE u.1 := by
      unfold eX1; rw [if_neg hne, if_neg hnlt]
    have hsE := snapE_spec u.1
    have hy1 : eY1 p u w z ≤ u.2 := by
      have hsSu := snapS_spec u.2
      unfold eY1; rw [if_pos e1, if_neg hnlt]; split_ifs <;> omega
    rw [hx0] at hqx0
    rw [hx1] at hqx1
    have hqy : q.2 < u.2 := by omega
    rcases (by omega : w.2 ≤ q.2 ∨ q.2 < w.2) with hql | hqg
    · -- within the edge span
      refine ⟨?_, ?_⟩
      · have hmem := band_in_south hfin hfat h2 e1 hlt q.2 (q.1 - u.1) hql hqy
          (by omega) (by omega)
        rw [show u.1 + (q.1 - u.1) = q.1 from by ring] at hmem
        exact hmem
      · intro hcore
        have hsub : offBox (cornerOf q) ⊆ P := hcore
        have hout := band_out_south hfin hfat h2 e1 hlt q.2 0 hql hqy le_rfl
          (by omega)
        rw [sub_zero] at hout
        exact hout (hsub (by simp only [offBox, cornerOf, mem_rect]; omega))
    · -- the reflex-end extension past `w`: the outgoing edge goes west
      have hz : z.1 < w.1 := by
        by_contra hz
        have hy0 : eY0 p u w z = w.2 := by
          unfold eY0; rw [if_pos e1, if_neg hnlt, if_neg hz]
        omega
      have hy0 : eY0 p u w z = snapS w.2 := by
        unfold eY0; rw [if_pos e1, if_neg hnlt, if_pos hz]
      rw [hy0] at hqy0
      have hsSw := snapS_spec w.2
      refine ⟨?_, ?_⟩
      · rcases h3.far hfat with ⟨-, f2, -⟩ | ⟨-, -, hr3⟩ | ⟨f1, -, -⟩ |
          ⟨f1, -, -⟩
        · exfalso; omega
        · have hA : ((w.1, w.2) : Cell) ∈ P := by
            have h' := (hr w.2 le_rfl (by omega)).1
            rwa [e1] at h'
          have hC : ((w.1 - 1, w.2) : Cell) ∉ P := by
            have h' := (hr w.2 le_rfl (by omega)).2
            rwa [e1] at h'
          have hB : ((w.1 - 1, w.2 - 1) : Cell) ∈ P :=
            (hr3 (w.1 - 1) (by omega) (by omega)).1
          obtain ⟨c, hcc | hcc⟩ := hfat.mem_iff h2.2.1
          · exfalso
            have hA' := (hcc (w.1, w.2)
              (by simp only [box, mem_rect]; omega)).mp hA
            have hB' := (hcc (w.1 - 1, w.2 - 1)
              (by simp only [box, mem_rect]; omega)).mp hB
            cases c <;> simp only [quadrant, Set.mem_setOf_eq] at hA' hB' <;>
              omega
          · have hC' : ((w.1 - 1, w.2) : Cell) ∈ quadrant w c := by
              by_contra hqd
              exact hC ((hcc (w.1 - 1, w.2)
                (by simp only [box, mem_rect]; omega)).mpr hqd)
            refine (hcc q (by simp only [box, mem_rect]; omega)).mpr ?_
            cases c <;> simp only [quadrant, Set.mem_setOf_eq] at hC' ⊢ <;>
              omega
        · exfalso; omega
        · exfalso; omega
      · intro hcore
        have hsub : offBox (cornerOf q) ⊆ P := hcore
        have hout := band_out_south hfin hfat h2 e1 hlt w.2 0 le_rfl (by omega)
          le_rfl (by omega)
        rw [sub_zero] at hout
        exact hout (hsub (by simp only [offBox, cornerOf, mem_rect]; omega))

/-! Proof of `edgePiece_disjoint` (primed name), for paste-back into
    `TilingPolyomino/OffsetPolyomino.lean`. -/

/-- Two distinct boundary vertices are ≥ 16 apart in x or in y
    (packaging of `Fat.vertex_isolated`). -/
private lemma sep16 {P : Set Cell} (hfat : Fat 16 P) {a b : Cell}
    (ha : IsVertex P a) (hb : IsVertex P b)
    (hxy : b.1 ≠ a.1 ∨ b.2 ≠ a.2)
    (h1 : a.1 - 16 < b.1) (h2 : b.1 < a.1 + 16)
    (h3 : a.2 - 16 < b.2) (h4 : b.2 < a.2 + 16) : False := by
  refine hfat.vertex_isolated ha hb (fun hh => ?_) h1 h2 h3 h4
  rcases hxy with h | h
  · exact h (congrArg Prod.fst hh)
  · exact h (congrArg Prod.snd hh)

/-- Coarse window of the corridor rectangle of an east edge. -/
private lemma windowE {p u w z q : Cell} (e1 : u.2 = w.2) (e2 : u.1 + 16 ≤ w.1)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z) :
    u.1 ≤ q.1 ∧ q.1 ≤ w.1 + 7 ∧ u.2 ≤ q.2 ∧ q.2 ≤ u.2 + 6 := by
  have hEu := snapE_spec u.1; have hEw := snapE_spec w.1
  have hNu := snapN_spec u.2
  unfold eX0 eX1 eY0 eY1 at hq
  split_ifs at hq <;> omega

/-- Coarse window of the corridor rectangle of a west edge. -/
private lemma windowW {p u w z q : Cell} (e1 : u.2 = w.2) (e2 : w.1 + 16 ≤ u.1)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z) :
    w.1 - 8 ≤ q.1 ∧ q.1 ≤ u.1 - 1 ∧ u.2 - 7 ≤ q.2 ∧ q.2 ≤ u.2 - 1 := by
  have hWu := snapW_spec u.1; have hWw := snapW_spec w.1
  have hSu := snapS_spec u.2
  unfold eX0 eX1 eY0 eY1 at hq
  split_ifs at hq <;> omega

/-- Coarse window of the corridor rectangle of a north edge. -/
private lemma windowN {p u w z q : Cell} (e1 : u.1 = w.1) (e2 : u.2 + 16 ≤ w.2)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z) :
    u.1 - 8 ≤ q.1 ∧ q.1 ≤ u.1 - 1 ∧ u.2 ≤ q.2 ∧ q.2 ≤ w.2 + 6 := by
  have hWu := snapW_spec u.1
  have hNu := snapN_spec u.2; have hNw := snapN_spec w.2
  unfold eX0 eX1 eY0 eY1 at hq
  split_ifs at hq <;> omega

/-- Coarse window of the corridor rectangle of a south edge. -/
private lemma windowS {p u w z q : Cell} (e1 : u.1 = w.1) (e2 : w.2 + 16 ≤ u.2)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z) :
    u.1 ≤ q.1 ∧ q.1 ≤ u.1 + 7 ∧ w.2 - 7 ≤ q.2 ∧ q.2 ≤ u.2 - 1 := by
  have hEu := snapE_spec u.1
  have hSu := snapS_spec u.2; have hSw := snapS_spec w.2
  unfold eX0 eX1 eY0 eY1 at hq
  split_ifs at hq <;> omega

/-- Two east edges with `u.2 ≤ u'.2`: no shared cell. -/
private lemma clash_EE {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {p u w z p' u' w' z' q : Cell}
    (h2 : NextVtx P u w) (h2' : NextVtx P u' w') (hne : u ≠ u')
    (e1 : u.2 = w.2) (e2 : u.1 + 16 ≤ w.1)
    (e1' : u'.2 = w'.2) (e2' : u'.1 + 16 ≤ w'.1)
    (hr' : HRunAbove P u'.2 u'.1 w'.1)
    (hle : u.2 ≤ u'.2)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z)
    (hq' : eX0 p' u' w' z' ≤ q.1 ∧ q.1 < eX1 p' u' w' z' ∧
      eY0 p' u' w' z' ≤ q.2 ∧ q.2 < eY1 p' u' w' z') :
    False := by
  have hW := windowE e1 e2 hq
  have hW' := windowE e1' e2' hq'
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- same boundary line
    by_cases hA1 : u.1 ≤ u'.1 ∧ u'.1 ≤ w.1
    · rcases endpoint_of_vertexH h2 h2'.1 (by omega) (Or.inl hA1) with hh | hh
      · exact hne hh.symm
      · have hh1 := congrArg Prod.fst hh
        rw [hh] at h2'
        rcases NextVtx.perp h2 h2' with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
    · by_cases hA2 : u'.1 ≤ u.1 ∧ u.1 ≤ w'.1
      · rcases endpoint_of_vertexH h2' h2.1 (by omega) (Or.inl hA2) with hh | hh
        · exact hne hh
        · have hh1 := congrArg Prod.fst hh
          rw [hh] at h2
          rcases NextVtx.perp h2' h2 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
      · rcases le_or_gt u.1 u'.1 with hc | hc
        · exact sep16 hfat h2.2.1 h2'.1 (Or.inl (by omega))
            (by omega) (by omega) (by omega) (by omega)
        · exact sep16 hfat h2'.2.1 h2.1 (Or.inl (by omega))
            (by omega) (by omega) (by omega) (by omega)
  · -- edge 2 strictly higher: run of edge 2 vs in-band of edge 1
    by_cases hB : u'.1 < w.1 ∧ u.1 < w'.1
    · have hin := band_in_east hfin hfat h2 e1 (by omega)
        (max u.1 u'.1) (u'.2 - 1 - u.2) (le_max_left _ _)
        (by omega) (by omega) (by omega)
      rw [show u.2 + (u'.2 - 1 - u.2) = u'.2 - 1 from by ring] at hin
      exact (hr' (max u.1 u'.1) (le_max_right _ _) (by omega)).2 hin
    · rcases le_or_gt w.1 u'.1 with hc | hc
      · exact sep16 hfat h2.2.1 h2'.1 (Or.inr (by omega))
          (by omega) (by omega) (by omega) (by omega)
      · exact sep16 hfat h2'.2.1 h2.1 (Or.inr (by omega))
          (by omega) (by omega) (by omega) (by omega)

/-- Two west edges with `u'.2 ≤ u.2`: no shared cell. -/
private lemma clash_WW {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {p u w z p' u' w' z' q : Cell}
    (h2 : NextVtx P u w) (h2' : NextVtx P u' w') (hne : u ≠ u')
    (e1 : u.2 = w.2) (e2 : w.1 + 16 ≤ u.1)
    (e1' : u'.2 = w'.2) (e2' : w'.1 + 16 ≤ u'.1)
    (hr' : HRunBelow P u'.2 w'.1 u'.1)
    (hle : u'.2 ≤ u.2)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z)
    (hq' : eX0 p' u' w' z' ≤ q.1 ∧ q.1 < eX1 p' u' w' z' ∧
      eY0 p' u' w' z' ≤ q.2 ∧ q.2 < eY1 p' u' w' z') :
    False := by
  have hW := windowW e1 e2 hq
  have hW' := windowW e1' e2' hq'
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- same boundary line
    by_cases hA1 : w.1 ≤ u'.1 ∧ u'.1 ≤ u.1
    · rcases endpoint_of_vertexH h2 h2'.1 (by omega) (Or.inr hA1) with hh | hh
      · exact hne hh.symm
      · have hh1 := congrArg Prod.fst hh
        rw [hh] at h2'
        rcases NextVtx.perp h2 h2' with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
    · by_cases hA2 : w'.1 ≤ u.1 ∧ u.1 ≤ u'.1
      · rcases endpoint_of_vertexH h2' h2.1 (by omega) (Or.inr hA2) with hh | hh
        · exact hne hh
        · have hh1 := congrArg Prod.fst hh
          rw [hh] at h2
          rcases NextVtx.perp h2' h2 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
      · rcases le_or_gt u'.1 u.1 with hc | hc
        · exact sep16 hfat h2.2.1 h2'.1 (Or.inl (by omega))
            (by omega) (by omega) (by omega) (by omega)
        · exact sep16 hfat h2'.2.1 h2.1 (Or.inl (by omega))
            (by omega) (by omega) (by omega) (by omega)
  · -- edge 2 strictly lower: run of edge 2 vs in-band of edge 1
    by_cases hB : w'.1 < u.1 ∧ w.1 < u'.1
    · have hin := band_in_west hfin hfat h2 e1 (by omega)
        (max w.1 w'.1) (u.2 - 1 - u'.2) (le_max_left _ _)
        (by omega) (by omega) (by omega)
      rw [show u.2 - 1 - (u.2 - 1 - u'.2) = u'.2 from by ring] at hin
      exact (hr' (max w.1 w'.1) (le_max_right _ _) (by omega)).2 hin
    · rcases le_or_gt u.1 w'.1 with hc | hc
      · exact sep16 hfat h2'.2.1 h2.1 (Or.inr (by omega))
          (by omega) (by omega) (by omega) (by omega)
      · exact sep16 hfat h2.2.1 h2'.1 (Or.inr (by omega))
          (by omega) (by omega) (by omega) (by omega)

/-- Two north edges with `u'.1 ≤ u.1`: no shared cell. -/
private lemma clash_NN {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {p u w z p' u' w' z' q : Cell}
    (h2 : NextVtx P u w) (h2' : NextVtx P u' w') (hne : u ≠ u')
    (e1 : u.1 = w.1) (e2 : u.2 + 16 ≤ w.2)
    (e1' : u'.1 = w'.1) (e2' : u'.2 + 16 ≤ w'.2)
    (hr' : VRunLeft P u'.1 u'.2 w'.2)
    (hle : u'.1 ≤ u.1)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z)
    (hq' : eX0 p' u' w' z' ≤ q.1 ∧ q.1 < eX1 p' u' w' z' ∧
      eY0 p' u' w' z' ≤ q.2 ∧ q.2 < eY1 p' u' w' z') :
    False := by
  have hW := windowN e1 e2 hq
  have hW' := windowN e1' e2' hq'
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- same boundary line
    by_cases hA1 : u.2 ≤ u'.2 ∧ u'.2 ≤ w.2
    · rcases endpoint_of_vertexV h2 h2'.1 (by omega) (Or.inl hA1) with hh | hh
      · exact hne hh.symm
      · have hh2 := congrArg Prod.snd hh
        rw [hh] at h2'
        rcases NextVtx.perp h2 h2' with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
    · by_cases hA2 : u'.2 ≤ u.2 ∧ u.2 ≤ w'.2
      · rcases endpoint_of_vertexV h2' h2.1 (by omega) (Or.inl hA2) with hh | hh
        · exact hne hh
        · have hh2 := congrArg Prod.snd hh
          rw [hh] at h2
          rcases NextVtx.perp h2' h2 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
      · rcases le_or_gt u.2 u'.2 with hc | hc
        · exact sep16 hfat h2.2.1 h2'.1 (Or.inr (by omega))
            (by omega) (by omega) (by omega) (by omega)
        · exact sep16 hfat h2'.2.1 h2.1 (Or.inr (by omega))
            (by omega) (by omega) (by omega) (by omega)
  · -- edge 2 strictly to the left: run of edge 2 vs in-band of edge 1
    by_cases hB : u'.2 < w.2 ∧ u.2 < w'.2
    · have hin := band_in_north hfin hfat h2 e1 (by omega)
        (max u.2 u'.2) (u.1 - 1 - u'.1) (le_max_left _ _)
        (by omega) (by omega) (by omega)
      rw [show u.1 - 1 - (u.1 - 1 - u'.1) = u'.1 from by ring] at hin
      exact (hr' (max u.2 u'.2) (le_max_right _ _) (by omega)).2 hin
    · rcases le_or_gt w.2 u'.2 with hc | hc
      · exact sep16 hfat h2.2.1 h2'.1 (Or.inl (by omega))
          (by omega) (by omega) (by omega) (by omega)
      · exact sep16 hfat h2'.2.1 h2.1 (Or.inl (by omega))
          (by omega) (by omega) (by omega) (by omega)

/-- Two south edges with `u.1 ≤ u'.1`: no shared cell. -/
private lemma clash_SS {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {p u w z p' u' w' z' q : Cell}
    (h2 : NextVtx P u w) (h2' : NextVtx P u' w') (hne : u ≠ u')
    (e1 : u.1 = w.1) (e2 : w.2 + 16 ≤ u.2)
    (e1' : u'.1 = w'.1) (e2' : w'.2 + 16 ≤ u'.2)
    (hr' : VRunRight P u'.1 w'.2 u'.2)
    (hle : u.1 ≤ u'.1)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z)
    (hq' : eX0 p' u' w' z' ≤ q.1 ∧ q.1 < eX1 p' u' w' z' ∧
      eY0 p' u' w' z' ≤ q.2 ∧ q.2 < eY1 p' u' w' z') :
    False := by
  have hW := windowS e1 e2 hq
  have hW' := windowS e1' e2' hq'
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- same boundary line
    by_cases hA1 : w.2 ≤ u'.2 ∧ u'.2 ≤ u.2
    · rcases endpoint_of_vertexV h2 h2'.1 (by omega) (Or.inr hA1) with hh | hh
      · exact hne hh.symm
      · have hh2 := congrArg Prod.snd hh
        rw [hh] at h2'
        rcases NextVtx.perp h2 h2' with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
    · by_cases hA2 : w'.2 ≤ u.2 ∧ u.2 ≤ u'.2
      · rcases endpoint_of_vertexV h2' h2.1 (by omega) (Or.inr hA2) with hh | hh
        · exact hne hh
        · have hh2 := congrArg Prod.snd hh
          rw [hh] at h2
          rcases NextVtx.perp h2' h2 with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega
      · rcases le_or_gt u'.2 u.2 with hc | hc
        · exact sep16 hfat h2.2.1 h2'.1 (Or.inr (by omega))
            (by omega) (by omega) (by omega) (by omega)
        · exact sep16 hfat h2'.2.1 h2.1 (Or.inr (by omega))
            (by omega) (by omega) (by omega) (by omega)
  · -- edge 2 strictly to the right: run of edge 2 vs in-band of edge 1
    by_cases hB : w.2 < u'.2 ∧ w'.2 < u.2
    · have hin := band_in_south hfin hfat h2 e1 (by omega)
        (max w.2 w'.2) (u'.1 - 1 - u.1) (le_max_left _ _)
        (by omega) (by omega) (by omega)
      rw [show u.1 + (u'.1 - 1 - u.1) = u'.1 - 1 from by ring] at hin
      exact (hr' (max w.2 w'.2) (le_max_right _ _) (by omega)).2 hin
    · rcases le_or_gt u.2 w'.2 with hc | hc
      · exact sep16 hfat h2'.2.1 h2.1 (Or.inl (by omega))
          (by omega) (by omega) (by omega) (by omega)
      · exact sep16 hfat h2.2.1 h2'.1 (Or.inl (by omega))
          (by omega) (by omega) (by omega) (by omega)

/-- An east edge vs a west edge: no shared cell. -/
private lemma clash_EW {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {p u w z p' u' w' z' q : Cell}
    (h2 : NextVtx P u w) (h2' : NextVtx P u' w')
    (e1 : u.2 = w.2) (e2 : u.1 + 16 ≤ w.1)
    (e1' : u'.2 = w'.2) (e2' : w'.1 + 16 ≤ u'.1)
    (hr' : HRunBelow P u'.2 w'.1 u'.1)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z)
    (hq' : eX0 p' u' w' z' ≤ q.1 ∧ q.1 < eX1 p' u' w' z' ∧
      eY0 p' u' w' z' ≤ q.2 ∧ q.2 < eY1 p' u' w' z') :
    False := by
  have hW := windowE e1 e2 hq
  have hW' := windowW e1' e2' hq'
  by_cases hB : u.1 < u'.1 ∧ w'.1 < w.1
  · have hin := band_in_east hfin hfat h2 e1 (by omega)
      (max u.1 w'.1) (u'.2 - u.2) (le_max_left _ _)
      (by omega) (by omega) (by omega)
    rw [show u.2 + (u'.2 - u.2) = u'.2 from by ring] at hin
    exact (hr' (max u.1 w'.1) (le_max_right _ _) (by omega)).2 hin
  · rcases le_or_gt u'.1 u.1 with hc | hc
    · omega
    · exact sep16 hfat h2.2.1 h2'.2.1 (Or.inr (by omega))
        (by omega) (by omega) (by omega) (by omega)

/-- A north edge vs a south edge: no shared cell. -/
private lemma clash_NS {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {p u w z p' u' w' z' q : Cell}
    (h2 : NextVtx P u w) (h2' : NextVtx P u' w')
    (e1 : u.1 = w.1) (e2 : u.2 + 16 ≤ w.2)
    (hr : VRunLeft P u.1 u.2 w.2)
    (e1' : u'.1 = w'.1) (e2' : w'.2 + 16 ≤ u'.2)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z)
    (hq' : eX0 p' u' w' z' ≤ q.1 ∧ q.1 < eX1 p' u' w' z' ∧
      eY0 p' u' w' z' ≤ q.2 ∧ q.2 < eY1 p' u' w' z') :
    False := by
  have hW := windowN e1 e2 hq
  have hW' := windowS e1' e2' hq'
  have hX0 : eX0 p u w z = snapW u.1 := by
    unfold eX0; split_ifs <;> omega
  have hX1' : eX1 p' u' w' z' = snapE u'.1 := by
    unfold eX1; split_ifs <;> omega
  have hsW := snapW_spec u.1
  have hsE := snapE_spec u'.1
  by_cases hB : u.2 < u'.2 ∧ w'.2 < w.2
  · have hin := band_in_south hfin hfat h2' e1' (by omega)
      (max u.2 w'.2) (u.1 - u'.1) (le_max_right _ _)
      (by omega) (by omega) (by omega)
    rw [show u'.1 + (u.1 - u'.1) = u.1 from by ring] at hin
    exact (hr (max u.2 w'.2) (le_max_left _ _) (by omega)).2 hin
  · rcases le_or_gt u'.2 u.2 with hc | hc
    · omega
    · exact sep16 hfat h2.2.1 h2'.2.1 (Or.inl (by omega))
        (by omega) (by omega) (by omega) (by omega)

/-- An east edge vs a north edge: no shared cell. -/
private lemma clash_EN {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {p u w z p' u' w' z' q : Cell}
    (h2 : NextVtx P u w) (h1' : NextVtx P p' u') (h2' : NextVtx P u' w')
    (e1 : u.2 = w.2) (e2 : u.1 + 16 ≤ w.1)
    (e1' : u'.1 = w'.1) (e2' : u'.2 + 16 ≤ w'.2)
    (hr' : VRunLeft P u'.1 u'.2 w'.2)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z)
    (hq' : eX0 p' u' w' z' ≤ q.1 ∧ q.1 < eX1 p' u' w' z' ∧
      eY0 p' u' w' z' ≤ q.2 ∧ q.2 < eY1 p' u' w' z') :
    False := by
  have hW := windowE e1 e2 hq
  have hW' := windowN e1' e2' hq'
  by_cases hD : u.2 ≤ u'.2
  · by_cases hA : w.1 ≤ u'.1
    · -- near the exit corner of the east edge
      by_cases hwu' : w = u'
      · have hw1 := congrArg Prod.fst hwu'
        have hw2 := congrArg Prod.snd hwu'
        rw [hwu'] at h2
        have hp1 := congrArg Prod.fst (NextVtx.pred_unique hfat h1' h2)
        have hY1 : eY1 p u w z = snapN u.2 := by
          unfold eY1; split_ifs <;> omega
        have hY0' : eY0 p' u' w' z' = snapN u'.2 := by
          unfold eY0; split_ifs <;> omega
        have hcong : snapN u'.2 = snapN u.2 := by
          rw [show u'.2 = u.2 from by omega]
        omega
      · have hxy : u'.1 ≠ w.1 ∨ u'.2 ≠ w.2 := by
          by_contra hcon
          push_neg at hcon
          exact hwu' (Prod.ext hcon.1.symm hcon.2.symm)
        exact sep16 hfat h2.2.1 h2'.1 hxy
          (by omega) (by omega) (by omega) (by omega)
    · -- the north line crosses the east in-band
      have hin := band_in_east hfin hfat h2 e1 (by omega) u'.1 (u'.2 - u.2)
        (by omega) (by omega) (by omega) (by omega)
      rw [show u.2 + (u'.2 - u.2) = u'.2 from by ring] at hin
      exact (hr' u'.2 (le_refl _) (by omega)).2 hin
  · -- east out-band vs north in-band
    have hX1 : eX1 p u w z = w.1 ∨ eX1 p u w z = snapE w.1 := by
      unfold eX1; split_ifs <;> omega
    have hX0' : eX0 p' u' w' z' = snapW u'.1 := by
      unfold eX0; split_ifs <;> omega
    have hsE := snapE_spec w.1
    have hsW := snapW_spec u'.1
    have hout := band_out_east hfin hfat h2 e1 (by omega)
      (max u.1 (u'.1 - 15)) (u.2 - 1 - min (u.2 - 1) (w'.2 - 1))
      (le_max_left _ _) (by omega) (by omega) (by omega)
    rw [show u.2 - 1 - (u.2 - 1 - min (u.2 - 1) (w'.2 - 1)) =
      min (u.2 - 1) (w'.2 - 1) from by omega] at hout
    have hin := band_in_north hfin hfat h2' e1' (by omega)
      (min (u.2 - 1) (w'.2 - 1)) (u'.1 - 1 - max u.1 (u'.1 - 15))
      (by omega) (by omega) (by omega) (by omega)
    rw [show u'.1 - 1 - (u'.1 - 1 - max u.1 (u'.1 - 15)) =
      max u.1 (u'.1 - 15) from by omega] at hin
    exact hout hin

/-- An east edge vs a south edge: no shared cell. -/
private lemma clash_ES {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {p u w z p' u' w' z' q : Cell}
    (h1 : NextVtx P p u) (h2 : NextVtx P u w) (h2' : NextVtx P u' w')
    (e1 : u.2 = w.2) (e2 : u.1 + 16 ≤ w.1) (hr : HRunAbove P u.2 u.1 w.1)
    (e1' : u'.1 = w'.1) (e2' : w'.2 + 16 ≤ u'.2)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z)
    (hq' : eX0 p' u' w' z' ≤ q.1 ∧ q.1 < eX1 p' u' w' z' ∧
      eY0 p' u' w' z' ≤ q.2 ∧ q.2 < eY1 p' u' w' z') :
    False := by
  have hW := windowE e1 e2 hq
  have hW' := windowS e1' e2' hq'
  by_cases h1x : u'.1 ≤ u.1
  · by_cases hB : u.2 ≤ w'.2
    · -- near the entry corner of the east edge
      by_cases huw' : u = w'
      · have hu1 := congrArg Prod.fst huw'
        rw [← huw'] at h2'
        have hp2 := congrArg Prod.snd (NextVtx.pred_unique hfat h1 h2')
        have hX0 : eX0 p u w z = snapE u.1 := by
          unfold eX0; split_ifs <;> omega
        have hX1' : eX1 p' u' w' z' = snapE u'.1 := by
          unfold eX1; split_ifs <;> omega
        have hcong : snapE u'.1 = snapE u.1 := by
          rw [show u'.1 = u.1 from by omega]
        omega
      · have hxy : u.1 ≠ w'.1 ∨ u.2 ≠ w'.2 := by
          by_contra hcon
          push_neg at hcon
          exact huw' (Prod.ext hcon.1 hcon.2)
        exact sep16 hfat h2'.2.1 h2.1 hxy
          (by omega) (by omega) (by omega) (by omega)
    · -- the east line crosses the south in-band
      have hin := band_in_south hfin hfat h2' e1' (by omega)
        (u.2 - 1) (u.1 - u'.1) (by omega) (by omega) (by omega) (by omega)
      rw [show u'.1 + (u.1 - u'.1) = u.1 from by ring] at hin
      exact (hr u.1 (le_refl _) (by omega)).2 hin
  · -- east in-band vs south out-band
    have hin := band_in_east hfin hfat h2 e1 (by omega)
      (max u.1 (u'.1 - 15)) (max u.2 w'.2 - u.2)
      (le_max_left _ _) (by omega) (by omega) (by omega)
    rw [show u.2 + (max u.2 w'.2 - u.2) = max u.2 w'.2 from by omega] at hin
    have hout := band_out_south hfin hfat h2' e1' (by omega)
      (max u.2 w'.2) (u'.1 - 1 - max u.1 (u'.1 - 15))
      (le_max_right _ _) (by omega) (by omega) (by omega)
    rw [show u'.1 - 1 - (u'.1 - 1 - max u.1 (u'.1 - 15)) =
      max u.1 (u'.1 - 15) from by omega] at hout
    exact hout hin

/-- A west edge vs a north edge: no shared cell. -/
private lemma clash_WN {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {p u w z p' u' w' z' q : Cell}
    (h1 : NextVtx P p u) (h2 : NextVtx P u w) (h2' : NextVtx P u' w')
    (e1 : u.2 = w.2) (e2 : w.1 + 16 ≤ u.1) (hr : HRunBelow P u.2 w.1 u.1)
    (e1' : u'.1 = w'.1) (e2' : u'.2 + 16 ≤ w'.2)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z)
    (hq' : eX0 p' u' w' z' ≤ q.1 ∧ q.1 < eX1 p' u' w' z' ∧
      eY0 p' u' w' z' ≤ q.2 ∧ q.2 < eY1 p' u' w' z') :
    False := by
  have hW := windowW e1 e2 hq
  have hW' := windowN e1' e2' hq'
  by_cases h1x : u.1 ≤ u'.1
  · by_cases hB : u.2 < w'.2
    · -- the west line crosses the north in-band
      have hin := band_in_north hfin hfat h2' e1' (by omega)
        u.2 (u'.1 - 1 - max w.1 (u'.1 - 15))
        (by omega) (by omega) (by omega) (by omega)
      rw [show u'.1 - 1 - (u'.1 - 1 - max w.1 (u'.1 - 15)) =
        max w.1 (u'.1 - 15) from by omega] at hin
      exact (hr (max w.1 (u'.1 - 15)) (le_max_left _ _) (by omega)).2 hin
    · -- near the entry corner of the west edge
      by_cases huw' : u = w'
      · have hu1 := congrArg Prod.fst huw'
        rw [← huw'] at h2'
        have hp2 := congrArg Prod.snd (NextVtx.pred_unique hfat h1 h2')
        have hX1 : eX1 p u w z = snapW u.1 := by
          unfold eX1; split_ifs <;> omega
        have hX0' : eX0 p' u' w' z' = snapW u'.1 := by
          unfold eX0; split_ifs <;> omega
        have hcong : snapW u'.1 = snapW u.1 := by
          rw [show u'.1 = u.1 from by omega]
        omega
      · have hxy : u.1 ≠ w'.1 ∨ u.2 ≠ w'.2 := by
          by_contra hcon
          push_neg at hcon
          exact huw' (Prod.ext hcon.1 hcon.2)
        exact sep16 hfat h2'.2.1 h2.1 hxy
          (by omega) (by omega) (by omega) (by omega)
  · -- west in-band vs north out-band
    have hin := band_in_west hfin hfat h2 e1 (by omega)
      (max w.1 u'.1) (u.2 - 1 - max (u.2 - 15) u'.2)
      (le_max_left _ _) (by omega) (by omega) (by omega)
    rw [show u.2 - 1 - (u.2 - 1 - max (u.2 - 15) u'.2) =
      max (u.2 - 15) u'.2 from by omega] at hin
    have hout := band_out_north hfin hfat h2' e1' (by omega)
      (max (u.2 - 15) u'.2) (max w.1 u'.1 - u'.1)
      (le_max_right _ _) (by omega) (by omega) (by omega)
    rw [show u'.1 + (max w.1 u'.1 - u'.1) = max w.1 u'.1 from by omega] at hout
    exact hout hin

/-- A west edge vs a south edge: no shared cell. -/
private lemma clash_WS {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {p u w z p' u' w' z' q : Cell}
    (h2 : NextVtx P u w) (h1' : NextVtx P p' u') (h2' : NextVtx P u' w')
    (e1 : u.2 = w.2) (e2 : w.1 + 16 ≤ u.1)
    (e1' : u'.1 = w'.1) (e2' : w'.2 + 16 ≤ u'.2)
    (hq : eX0 p u w z ≤ q.1 ∧ q.1 < eX1 p u w z ∧
      eY0 p u w z ≤ q.2 ∧ q.2 < eY1 p u w z)
    (hq' : eX0 p' u' w' z' ≤ q.1 ∧ q.1 < eX1 p' u' w' z' ∧
      eY0 p' u' w' z' ≤ q.2 ∧ q.2 < eY1 p' u' w' z') :
    False := by
  have hW := windowW e1 e2 hq
  have hW' := windowS e1' e2' hq'
  by_cases hB : w.1 < u'.1 ∧ w'.2 < u.2
  · -- west in-band vs south out-band
    have hin := band_in_west hfin hfat h2 e1 (by omega)
      (max w.1 (u'.1 - 15)) (u.2 - 1 - max (u.2 - 15) w'.2)
      (le_max_left _ _) (by omega) (by omega) (by omega)
    rw [show u.2 - 1 - (u.2 - 1 - max (u.2 - 15) w'.2) =
      max (u.2 - 15) w'.2 from by omega] at hin
    have hout := band_out_south hfin hfat h2' e1' (by omega)
      (max (u.2 - 15) w'.2) (u'.1 - 1 - max w.1 (u'.1 - 15))
      (le_max_right _ _) (by omega) (by omega) (by omega)
    rw [show u'.1 - 1 - (u'.1 - 1 - max w.1 (u'.1 - 15)) =
      max w.1 (u'.1 - 15) from by omega] at hout
    exact hout hin
  · by_cases hC : u.2 < u'.2
    · -- west out-band vs south in-band (mod-3 tightening)
      have hX0 : eX0 p u w z = w.1 ∨ eX0 p u w z = snapW w.1 := by
        unfold eX0; split_ifs <;> omega
      have hX1' : eX1 p' u' w' z' = snapE u'.1 := by
        unfold eX1; split_ifs <;> omega
      have hsW := snapW_spec w.1
      have hsE := snapE_spec u'.1
      have hout := band_out_west hfin hfat h2 e1 (by omega)
        (max w.1 u'.1) (max u.2 w'.2 - u.2)
        (le_max_left _ _) (by omega) (by omega) (by omega)
      rw [show u.2 + (max u.2 w'.2 - u.2) = max u.2 w'.2 from by omega] at hout
      have hin := band_in_south hfin hfat h2' e1' (by omega)
        (max u.2 w'.2) (max w.1 u'.1 - u'.1)
        (le_max_right _ _) (by omega) (by omega) (by omega)
      rw [show u'.1 + (max w.1 u'.1 - u'.1) = max w.1 u'.1 from by omega] at hin
      exact hout hin
    · rcases le_or_gt u'.1 w.1 with hc | hc
      · -- near the exit corner of the west edge
        by_cases hwu : w = u'
        · have hw1 := congrArg Prod.fst hwu
          have hw2 := congrArg Prod.snd hwu
          rw [hwu] at h2
          have hp1 := congrArg Prod.fst (NextVtx.pred_unique hfat h1' h2)
          have hY0 : eY0 p u w z = snapS u.2 := by
            unfold eY0; split_ifs <;> omega
          have hY1' : eY1 p' u' w' z' = snapS u'.2 := by
            unfold eY1; split_ifs <;> omega
          have hcong : snapS u'.2 = snapS u.2 := by
            rw [show u'.2 = u.2 from by omega]
          omega
        · have hxy : u'.1 ≠ w.1 ∨ u'.2 ≠ w.2 := by
            by_contra hcon
            push_neg at hcon
            exact hwu (Prod.ext hcon.1.symm hcon.2.symm)
          exact sep16 hfat h2.2.1 h2'.1 hxy
            (by omega) (by omega) (by omega) (by omega)
      · omega

set_option linter.unusedVariables false in
theorem edgePiece_disjoint {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {p u w z p' u' w' z' : Cell}
    (h1 : NextVtx P p u) (h2 : NextVtx P u w) (h3 : NextVtx P w z)
    (h1' : NextVtx P p' u') (h2' : NextVtx P u' w') (h3' : NextVtx P w' z')
    (hne : u ≠ u') :
    Disjoint (edgePiece p u w z).cells (edgePiece p' u' w' z').cells := by
  rw [Set.disjoint_left]
  intro q hq hq'
  simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
    edgePiece_x1 hfat h2, edgePiece_y1 hfat h2] at hq
  simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
    edgePiece_x1 hfat h2', edgePiece_y1 hfat h2'] at hq'
  rcases h2.far hfat with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ <;>
    rcases h2'.far hfat with ⟨e1', e2', hr'⟩ | ⟨e1', e2', hr'⟩ | ⟨e1', e2', hr'⟩ | ⟨e1', e2', hr'⟩
  · rcases le_total u.2 u'.2 with hle | hle
    · exact clash_EE hfin hfat h2 h2' hne e1 e2 e1' e2' hr' hle hq hq'
    · exact clash_EE hfin hfat h2' h2 hne.symm e1' e2' e1 e2 hr hle hq' hq
  · exact clash_EW hfin hfat h2 h2' e1 e2 e1' e2' hr' hq hq'
  · exact clash_EN hfin hfat h2 h1' h2' e1 e2 e1' e2' hr' hq hq'
  · exact clash_ES hfin hfat h1 h2 h2' e1 e2 hr e1' e2' hq hq'
  · exact clash_EW hfin hfat h2' h2 e1' e2' e1 e2 hr hq' hq
  · rcases le_total u'.2 u.2 with hle | hle
    · exact clash_WW hfin hfat h2 h2' hne e1 e2 e1' e2' hr' hle hq hq'
    · exact clash_WW hfin hfat h2' h2 hne.symm e1' e2' e1 e2 hr hle hq' hq
  · exact clash_WN hfin hfat h1 h2 h2' e1 e2 hr e1' e2' hq hq'
  · exact clash_WS hfin hfat h2 h1' h2' e1 e2 e1' e2' hq hq'
  · exact clash_EN hfin hfat h2' h1 h2 e1' e2' e1 e2 hr hq' hq
  · exact clash_WN hfin hfat h1' h2' h2 e1' e2' hr' e1 e2 hq' hq
  · rcases le_total u'.1 u.1 with hle | hle
    · exact clash_NN hfin hfat h2 h2' hne e1 e2 e1' e2' hr' hle hq hq'
    · exact clash_NN hfin hfat h2' h2 hne.symm e1' e2' e1 e2 hr hle hq' hq
  · exact clash_NS hfin hfat h2 h2' e1 e2 hr e1' e2' hq hq'
  · exact clash_ES hfin hfat h1' h2' h2 e1' e2' hr' e1 e2 hq' hq
  · exact clash_WS hfin hfat h2' h1 h2 e1' e2' e1 e2 hq' hq
  · exact clash_NS hfin hfat h2' h2 e1' e2' hr' e1 e2 hq' hq
  · rcases le_total u.1 u'.1 with hle | hle
    · exact clash_SS hfin hfat h2 h2' hne e1 e2 e1' e2' hr' hle hq hq'
    · exact clash_SS hfin hfat h2' h2 hne.symm e1' e2' e1 e2 hr hle hq' hq

/-!
# Every corridor cell lies in some corridor rectangle (`corridor_covered`)

Plan: a corridor cell `q` has a witness `zc ∉ P` in its safety box; walking
the L-path from `q` to `zc` finds a boundary flip.  A flip on the vertical
leg gives a horizontal governing edge whose strip contains `q`
(`strip_east`/`strip_west`); a flip on the horizontal leg gives a vertical
governing edge, whose strip contains `q` when its span covers `q.2`
(`strip_north`/`strip_south`) and whose near endpoint is otherwise a reflex
corner, with `q` in the reflex extension of the incoming edge
(`block_NE/WN/ES/SW` after the quadrant classification `quad_NW/SW/NE/SE`).
The snap criteria turn the safety-box bounds into strict snap-line bounds.
-/

open Set

-- ============================================================
-- §1 Predecessor existence
-- ============================================================

private lemma exists_prevVtx {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u : Cell} (hu : IsVertex P u) : ∃ p, NextVtx P p u := by
  classical
  haveI : Finite {v : Cell // IsVertex P v} := (vertexSet_finite hfin).to_subtype
  have hstep : ∀ v : {v : Cell // IsVertex P v},
      ∃ w : {v : Cell // IsVertex P v}, NextVtx P v.1 w.1 := by
    intro v
    obtain ⟨w, hw⟩ := exists_nextVtx hfin hfat v.2
    exact ⟨⟨w, hw.2.1⟩, hw⟩
  choose f hf using hstep
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := hf a
    have h2 := hf b
    rw [hab] at h1
    exact Subtype.ext (NextVtx.pred_unique hfat h1 h2)
  obtain ⟨p, hp⟩ := Finite.injective_iff_surjective.mp hinj ⟨u, hu⟩
  refine ⟨p.1, ?_⟩
  have h := hf p
  rwa [hp] at h

-- ============================================================
-- §2 Snap criteria (safety-box poke ⇒ strict snap bounds)
-- ============================================================

private lemma snapN_crit {Y b : ℤ} (h1 : b - b % 2 - 5 ≤ Y) (h2 : Y ≤ b) :
    b < snapN Y := by unfold snapN; omega

private lemma snapS_crit {Y b : ℤ} (h1 : Y ≤ b - b % 2 + 7) (h2 : b < Y) :
    snapS Y ≤ b := by unfold snapS; omega

private lemma snapE_crit {X a : ℤ} (h1 : a - a % 3 - 5 ≤ X) (h2 : X ≤ a) :
    a < snapE X := by unfold snapE; omega

private lemma snapW_crit {X a : ℤ} (h1 : X ≤ a - a % 3 + 8) (h2 : a < X) :
    snapW X ≤ a := by unfold snapW; omega

-- ============================================================
-- §3 Arm directions at the ends of an edge
-- ============================================================

/-- The predecessor arm of a vertical edge is horizontal. -/
private lemma pred_horiz {P : Set Cell} (hfat : Fat 16 P) {p u w : Cell}
    (hpu : NextVtx P p u) (huw : NextVtx P u w) (hne : u.2 ≠ w.2) :
    p.2 = u.2 ∧
      ((p.1 + 16 ≤ u.1 ∧ HRunAbove P u.2 p.1 u.1) ∨
       (u.1 + 16 ≤ p.1 ∧ HRunBelow P u.2 u.1 p.1)) := by
  have h2 : p.2 = u.2 := by
    rcases NextVtx.perp hpu huw with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h hne
  refine ⟨h2, ?_⟩
  rcases hpu.far hfat with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ |
    ⟨e1, e2, hr⟩
  · rw [e1] at hr
    exact Or.inl ⟨e2, hr⟩
  · rw [e1] at hr
    exact Or.inr ⟨e2, hr⟩
  · omega
  · omega

/-- The predecessor arm of a horizontal edge is vertical. -/
private lemma pred_vert {P : Set Cell} (hfat : Fat 16 P) {p u w : Cell}
    (hpu : NextVtx P p u) (huw : NextVtx P u w) (hne : u.1 ≠ w.1) :
    p.1 = u.1 ∧
      ((p.2 + 16 ≤ u.2 ∧ VRunLeft P u.1 p.2 u.2) ∨
       (u.2 + 16 ≤ p.2 ∧ VRunRight P u.1 u.2 p.2)) := by
  have h1 : p.1 = u.1 := by
    rcases NextVtx.perp hpu huw with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h hne
    · exact h
  refine ⟨h1, ?_⟩
  rcases hpu.far hfat with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ |
    ⟨e1, e2, hr⟩
  · omega
  · omega
  · rw [e1] at hr
    exact Or.inl ⟨e2, hr⟩
  · rw [e1] at hr
    exact Or.inr ⟨e2, hr⟩

/-- The successor arm of a vertical edge is horizontal. -/
private lemma succ_horiz {P : Set Cell} (hfat : Fat 16 P) {u w z : Cell}
    (huw : NextVtx P u w) (hwz : NextVtx P w z) (hne : u.2 ≠ w.2) :
    w.2 = z.2 ∧
      ((w.1 + 16 ≤ z.1 ∧ HRunAbove P w.2 w.1 z.1) ∨
       (z.1 + 16 ≤ w.1 ∧ HRunBelow P w.2 z.1 w.1)) := by
  have h2 : w.2 = z.2 := by
    rcases NextVtx.perp huw hwz with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h hne
    · exact h
  refine ⟨h2, ?_⟩
  rcases hwz.far hfat with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ |
    ⟨e1, e2, hr⟩
  · exact Or.inl ⟨e2, hr⟩
  · exact Or.inr ⟨e2, hr⟩
  · omega
  · omega

/-- The successor arm of a horizontal edge is vertical. -/
private lemma succ_vert {P : Set Cell} (hfat : Fat 16 P) {u w z : Cell}
    (huw : NextVtx P u w) (hwz : NextVtx P w z) (hne : u.1 ≠ w.1) :
    w.1 = z.1 ∧
      ((w.2 + 16 ≤ z.2 ∧ VRunLeft P w.1 w.2 z.2) ∨
       (z.2 + 16 ≤ w.2 ∧ VRunRight P w.1 z.2 w.2)) := by
  have h1 : w.1 = z.1 := by
    rcases NextVtx.perp huw hwz with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hne
  refine ⟨h1, ?_⟩
  rcases hwz.far hfat with ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ | ⟨e1, e2, hr⟩ |
    ⟨e1, e2, hr⟩
  · omega
  · omega
  · exact Or.inl ⟨e2, hr⟩
  · exact Or.inr ⟨e2, hr⟩

-- ============================================================
-- §4 Quadrant classification at a vertex near a corridor cell
-- ============================================================

/-- Vertical boundary below `v` (interior west), `P`-cell to the upper
    left: the corner is reflex and the cell NW of `v` lies in `P`. -/
private lemma quad_NW {P : Set Cell} (hfat : Fat 16 P) {v : Cell}
    (hv : IsVertex P v)
    (h1 : (v.1 - 1, v.2 - 1) ∈ P) (h2 : (v.1, v.2 - 1) ∉ P)
    {q : Cell} (hq : q ∈ P)
    (hx1 : v.1 - 16 ≤ q.1) (hx2 : q.1 < v.1)
    (hy1 : v.2 ≤ q.2) (hy2 : q.2 < v.2 + 16) :
    (v.1 - 1, v.2) ∈ P := by
  obtain ⟨c, hc | hc⟩ := hfat.mem_iff hv
  · have H1 := (hc (v.1 - 1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mp h1
    have H2 : (v.1, v.2 - 1) ∉ quadrant v c := fun h =>
      h2 ((hc (v.1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mpr h)
    have Hq := (hc q (by simp only [box, mem_rect]; omega)).mp hq
    refine (hc (v.1 - 1, v.2) (by simp only [box, mem_rect]; omega)).mpr ?_
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at H1 H2 Hq ⊢ <;> omega
  · have H1 := (hc (v.1 - 1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mp h1
    have H2 : (v.1, v.2 - 1) ∈ quadrant v c := by
      by_contra h
      exact h2 ((hc (v.1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mpr h)
    have Hq := (hc q (by simp only [box, mem_rect]; omega)).mp hq
    refine (hc (v.1 - 1, v.2) (by simp only [box, mem_rect]; omega)).mpr ?_
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at H1 H2 Hq ⊢ <;> omega

/-- Vertical boundary above `v` (interior west), `P`-cell to the lower
    left: reflex, and the cell SW of `v` lies in `P`. -/
private lemma quad_SW {P : Set Cell} (hfat : Fat 16 P) {v : Cell}
    (hv : IsVertex P v)
    (h1 : (v.1 - 1, v.2) ∈ P) (h2 : (v.1, v.2) ∉ P)
    {q : Cell} (hq : q ∈ P)
    (hx1 : v.1 - 16 ≤ q.1) (hx2 : q.1 < v.1)
    (hy1 : v.2 - 16 ≤ q.2) (hy2 : q.2 < v.2) :
    (v.1 - 1, v.2 - 1) ∈ P := by
  obtain ⟨c, hc | hc⟩ := hfat.mem_iff hv
  · have H1 := (hc (v.1 - 1, v.2) (by simp only [box, mem_rect]; omega)).mp h1
    have H2 : (v.1, v.2) ∉ quadrant v c := fun h =>
      h2 ((hc (v.1, v.2) (by simp only [box, mem_rect]; omega)).mpr h)
    have Hq := (hc q (by simp only [box, mem_rect]; omega)).mp hq
    refine (hc (v.1 - 1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mpr ?_
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at H1 H2 Hq ⊢ <;> omega
  · have H1 := (hc (v.1 - 1, v.2) (by simp only [box, mem_rect]; omega)).mp h1
    have H2 : (v.1, v.2) ∈ quadrant v c := by
      by_contra h
      exact h2 ((hc (v.1, v.2) (by simp only [box, mem_rect]; omega)).mpr h)
    have Hq := (hc q (by simp only [box, mem_rect]; omega)).mp hq
    refine (hc (v.1 - 1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mpr ?_
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at H1 H2 Hq ⊢ <;> omega

/-- Vertical boundary below `v` (interior east), `P`-cell to the upper
    right: reflex, and the cell NE of `v` lies in `P`. -/
private lemma quad_NE {P : Set Cell} (hfat : Fat 16 P) {v : Cell}
    (hv : IsVertex P v)
    (h1 : (v.1, v.2 - 1) ∈ P) (h2 : (v.1 - 1, v.2 - 1) ∉ P)
    {q : Cell} (hq : q ∈ P)
    (hx1 : v.1 ≤ q.1) (hx2 : q.1 < v.1 + 16)
    (hy1 : v.2 ≤ q.2) (hy2 : q.2 < v.2 + 16) :
    (v.1, v.2) ∈ P := by
  obtain ⟨c, hc | hc⟩ := hfat.mem_iff hv
  · have H1 := (hc (v.1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mp h1
    have H2 : (v.1 - 1, v.2 - 1) ∉ quadrant v c := fun h =>
      h2 ((hc (v.1 - 1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mpr h)
    have Hq := (hc q (by simp only [box, mem_rect]; omega)).mp hq
    refine (hc (v.1, v.2) (by simp only [box, mem_rect]; omega)).mpr ?_
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at H1 H2 Hq ⊢ <;> omega
  · have H1 := (hc (v.1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mp h1
    have H2 : (v.1 - 1, v.2 - 1) ∈ quadrant v c := by
      by_contra h
      exact h2 ((hc (v.1 - 1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mpr h)
    have Hq := (hc q (by simp only [box, mem_rect]; omega)).mp hq
    refine (hc (v.1, v.2) (by simp only [box, mem_rect]; omega)).mpr ?_
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at H1 H2 Hq ⊢ <;> omega

/-- Vertical boundary above `v` (interior east), `P`-cell to the lower
    right: reflex, and the cell SE of `v` lies in `P`. -/
private lemma quad_SE {P : Set Cell} (hfat : Fat 16 P) {v : Cell}
    (hv : IsVertex P v)
    (h1 : (v.1, v.2) ∈ P) (h2 : (v.1 - 1, v.2) ∉ P)
    {q : Cell} (hq : q ∈ P)
    (hx1 : v.1 ≤ q.1) (hx2 : q.1 < v.1 + 16)
    (hy1 : v.2 - 16 ≤ q.2) (hy2 : q.2 < v.2) :
    (v.1, v.2 - 1) ∈ P := by
  obtain ⟨c, hc | hc⟩ := hfat.mem_iff hv
  · have H1 := (hc (v.1, v.2) (by simp only [box, mem_rect]; omega)).mp h1
    have H2 : (v.1 - 1, v.2) ∉ quadrant v c := fun h =>
      h2 ((hc (v.1 - 1, v.2) (by simp only [box, mem_rect]; omega)).mpr h)
    have Hq := (hc q (by simp only [box, mem_rect]; omega)).mp hq
    refine (hc (v.1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mpr ?_
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at H1 H2 Hq ⊢ <;> omega
  · have H1 := (hc (v.1, v.2) (by simp only [box, mem_rect]; omega)).mp h1
    have H2 : (v.1 - 1, v.2) ∈ quadrant v c := by
      by_contra h
      exact h2 ((hc (v.1 - 1, v.2) (by simp only [box, mem_rect]; omega)).mpr h)
    have Hq := (hc q (by simp only [box, mem_rect]; omega)).mp hq
    refine (hc (v.1, v.2 - 1) (by simp only [box, mem_rect]; omega)).mpr ?_
    cases c <;> simp only [quadrant, Set.mem_setOf_eq] at H1 H2 Hq ⊢ <;> omega

-- ============================================================
-- §5 Strip lemmas: a cell in the full strip of an edge lies in its
-- rectangle or (at a trimmed convex start) in the predecessor's
-- ============================================================

private lemma strip_east {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (huw : NextVtx P u w) (he : u.2 = w.2) (hlt : u.1 < w.1)
    {q : Cell} (hx0 : u.1 ≤ q.1) (hx1 : q.1 < w.1)
    (hy0 : u.2 ≤ q.2) (hy1 : q.2 < snapN u.2) :
    ∃ p a b z : Cell, NextVtx P p a ∧ NextVtx P a b ∧ NextVtx P b z ∧
      q ∈ (edgePiece p a b z).cells := by
  obtain ⟨p, hpu⟩ := exists_prevVtx hfin hfat huw.1
  obtain ⟨z, hwz⟩ := exists_nextVtx hfin hfat huw.2.1
  obtain ⟨hp1, hpdir⟩ := pred_vert hfat hpu huw (by omega)
  have hEu := snapE_spec u.1
  have hEw := snapE_spec w.1
  have hNu := snapN_spec u.2
  by_cases hcv : u.2 < p.2
  · by_cases hq3 : snapE u.1 ≤ q.1
    · refine ⟨p, u, w, z, hpu, huw, hwz, ?_⟩
      simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat huw p z, edgePiece_y1 hfat huw p z]
      unfold eX0 eX1 eY0 eY1
      split_ifs <;> omega
    · -- corner block: the rectangle of the incoming south edge `(p, u)`
      push_neg at hq3
      have hfarS : u.2 + 16 ≤ p.2 := by
        rcases hpdir with ⟨h16, -⟩ | ⟨h16, -⟩
        · omega
        · exact h16
      obtain ⟨p0, hp0⟩ := exists_prevVtx hfin hfat hpu.1
      refine ⟨p0, p, u, w, hp0, hpu, huw, ?_⟩
      have hEp := snapE_spec p.1
      have hSp := snapS_spec p.2
      simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat hpu p0 w, edgePiece_y1 hfat hpu p0 w]
      unfold eX0 eX1 eY0 eY1
      split_ifs <;> omega
  · refine ⟨p, u, w, z, hpu, huw, hwz, ?_⟩
    simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
      edgePiece_x1 hfat huw p z, edgePiece_y1 hfat huw p z]
    unfold eX0 eX1 eY0 eY1
    split_ifs <;> omega

private lemma strip_west {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (huw : NextVtx P u w) (he : u.2 = w.2) (hlt : w.1 < u.1)
    {q : Cell} (hx0 : w.1 ≤ q.1) (hx1 : q.1 < u.1)
    (hy0 : snapS u.2 ≤ q.2) (hy1 : q.2 < u.2) :
    ∃ p a b z : Cell, NextVtx P p a ∧ NextVtx P a b ∧ NextVtx P b z ∧
      q ∈ (edgePiece p a b z).cells := by
  obtain ⟨p, hpu⟩ := exists_prevVtx hfin hfat huw.1
  obtain ⟨z, hwz⟩ := exists_nextVtx hfin hfat huw.2.1
  obtain ⟨hp1, hpdir⟩ := pred_vert hfat hpu huw (by omega)
  have hWu := snapW_spec u.1
  have hWw := snapW_spec w.1
  have hSu := snapS_spec u.2
  by_cases hcv : u.2 < p.2
  · refine ⟨p, u, w, z, hpu, huw, hwz, ?_⟩
    simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
      edgePiece_x1 hfat huw p z, edgePiece_y1 hfat huw p z]
    unfold eX0 eX1 eY0 eY1
    split_ifs <;> omega
  · by_cases hq3 : q.1 < snapW u.1
    · refine ⟨p, u, w, z, hpu, huw, hwz, ?_⟩
      simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat huw p z, edgePiece_y1 hfat huw p z]
      unfold eX0 eX1 eY0 eY1
      split_ifs <;> omega
    · -- corner block: the rectangle of the incoming north edge `(p, u)`
      push_neg at hq3
      have hfarN : p.2 + 16 ≤ u.2 := by
        rcases hpdir with ⟨h16, -⟩ | ⟨h16, -⟩
        · exact h16
        · omega
      obtain ⟨p0, hp0⟩ := exists_prevVtx hfin hfat hpu.1
      refine ⟨p0, p, u, w, hp0, hpu, huw, ?_⟩
      have hWp := snapW_spec p.1
      have hNp := snapN_spec p.2
      simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat hpu p0 w, edgePiece_y1 hfat hpu p0 w]
      unfold eX0 eX1 eY0 eY1
      split_ifs <;> omega

private lemma strip_north {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (huw : NextVtx P u w) (hv : u.1 = w.1) (hlt : u.2 < w.2)
    {q : Cell} (hx0 : snapW u.1 ≤ q.1) (hx1 : q.1 < u.1)
    (hy0 : u.2 ≤ q.2) (hy1 : q.2 < w.2) :
    ∃ p a b z : Cell, NextVtx P p a ∧ NextVtx P a b ∧ NextVtx P b z ∧
      q ∈ (edgePiece p a b z).cells := by
  obtain ⟨p, hpu⟩ := exists_prevVtx hfin hfat huw.1
  obtain ⟨z, hwz⟩ := exists_nextVtx hfin hfat huw.2.1
  obtain ⟨hp2, hpdir⟩ := pred_horiz hfat hpu huw (by omega)
  have hWu := snapW_spec u.1
  have hNu := snapN_spec u.2
  have hNw := snapN_spec w.2
  by_cases hcv : p.1 < u.1
  · by_cases hq3 : snapN u.2 ≤ q.2
    · refine ⟨p, u, w, z, hpu, huw, hwz, ?_⟩
      simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat huw p z, edgePiece_y1 hfat huw p z]
      unfold eX0 eX1 eY0 eY1
      split_ifs <;> omega
    · -- corner block: the rectangle of the incoming east edge `(p, u)`
      push_neg at hq3
      have hfarE : p.1 + 16 ≤ u.1 := by
        rcases hpdir with ⟨h16, -⟩ | ⟨h16, -⟩
        · exact h16
        · omega
      obtain ⟨p0, hp0⟩ := exists_prevVtx hfin hfat hpu.1
      refine ⟨p0, p, u, w, hp0, hpu, huw, ?_⟩
      have hEp := snapE_spec p.1
      have hNp := snapN_spec p.2
      simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat hpu p0 w, edgePiece_y1 hfat hpu p0 w]
      unfold eX0 eX1 eY0 eY1
      split_ifs <;> omega
  · refine ⟨p, u, w, z, hpu, huw, hwz, ?_⟩
    simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
      edgePiece_x1 hfat huw p z, edgePiece_y1 hfat huw p z]
    unfold eX0 eX1 eY0 eY1
    split_ifs <;> omega

private lemma strip_south {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (huw : NextVtx P u w) (hv : u.1 = w.1) (hlt : w.2 < u.2)
    {q : Cell} (hx0 : u.1 ≤ q.1) (hx1 : q.1 < snapE u.1)
    (hy0 : w.2 ≤ q.2) (hy1 : q.2 < u.2) :
    ∃ p a b z : Cell, NextVtx P p a ∧ NextVtx P a b ∧ NextVtx P b z ∧
      q ∈ (edgePiece p a b z).cells := by
  obtain ⟨p, hpu⟩ := exists_prevVtx hfin hfat huw.1
  obtain ⟨z, hwz⟩ := exists_nextVtx hfin hfat huw.2.1
  obtain ⟨hp2, hpdir⟩ := pred_horiz hfat hpu huw (by omega)
  have hEu := snapE_spec u.1
  have hSu := snapS_spec u.2
  have hSw := snapS_spec w.2
  by_cases hcv : u.1 < p.1
  · by_cases hq3 : q.2 < snapS u.2
    · refine ⟨p, u, w, z, hpu, huw, hwz, ?_⟩
      simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat huw p z, edgePiece_y1 hfat huw p z]
      unfold eX0 eX1 eY0 eY1
      split_ifs <;> omega
    · -- corner block: the rectangle of the incoming west edge `(p, u)`
      push_neg at hq3
      have hfarW : u.1 + 16 ≤ p.1 := by
        rcases hpdir with ⟨h16, -⟩ | ⟨h16, -⟩
        · omega
        · exact h16
      obtain ⟨p0, hp0⟩ := exists_prevVtx hfin hfat hpu.1
      refine ⟨p0, p, u, w, hp0, hpu, huw, ?_⟩
      have hWp := snapW_spec p.1
      have hSp := snapS_spec p.2
      simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
        edgePiece_x1 hfat hpu p0 w, edgePiece_y1 hfat hpu p0 w]
      unfold eX0 eX1 eY0 eY1
      split_ifs <;> omega
  · refine ⟨p, u, w, z, hpu, huw, hwz, ?_⟩
    simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
      edgePiece_x1 hfat huw p z, edgePiece_y1 hfat huw p z]
    unfold eX0 eX1 eY0 eY1
    split_ifs <;> omega

-- ============================================================
-- §6 Reflex corner blocks: a cell in the diagonal corner block at a
-- reflex vertex lies in the reflex extension of the incoming rectangle
-- ============================================================

/-- Reflex `N→E` at the top `w` of a north edge. -/
private lemma block_NE {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (huw : NextVtx P u w) (hv : u.1 = w.1) (hlt : u.2 < w.2)
    (hcell : (w.1 - 1, w.2) ∈ P)
    {q : Cell} (hx0 : snapW w.1 ≤ q.1) (hx1 : q.1 < w.1)
    (hy0 : w.2 ≤ q.2) (hy1 : q.2 < snapN w.2) :
    ∃ p a b z : Cell, NextVtx P p a ∧ NextVtx P a b ∧ NextVtx P b z ∧
      q ∈ (edgePiece p a b z).cells := by
  obtain ⟨p, hpu⟩ := exists_prevVtx hfin hfat huw.1
  obtain ⟨z, hwz⟩ := exists_nextVtx hfin hfat huw.2.1
  have hfar : u.2 + 16 ≤ w.2 := by
    rcases huw.far hfat with ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ |
      ⟨e1, e2, -⟩ <;> omega
  obtain ⟨hz2, hzdir⟩ := succ_horiz hfat huw hwz (by omega)
  have hzE : w.1 + 16 ≤ z.1 := by
    rcases hzdir with ⟨h16, -⟩ | ⟨h16, hr⟩
    · exact h16
    · exact absurd hcell (hr (w.1 - 1) (by omega) (by omega)).2
  refine ⟨p, u, w, z, hpu, huw, hwz, ?_⟩
  have hWu := snapW_spec u.1
  have hWw := snapW_spec w.1
  have hNu := snapN_spec u.2
  simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
    edgePiece_x1 hfat huw p z, edgePiece_y1 hfat huw p z]
  unfold eX0 eX1 eY0 eY1
  split_ifs <;> omega

/-- Reflex `W→N` at the bottom `u` of a north edge. -/
private lemma block_WN {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (huw : NextVtx P u w) (hv : u.1 = w.1) (hlt : u.2 < w.2)
    (hcell : (u.1 - 1, u.2 - 1) ∈ P)
    {q : Cell} (hx0 : snapW u.1 ≤ q.1) (hx1 : q.1 < u.1)
    (hy0 : snapS u.2 ≤ q.2) (hy1 : q.2 < u.2) :
    ∃ p a b z : Cell, NextVtx P p a ∧ NextVtx P a b ∧ NextVtx P b z ∧
      q ∈ (edgePiece p a b z).cells := by
  obtain ⟨p, hpu⟩ := exists_prevVtx hfin hfat huw.1
  obtain ⟨hp2, hpdir⟩ := pred_horiz hfat hpu huw (by omega)
  have hpW : u.1 + 16 ≤ p.1 := by
    rcases hpdir with ⟨h16, hr⟩ | ⟨h16, -⟩
    · exact absurd hcell (hr (u.1 - 1) (by omega) (by omega)).2
    · exact h16
  obtain ⟨p0, hp0⟩ := exists_prevVtx hfin hfat hpu.1
  refine ⟨p0, p, u, w, hp0, hpu, huw, ?_⟩
  have hWp := snapW_spec p.1
  have hWu := snapW_spec u.1
  have hSp := snapS_spec p.2
  have hSu := snapS_spec u.2
  simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
    edgePiece_x1 hfat hpu p0 w, edgePiece_y1 hfat hpu p0 w]
  unfold eX0 eX1 eY0 eY1
  split_ifs <;> omega

/-- Reflex `E→S` at the top `u` of a south edge. -/
private lemma block_ES {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (huw : NextVtx P u w) (hv : u.1 = w.1) (hlt : w.2 < u.2)
    (hcell : (u.1, u.2) ∈ P)
    {q : Cell} (hx0 : u.1 ≤ q.1) (hx1 : q.1 < snapE u.1)
    (hy0 : u.2 ≤ q.2) (hy1 : q.2 < snapN u.2) :
    ∃ p a b z : Cell, NextVtx P p a ∧ NextVtx P a b ∧ NextVtx P b z ∧
      q ∈ (edgePiece p a b z).cells := by
  obtain ⟨p, hpu⟩ := exists_prevVtx hfin hfat huw.1
  obtain ⟨hp2, hpdir⟩ := pred_horiz hfat hpu huw (by omega)
  have hpE : p.1 + 16 ≤ u.1 := by
    rcases hpdir with ⟨h16, -⟩ | ⟨h16, hr⟩
    · exact h16
    · exact absurd hcell (hr u.1 (by omega) (by omega)).2
  obtain ⟨p0, hp0⟩ := exists_prevVtx hfin hfat hpu.1
  refine ⟨p0, p, u, w, hp0, hpu, huw, ?_⟩
  have hEp := snapE_spec p.1
  have hEu := snapE_spec u.1
  have hNp := snapN_spec p.2
  have hNu := snapN_spec u.2
  simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
    edgePiece_x1 hfat hpu p0 w, edgePiece_y1 hfat hpu p0 w]
  unfold eX0 eX1 eY0 eY1
  split_ifs <;> omega

/-- Reflex `S→W` at the bottom `w` of a south edge. -/
private lemma block_SW {P : Set Cell} (hfin : P.Finite) (hfat : Fat 16 P)
    {u w : Cell} (huw : NextVtx P u w) (hv : u.1 = w.1) (hlt : w.2 < u.2)
    (hcell : (w.1, w.2 - 1) ∈ P)
    {q : Cell} (hx0 : w.1 ≤ q.1) (hx1 : q.1 < snapE w.1)
    (hy0 : snapS w.2 ≤ q.2) (hy1 : q.2 < w.2) :
    ∃ p a b z : Cell, NextVtx P p a ∧ NextVtx P a b ∧ NextVtx P b z ∧
      q ∈ (edgePiece p a b z).cells := by
  obtain ⟨p, hpu⟩ := exists_prevVtx hfin hfat huw.1
  obtain ⟨z, hwz⟩ := exists_nextVtx hfin hfat huw.2.1
  have hfar : w.2 + 16 ≤ u.2 := by
    rcases huw.far hfat with ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ |
      ⟨e1, e2, -⟩ <;> omega
  obtain ⟨hz2, hzdir⟩ := succ_horiz hfat huw hwz (by omega)
  have hzW : z.1 + 16 ≤ w.1 := by
    rcases hzdir with ⟨h16, hr⟩ | ⟨h16, -⟩
    · exact absurd hcell (hr w.1 (by omega) (by omega)).2
    · exact h16
  refine ⟨p, u, w, z, hpu, huw, hwz, ?_⟩
  have hEu := snapE_spec u.1
  have hEw := snapE_spec w.1
  have hSu := snapS_spec u.2
  simp only [RectPiece.cells, mem_rect, edgePiece_x0, edgePiece_y0,
    edgePiece_x1 hfat huw p z, edgePiece_y1 hfat huw p z]
  unfold eX0 eX1 eY0 eY1
  split_ifs <;> omega

-- ============================================================
-- §7 The main theorem
-- ============================================================

set_option linter.unusedVariables false in
/-- **Every corridor cell lies in some corridor rectangle.**  (`hconn` and
    `hsimp` are carried for uniformity with the sibling lemmas; the proof
    does not use them.) -/
theorem corridor_covered {P : Set Cell} (hfin : P.Finite)
    (hconn : CellConnected P) (hsimp : CellConnected Pᶜ) (hfat : Fat 16 P)
    {q : Cell} (hq : q ∈ corridor P) :
    ∃ p u w z : Cell, NextVtx P p u ∧ NextVtx P u w ∧ NextVtx P w z ∧
      q ∈ (edgePiece p u w z).cells := by
  obtain ⟨hqP, hqcore⟩ := hq
  rw [mem_offsetCore, Set.not_subset] at hqcore
  obtain ⟨zc, hzcbox, hzcP⟩ := hqcore
  have hzb : q.1 - q.1 % 3 - 6 ≤ zc.1 ∧ zc.1 < q.1 - q.1 % 3 + 9 ∧
      q.2 - q.2 % 2 - 6 ≤ zc.2 ∧ zc.2 < q.2 - q.2 % 2 + 8 := by
    simpa only [offBox, cornerOf, mem_rect] using hzcbox
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hzb
  have hqmem : ((q.1, q.2) : Cell) ∈ P := by rwa [Prod.mk.eta]
  have hzmem : ((zc.1, zc.2) : Cell) ∉ P := by rwa [Prod.mk.eta]
  by_cases hA : ∃ y, ((q.2 ≤ y ∧ y ≤ zc.2) ∨ (zc.2 ≤ y ∧ y ≤ q.2)) ∧
      (q.1, y) ∉ P
  · -- a flip on the vertical leg: a horizontal governing edge through
    -- column `q.1`, with `q` in its strip
    obtain ⟨y0, hy0rng, hy0P⟩ := hA
    rcases lt_trichotomy q.2 y0 with hup | heq | hdn
    · -- flip above `q`: west edge (interior below) at height `r`
      have hy0z : y0 ≤ zc.2 := by omega
      obtain ⟨r, ⟨hrgt, hrP⟩, hleast⟩ :=
        Int.exists_least_of_bdd (P := fun y => q.2 < y ∧ (q.1, y) ∉ P)
          ⟨q.2, fun z hz => le_of_lt hz.1⟩ ⟨y0, hup, hy0P⟩
      have hry0 : r ≤ y0 := hleast y0 ⟨hup, hy0P⟩
      have hprev : (q.1, r - 1) ∈ P := by
        rcases eq_or_lt_of_le (show q.2 + 1 ≤ r by omega) with heq' | hlt'
        · rw [show r - 1 = q.2 by omega]
          exact hqmem
        · by_contra hnp
          have := hleast (r - 1) ⟨by omega, hnp⟩
          omega
      obtain ⟨u, w, huw, hu2, hw2, hwx, hux, hrun⟩ :=
        govern_H_below hfin hprev hrP
      exact strip_west hfin hfat huw (hu2.trans hw2.symm) (by omega) hwx hux
        (by rw [hu2]; exact snapS_crit (by omega) (by omega)) (by omega)
    · rw [← heq] at hy0P
      exact absurd hqmem hy0P
    · -- flip below `q`: east edge (interior above) at height `r + 1`
      have hy0z : zc.2 ≤ y0 := by omega
      obtain ⟨r, ⟨hrlt, hrP⟩, hgreatest⟩ :=
        Int.exists_greatest_of_bdd (P := fun y => y < q.2 ∧ (q.1, y) ∉ P)
          ⟨q.2, fun z hz => le_of_lt hz.1⟩ ⟨y0, hdn, hy0P⟩
      have hry0 : y0 ≤ r := hgreatest y0 ⟨hdn, hy0P⟩
      have hnext : (q.1, r + 1) ∈ P := by
        rcases eq_or_lt_of_le (show r + 1 ≤ q.2 by omega) with heq' | hlt'
        · rw [heq']
          exact hqmem
        · by_contra hnp
          have := hgreatest (r + 1) ⟨by omega, hnp⟩
          omega
      have hrP' : (q.1, r + 1 - 1) ∉ P := by
        rw [show r + 1 - 1 = r from by ring]
        exact hrP
      obtain ⟨u, w, huw, hu2, hw2, hux, hwx, hrun⟩ :=
        govern_H_above hfin hnext hrP'
      exact strip_east hfin hfat huw (hu2.trans hw2.symm) (by omega) hux hwx
        (by omega) (by rw [hu2]; exact snapN_crit (by omega) (by omega))
  · -- the vertical leg is clean: a flip on the horizontal leg at row `zc.2`
    push_neg at hA
    have hbase : (q.1, zc.2) ∈ P := hA zc.2 (by omega)
    rcases lt_trichotomy q.1 zc.1 with hR | heq | hL
    · -- flip to the right of `q`: north edge (interior west) at column `c`
      obtain ⟨c, ⟨hcgt, hcP⟩, hleast⟩ :=
        Int.exists_least_of_bdd (P := fun x => q.1 < x ∧ (x, zc.2) ∉ P)
          ⟨q.1, fun z hz => le_of_lt hz.1⟩ ⟨zc.1, hR, hzmem⟩
      have hczc : c ≤ zc.1 := hleast zc.1 ⟨hR, hzmem⟩
      have hprev : (c - 1, zc.2) ∈ P := by
        rcases eq_or_lt_of_le (show q.1 + 1 ≤ c by omega) with heq' | hlt'
        · rw [show c - 1 = q.1 by omega]
          exact hbase
        · by_contra hnp
          have := hleast (c - 1) ⟨by omega, hnp⟩
          omega
      obtain ⟨u, w, huw, hu1, hw1, hu2b, hbw, hrun⟩ :=
        govern_V_left hfin hprev hcP
      rcases (by omega : (u.2 ≤ q.2 ∧ q.2 < w.2) ∨ w.2 ≤ q.2 ∨ q.2 < u.2)
        with ⟨hin1, hin2⟩ | hmt | hmb
      · -- the span covers `q.2`: the north strip
        exact strip_north hfin hfat huw (hu1.trans hw1.symm) (by omega)
          (by rw [hu1]; exact snapW_crit (by omega) (by omega)) (by omega)
          hin1 hin2
      · -- span-miss above: reflex `N→E` at `w`
        have hrw := hrun (w.2 - 1) (by omega) (by omega)
        have hcell : (w.1 - 1, w.2) ∈ P :=
          quad_NW hfat huw.2.1 (by rw [hw1]; exact hrw.1)
            (by rw [hw1]; exact hrw.2) hqP (by omega) (by omega) hmt
            (by omega)
        exact block_NE hfin hfat huw (hu1.trans hw1.symm) (by omega) hcell
          (by rw [hw1]; exact snapW_crit (by omega) (by omega)) (by omega)
          hmt (snapN_crit (by omega) hmt)
      · -- span-miss below: reflex `W→N` at `u`
        have hru := hrun u.2 le_rfl (by omega)
        have hcell : (u.1 - 1, u.2 - 1) ∈ P :=
          quad_SW hfat huw.1 (by rw [hu1]; exact hru.1)
            (by rw [hu1]; exact hru.2) hqP (by omega) (by omega) (by omega)
            hmb
        exact block_WN hfin hfat huw (hu1.trans hw1.symm) (by omega) hcell
          (by rw [hu1]; exact snapW_crit (by omega) (by omega)) (by omega)
          (snapS_crit (by omega) hmb) hmb
    · rw [heq] at hbase
      rw [Prod.mk.eta] at hbase
      exact absurd hbase hzcP
    · -- flip to the left of `q`: south edge (interior east)
      obtain ⟨xf, ⟨hxlt, hxP⟩, hgreatest⟩ :=
        Int.exists_greatest_of_bdd (P := fun x => x < q.1 ∧ (x, zc.2) ∉ P)
          ⟨q.1, fun z hz => le_of_lt hz.1⟩ ⟨zc.1, hL, hzmem⟩
      have hxzc : zc.1 ≤ xf := hgreatest zc.1 ⟨hL, hzmem⟩
      have hnext : (xf + 1, zc.2) ∈ P := by
        rcases eq_or_lt_of_le (show xf + 1 ≤ q.1 by omega) with heq' | hlt'
        · rw [heq']
          exact hbase
        · by_contra hnp
          have := hgreatest (xf + 1) ⟨by omega, hnp⟩
          omega
      have hxP' : (xf + 1 - 1, zc.2) ∉ P := by
        rw [show xf + 1 - 1 = xf from by ring]
        exact hxP
      obtain ⟨u, w, huw, hu1, hw1, hw2b, hbu, hrun⟩ :=
        govern_V_right hfin hnext hxP'
      rcases (by omega : (w.2 ≤ q.2 ∧ q.2 < u.2) ∨ u.2 ≤ q.2 ∨ q.2 < w.2)
        with ⟨hin1, hin2⟩ | hmt | hmb
      · -- the span covers `q.2`: the south strip
        exact strip_south hfin hfat huw (hu1.trans hw1.symm) (by omega)
          (by omega) (by rw [hu1]; exact snapE_crit (by omega) (by omega))
          hin1 hin2
      · -- span-miss above: reflex `E→S` at `u`
        have hru := hrun (u.2 - 1) (by omega) (by omega)
        have hcell : (u.1, u.2) ∈ P :=
          quad_NE hfat huw.1 (by rw [hu1]; exact hru.1)
            (by rw [hu1]; exact hru.2) hqP (by omega) (by omega) hmt
            (by omega)
        exact block_ES hfin hfat huw (hu1.trans hw1.symm) (by omega) hcell
          (by omega) (by rw [hu1]; exact snapE_crit (by omega) (by omega))
          hmt (snapN_crit (by omega) hmt)
      · -- span-miss below: reflex `S→W` at `w`
        have hrw := hrun w.2 le_rfl (by omega)
        have hcell : (w.1, w.2 - 1) ∈ P :=
          quad_SE hfat huw.2.1 (by rw [hw1]; exact hrw.1)
            (by rw [hw1]; exact hrw.2) hqP (by omega) (by omega) (by omega)
            hmb
        exact block_SW hfin hfat huw (hu1.trans hw1.symm) (by omega) hcell
          (by omega) (by rw [hw1]; exact snapE_crit (by omega) (by omega))
          (snapS_crit (by omega) hmb) hmb

/-- **Corridor chain existence** — the assembly.  Iterate the successor
    from any vertex; injectivity makes the orbit periodic, the single-
    cycle theorem makes it exhaust the vertices, and the corridor
    rectangles of its edges form the corner chain. -/
theorem exists_corridorChain (P : Set Cell) (hfin : P.Finite)
    (hconn : CellConnected P) (hsimp : CellConnected Pᶜ)
    (hfat : Fat 16 P) (hne : (corridor P).Nonempty) :
    ∃ l : List ChainLink, IsCornerChain l (corridor P) := by
  classical
  -- a vertex exists: the cell of maximal abscissa carries boundary
  have hvex : ∃ v : Cell, IsVertex P v := by
    obtain ⟨q0, hq0⟩ := hne
    obtain ⟨⟨a, b⟩, hpP, hmax⟩ :=
      Set.exists_max_image P Prod.fst hfin ⟨q0, hq0.1⟩
    have hbnd : ((a + 1, b) : ℤ × ℤ) ∈ bndV P := by
      intro hiff
      have hmem : ((a + 1, b) : Cell) ∈ P := hiff.mp
        (show ((a + 1 - 1, b) : Cell) ∈ P by
          rw [show a + 1 - 1 = a from by ring]
          exact hpP)
      have h1 : a + 1 ≤ a := hmax (a + 1, b) hmem
      omega
    obtain ⟨u, w, hnw, -, -⟩ := govern_V hfin hbnd
    exact ⟨u, hnw.1⟩
  obtain ⟨v0, hv0⟩ := hvex
  -- the successor as a function on the (finite) vertex subtype
  haveI : Finite {v : Cell // IsVertex P v} := (vertexSet_finite hfin).to_subtype
  have hstep : ∀ v : {v : Cell // IsVertex P v},
      ∃ w : {v : Cell // IsVertex P v}, NextVtx P v.1 w.1 := by
    intro v
    obtain ⟨w, hw⟩ := exists_nextVtx hfin hfat v.2
    exact ⟨⟨w, hw.2.1⟩, hw⟩
  choose f hf using hstep
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := hf a
    have h2 := hf b
    rw [hab] at h1
    exact Subtype.ext (NextVtx.pred_unique hfat h1 h2)
  -- the orbit of `v0` is periodic
  have hper : ∃ n, 0 < n ∧ f^[n] ⟨v0, hv0⟩ = ⟨v0, hv0⟩ := by
    obtain ⟨i, j, hij, hgij⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => f^[i] ⟨v0, hv0⟩)
    rcases (by omega : i < j ∨ j < i) with h | h
    · refine ⟨j - i, by omega, hinj.iterate i ?_⟩
      have hadd := Function.iterate_add_apply f i (j - i) (⟨v0, hv0⟩ : _)
      rw [show i + (j - i) = j from by omega] at hadd
      rw [← hadd, ← hgij]
    · refine ⟨i - j, by omega, hinj.iterate j ?_⟩
      have hadd := Function.iterate_add_apply f j (i - j) (⟨v0, hv0⟩ : _)
      rw [show j + (i - j) = i from by omega] at hadd
      rw [← hadd, hgij]
  set k := Nat.find hper with hkdef
  have hk_spec := Nat.find_spec hper
  have hk_pos : 0 < k := hk_spec.1
  have hk_min : ∀ m, 0 < m → m < k → f^[m] ⟨v0, hv0⟩ ≠ ⟨v0, hv0⟩ :=
    fun m h1 h2 hm => Nat.find_min hper h2 ⟨h1, hm⟩
  -- the orbit, at the level of cells
  set orb : ℕ → Cell := fun i => (f^[i] ⟨v0, hv0⟩).1 with horbdef
  have horbv : ∀ i, IsVertex P (orb i) := fun i => (f^[i] ⟨v0, hv0⟩).2
  have horb : ∀ i, NextVtx P (orb i) (orb (i + 1)) := by
    intro i
    have h := hf (f^[i] ⟨v0, hv0⟩)
    rwa [← Function.iterate_succ_apply' f i] at h
  have hperiod : ∀ i, orb (i + k) = orb i := by
    intro i
    change (f^[i + k] ⟨v0, hv0⟩).1 = (f^[i] ⟨v0, hv0⟩).1
    rw [Function.iterate_add_apply, hk_spec.2]
  have horbpred : ∀ i, NextVtx P (orb (i + k - 1)) (orb i) := by
    intro i
    have h := horb (i + k - 1)
    rwa [show i + k - 1 + 1 = i + k from by omega, hperiod] at h
  have horbinj : ∀ i j, i < k → j < k → orb i = orb j → i = j := by
    intro i j hi hj hij
    by_contra hne'
    have hsub : f^[i] (⟨v0, hv0⟩ : {v : Cell // IsVertex P v}) =
        f^[j] ⟨v0, hv0⟩ := Subtype.ext hij
    rcases (by omega : i < j ∨ j < i) with h | h
    · refine hk_min (j - i) (by omega) (by omega) (hinj.iterate i ?_)
      have hadd := Function.iterate_add_apply f i (j - i) (⟨v0, hv0⟩ : _)
      rw [show i + (j - i) = j from by omega] at hadd
      rw [← hadd, ← hsub]
    · refine hk_min (i - j) (by omega) (by omega) (hinj.iterate j ?_)
      have hadd := Function.iterate_add_apply f j (i - j) (⟨v0, hv0⟩ : _)
      rw [show j + (i - j) = i from by omega] at hadd
      rw [← hadd, hsub]
  -- the orbit exhausts the vertices (the single-cycle theorem)
  have hStot : ∀ v : Cell, IsVertex P v → ∃ i, i < k ∧ orb i = v := by
    have := vertex_mem_of_closed (S := {v : Cell | ∃ i, i < k ∧ orb i = v})
      hfin hconn hsimp hfat
      (by rintro v ⟨i, hik, rfl⟩; exact horbv i)
      (by
        rintro v ⟨i, hik, rfl⟩ w hw
        have hww : w = orb (i + 1) := NextVtx.unique hfat hw (horb i)
        rcases (by omega : i + 1 < k ∨ i + 1 = k) with h | h
        · exact ⟨i + 1, h, hww.symm⟩
        · refine ⟨0, hk_pos, ?_⟩
          rw [hww, show i + 1 = k from h, show (k : ℕ) = 0 + k from by omega,
            hperiod]
      )
      (by
        intro a b hab hbS
        obtain ⟨i, hik, hb⟩ := hbS
        have hpred := horbpred i
        rw [hb] at hpred
        have haa : a = orb (i + k - 1) := NextVtx.pred_unique hfat hab hpred
        rcases (by omega : i = 0 ∨ 1 ≤ i) with rfl | h
        · exact ⟨k - 1, by omega, by
            rw [haa, show 0 + k - 1 = k - 1 from by omega]⟩
        · exact ⟨i - 1, by omega, by
            rw [haa, show i + k - 1 = i - 1 + k from by omega, hperiod]⟩
      )
      ⟨orb 0, 0, hk_pos, rfl⟩
    exact fun v hv => this v hv
  -- the chain: one rectangle per orbit edge
  refine ⟨(List.range k).map (fun i =>
    ⟨edgePiece (orb (i + k - 1)) (orb i) (orb (i + 1)) (orb (i + 2)),
      eEntry (orb (i + k - 1)) (orb i) (orb (i + 1)),
      eExit (orb i) (orb (i + 1)) (orb (i + 2))⟩), ?_, ?_, ?_, ?_, ?_⟩
  · -- nonempty
    simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    omega
  · -- the chain property: consecutive rectangles push
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    change PushAdj _ _ _ _
    rw [show i + 1 + k - 1 = i + k from by omega, hperiod,
      show i + 1 + 1 = i + 2 from by omega, show i + 1 + 2 = i + 3 from by omega]
    exact edgePiece_pushAdj hfat (horb i) (horb (i + 1))
  · -- pairwise disjointness
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range).imp_of_mem ?_
    intro i j hi hj hij
    simp only [List.mem_range] at hi hj
    exact edgePiece_disjoint hfin hfat (horbpred i) (horb i)
      (by rw [show i + 2 = i + 1 + 1 from by omega]; exact horb (i + 1))
      (horbpred j) (horb j)
      (by rw [show j + 2 = j + 1 + 1 from by omega]; exact horb (j + 1))
      (fun h => absurd (horbinj i j hi hj h) (by omega))
  · -- the cells are exactly the corridor
    apply Set.Subset.antisymm
    · intro q hq'
      simp only [chainCells, Set.mem_iUnion, exists_prop, List.mem_map,
        List.mem_range] at hq'
      obtain ⟨K, ⟨i, hik, rfl⟩, hqK⟩ := hq'
      exact edgePiece_subset_corridor hfin hfat (horbpred i) (horb i)
        (by rw [show i + 2 = i + 1 + 1 from by omega]; exact horb (i + 1)) hqK
    · intro q hq'
      obtain ⟨p, u, w, z, hpu, huw, hwz, hqmem⟩ :=
        corridor_covered hfin hconn hsimp hfat hq'
      obtain ⟨i, hik, hu⟩ := hStot u huw.1
      have hw' : orb (i + 1) = w := by
        have h := horb i
        rw [hu] at h
        exact NextVtx.unique hfat h huw
      have hz' : orb (i + 2) = z := by
        have h := horb (i + 1)
        rw [show i + 1 + 1 = i + 2 from by omega, hw'] at h
        exact NextVtx.unique hfat h hwz
      have hp' : orb (i + k - 1) = p := by
        have h := horbpred i
        rw [hu] at h
        exact NextVtx.pred_unique hfat h hpu
      simp only [chainCells, Set.mem_iUnion, exists_prop, List.mem_map,
        List.mem_range]
      refine ⟨⟨edgePiece (orb (i + k - 1)) (orb i) (orb (i + 1)) (orb (i + 2)),
        eEntry (orb (i + k - 1)) (orb i) (orb (i + 1)),
        eExit (orb i) (orb (i + 1)) (orb (i + 2))⟩, ⟨i, hik, rfl⟩, ?_⟩
      change q ∈ (edgePiece (orb (i + k - 1)) (orb i) (orb (i + 1))
        (orb (i + 2))).cells
      rw [hp', hu, hw', hz']
      exact hqmem
  · -- entry and exit corners are distinct
    intro K hK
    simp only [List.mem_map, List.mem_range] at hK
    obtain ⟨i, -, rfl⟩ := hK
    exact eEntry_ne_eExit _ _ _ _

/-- **Fat polyominoes are L-tileable.**  A finite, connected, simply
    connected (`Pᶜ` connected) 16-fat polyomino whose area is divisible
    by 3 is L-tileable. -/
theorem LTileable_of_fat (P : Set Cell) (hfin : P.Finite)
    (hconn : CellConnected P) (hsimp : CellConnected Pᶜ)
    (hfat : Fat 16 P) (harea : 3 ∣ P.ncard) : LTileable P := by
  rcases P.eq_empty_or_nonempty with rfl | hne
  · exact Tileable.empty _
  obtain ⟨l, hl⟩ := exists_corridorChain P hfin hconn hsimp hfat
    (corridor_nonempty hfin hne)
  have hcorr : LTileable (corridor P) :=
    hl.tileable (dvd_ncard_corridor hfin harea)
  rw [← offsetCore_union_corridor P]
  exact Tileable.union (LTileable_offsetCore hfin) hcorr
    (disjoint_offsetCore_corridor P)
