import TilingPolyomino.AlignedPolyomino
import Mathlib.Data.Int.LeastGreatest

/-!
# The offset polyomino and its corridor

`offsetCore P`: the union of the complete 3×2 grid cells whose inflation by
6 in all directions (`offBox`) lies inside `P` — the formal "offset every
edge inwards by ≥ 6, then snap onto the 3×2 grid".  For *any* `P`:

* `offsetCore P ⊆ P`, finite, with all vertices on the 3×2 grid, hence
  L-tileable with no connectivity or area hypothesis
  (`LTileable_offsetCore`);
* `6 ∣ |offsetCore P|`, so the **corridor** `P \ offsetCore P` has area
  `≡ |P| (mod 3)` (`dvd_ncard_corridor`).
-/

open Set

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

