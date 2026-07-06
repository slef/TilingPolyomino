import TilingPolyomino.VerticalDecomposition

/-!
# The Euler tour: from a spanning tree to a corner chain

Final stage of `exists_cornerChain`: every piece of the spanning tree is
subdivided and the sub-pieces are walked in clockwise order, recursing
through each tree door.  This file proves `exists_cornerChain` and the
main lemma `LTileable_of_vertexAligned` (both formerly stated in
`FatPolyomino.lean`).

## The construction (SL's step 4, as refined)

* Every piece with at least one door is **split** at its vertical midline
  (uniformly — also when all doors are on one side, which the original
  sketch did not split; without the split, a piece whose entry door is
  surrounded by other doors on the same edge admits no chain order).
* Each column of a split piece is cut horizontally at the **midpoints of
  the doors** on its outer edge — nothing else; the sub-piece between two
  consecutive door midpoints serves both as landing area of one door and
  as take-off area of the next.
* The chain walks the west column upward and the east column downward
  (clockwise), detouring into the subtree behind each door as its midpoint
  is passed.  Door crossings are always

  - **west → east** between the two sub-pieces whose *bottom* edges lie at
    the door midpoint — configuration `(BR, BL)`,
  - **east → west** between the two sub-pieces whose *top* edges lie at
    the midpoint — configuration `(TL, TR)`,

  and the two column turns are `(TR, TL)` at the top and `(BL, BR)` at the
  bottom.  All four are proved instances of `PushAdj`.
* The root's cycle is broken at the top turn, so **any** root works and no
  re-rooting of the spanning tree is needed.

All sub-pieces have sides ≥ 6 (column widths are half of ≥ 12; cut
heights are multiples of 6, consecutive ones ≥ 6 apart because doors
have length ≥ 12 and same-side doors are ≥ 12 apart).  The bound 12 = 2·6
is tight: the vertical split needs each column ≥ 6, so pieces ≥ 12 wide,
and a door midpoint sits ≥ 6 (half the door length) from the piece edges.
-/

open Set

-- ============================================================
-- §1 Chain and tree cell bookkeeping
-- ============================================================

lemma chainCells_append (l₁ l₂ : List ChainLink) :
    chainCells (l₁ ++ l₂) = chainCells l₁ ∪ chainCells l₂ := by
  induction l₁ with
  | nil => simp
  | cons K t ih => simp [ih, Set.union_assoc]

lemma cells_subset_chainCells {K : ChainLink} {l : List ChainLink}
    (h : K ∈ l) : K.piece.cells ⊆ chainCells l := by
  induction l with
  | nil => simp at h
  | cons L t ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · rw [chainCells_cons]; exact Set.subset_union_left
    · rw [chainCells_cons]; exact (ih h').trans Set.subset_union_right

/-- Two chains with disjoint total cells can be concatenated keeping
    pairwise disjointness of the links. -/
lemma pairwise_disjoint_append {l₁ l₂ : List ChainLink}
    (h₁ : l₁.Pairwise fun a b => Disjoint a.piece.cells b.piece.cells)
    (h₂ : l₂.Pairwise fun a b => Disjoint a.piece.cells b.piece.cells)
    (h : Disjoint (chainCells l₁) (chainCells l₂)) :
    (l₁ ++ l₂).Pairwise fun a b => Disjoint a.piece.cells b.piece.cells := by
  rw [List.pairwise_append]
  exact ⟨h₁, h₂, fun a ha b hb =>
    h.mono (cells_subset_chainCells ha) (cells_subset_chainCells hb)⟩

/-- The cells of all pieces of a forest. -/
def forestCells (cs : List PieceTree) : Set Cell :=
  ⋃ s ∈ PieceTree.piecesList cs, s.cells

/-- The cells of all pieces of a tree. -/
def treeCells (T : PieceTree) : Set Cell :=
  ⋃ s ∈ T.pieces, s.cells

@[simp] lemma forestCells_nil : forestCells [] = ∅ := by
  simp [forestCells]

@[simp] lemma forestCells_cons (c : PieceTree) (cs : List PieceTree) :
    forestCells (c :: cs) = treeCells c ∪ forestCells cs := by
  ext p
  simp [forestCells, treeCells, List.mem_append, or_and_right, exists_or]

@[simp] lemma treeCells_node (s : VPiece) (cs : List PieceTree) :
    treeCells (.node s cs) = s.cells ∪ forestCells cs := by
  ext p
  simp [treeCells, forestCells]

/-- The cells of a list of door events. -/
def evCells (evs : List (ℤ × Set Cell)) : Set Cell :=
  ⋃ e ∈ evs, e.2

@[simp] lemma evCells_nil : evCells [] = ∅ := by simp [evCells]

@[simp] lemma evCells_cons (e : ℤ × Set Cell) (evs : List (ℤ × Set Cell)) :
    evCells (e :: evs) = e.2 ∪ evCells evs := by
  ext p
  simp [evCells]

lemma evCells_perm {evs evs' : List (ℤ × Set Cell)} (h : evs.Perm evs') :
    evCells evs = evCells evs' := by
  ext p
  simp only [evCells, Set.mem_iUnion]
  constructor
  · rintro ⟨e, he, hp⟩; exact ⟨e, h.mem_iff.mp he, hp⟩
  · rintro ⟨e, he, hp⟩; exact ⟨e, h.mem_iff.mpr he, hp⟩

lemma evCells_append (evs evs' : List (ℤ × Set Cell)) :
    evCells (evs ++ evs') = evCells evs ∪ evCells evs' := by
  induction evs with
  | nil => simp
  | cons e t ih => simp [ih, Set.union_assoc]

-- ============================================================
-- §2 The four door-crossing configurations
-- ============================================================

/-- West → east crossing (or bottom turn): both pieces' bottom edges at the
    shared corner. -/
lemma pushAdj_BR_BL {p q : RectPiece} (hx : q.x0 = p.x1) (hy : q.y0 = p.y0) :
    PushAdj p q .BR .BL := by
  constructor
  · simp only [RectPiece.cornerPt, Prod.mk.injEq]
    omega
  · simp only [RectPiece.cornerCell, CellAdj]
    omega

/-- East → west crossing: both pieces' top edges at the shared corner. -/
lemma pushAdj_TL_TR {p q : RectPiece} (hx : q.x1 = p.x0) (hy : q.y1 = p.y1) :
    PushAdj p q .TL .TR := by
  constructor
  · simp only [RectPiece.cornerPt, Prod.mk.injEq]
    omega
  · simp only [RectPiece.cornerCell, CellAdj]
    omega

/-- Top turn of a piece's cycle: west column to east column. -/
lemma pushAdj_TR_TL {p q : RectPiece} (hx : q.x0 = p.x1) (hy : q.y1 = p.y1) :
    PushAdj p q .TR .TL := by
  constructor
  · simp only [RectPiece.cornerPt, Prod.mk.injEq]
    omega
  · simp only [RectPiece.cornerCell, CellAdj]
    omega

/-- Bottom turn of a piece's cycle: east column to west column. -/
lemma pushAdj_BL_BR {p q : RectPiece} (hx : q.x1 = p.x0) (hy : q.y0 = p.y0) :
    PushAdj p q .BL .BR := by
  constructor
  · simp only [RectPiece.cornerPt, Prod.mk.injEq]
    omega
  · simp only [RectPiece.cornerCell, CellAdj]
    omega

-- ============================================================
-- §3 Door midpoints
-- ============================================================

/-- The midpoint of the (unique) door between two adjacent pieces. -/
def doorMid (s t : VPiece) : ℤ :=
  (max s.y0 t.y0 + min s.y1 t.y1) / 2

lemma doorMid_comm (s t : VPiece) : doorMid s t = doorMid t s := by
  simp [doorMid, max_comm, min_comm]

/-- Margins of a door midpoint, for a `12`-aligned polyomino: it is a
    multiple of `6` sitting at distance ≥ 6 from both ends of the door
    (hence from the tops and bottoms of both pieces). -/
lemma doorMid_spec {P : Set Cell} (hfin : P.Finite)
    (hal : VertexAligned 12 P) {s t : VPiece}
    (hs : s.IsPieceOf P) (ht : t.IsPieceOf P) (hadj : s.Adj t) :
    6 ∣ doorMid s t ∧
    max s.y0 t.y0 + 6 ≤ doorMid s t ∧ doorMid s t + 6 ≤ min s.y1 t.y1 := by
  obtain ⟨-, hs0, -, hs1⟩ := hs.aligned hfin hal
  obtain ⟨-, ht0, -, ht1⟩ := ht.aligned hfin hal
  have hoverlap : max s.y0 t.y0 < min s.y1 t.y1 := by
    rcases hadj with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · omega
  obtain ⟨a, ha⟩ := hs0
  obtain ⟨b, hb⟩ := hs1
  obtain ⟨c, hc⟩ := ht0
  obtain ⟨d, hd⟩ := ht1
  unfold doorMid
  omega

-- ============================================================
-- §4 Sorting the door events
-- ============================================================

private lemma insert_sorted {α : Type*} (key : α → ℤ) (a : α) :
    ∀ l : List α, l.Pairwise (fun x y => key x ≤ key y) →
    ∃ l', (a :: l).Perm l' ∧ l'.Pairwise fun x y => key x ≤ key y := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨[a], .rfl, List.pairwise_singleton _ _⟩
  | cons b t ih =>
    intro hp
    by_cases hab : key a ≤ key b
    · refine ⟨a :: b :: t, .rfl, List.pairwise_cons.mpr ⟨?_, hp⟩⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hab
      · exact hab.trans ((List.pairwise_cons.mp hp).1 y hy')
    · obtain ⟨l', hperm, hsorted⟩ := ih (List.pairwise_cons.mp hp).2
      refine ⟨b :: l', ?_, List.pairwise_cons.mpr ⟨?_, hsorted⟩⟩
      · exact (List.Perm.swap b a t).trans (hperm.cons b)
      · intro y hy
        have hy' : y ∈ a :: t := hperm.mem_iff.mpr hy
        rcases List.mem_cons.mp hy' with rfl | hy''
        · omega
        · exact (List.pairwise_cons.mp hp).1 y hy''

/-- Every list can be permuted into one sorted by an integer key. -/
private lemma exists_sorted_perm {α : Type*} (key : α → ℤ) (l : List α) :
    ∃ l', l.Perm l' ∧ l'.Pairwise fun x y => key x ≤ key y := by
  induction l with
  | nil => exact ⟨[], .rfl, .nil⟩
  | cons a t ih =>
    obtain ⟨t', hperm, hsorted⟩ := ih
    obtain ⟨l', hperm', hsorted'⟩ := insert_sorted key a t' hsorted
    exact ⟨l', (hperm.cons a).trans hperm', hsorted'⟩

-- ============================================================
-- §5 Tour and segment interfaces
-- ============================================================

private lemma ne_nil_of_head? {α : Type*} {l : List α} {a : α}
    (h : l.head? = some a) : l ≠ [] := by
  intro h'
  subst h'
  simp at h

private lemma ne_nil_of_getLast? {α : Type*} {l : List α} {a : α}
    (h : l.getLast? = some a) : l ≠ [] := by
  intro h'
  subst h'
  simp at h

private lemma disjoint_evCells {A : Set Cell} {evs : List (ℤ × Set Cell)}
    (h : ∀ e ∈ evs, Disjoint A e.2) : Disjoint A (evCells evs) := by
  induction evs with
  | nil => simp
  | cons e t ih =>
    rw [evCells_cons]
    exact Set.disjoint_union_right.mpr
      ⟨h e (by simp), ih fun e' he' => h e' (by simp [he'])⟩

/-- A chain touring a region `A` hanging **west** of the door line `xd`
    with door midpoint `m`: entered from the east into the sub-piece just
    below the midpoint (entry corner `TR`), left from the sub-piece just
    above it (exit corner `BR`). -/
structure WestTour (xd m : ℤ) (A : Set Cell) (l : List ChainLink) : Prop where
  chain : l.IsChain LinkAdj
  disjoint : l.Pairwise fun a b => Disjoint a.piece.cells b.piece.cells
  ne : ∀ K ∈ l, K.entry ≠ K.exit
  cells : chainCells l = A
  head : ∃ K, l.head? = some K ∧ K.entry = .TR ∧
    K.piece.x1 = xd ∧ K.piece.y1 = m
  last : ∃ K, l.getLast? = some K ∧ K.exit = .BR ∧
    K.piece.x1 = xd ∧ K.piece.y0 = m

/-- Mirror image: the region hangs **east** of the door line: entered from
    the west into the sub-piece just above the midpoint (entry `BL`), left
    from the sub-piece just below it (exit `TL`). -/
structure EastTour (xd m : ℤ) (A : Set Cell) (l : List ChainLink) : Prop where
  chain : l.IsChain LinkAdj
  disjoint : l.Pairwise fun a b => Disjoint a.piece.cells b.piece.cells
  ne : ∀ K ∈ l, K.entry ≠ K.exit
  cells : chainCells l = A
  head : ∃ K, l.head? = some K ∧ K.entry = .BL ∧
    K.piece.x0 = xd ∧ K.piece.y0 = m
  last : ∃ K, l.getLast? = some K ∧ K.exit = .TL ∧
    K.piece.x0 = xd ∧ K.piece.y1 = m

/-- Chain segment covering the column `[x0, x1) × [lo, hi)` walking
    **upward** with door events on the west edge; `Extra` is the region of
    the subtrees hanging behind those doors. -/
structure SegUp (x0 x1 lo hi : ℤ) (ec xc : Corner) (Extra : Set Cell)
    (l : List ChainLink) : Prop where
  chain : l.IsChain LinkAdj
  disjoint : l.Pairwise fun a b => Disjoint a.piece.cells b.piece.cells
  ne : ∀ K ∈ l, K.entry ≠ K.exit
  cells : chainCells l = rect x0 lo x1 hi ∪ Extra
  head : ∃ K, l.head? = some K ∧ K.entry = ec ∧ K.piece.x0 = x0 ∧
    K.piece.x1 = x1 ∧ K.piece.y0 = lo
  last : ∃ K, l.getLast? = some K ∧ K.exit = xc ∧ K.piece.x0 = x0 ∧
    K.piece.x1 = x1 ∧ K.piece.y1 = hi

/-- Chain segment covering the column `[x0, x1) × [lo, hi)` walking
    **downward** with door events on the east edge. -/
structure SegDown (x0 x1 lo hi : ℤ) (ec xc : Corner) (Extra : Set Cell)
    (l : List ChainLink) : Prop where
  chain : l.IsChain LinkAdj
  disjoint : l.Pairwise fun a b => Disjoint a.piece.cells b.piece.cells
  ne : ∀ K ∈ l, K.entry ≠ K.exit
  cells : chainCells l = rect x0 lo x1 hi ∪ Extra
  head : ∃ K, l.head? = some K ∧ K.entry = ec ∧ K.piece.x0 = x0 ∧
    K.piece.x1 = x1 ∧ K.piece.y1 = hi
  last : ∃ K, l.getLast? = some K ∧ K.exit = xc ∧ K.piece.x0 = x0 ∧
    K.piece.x1 = x1 ∧ K.piece.y0 = lo

-- ============================================================
-- §6 Building one column: fold over the sorted door events
-- ============================================================

/-- **Upward column fold.**  The chain of a west column walking upward:
    sub-pieces between consecutive west-door midpoints, interleaved with
    the tours of the subtrees hanging behind those doors. -/
private theorem exists_segUp (x0 x1 : ℤ) (hx : x0 + 6 ≤ x1) :
    ∀ (evs : List (ℤ × Set Cell)) (lo hi : ℤ) (ec xc : Corner),
      (ec = .BL ∨ ec = .BR) → (xc = .TL ∨ xc = .TR) → lo + 6 ≤ hi →
      evs.Pairwise (fun e f => e.1 + 6 ≤ f.1) →
      (∀ e ∈ evs, lo + 6 ≤ e.1 ∧ e.1 + 6 ≤ hi) →
      (∀ e ∈ evs, ∃ l, WestTour x0 e.1 e.2 l) →
      evs.Pairwise (fun e f => Disjoint e.2 f.2) →
      (∀ e ∈ evs, Disjoint (rect x0 lo x1 hi) e.2) →
      ∃ l, SegUp x0 x1 lo hi ec xc (evCells evs) l := by
  intro evs
  induction evs with
  | nil =>
    intro lo hi ec xc hec hxc hlohi _ _ _ _ _
    refine ⟨[⟨⟨x0, lo, x1, hi, hx, hlohi⟩, ec, xc⟩],
      List.isChain_singleton _, by simp, ?_, by simp [RectPiece.cells],
      ⟨_, rfl, rfl, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl, rfl, rfl⟩⟩
    intro K hK
    obtain rfl : K = _ := by simpa using hK
    rcases hec with rfl | rfl <;> rcases hxc with rfl | rfl <;> simp
  | cons e rest ih =>
    intro lo hi ec xc hec hxc hlohi hpair hbounds htours hdisjE hdisjR
    obtain ⟨m, A⟩ := e
    have hbm : lo + 6 ≤ m ∧ m + 6 ≤ hi := hbounds (m, A) (by simp)
    have hrectsub : rect x0 lo x1 m ⊆ rect x0 lo x1 hi := by
      rintro ⟨x, y⟩ hp
      simp only [mem_rect] at hp ⊢
      omega
    have hrectsub' : rect x0 m x1 hi ⊆ rect x0 lo x1 hi := by
      rintro ⟨x, y⟩ hp
      simp only [mem_rect] at hp ⊢
      omega
    -- the tour behind the door at `m`, and the rest of the column above it
    obtain ⟨lc, hlc⟩ := htours (m, A) (by simp)
    obtain ⟨lr, hlr⟩ := ih m hi .BL xc (Or.inl rfl) hxc (by omega)
      (List.pairwise_cons.mp hpair).2
      (fun e' he' => ⟨by have := (List.pairwise_cons.mp hpair).1 e' he'; omega,
        (hbounds e' (by simp [he'])).2⟩)
      (fun e' he' => htours e' (by simp [he']))
      (List.pairwise_cons.mp hdisjE).2
      (fun e' he' => (hdisjR e' (by simp [he'])).mono_left hrectsub')
    obtain ⟨Kc, hKc_head, hKc_entry, hKc_x1, hKc_y1⟩ := hlc.head
    obtain ⟨Kl, hKl_last, hKl_exit, hKl_x1, hKl_y0⟩ := hlc.last
    obtain ⟨Kr, hKr_head, hKr_entry, hKr_x0, hKr_x1, hKr_y0⟩ := hlr.head
    have hlc_ne : lc ≠ [] := ne_nil_of_head? hKc_head
    have hlr_ne : lr ≠ [] := ne_nil_of_head? hKr_head
    -- disjointness of the landing sub-piece from everything above
    have hQA : Disjoint (rect x0 lo x1 m) A :=
      (hdisjR (m, A) (by simp)).mono_left hrectsub
    have hQrect : Disjoint (rect x0 lo x1 m) (rect x0 m x1 hi) := by
      rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [mem_rect] at h1 h2
      omega
    have hQrest : Disjoint (rect x0 lo x1 m) (evCells rest) :=
      disjoint_evCells fun e' he' =>
        (hdisjR e' (by simp [he'])).mono_left hrectsub
    have hArest : Disjoint A (evCells rest) :=
      disjoint_evCells fun e' he' => (List.pairwise_cons.mp hdisjE).1 e' he'
    have hAup : Disjoint A (rect x0 m x1 hi) :=
      ((hdisjR (m, A) (by simp)).mono_left hrectsub').symm
    have hccells : chainCells (lc ++ lr) =
        A ∪ (rect x0 m x1 hi ∪ evCells rest) := by
      rw [chainCells_append, hlc.cells, hlr.cells]
    refine ⟨⟨⟨x0, lo, x1, m, hx, hbm.1⟩, ec, .TL⟩ :: (lc ++ lr),
      ?_, ?_, ?_, ?_, ⟨_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · -- the chain property
      rw [List.isChain_cons]
      constructor
      · intro y hy
        rw [List.head?_append_of_ne_nil _ hlc_ne, hKc_head] at hy
        obtain rfl : Kc = y := by simpa using hy
        unfold LinkAdj
        rw [hKc_entry]
        exact pushAdj_TL_TR hKc_x1 hKc_y1
      · rw [List.isChain_append]
        refine ⟨hlc.chain, hlr.chain, ?_⟩
        intro a ha b hb
        rw [hKl_last] at ha
        rw [hKr_head] at hb
        obtain rfl : Kl = a := by simpa using ha
        obtain rfl : Kr = b := by simpa using hb
        unfold LinkAdj
        rw [hKl_exit, hKr_entry]
        exact pushAdj_BR_BL (hKr_x0.trans hKl_x1.symm) (hKr_y0.trans hKl_y0.symm)
    · -- pairwise disjointness
      refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro b hb
        have hQall : Disjoint (rect x0 lo x1 m) (chainCells (lc ++ lr)) := by
          rw [hccells]
          exact Set.disjoint_union_right.mpr
            ⟨hQA, Set.disjoint_union_right.mpr ⟨hQrect, hQrest⟩⟩
        exact hQall.mono_right (cells_subset_chainCells hb)
      · refine pairwise_disjoint_append hlc.disjoint hlr.disjoint ?_
        rw [hlc.cells, hlr.cells]
        exact Set.disjoint_union_right.mpr ⟨hAup, hArest⟩
    · -- entry ≠ exit
      intro K hK
      rcases List.mem_cons.mp hK with rfl | hK'
      · rcases hec with rfl | rfl <;> simp
      · rcases List.mem_append.mp hK' with h | h
        · exact hlc.ne K h
        · exact hlr.ne K h
    · -- the cells
      have hmerge : rect x0 lo x1 m ∪ rect x0 m x1 hi = rect x0 lo x1 hi := by
        ext ⟨x, y⟩
        simp only [Set.mem_union, mem_rect]
        omega
      rw [chainCells_cons, chainCells_append, hlc.cells, hlr.cells,
        evCells_cons, ← hmerge]
      have hQc : (⟨⟨x0, lo, x1, m, hx, hbm.1⟩, ec, Corner.TL⟩ :
          ChainLink).piece.cells = rect x0 lo x1 m := rfl
      rw [hQc]
      ext p
      simp only [Set.mem_union]
      tauto
    · -- the last link
      obtain ⟨Ke, hKe_last, hKe_exit, hKe_x0, hKe_x1, hKe_y1⟩ := hlr.last
      refine ⟨Ke, ?_, hKe_exit, hKe_x0, hKe_x1, hKe_y1⟩
      rw [← List.cons_append, List.getLast?_append_of_ne_nil _ hlr_ne]
      exact hKe_last

/-- **Downward column fold.**  The chain of an east column walking
    downward, with the door events sorted from top to bottom. -/
private theorem exists_segDown (x0 x1 : ℤ) (hx : x0 + 6 ≤ x1) :
    ∀ (evs : List (ℤ × Set Cell)) (lo hi : ℤ) (ec xc : Corner),
      (ec = .TL ∨ ec = .TR) → (xc = .BL ∨ xc = .BR) → lo + 6 ≤ hi →
      evs.Pairwise (fun e f => f.1 + 6 ≤ e.1) →
      (∀ e ∈ evs, lo + 6 ≤ e.1 ∧ e.1 + 6 ≤ hi) →
      (∀ e ∈ evs, ∃ l, EastTour x1 e.1 e.2 l) →
      evs.Pairwise (fun e f => Disjoint e.2 f.2) →
      (∀ e ∈ evs, Disjoint (rect x0 lo x1 hi) e.2) →
      ∃ l, SegDown x0 x1 lo hi ec xc (evCells evs) l := by
  intro evs
  induction evs with
  | nil =>
    intro lo hi ec xc hec hxc hlohi _ _ _ _ _
    refine ⟨[⟨⟨x0, lo, x1, hi, hx, hlohi⟩, ec, xc⟩],
      List.isChain_singleton _, by simp, ?_, by simp [RectPiece.cells],
      ⟨_, rfl, rfl, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl, rfl, rfl⟩⟩
    intro K hK
    obtain rfl : K = _ := by simpa using hK
    rcases hec with rfl | rfl <;> rcases hxc with rfl | rfl <;> simp
  | cons e rest ih =>
    intro lo hi ec xc hec hxc hlohi hpair hbounds htours hdisjE hdisjR
    obtain ⟨m, A⟩ := e
    have hbm : lo + 6 ≤ m ∧ m + 6 ≤ hi := hbounds (m, A) (by simp)
    have hrectsub : rect x0 m x1 hi ⊆ rect x0 lo x1 hi := by
      rintro ⟨x, y⟩ hp
      simp only [mem_rect] at hp ⊢
      omega
    have hrectsub' : rect x0 lo x1 m ⊆ rect x0 lo x1 hi := by
      rintro ⟨x, y⟩ hp
      simp only [mem_rect] at hp ⊢
      omega
    -- the tour behind the door at `m`, and the rest of the column below it
    obtain ⟨lc, hlc⟩ := htours (m, A) (by simp)
    obtain ⟨lr, hlr⟩ := ih lo m .TR xc (Or.inr rfl) hxc (by omega)
      (List.pairwise_cons.mp hpair).2
      (fun e' he' => ⟨(hbounds e' (by simp [he'])).1,
        by have := (List.pairwise_cons.mp hpair).1 e' he'; omega⟩)
      (fun e' he' => htours e' (by simp [he']))
      (List.pairwise_cons.mp hdisjE).2
      (fun e' he' => (hdisjR e' (by simp [he'])).mono_left hrectsub')
    obtain ⟨Kc, hKc_head, hKc_entry, hKc_x0, hKc_y0⟩ := hlc.head
    obtain ⟨Kl, hKl_last, hKl_exit, hKl_x0, hKl_y1⟩ := hlc.last
    obtain ⟨Kr, hKr_head, hKr_entry, hKr_x0, hKr_x1, hKr_y1⟩ := hlr.head
    have hlc_ne : lc ≠ [] := ne_nil_of_head? hKc_head
    have hlr_ne : lr ≠ [] := ne_nil_of_head? hKr_head
    -- disjointness of the take-off sub-piece from everything below
    have hQA : Disjoint (rect x0 m x1 hi) A :=
      (hdisjR (m, A) (by simp)).mono_left hrectsub
    have hQrect : Disjoint (rect x0 m x1 hi) (rect x0 lo x1 m) := by
      rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [mem_rect] at h1 h2
      omega
    have hQrest : Disjoint (rect x0 m x1 hi) (evCells rest) :=
      disjoint_evCells fun e' he' =>
        (hdisjR e' (by simp [he'])).mono_left hrectsub
    have hArest : Disjoint A (evCells rest) :=
      disjoint_evCells fun e' he' => (List.pairwise_cons.mp hdisjE).1 e' he'
    have hAdown : Disjoint A (rect x0 lo x1 m) :=
      ((hdisjR (m, A) (by simp)).mono_left hrectsub').symm
    refine ⟨⟨⟨x0, m, x1, hi, hx, hbm.2⟩, ec, .BR⟩ :: (lc ++ lr),
      ?_, ?_, ?_, ?_, ⟨_, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    · rw [List.isChain_cons]
      constructor
      · intro y hy
        rw [List.head?_append_of_ne_nil _ hlc_ne, hKc_head] at hy
        obtain rfl : Kc = y := by simpa using hy
        unfold LinkAdj
        rw [hKc_entry]
        exact pushAdj_BR_BL hKc_x0 hKc_y0
      · rw [List.isChain_append]
        refine ⟨hlc.chain, hlr.chain, ?_⟩
        intro a ha b hb
        rw [hKl_last] at ha
        rw [hKr_head] at hb
        obtain rfl : Kl = a := by simpa using ha
        obtain rfl : Kr = b := by simpa using hb
        unfold LinkAdj
        rw [hKl_exit, hKr_entry]
        exact pushAdj_TL_TR (hKr_x1.trans hKl_x0.symm) (hKr_y1.trans hKl_y1.symm)
    · refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro b hb
        have hQall : Disjoint (rect x0 m x1 hi) (chainCells (lc ++ lr)) := by
          rw [chainCells_append, hlc.cells, hlr.cells]
          exact Set.disjoint_union_right.mpr
            ⟨hQA, Set.disjoint_union_right.mpr ⟨hQrect, hQrest⟩⟩
        exact hQall.mono_right (cells_subset_chainCells hb)
      · refine pairwise_disjoint_append hlc.disjoint hlr.disjoint ?_
        rw [hlc.cells, hlr.cells]
        exact Set.disjoint_union_right.mpr ⟨hAdown, hArest⟩
    · intro K hK
      rcases List.mem_cons.mp hK with rfl | hK'
      · rcases hec with rfl | rfl <;> simp
      · rcases List.mem_append.mp hK' with h | h
        · exact hlc.ne K h
        · exact hlr.ne K h
    · have hmerge : rect x0 m x1 hi ∪ rect x0 lo x1 m = rect x0 lo x1 hi := by
        ext ⟨x, y⟩
        simp only [Set.mem_union, mem_rect]
        omega
      rw [chainCells_cons, chainCells_append, hlc.cells, hlr.cells,
        evCells_cons, ← hmerge]
      have hQc : (⟨⟨x0, m, x1, hi, hx, hbm.2⟩, ec, Corner.BR⟩ :
          ChainLink).piece.cells = rect x0 m x1 hi := rfl
      rw [hQc]
      ext p
      simp only [Set.mem_union]
      tauto
    · obtain ⟨Ke, hKe_last, hKe_exit, hKe_x0, hKe_x1, hKe_y0⟩ := hlr.last
      refine ⟨Ke, ?_, hKe_exit, hKe_x0, hKe_x1, hKe_y0⟩
      rw [← List.cons_append, List.getLast?_append_of_ne_nil _ hlr_ne]
      exact hKe_last

-- ============================================================
-- §7 Tree bookkeeping for the tour induction
-- ============================================================

namespace PieceTree

lemma piecesList_append (l₁ l₂ : List PieceTree) :
    piecesList (l₁ ++ l₂) = piecesList l₁ ++ piecesList l₂ := by
  induction l₁ with
  | nil => simp
  | cons c t ih => simp [ih]

lemma root_mem_pieces (T : PieceTree) : T.root ∈ T.pieces := by
  cases T
  simp

lemma mem_piecesList {c : PieceTree} {cs : List PieceTree} (hc : c ∈ cs)
    {s : VPiece} (hs : s ∈ c.pieces) : s ∈ piecesList cs := by
  induction cs with
  | nil => simp at hc
  | cons d t ih =>
    rcases List.mem_cons.mp hc with rfl | hc'
    · simp [List.mem_append, hs]
    · simp [List.mem_append, ih hc']

lemma pieces_sublist {c : PieceTree} {cs : List PieceTree} (hc : c ∈ cs) :
    c.pieces.Sublist (piecesList cs) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hc
  rw [piecesList_append, piecesList_cons]
  exact ((List.sublist_append_left _ _).trans
    (List.sublist_append_right _ _))

lemma pieces_length_lt {c : PieceTree} {cs : List PieceTree} (hc : c ∈ cs)
    (s : VPiece) : c.pieces.length < (node s cs).pieces.length := by
  have h := (pieces_sublist hc).length_le
  simp only [pieces_node, List.length_cons]
  omega

/-- Distinct children of a nodup forest have disjoint piece lists. -/
lemma piecesList_nodup_pairwise :
    ∀ {cs : List PieceTree}, (piecesList cs).Nodup →
      cs.Pairwise fun c d => ∀ s ∈ c.pieces, s ∉ d.pieces := by
  intro cs
  induction cs with
  | nil => exact fun _ => .nil
  | cons c t ih =>
    intro h
    rw [piecesList_cons, List.nodup_append'] at h
    exact List.pairwise_cons.mpr
      ⟨fun d hd s hsc hsd => h.2.2 hsc (mem_piecesList hd hsd),
        ih h.2.1⟩

/-- Convert the recursive `WFChildren` into a per-child statement. -/
lemma wfChildren_forall {P : Set Cell} {parent : VPiece} :
    ∀ {cs : List PieceTree}, WFChildren P parent cs →
      ∀ c ∈ cs, parent.Adj c.root ∧ c.WF P := by
  intro cs
  induction cs with
  | nil => exact fun _ c hc => absurd hc (by simp)
  | cons d t ih =>
    intro h c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨h.1, h.2.1⟩
    · exact ih h.2.2 c hc'

end PieceTree

/-- Trees with disjoint piece lists (all from the decomposition) occupy
    disjoint regions. -/
private lemma treeCells_disjoint {P : Set Cell} {T₁ T₂ : PieceTree}
    (h₁ : ∀ s ∈ T₁.pieces, s.IsPieceOf P)
    (h₂ : ∀ s ∈ T₂.pieces, s.IsPieceOf P)
    (hdisj : ∀ s ∈ T₁.pieces, s ∉ T₂.pieces) :
    Disjoint (treeCells T₁) (treeCells T₂) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  simp only [treeCells, Set.mem_iUnion] at hp₁ hp₂
  obtain ⟨s, hs, hps⟩ := hp₁
  obtain ⟨t, ht, hpt⟩ := hp₂
  have hne : s ≠ t := fun h => hdisj s hs (h ▸ ht)
  exact Set.disjoint_left.mp ((h₁ s hs).disjoint (h₂ t ht) hne) hps hpt

/-- A decomposition piece not occurring in a tree is disjoint from it. -/
private lemma cells_disjoint_treeCells {P : Set Cell} {R : VPiece}
    (hR : R.IsPieceOf P) {T : PieceTree}
    (hT : ∀ s ∈ T.pieces, s.IsPieceOf P) (hnot : R ∉ T.pieces) :
    Disjoint R.cells (treeCells T) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  simp only [treeCells, Set.mem_iUnion] at hp₂
  obtain ⟨t, ht, hpt⟩ := hp₂
  have hne : R ≠ t := fun h => hnot (h ▸ ht)
  exact Set.disjoint_left.mp (hR.disjoint (hT t ht) hne) hp₁ hpt

/-- The region of a list of subtrees. -/
private def childCells (l : List PieceTree) : Set Cell :=
  ⋃ c ∈ l, treeCells c

@[simp] private lemma childCells_nil : childCells [] = ∅ := by
  simp [childCells]

@[simp] private lemma childCells_cons (c : PieceTree) (l : List PieceTree) :
    childCells (c :: l) = treeCells c ∪ childCells l := by
  ext p
  simp [childCells]

private lemma childCells_eq_forestCells (l : List PieceTree) :
    childCells l = forestCells l := by
  induction l with
  | nil => simp
  | cons c t ih => simp [ih]

private lemma childCells_perm {l l' : List PieceTree} (h : l.Perm l') :
    childCells l = childCells l' := by
  ext p
  simp only [childCells, Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc, hp⟩; exact ⟨c, h.mem_iff.mp hc, hp⟩
  · rintro ⟨c, hc, hp⟩; exact ⟨c, h.mem_iff.mpr hc, hp⟩

private lemma childCells_append (l₁ l₂ : List PieceTree) :
    childCells (l₁ ++ l₂) = childCells l₁ ∪ childCells l₂ := by
  induction l₁ with
  | nil => simp
  | cons c t ih => simp [ih, Set.union_assoc]

private lemma evCells_map (f : PieceTree → ℤ) (l : List PieceTree) :
    evCells (l.map fun c => (f c, treeCells c)) = childCells l := by
  induction l with
  | nil => simp
  | cons c t ih => simp [ih]

-- ============================================================
-- §8 Separation of doors on a common strip
-- ============================================================

/-- Two pieces closing the same strip on the right have the same strip. -/
private lemma strip_eq_of_b_eq {P : Set Cell} {c d : VPiece}
    (hc : c.IsPieceOf P) (hd : d.IsPieceOf P) (h : c.b = d.b) : c.a = d.a := by
  rcases lt_trichotomy c.a d.a with hlt | heq | hgt
  · exact absurd hd.cut_left (hc.no_cut d.a hlt (by have := hd.lt_x; omega))
  · exact heq
  · exact absurd hc.cut_left (hd.no_cut c.a hgt (by have := hc.lt_x; omega))

/-- Two pieces opening the same strip on the left have the same strip. -/
private lemma strip_eq_of_a_eq {P : Set Cell} {c d : VPiece}
    (hc : c.IsPieceOf P) (hd : d.IsPieceOf P) (h : c.a = d.a) : c.b = d.b := by
  rcases lt_trichotomy c.b d.b with hlt | heq | hgt
  · exact absurd hc.cut_right (hd.no_cut c.b (by have := hc.lt_x; omega) hlt)
  · exact heq
  · exact absurd hd.cut_right (hc.no_cut d.b (by have := hd.lt_x; omega) hgt)

/-- Two distinct pieces of one strip have disjoint runs. -/
private lemma runs_disjoint {P : Set Cell} {c d : VPiece}
    (hc : c.IsPieceOf P) (hd : d.IsPieceOf P) (ha : c.a = d.a)
    (hne : c ≠ d) : c.y1 ≤ d.y0 ∨ d.y1 ≤ c.y0 := by
  by_contra hcon
  push_neg at hcon
  have hb := strip_eq_of_a_eq hc hd ha
  have h1 := hc.lt_x
  have h2 := hc.lt_y
  have h3 := hd.lt_y
  refine hne (hc.eq_of_mem hd (p := (c.a, max c.y0 d.y0)) ?_ ?_) <;>
    simp only [VPiece.cells, mem_rect] <;> omega

/-- Doors from two distinct west neighbours into `R` have midpoints at
    least 12 apart. -/
private lemma doorMid_sep_west {P : Set Cell} (hfin : P.Finite)
    (hal : VertexAligned 12 P) {R c d : VPiece} (hR : R.IsPieceOf P)
    (hc : c.IsPieceOf P) (hd : d.IsPieceOf P) (hne : c ≠ d)
    (h1 : DoorBetween c R) (h2 : DoorBetween d R) :
    doorMid R c + 12 ≤ doorMid R d ∨ doorMid R d + 12 ≤ doorMid R c := by
  have hs1 := doorMid_spec hfin hal hR hc (Or.inr h1)
  have hs2 := doorMid_spec hfin hal hR hd (Or.inr h2)
  have hrun := runs_disjoint hc hd
    (strip_eq_of_b_eq hc hd (h1.1.trans h2.1.symm)) hne
  rcases hrun with h | h
  · left; omega
  · right; omega

/-- Doors from `R` into two distinct east neighbours have midpoints at
    least 12 apart. -/
private lemma doorMid_sep_east {P : Set Cell} (hfin : P.Finite)
    (hal : VertexAligned 12 P) {R c d : VPiece} (hR : R.IsPieceOf P)
    (hc : c.IsPieceOf P) (hd : d.IsPieceOf P) (hne : c ≠ d)
    (h1 : DoorBetween R c) (h2 : DoorBetween R d) :
    doorMid R c + 12 ≤ doorMid R d ∨ doorMid R d + 12 ≤ doorMid R c := by
  have hs1 := doorMid_spec hfin hal hR hc (Or.inl h1)
  have hs2 := doorMid_spec hfin hal hR hd (Or.inl h2)
  have hrun := runs_disjoint hc hd (h1.1.symm.trans h2.1) hne
  rcases hrun with h | h
  · left; omega
  · right; omega

private lemma evCells_disjoint {evs₁ evs₂ : List (ℤ × Set Cell)}
    (h : ∀ e ∈ evs₁, ∀ f ∈ evs₂, Disjoint e.2 f.2) :
    Disjoint (evCells evs₁) (evCells evs₂) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  simp only [evCells, Set.mem_iUnion] at hp₁ hp₂
  obtain ⟨e, he, hpe⟩ := hp₁
  obtain ⟨f, hf, hpf⟩ := hp₂
  exact Set.disjoint_left.mp (h e he f hf) hpe hpf

-- ============================================================
-- §9 The tour of a subtree
-- ============================================================

/-- **The Euler tour of a subtree.**  For every subtree `T` of the spanning
    tree and every prospective parent piece `pp` behind a door of `T`'s
    root, there is a chain touring exactly the region of `T`, entering and
    leaving through the two halves of that door (`WestTour` when `T` hangs
    west of the parent, `EastTour` when it hangs east). -/
private theorem exists_tour (P : Set Cell) (hfin : P.Finite)
    (hal : VertexAligned 12 P) :
    ∀ n : ℕ, ∀ T : PieceTree, T.pieces.length ≤ n → T.WF P →
      (∀ s ∈ T.pieces, s.IsPieceOf P) → T.pieces.Nodup →
      (∀ pp : VPiece, pp.IsPieceOf P → pp ∉ T.pieces →
        DoorBetween T.root pp →
        ∃ l, WestTour pp.a (doorMid T.root pp) (treeCells T) l) ∧
      (∀ pp : VPiece, pp.IsPieceOf P → pp ∉ T.pieces →
        DoorBetween pp T.root →
        ∃ l, EastTour pp.b (doorMid pp T.root) (treeCells T) l) ∧
      (∃ l : List ChainLink, l ≠ [] ∧ l.IsChain LinkAdj ∧
        (l.Pairwise fun a b => Disjoint a.piece.cells b.piece.cells) ∧
        (∀ K ∈ l, K.entry ≠ K.exit) ∧ chainCells l = treeCells T) := by
  intro n
  induction n with
  | zero =>
    intro T hlen _ _ _
    have h1 := PieceTree.root_mem_pieces T
    have h2 : T.pieces ≠ [] := List.ne_nil_of_mem h1
    have h3 : 0 < T.pieces.length := List.length_pos_of_ne_nil h2
    omega
  | succ n IHn =>
    rintro ⟨R, cs⟩ hlen hwf hpieces hnodup
    obtain ⟨hR, hwfc⟩ := hwf
    -- ------------------------------------------------------------------
    -- shared preparation: split line, per-child data, event lists
    -- ------------------------------------------------------------------
    have hRal := hR.aligned hfin hal
    obtain ⟨ka, hka⟩ := hRal.1
    obtain ⟨kb, hkb⟩ := hRal.2.2.1
    have h20 := hR.side_ge hfin hal
    set xm := (R.a + R.b) / 2 with hxm
    have hxm1 : R.a + 6 ≤ xm := by omega
    have hxm2 : xm + 6 ≤ R.b := by omega
    have hRnodup' : (R :: PieceTree.piecesList cs).Nodup := by
      have h := hnodup
      rwa [PieceTree.pieces_node] at h
    have hRnotin : R ∉ PieceTree.piecesList cs := (List.nodup_cons.mp hRnodup').1
    have hcsnodup : (PieceTree.piecesList cs).Nodup := (List.nodup_cons.mp hRnodup').2
    have hchild := PieceTree.wfChildren_forall hwfc
    have hcP : ∀ c ∈ cs, ∀ s ∈ c.pieces, s.IsPieceOf P := fun c hc s hs =>
      hpieces s (by
        rw [PieceTree.pieces_node]
        exact List.mem_cons_of_mem _ (PieceTree.mem_piecesList hc hs))
    have hcrootP : ∀ c ∈ cs, c.root.IsPieceOf P := fun c hc =>
      hcP c hc _ (PieceTree.root_mem_pieces c)
    have hRnotc : ∀ c ∈ cs, R ∉ c.pieces := fun c hc h =>
      hRnotin (PieceTree.mem_piecesList hc h)
    have hcnodup : ∀ c ∈ cs, c.pieces.Nodup := fun c hc =>
      hcsnodup.sublist (PieceTree.pieces_sublist hc)
    have htours := fun c (hc : c ∈ cs) =>
      IHn c (by have := PieceTree.pieces_length_lt hc R
                simp only [PieceTree.pieces_node] at hlen this
                omega)
        (hchild c hc).2 (hcP c hc) (hcnodup c hc)
    have hpw := PieceTree.piecesList_nodup_pairwise hcsnodup
    have hpwT : cs.Pairwise fun c d => Disjoint (treeCells c) (treeCells d) :=
      hpw.imp_of_mem fun {c d} hc hd h =>
        treeCells_disjoint (hcP c hc) (hcP d hd) h
    have hRdisj : ∀ c ∈ cs, Disjoint R.cells (treeCells c) := fun c hc =>
      cells_disjoint_treeCells hR (hcP c hc) (hRnotc c hc)
    have hcsides : ∀ c ∈ cs, (DoorBetween c.root R ∧ c.root.b = R.a) ∨
        (DoorBetween R c.root ∧ ¬(c.root.b = R.a)) := by
      intro c hc
      rcases (hchild c hc).1 with hdb | hdb
      · right
        refine ⟨hdb, fun hb => ?_⟩
        have h1 := hR.lt_x
        have h2 := (hcrootP c hc).lt_x
        have h3 := hdb.1
        omega
      · exact Or.inl ⟨hdb, hdb.1⟩
    set westCs := cs.filter (fun c => decide (c.root.b = R.a)) with hWdef
    set eastCs := cs.filter (fun c => !decide (c.root.b = R.a)) with hEdef
    have hsplitperm : (westCs ++ eastCs).Perm cs := List.filter_append_perm _ cs
    have hWmem : ∀ c ∈ westCs, c ∈ cs ∧ DoorBetween c.root R := by
      intro c hc
      rw [hWdef, List.mem_filter] at hc
      rcases hcsides c hc.1 with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact ⟨hc.1, h1⟩
      · exact absurd (of_decide_eq_true hc.2) h2
    have hEmem : ∀ c ∈ eastCs, c ∈ cs ∧ DoorBetween R c.root := by
      intro c hc
      rw [hEdef, List.mem_filter] at hc
      rcases hcsides c hc.1 with ⟨_, h1⟩ | ⟨h2, _⟩
      · exact absurd h1 (by simpa using hc.2)
      · exact ⟨hc.1, h2⟩
    set westEvs := westCs.map (fun c => (doorMid R c.root, treeCells c)) with hWEdef
    set eastEvs := eastCs.map (fun c => (doorMid R c.root, treeCells c)) with hEEdef
    have hWtour : ∀ e ∈ westEvs, ∃ l, WestTour R.a e.1 e.2 l := by
      intro e he
      rw [hWEdef, List.mem_map] at he
      obtain ⟨c, hc, rfl⟩ := he
      obtain ⟨hcs', hdb⟩ := hWmem c hc
      have h := (htours c hcs').1 R hR (hRnotc c hcs') hdb
      rw [doorMid_comm] at h
      exact h
    have hEtour : ∀ e ∈ eastEvs, ∃ l, EastTour R.b e.1 e.2 l := by
      intro e he
      rw [hEEdef, List.mem_map] at he
      obtain ⟨c, hc, rfl⟩ := he
      obtain ⟨hcs', hdb⟩ := hEmem c hc
      exact (htours c hcs').2.1 R hR (hRnotc c hcs') hdb
    have hWbounds : ∀ e ∈ westEvs, R.y0 + 6 ≤ e.1 ∧ e.1 + 6 ≤ R.y1 := by
      intro e he
      rw [hWEdef, List.mem_map] at he
      obtain ⟨c, hc, rfl⟩ := he
      obtain ⟨hcs', hdb⟩ := hWmem c hc
      have h := doorMid_spec hfin hal hR (hcrootP c hcs') (Or.inr hdb)
      have h1 := le_max_left R.y0 c.root.y0
      have h2 := min_le_left R.y1 c.root.y1
      exact ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hEbounds : ∀ e ∈ eastEvs, R.y0 + 6 ≤ e.1 ∧ e.1 + 6 ≤ R.y1 := by
      intro e he
      rw [hEEdef, List.mem_map] at he
      obtain ⟨c, hc, rfl⟩ := he
      obtain ⟨hcs', hdb⟩ := hEmem c hc
      have h := doorMid_spec hfin hal hR (hcrootP c hcs') (Or.inl hdb)
      have h1 := le_max_left R.y0 c.root.y0
      have h2 := min_le_left R.y1 c.root.y1
      exact ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hWdisjR : ∀ e ∈ westEvs, Disjoint R.cells e.2 := by
      intro e he
      rw [hWEdef, List.mem_map] at he
      obtain ⟨c, hc, rfl⟩ := he
      exact hRdisj c (hWmem c hc).1
    have hEdisjR : ∀ e ∈ eastEvs, Disjoint R.cells e.2 := by
      intro e he
      rw [hEEdef, List.mem_map] at he
      obtain ⟨c, hc, rfl⟩ := he
      exact hRdisj c (hEmem c hc).1
    have hWsep : westEvs.Pairwise
        (fun e f => e.1 + 12 ≤ f.1 ∨ f.1 + 12 ≤ e.1) := by
      rw [hWEdef, List.pairwise_map]
      refine ((hpw.filter _).imp_of_mem fun {c d} hc hd h => ?_)
      have hcw := hWmem c hc
      have hdw := hWmem d hd
      have hne : c.root ≠ d.root := fun heq =>
        h c.root (PieceTree.root_mem_pieces c) (heq ▸ PieceTree.root_mem_pieces d)
      exact doorMid_sep_west hfin hal hR (hcrootP c hcw.1) (hcrootP d hdw.1)
        hne hcw.2 hdw.2
    have hEsep : eastEvs.Pairwise
        (fun e f => e.1 + 12 ≤ f.1 ∨ f.1 + 12 ≤ e.1) := by
      rw [hEEdef, List.pairwise_map]
      refine ((hpw.filter _).imp_of_mem fun {c d} hc hd h => ?_)
      have hce := hEmem c hc
      have hde := hEmem d hd
      have hne : c.root ≠ d.root := fun heq =>
        h c.root (PieceTree.root_mem_pieces c) (heq ▸ PieceTree.root_mem_pieces d)
      exact doorMid_sep_east hfin hal hR (hcrootP c hce.1) (hcrootP d hde.1)
        hne hce.2 hde.2
    have hWcellpw : westEvs.Pairwise (fun e f => Disjoint e.2 f.2) := by
      rw [hWEdef, List.pairwise_map]
      exact hpwT.filter _
    have hEcellpw : eastEvs.Pairwise (fun e f => Disjoint e.2 f.2) := by
      rw [hEEdef, List.pairwise_map]
      exact hpwT.filter _
    have hcross : ∀ e ∈ westEvs, ∀ f ∈ eastEvs, Disjoint e.2 f.2 := by
      intro e he f hf
      rw [hWEdef, List.mem_map] at he
      rw [hEEdef, List.mem_map] at hf
      obtain ⟨c, hc, rfl⟩ := he
      obtain ⟨d, hd, rfl⟩ := hf
      have hcw := hWmem c hc
      have hde := hEmem d hd
      have hne : c ≠ d := by
        intro h
        subst h
        rw [hWdef, List.mem_filter] at hc
        rw [hEdef, List.mem_filter] at hd
        have h1 := of_decide_eq_true hc.2
        have h2 : ¬(c.root.b = R.a) := by simpa using hd.2
        exact h2 h1
      exact (hpwT.forall (fun _ _ h => h.symm)) hcw.1 hde.1 hne
    -- sort the two event lists
    obtain ⟨sW, hsWperm, hsWsorted⟩ := exists_sorted_perm (fun e => e.1) westEvs
    obtain ⟨sE, hsEperm, hsEsorted⟩ := exists_sorted_perm (fun e => -e.1) eastEvs
    have hsWmem : ∀ e ∈ sW, e ∈ westEvs := fun e he => hsWperm.mem_iff.mpr he
    have hsEmem : ∀ e ∈ sE, e ∈ eastEvs := fun e he => hsEperm.mem_iff.mpr he
    have hsWsep := (hsWperm.pairwise_iff
      (fun {e f} (h : _ ∨ _) => h.symm)).mp hWsep
    have hsEsep := (hsEperm.pairwise_iff
      (fun {e f} (h : _ ∨ _) => h.symm)).mp hEsep
    have hsWgap : sW.Pairwise (fun e f => e.1 + 6 ≤ f.1) :=
      (hsWsorted.and hsWsep).imp fun {e f} h => by
        obtain ⟨h1, h2⟩ := h
        omega
    have hsEgap : sE.Pairwise (fun e f => f.1 + 6 ≤ e.1) :=
      (hsEsorted.and hsEsep).imp fun {e f} h => by
        obtain ⟨h1, h2⟩ := h
        omega
    have hsWcell : sW.Pairwise (fun e f => Disjoint e.2 f.2) :=
      (hsWperm.pairwise_iff (fun {e f} h => h.symm)).mp hWcellpw
    have hsEcell : sE.Pairwise (fun e f => Disjoint e.2 f.2) :=
      (hsEperm.pairwise_iff (fun {e f} h => h.symm)).mp hEcellpw
    have hsEforall : ∀ e ∈ sE, ∀ f ∈ sE, e ≠ f → Disjoint e.2 f.2 :=
      fun e he f hf hne => (hsEcell.forall (fun _ _ h => h.symm)) he hf hne
    have hsWforall : ∀ e ∈ sW, ∀ f ∈ sW, e ≠ f → Disjoint e.2 f.2 :=
      fun e he f hf hne => (hsWcell.forall (fun _ _ h => h.symm)) he hf hne
    -- total region of the children
    have hkidsW : evCells sW = childCells westCs := by
      rw [← evCells_perm hsWperm, hWEdef, evCells_map]
    have hkidsE : evCells sE = childCells eastCs := by
      rw [← evCells_perm hsEperm, hEEdef, evCells_map]
    have hkidsAll : childCells westCs ∪ childCells eastCs = childCells cs := by
      rw [← childCells_append]
      exact childCells_perm hsplitperm
    have hrectWfull : rect R.a R.y0 xm R.y1 ⊆ R.cells := by
      rintro ⟨x, y⟩ hp
      simp only [mem_rect, VPiece.cells] at hp ⊢
      omega
    have hrectEfull : rect xm R.y0 R.b R.y1 ⊆ R.cells := by
      rintro ⟨x, y⟩ hp
      simp only [mem_rect, VPiece.cells] at hp ⊢
      omega
    refine ⟨?_, ?_, ?_⟩
    -- ==================================================================
    -- the subtree hangs WEST of its parent: enter over, leave under `mp`
    -- ==================================================================
    · intro pp hppP hppnot hdoor
      simp only [PieceTree.root_node] at hdoor ⊢
      set mp := doorMid R pp with hmp
      have hmpspec := doorMid_spec hfin hal hR hppP (Or.inl hdoor)
      have hy0mp : R.y0 + 6 ≤ mp := by
        have := le_max_left R.y0 pp.y0
        omega
      have hmpy1 : mp + 6 ≤ R.y1 := by
        have := min_le_left R.y1 pp.y1
        omega
      have hppne : ∀ c ∈ cs, pp ∉ c.pieces := fun c hc h => hppnot (by
        rw [PieceTree.pieces_node]
        exact List.mem_cons_of_mem _ (PieceTree.mem_piecesList hc h))
      have hsepP : ∀ e ∈ eastEvs, e.1 + 12 ≤ mp ∨ mp + 12 ≤ e.1 := by
        intro e he
        rw [hEEdef, List.mem_map] at he
        obtain ⟨c, hc, rfl⟩ := he
        obtain ⟨hcs', hdb⟩ := hEmem c hc
        have hnepc : c.root ≠ pp := fun h =>
          hppne c hcs' (h ▸ PieceTree.root_mem_pieces c)
        have h := doorMid_sep_east hfin hal hR (hcrootP c hcs') hppP hnepc hdb hdoor
        rcases h with h | h
        · exact Or.inl (by dsimp only; omega)
        · exact Or.inr (by dsimp only; omega)
      -- split the east events at the parent door
      set eA := sE.filter (fun e => decide (mp < e.1)) with heA
      set eB := sE.filter (fun e => !decide (mp < e.1)) with heB
      have hsplitE : (eA ++ eB).Perm sE := List.filter_append_perm _ sE
      have heAmem : ∀ e ∈ eA, e ∈ sE ∧ mp + 12 ≤ e.1 := by
        intro e he
        rw [heA, List.mem_filter] at he
        have hlt := of_decide_eq_true he.2
        have := hsepP e (hsEmem e he.1)
        exact ⟨he.1, by omega⟩
      have heBmem : ∀ e ∈ eB, e ∈ sE ∧ e.1 + 12 ≤ mp := by
        intro e he
        rw [heB, List.mem_filter] at he
        have hge : ¬(mp < e.1) := by simpa using he.2
        have := hsepP e (hsEmem e he.1)
        exact ⟨he.1, by omega⟩
      have hrectB : rect xm R.y0 R.b mp ⊆ R.cells := by
        rintro ⟨x, y⟩ hp
        simp only [mem_rect, VPiece.cells] at hp ⊢
        omega
      have hrectW : rect R.a R.y0 xm R.y1 ⊆ R.cells := by
        rintro ⟨x, y⟩ hp
        simp only [mem_rect, VPiece.cells] at hp ⊢
        omega
      have hrectA : rect xm mp R.b R.y1 ⊆ R.cells := by
        rintro ⟨x, y⟩ hp
        simp only [mem_rect, VPiece.cells] at hp ⊢
        omega
      -- the three segments
      obtain ⟨lB, hlB⟩ := exists_segDown xm R.b (by omega) eB R.y0 mp
        .TR .BL (Or.inr rfl) (Or.inl rfl) (by omega)
        (hsEgap.filter _)
        (fun e he => ⟨(hEbounds e (hsEmem e (heBmem e he).1)).1,
          by have := (heBmem e he).2; omega⟩)
        (fun e he => hEtour e (hsEmem e (heBmem e he).1))
        (hsEcell.filter _)
        (fun e he => ((hEdisjR e (hsEmem e (heBmem e he).1)).mono_left hrectB))
      obtain ⟨lW, hlW⟩ := exists_segUp R.a xm (by omega) sW R.y0 R.y1
        .BR .TR (Or.inr rfl) (Or.inr rfl) (by omega)
        hsWgap
        (fun e he => hWbounds e (hsWmem e he))
        (fun e he => hWtour e (hsWmem e he))
        hsWcell
        (fun e he => ((hWdisjR e (hsWmem e he)).mono_left hrectW))
      obtain ⟨lA, hlA⟩ := exists_segDown xm R.b (by omega) eA mp R.y1
        .TL .BR (Or.inl rfl) (Or.inr rfl) (by omega)
        (hsEgap.filter _)
        (fun e he => ⟨by have := (heAmem e he).2; omega,
          (hEbounds e (hsEmem e (heAmem e he).1)).2⟩)
        (fun e he => hEtour e (hsEmem e (heAmem e he).1))
        (hsEcell.filter _)
        (fun e he => ((hEdisjR e (hsEmem e (heAmem e he).1)).mono_left hrectA))
      obtain ⟨KB1, hKB1h, hKB1e, hKB1x0, hKB1x1, hKB1y1⟩ := hlB.head
      obtain ⟨KB2, hKB2l, hKB2e, hKB2x0, hKB2x1, hKB2y0⟩ := hlB.last
      obtain ⟨KW1, hKW1h, hKW1e, hKW1x0, hKW1x1, hKW1y0⟩ := hlW.head
      obtain ⟨KW2, hKW2l, hKW2e, hKW2x0, hKW2x1, hKW2y1⟩ := hlW.last
      obtain ⟨KA1, hKA1h, hKA1e, hKA1x0, hKA1x1, hKA1y1⟩ := hlA.head
      obtain ⟨KA2, hKA2l, hKA2e, hKA2x0, hKA2x1, hKA2y0⟩ := hlA.last
      have hlBne : lB ≠ [] := ne_nil_of_head? hKB1h
      have hlWne : lW ≠ [] := ne_nil_of_head? hKW1h
      have hlAne : lA ≠ [] := ne_nil_of_head? hKA1h
      -- cross-segment disjointness
      have hWA : Disjoint (chainCells lW) (chainCells lA) := by
        rw [hlW.cells, hlA.cells]
        refine Set.disjoint_union_left.mpr ⟨?_, ?_⟩
        · refine Set.disjoint_union_right.mpr ⟨?_, ?_⟩
          · rw [Set.disjoint_left]
            rintro ⟨x, y⟩ h1 h2
            simp only [mem_rect] at h1 h2
            omega
          · exact disjoint_evCells fun e he =>
              (hEdisjR e (hsEmem e (heAmem e he).1)).mono_left hrectW
        · refine Set.disjoint_union_right.mpr ⟨?_, ?_⟩
          · exact (disjoint_evCells fun e he =>
              (hWdisjR e (hsWmem e he)).mono_left hrectA).symm
          · exact evCells_disjoint fun e he f hf =>
              hcross e (hsWmem e he) f (hsEmem f (heAmem f hf).1)
      have hBWA : Disjoint (chainCells lB) (chainCells (lW ++ lA)) := by
        rw [chainCells_append, hlB.cells, hlW.cells, hlA.cells]
        have h1 : Disjoint (rect xm R.y0 R.b mp) (rect R.a R.y0 xm R.y1) := by
          rw [Set.disjoint_left]
          rintro ⟨x, y⟩ h1 h2
          simp only [mem_rect] at h1 h2
          omega
        have h2 : Disjoint (rect xm R.y0 R.b mp) (rect xm mp R.b R.y1) := by
          rw [Set.disjoint_left]
          rintro ⟨x, y⟩ h1 h2
          simp only [mem_rect] at h1 h2
          omega
        have hBA : ∀ f ∈ eA, ∀ e ∈ eB, Disjoint e.2 f.2 := by
          intro f hf e he
          refine hsEforall e (heBmem e he).1 f (heAmem f hf).1 fun heq => ?_
          have hA := (heAmem f hf).2
          have hB := (heBmem e he).2
          rw [heq] at hB
          omega
        refine Set.disjoint_union_left.mpr ⟨?_, ?_⟩
        · refine Set.disjoint_union_right.mpr ⟨Set.disjoint_union_right.mpr
            ⟨h1, ?_⟩, Set.disjoint_union_right.mpr ⟨h2, ?_⟩⟩
          · exact disjoint_evCells fun e he =>
              (hWdisjR e (hsWmem e he)).mono_left hrectB
          · exact disjoint_evCells fun e he =>
              (hEdisjR e (hsEmem e (heAmem e he).1)).mono_left hrectB
        · refine Set.disjoint_union_right.mpr ⟨Set.disjoint_union_right.mpr
            ⟨?_, ?_⟩, Set.disjoint_union_right.mpr ⟨?_, ?_⟩⟩
          · exact (disjoint_evCells fun e he =>
              (hEdisjR e (hsEmem e (heBmem e he).1)).mono_left hrectW).symm
          · exact (evCells_disjoint fun e he f hf =>
              hcross e (hsWmem e he) f (hsEmem f (heBmem f hf).1)).symm
          · exact (disjoint_evCells fun e he =>
              (hEdisjR e (hsEmem e (heBmem e he).1)).mono_left hrectA).symm
          · exact evCells_disjoint fun e he f hf => hBA f hf e he
      refine ⟨lB ++ (lW ++ lA), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- chain
        rw [List.isChain_append]
        refine ⟨hlB.chain, ?_, ?_⟩
        · rw [List.isChain_append]
          refine ⟨hlW.chain, hlA.chain, ?_⟩
          intro a ha b hb
          rw [hKW2l] at ha
          rw [hKA1h] at hb
          obtain rfl : KW2 = a := by simpa using ha
          obtain rfl : KA1 = b := by simpa using hb
          unfold LinkAdj
          rw [hKW2e, hKA1e]
          exact pushAdj_TR_TL (hKA1x0.trans hKW2x1.symm) (hKA1y1.trans hKW2y1.symm)
        · intro a ha b hb
          rw [hKB2l] at ha
          rw [List.head?_append_of_ne_nil _ hlWne, hKW1h] at hb
          obtain rfl : KB2 = a := by simpa using ha
          obtain rfl : KW1 = b := by simpa using hb
          unfold LinkAdj
          rw [hKB2e, hKW1e]
          exact pushAdj_BL_BR (hKW1x1.trans hKB2x0.symm) (hKW1y0.trans hKB2y0.symm)
      · -- pairwise disjointness
        exact pairwise_disjoint_append hlB.disjoint
          (pairwise_disjoint_append hlW.disjoint hlA.disjoint hWA) hBWA
      · -- entry ≠ exit
        intro K hK
        rcases List.mem_append.mp hK with h | h
        · exact hlB.ne K h
        rcases List.mem_append.mp h with h' | h'
        · exact hlW.ne K h'
        · exact hlA.ne K h'
      · -- the cells
        have hrects : rect xm R.y0 R.b mp ∪
            (rect R.a R.y0 xm R.y1 ∪ rect xm mp R.b R.y1) = R.cells := by
          ext ⟨x, y⟩
          simp only [Set.mem_union, mem_rect, VPiece.cells]
          omega
        have hEsplitcells : evCells eA ∪ evCells eB = childCells eastCs := by
          rw [← evCells_append, evCells_perm hsplitE, hkidsE]
        rw [chainCells_append, chainCells_append, hlB.cells, hlW.cells,
          hlA.cells, treeCells_node, ← childCells_eq_forestCells,
          ← hkidsAll, ← hrects, ← hEsplitcells, ← hkidsW]
        simp only [Set.union_assoc, Set.union_left_comm, Set.union_comm]
      · -- head: entered from the east, above the midpoint of the door
        refine ⟨KB1, ?_, hKB1e, hKB1x1.trans hdoor.1, hKB1y1⟩
        rw [List.head?_append_of_ne_nil _ hlBne]
        exact hKB1h
      · -- last: left towards the east, below the midpoint
        refine ⟨KA2, ?_, hKA2e, hKA2x1.trans hdoor.1, hKA2y0⟩
        rw [List.getLast?_append_of_ne_nil _ (by simp [hlAne]),
          List.getLast?_append_of_ne_nil _ hlAne]
        exact hKA2l
    -- ==================================================================
    -- the subtree hangs EAST of its parent: enter over, leave under `mp`
    -- ==================================================================
    · intro pp hppP hppnot hdoor
      simp only [PieceTree.root_node] at hdoor ⊢
      set mp := doorMid pp R with hmp
      have hmpspec := doorMid_spec hfin hal hppP hR (Or.inl hdoor)
      have hcomm : doorMid R pp = mp := doorMid_comm R pp
      have hy0mp : R.y0 + 6 ≤ mp := by
        have := le_max_right pp.y0 R.y0
        omega
      have hmpy1 : mp + 6 ≤ R.y1 := by
        have := min_le_right pp.y1 R.y1
        omega
      have hppne : ∀ c ∈ cs, pp ∉ c.pieces := fun c hc h => hppnot (by
        rw [PieceTree.pieces_node]
        exact List.mem_cons_of_mem _ (PieceTree.mem_piecesList hc h))
      have hsepP : ∀ e ∈ westEvs, e.1 + 12 ≤ mp ∨ mp + 12 ≤ e.1 := by
        intro e he
        rw [hWEdef, List.mem_map] at he
        obtain ⟨c, hc, rfl⟩ := he
        obtain ⟨hcs', hdb⟩ := hWmem c hc
        have hnepc : c.root ≠ pp := fun h =>
          hppne c hcs' (h ▸ PieceTree.root_mem_pieces c)
        have h := doorMid_sep_west hfin hal hR (hcrootP c hcs') hppP hnepc hdb hdoor
        rcases h with h | h
        · exact Or.inl (by dsimp only; omega)
        · exact Or.inr (by dsimp only; omega)
      -- split the west events at the parent door
      set wA := sW.filter (fun e => decide (mp < e.1)) with hwA
      set wB := sW.filter (fun e => !decide (mp < e.1)) with hwB
      have hsplitW : (wA ++ wB).Perm sW := List.filter_append_perm _ sW
      have hwAmem : ∀ e ∈ wA, e ∈ sW ∧ mp + 12 ≤ e.1 := by
        intro e he
        rw [hwA, List.mem_filter] at he
        have hlt := of_decide_eq_true he.2
        have := hsepP e (hsWmem e he.1)
        exact ⟨he.1, by omega⟩
      have hwBmem : ∀ e ∈ wB, e ∈ sW ∧ e.1 + 12 ≤ mp := by
        intro e he
        rw [hwB, List.mem_filter] at he
        have hge : ¬(mp < e.1) := by simpa using he.2
        have := hsepP e (hsWmem e he.1)
        exact ⟨he.1, by omega⟩
      have hrectA : rect R.a mp xm R.y1 ⊆ R.cells := by
        rintro ⟨x, y⟩ hp
        simp only [mem_rect, VPiece.cells] at hp ⊢
        omega
      have hrectE : rect xm R.y0 R.b R.y1 ⊆ R.cells := by
        rintro ⟨x, y⟩ hp
        simp only [mem_rect, VPiece.cells] at hp ⊢
        omega
      have hrectB : rect R.a R.y0 xm mp ⊆ R.cells := by
        rintro ⟨x, y⟩ hp
        simp only [mem_rect, VPiece.cells] at hp ⊢
        omega
      -- the three segments
      obtain ⟨lA, hlA⟩ := exists_segUp R.a xm (by omega) wA mp R.y1
        .BL .TR (Or.inl rfl) (Or.inr rfl) (by omega)
        (hsWgap.filter _)
        (fun e he => ⟨by have := (hwAmem e he).2; omega,
          (hWbounds e (hsWmem e (hwAmem e he).1)).2⟩)
        (fun e he => hWtour e (hsWmem e (hwAmem e he).1))
        (hsWcell.filter _)
        (fun e he => ((hWdisjR e (hsWmem e (hwAmem e he).1)).mono_left hrectA))
      obtain ⟨lE, hlE⟩ := exists_segDown xm R.b (by omega) sE R.y0 R.y1
        .TL .BL (Or.inl rfl) (Or.inl rfl) (by omega)
        hsEgap
        (fun e he => hEbounds e (hsEmem e he))
        (fun e he => hEtour e (hsEmem e he))
        hsEcell
        (fun e he => ((hEdisjR e (hsEmem e he)).mono_left hrectE))
      obtain ⟨lB, hlB⟩ := exists_segUp R.a xm (by omega) wB R.y0 mp
        .BR .TL (Or.inr rfl) (Or.inl rfl) (by omega)
        (hsWgap.filter _)
        (fun e he => ⟨(hWbounds e (hsWmem e (hwBmem e he).1)).1,
          by have := (hwBmem e he).2; omega⟩)
        (fun e he => hWtour e (hsWmem e (hwBmem e he).1))
        (hsWcell.filter _)
        (fun e he => ((hWdisjR e (hsWmem e (hwBmem e he).1)).mono_left hrectB))
      obtain ⟨KA1, hKA1h, hKA1e, hKA1x0, hKA1x1, hKA1y0⟩ := hlA.head
      obtain ⟨KA2, hKA2l, hKA2e, hKA2x0, hKA2x1, hKA2y1⟩ := hlA.last
      obtain ⟨KE1, hKE1h, hKE1e, hKE1x0, hKE1x1, hKE1y1⟩ := hlE.head
      obtain ⟨KE2, hKE2l, hKE2e, hKE2x0, hKE2x1, hKE2y0⟩ := hlE.last
      obtain ⟨KB1, hKB1h, hKB1e, hKB1x0, hKB1x1, hKB1y0⟩ := hlB.head
      obtain ⟨KB2, hKB2l, hKB2e, hKB2x0, hKB2x1, hKB2y1⟩ := hlB.last
      have hlAne : lA ≠ [] := ne_nil_of_head? hKA1h
      have hlEne : lE ≠ [] := ne_nil_of_head? hKE1h
      have hlBne : lB ≠ [] := ne_nil_of_head? hKB1h
      -- cross-segment disjointness
      have hEB : Disjoint (chainCells lE) (chainCells lB) := by
        rw [hlE.cells, hlB.cells]
        refine Set.disjoint_union_left.mpr ⟨?_, ?_⟩
        · refine Set.disjoint_union_right.mpr ⟨?_, ?_⟩
          · rw [Set.disjoint_left]
            rintro ⟨x, y⟩ h1 h2
            simp only [mem_rect] at h1 h2
            omega
          · exact disjoint_evCells fun e he =>
              (hWdisjR e (hsWmem e (hwBmem e he).1)).mono_left hrectE
        · refine Set.disjoint_union_right.mpr ⟨?_, ?_⟩
          · exact (disjoint_evCells fun e he =>
              (hEdisjR e (hsEmem e he)).mono_left hrectB).symm
          · exact (evCells_disjoint fun e he f hf =>
              hcross e (hsWmem e (hwBmem e he).1) f (hsEmem f hf)).symm
      have hAEB : Disjoint (chainCells lA) (chainCells (lE ++ lB)) := by
        rw [chainCells_append, hlA.cells, hlE.cells, hlB.cells]
        have h1 : Disjoint (rect R.a mp xm R.y1) (rect xm R.y0 R.b R.y1) := by
          rw [Set.disjoint_left]
          rintro ⟨x, y⟩ h1 h2
          simp only [mem_rect] at h1 h2
          omega
        have h2 : Disjoint (rect R.a mp xm R.y1) (rect R.a R.y0 xm mp) := by
          rw [Set.disjoint_left]
          rintro ⟨x, y⟩ h1 h2
          simp only [mem_rect] at h1 h2
          omega
        have hAB : ∀ e ∈ wA, ∀ f ∈ wB, Disjoint e.2 f.2 := by
          intro e he f hf
          refine hsWforall e (hwAmem e he).1 f (hwBmem f hf).1 fun heq => ?_
          have hA := (hwAmem e he).2
          have hB := (hwBmem f hf).2
          rw [heq] at hA
          omega
        refine Set.disjoint_union_left.mpr ⟨?_, ?_⟩
        · refine Set.disjoint_union_right.mpr ⟨Set.disjoint_union_right.mpr
            ⟨h1, ?_⟩, Set.disjoint_union_right.mpr ⟨h2, ?_⟩⟩
          · exact disjoint_evCells fun e he =>
              (hEdisjR e (hsEmem e he)).mono_left hrectA
          · exact disjoint_evCells fun e he =>
              (hWdisjR e (hsWmem e (hwBmem e he).1)).mono_left hrectA
        · refine Set.disjoint_union_right.mpr ⟨Set.disjoint_union_right.mpr
            ⟨?_, ?_⟩, Set.disjoint_union_right.mpr ⟨?_, ?_⟩⟩
          · exact (disjoint_evCells fun e he =>
              (hWdisjR e (hsWmem e (hwAmem e he).1)).mono_left hrectE).symm
          · exact evCells_disjoint fun e he f hf =>
              hcross e (hsWmem e (hwAmem e he).1) f (hsEmem f hf)
          · exact (disjoint_evCells fun e he =>
              (hWdisjR e (hsWmem e (hwAmem e he).1)).mono_left hrectB).symm
          · exact evCells_disjoint hAB
      refine ⟨lA ++ (lE ++ lB), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- chain
        rw [List.isChain_append]
        refine ⟨hlA.chain, ?_, ?_⟩
        · rw [List.isChain_append]
          refine ⟨hlE.chain, hlB.chain, ?_⟩
          intro a ha b hb
          rw [hKE2l] at ha
          rw [hKB1h] at hb
          obtain rfl : KE2 = a := by simpa using ha
          obtain rfl : KB1 = b := by simpa using hb
          unfold LinkAdj
          rw [hKE2e, hKB1e]
          exact pushAdj_BL_BR (hKB1x1.trans hKE2x0.symm) (hKB1y0.trans hKE2y0.symm)
        · intro a ha b hb
          rw [hKA2l] at ha
          rw [List.head?_append_of_ne_nil _ hlEne, hKE1h] at hb
          obtain rfl : KA2 = a := by simpa using ha
          obtain rfl : KE1 = b := by simpa using hb
          unfold LinkAdj
          rw [hKA2e, hKE1e]
          exact pushAdj_TR_TL (hKE1x0.trans hKA2x1.symm) (hKE1y1.trans hKA2y1.symm)
      · -- pairwise disjointness
        exact pairwise_disjoint_append hlA.disjoint
          (pairwise_disjoint_append hlE.disjoint hlB.disjoint hEB) hAEB
      · -- entry ≠ exit
        intro K hK
        rcases List.mem_append.mp hK with h | h
        · exact hlA.ne K h
        rcases List.mem_append.mp h with h' | h'
        · exact hlE.ne K h'
        · exact hlB.ne K h'
      · -- the cells
        have hrects : rect R.a mp xm R.y1 ∪
            (rect xm R.y0 R.b R.y1 ∪ rect R.a R.y0 xm mp) = R.cells := by
          ext ⟨x, y⟩
          simp only [Set.mem_union, mem_rect, VPiece.cells]
          omega
        have hWsplitcells : evCells wA ∪ evCells wB = childCells westCs := by
          rw [← evCells_append, evCells_perm hsplitW, hkidsW]
        rw [chainCells_append, chainCells_append, hlA.cells, hlE.cells,
          hlB.cells, treeCells_node, ← childCells_eq_forestCells,
          ← hkidsAll, ← hrects, ← hWsplitcells, ← hkidsE]
        simp only [Set.union_assoc, Set.union_left_comm, Set.union_comm]
      · -- head: entered from the west, above the midpoint of the door
        refine ⟨KA1, ?_, hKA1e, hKA1x0.trans hdoor.1.symm, hKA1y0⟩
        rw [List.head?_append_of_ne_nil _ hlAne]
        exact hKA1h
      · -- last: left towards the west, below the midpoint
        refine ⟨KB2, ?_, hKB2e, hKB2x0.trans hdoor.1.symm, hKB2y1⟩
        rw [List.getLast?_append_of_ne_nil _ (by simp [hlBne]),
          List.getLast?_append_of_ne_nil _ hlBne]
        exact hKB2l
    -- ==================================================================
    -- the root chain: break the root's cycle at the top turn
    -- ==================================================================
    · obtain ⟨lE, hlE⟩ := exists_segDown xm R.b (by omega) sE R.y0 R.y1
        .TR .BL (Or.inr rfl) (Or.inl rfl) (by omega)
        hsEgap
        (fun e he => hEbounds e (hsEmem e he))
        (fun e he => hEtour e (hsEmem e he))
        hsEcell
        (fun e he => ((hEdisjR e (hsEmem e he)).mono_left hrectEfull))
      obtain ⟨lW, hlW⟩ := exists_segUp R.a xm (by omega) sW R.y0 R.y1
        .BR .TL (Or.inr rfl) (Or.inl rfl) (by omega)
        hsWgap
        (fun e he => hWbounds e (hsWmem e he))
        (fun e he => hWtour e (hsWmem e he))
        hsWcell
        (fun e he => ((hWdisjR e (hsWmem e he)).mono_left hrectWfull))
      obtain ⟨KE1, hKE1h, hKE1e, hKE1x0, hKE1x1, hKE1y1⟩ := hlE.head
      obtain ⟨KE2, hKE2l, hKE2e, hKE2x0, hKE2x1, hKE2y0⟩ := hlE.last
      obtain ⟨KW1, hKW1h, hKW1e, hKW1x0, hKW1x1, hKW1y0⟩ := hlW.head
      have hlEne : lE ≠ [] := ne_nil_of_head? hKE1h
      have hlWne : lW ≠ [] := ne_nil_of_head? hKW1h
      have hEW : Disjoint (chainCells lE) (chainCells lW) := by
        rw [hlE.cells, hlW.cells]
        refine Set.disjoint_union_left.mpr ⟨?_, ?_⟩
        · refine Set.disjoint_union_right.mpr ⟨?_, ?_⟩
          · rw [Set.disjoint_left]
            rintro ⟨x, y⟩ h1 h2
            simp only [mem_rect] at h1 h2
            omega
          · exact disjoint_evCells fun e he =>
              (hWdisjR e (hsWmem e he)).mono_left hrectEfull
        · refine Set.disjoint_union_right.mpr ⟨?_, ?_⟩
          · exact (disjoint_evCells fun e he =>
              (hEdisjR e (hsEmem e he)).mono_left hrectWfull).symm
          · exact (evCells_disjoint fun e he f hf =>
              hcross e (hsWmem e he) f (hsEmem f hf)).symm
      refine ⟨lE ++ lW, by simp [hlEne], ?_, ?_, ?_, ?_⟩
      · rw [List.isChain_append]
        refine ⟨hlE.chain, hlW.chain, ?_⟩
        intro a ha b hb
        rw [hKE2l] at ha
        rw [hKW1h] at hb
        obtain rfl : KE2 = a := by simpa using ha
        obtain rfl : KW1 = b := by simpa using hb
        unfold LinkAdj
        rw [hKE2e, hKW1e]
        exact pushAdj_BL_BR (hKW1x1.trans hKE2x0.symm) (hKW1y0.trans hKE2y0.symm)
      · exact pairwise_disjoint_append hlE.disjoint hlW.disjoint hEW
      · intro K hK
        rcases List.mem_append.mp hK with h | h
        · exact hlE.ne K h
        · exact hlW.ne K h
      · have hrects : rect xm R.y0 R.b R.y1 ∪ rect R.a R.y0 xm R.y1 =
            R.cells := by
          ext ⟨x, y⟩
          simp only [Set.mem_union, mem_rect, VPiece.cells]
          omega
        have hkids : evCells sE ∪ evCells sW = childCells cs := by
          rw [hkidsE, hkidsW, Set.union_comm]
          exact hkidsAll
        rw [chainCells_append, hlE.cells, hlW.cells, treeCells_node,
          ← childCells_eq_forestCells, ← hkids, ← hrects]
        exact Set.union_union_union_comm _ _ _ _

-- ============================================================
-- §10 The corner chain, and the main lemma
-- ============================================================

private lemma exists_of_mem_piecesList {s : VPiece} :
    ∀ {cs : List PieceTree}, s ∈ PieceTree.piecesList cs →
      ∃ c ∈ cs, s ∈ c.pieces := by
  intro cs
  induction cs with
  | nil => intro h; simp at h
  | cons c t ih =>
    intro h
    rw [PieceTree.piecesList_cons, List.mem_append] at h
    rcases h with h | h
    · exact ⟨c, by simp, h⟩
    · obtain ⟨d, hd, hs⟩ := ih h
      exact ⟨d, by simp [hd], hs⟩

/-- Well-formedness spreads to every piece of the tree. -/
private lemma wf_pieces {P : Set Cell} :
    ∀ n : ℕ, ∀ T : PieceTree, T.pieces.length ≤ n → T.WF P →
      ∀ s ∈ T.pieces, s.IsPieceOf P := by
  intro n
  induction n with
  | zero =>
    intro T hlen _
    have h1 := PieceTree.root_mem_pieces T
    have h3 : 0 < T.pieces.length :=
      List.length_pos_of_ne_nil (List.ne_nil_of_mem h1)
    omega
  | succ n IHn =>
    rintro ⟨R, cs⟩ hlen hwf s hs
    obtain ⟨hR, hwfc⟩ := hwf
    rw [PieceTree.pieces_node] at hs
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact hR
    · obtain ⟨c, hc, hsc⟩ := exists_of_mem_piecesList hs'
      refine IHn c ?_ (PieceTree.wfChildren_forall hwfc c hc).2 s hsc
      have := PieceTree.pieces_length_lt hc R
      simp only [PieceTree.pieces_node] at hlen this
      omega

/-- **Corner-chain existence** (formerly the last `sorry` of
    `FatPolyomino.lean`).  A nonempty finite connected 12-aligned polyomino
    admits a corner chain: vertical decomposition, spanning tree of the
    door graph, and the clockwise Euler tour of its subdivided pieces. -/
theorem exists_cornerChain (P : Set Cell) (hfin : P.Finite) (hne : P.Nonempty)
    (hconn : CellConnected P) (hal : VertexAligned 12 P) :
    ∃ l : List ChainLink, IsCornerChain l P := by
  obtain ⟨T, hT⟩ := exists_spanning_pieceTree P hfin hne hconn
  have hpieces : ∀ s ∈ T.pieces, s.IsPieceOf P :=
    wf_pieces T.pieces.length T le_rfl hT.wf
  obtain ⟨-, -, l, hlne, hlchain, hldisj, hlnex, hlcells⟩ :=
    exists_tour P hfin hal T.pieces.length T le_rfl hT.wf hpieces hT.nodup
  have hcov : treeCells T = P := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset fun s hs => (hpieces s hs).subset
    · intro p hp
      obtain ⟨s, hsP, hps⟩ := exists_vPiece_mem P hfin hp
      exact Set.mem_biUnion (hT.complete s hsP) hps
  exact ⟨l, hlne, hlchain, hldisj, hlcells.trans hcov, hlnex⟩

/-- **Main lemma (12-aligned polyominoes).**  A finite connected polyomino
    all of whose vertices lie on the pitch-12 grid is L-tileable if its
    area is divisible by 3.  (Moved here from `FatPolyomino.lean`, whose
    corner-chain machinery supplies `IsCornerChain.tileable`.) -/
theorem LTileable_of_vertexAligned (P : Set Cell) (hfin : P.Finite)
    (hconn : CellConnected P) (hal : VertexAligned 12 P)
    (harea : 3 ∣ P.ncard) : LTileable P := by
  rcases P.eq_empty_or_nonempty with rfl | hne
  · exact Tileable.empty _
  · obtain ⟨l, hl⟩ := exists_cornerChain P hfin hne hconn hal
    exact hl.tileable harea
