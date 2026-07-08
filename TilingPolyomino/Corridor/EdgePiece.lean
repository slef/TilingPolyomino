import TilingPolyomino.Corridor.OffsetCore
import TilingPolyomino.Polyomino.BoundaryCycle
import TilingPolyomino.CornerChain.Defs

/-!
# The corridor rectangle of a boundary edge

Given three consecutive vertices `p → u → w → z` of a 16-fat polyomino, the
edge `u → w` receives the corridor rectangle `edgePiece p u w z`, bounded
transversally by the boundary and the snapped offset line (`snapE/W/N/S`,
distance 6–8) and longitudinally by the forward cuts at `u` and `w`
(convex: at the offset corner; reflex: absorbing the corner block).  Both
sides are ≥ 6, so it is a `RectPiece`; its entry and exit corners
(`eEntry`, `eExit`) are distinct, consecutive rectangles meet at pushing
corners (`edgePiece_pushAdj`), and each rectangle lies in the corridor
(`edgePiece_subset_corridor`).
-/

open Set

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
