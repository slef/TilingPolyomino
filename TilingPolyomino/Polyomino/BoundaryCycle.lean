import TilingPolyomino.Polyomino.NextVtx
import TilingPolyomino.Polyomino.Boundary
import TilingPolyomino.Polyomino.RayParity
import Mathlib.Data.Int.LeastGreatest

/-!
# The boundary of a fat polyomino is a single cycle

For a family `S` of vertices closed under the boundary successor and
predecessor, `curveV P S`/`curveH P S` are the boundary segments of the
edges emanating from `S`.  The **single-cycle theorem**
(`vertex_mem_of_closed`): if `P` is finite, connected, simply connected
(`Pᶜ` connected) and 16-fat, a nonempty closed family contains *every*
vertex of `P` — by the ray-crossing parity argument: the parity of
crossings of `curveV` is constant on `P` and on `Pᶜ` but differs across a
curve segment, so no boundary segment can lie off the curve
(`curve_covers`).
-/

open Set

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

