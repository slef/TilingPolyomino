import TilingPolyomino.Corridor.EdgePiece
import Mathlib.Data.Int.LeastGreatest

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

