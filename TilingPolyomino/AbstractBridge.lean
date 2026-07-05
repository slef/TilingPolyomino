import TilingPolyomino

/-!
# Bridge to the abstract layer

This file proves the theorems stated in `Abstract.lean`.  The definitions
below are *verbatim copies* of the elementary definitions in `Abstract.lean`;
each headline theorem there is proved by directly delegating (`:=`) to the
corresponding theorem here, which Lean accepts because the two copies are
definitionally equal.  Any drift between the copies would therefore fail to
compile — `Abstract.lean` remains the single reader-facing contract, and this
file carries the proof machinery connecting it to the general layer.
-/

namespace AbstractBridge

/-! ## Copies of the elementary definitions (see `Abstract.lean`) -/

def IsLTromino (T : Set (ℤ × ℤ)) : Prop :=
  ∃ x y : ℤ,
    T = {(x, y), (x, y + 1), (x + 1, y)} ∨
    T = {(x, y), (x + 1, y), (x + 1, y + 1)} ∨
    T = {(x, y + 1), (x + 1, y), (x + 1, y + 1)} ∨
    T = {(x, y), (x, y + 1), (x + 1, y + 1)}

def LTileable (R : Set (ℤ × ℤ)) : Prop :=
  ∃ (k : ℕ) (t : Fin k → Set (ℤ × ℤ)),
    (∀ i, IsLTromino (t i)) ∧
    (∀ i j, i ≠ j → Disjoint (t i) (t j)) ∧
    (⋃ i, t i) = R

def rectangle (n m : ℤ) : Set (ℤ × ℤ) :=
  {p | 0 ≤ p.1 ∧ p.1 < n ∧ 0 ≤ p.2 ∧ p.2 < m}

def IsCornerDefect (n m : ℤ) (p : ℤ × ℤ) (D : Set (ℤ × ℤ)) : Prop :=
  (p = (0, 0) ∧
    (D = {(0, 0)} ∨ D = {(0, 0), (1, 0)} ∨ D = {(0, 0), (0, 1)})) ∨
  (p = (n - 1, 0) ∧
    (D = {(n - 1, 0)} ∨ D = {(n - 1, 0), (n - 2, 0)} ∨
     D = {(n - 1, 0), (n - 1, 1)})) ∨
  (p = (0, m - 1) ∧
    (D = {(0, m - 1)} ∨ D = {(0, m - 1), (1, m - 1)} ∨
     D = {(0, m - 1), (0, m - 2)})) ∨
  (p = (n - 1, m - 1) ∧
    (D = {(n - 1, m - 1)} ∨ D = {(n - 1, m - 1), (n - 2, m - 1)} ∨
     D = {(n - 1, m - 1), (n - 1, m - 2)}))

/-! ## Elementary tilings ↔ general-layer tilings -/

private lemma placedTile_cells_isLTromino (pt : PlacedTile Unit) :
    IsLTromino (pt.cells LProtoset) := by
  obtain ⟨_u, ⟨tx, ty⟩, r⟩ := pt
  fin_cases r
  · refine ⟨tx, ty, Or.inl ?_⟩
    ext ⟨a, b⟩
    simp only [PlacedTile.cells, LProtoset, LPrototile, LShape_cells, mem_translate, mem_rotate,
      inverseRot, rotateCell_0, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  · refine ⟨tx - 1, ty, Or.inr (Or.inl ?_)⟩
    ext ⟨a, b⟩
    simp only [PlacedTile.cells, LProtoset, LPrototile, LShape_cells, mem_translate, mem_rotate,
      inverseRot, rotateCell_3, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  · refine ⟨tx - 1, ty - 1, Or.inr (Or.inr (Or.inl ?_))⟩
    ext ⟨a, b⟩
    simp only [PlacedTile.cells, LProtoset, LPrototile, LShape_cells, mem_translate, mem_rotate,
      inverseRot, rotateCell_2, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  · refine ⟨tx, ty - 1, Or.inr (Or.inr (Or.inr ?_))⟩
    ext ⟨a, b⟩
    simp only [PlacedTile.cells, LProtoset, LPrototile, LShape_cells, mem_translate, mem_rotate,
      inverseRot, rotateCell_1, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega

private lemma exists_placedTile_of_isLTromino {T : Set (ℤ × ℤ)} (h : IsLTromino T) :
    ∃ pt : PlacedTile Unit, pt.cells LProtoset = T := by
  obtain ⟨x, y, h | h | h | h⟩ := h <;> subst h
  · refine ⟨⟨(), (x, y), 0⟩, ?_⟩
    ext ⟨a, b⟩
    simp only [PlacedTile.cells, LProtoset, LPrototile, LShape_cells, mem_translate, mem_rotate,
      inverseRot, rotateCell_0, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  · refine ⟨⟨(), (x + 1, y), 1⟩, ?_⟩
    ext ⟨a, b⟩
    simp only [PlacedTile.cells, LProtoset, LPrototile, LShape_cells, mem_translate, mem_rotate,
      inverseRot, rotateCell_3, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  · refine ⟨⟨(), (x + 1, y + 1), 2⟩, ?_⟩
    ext ⟨a, b⟩
    simp only [PlacedTile.cells, LProtoset, LPrototile, LShape_cells, mem_translate, mem_rotate,
      inverseRot, rotateCell_2, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  · refine ⟨⟨(), (x, y + 1), 3⟩, ?_⟩
    ext ⟨a, b⟩
    simp only [PlacedTile.cells, LProtoset, LPrototile, LShape_cells, mem_translate, mem_rotate,
      inverseRot, rotateCell_1, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega

/-- The elementary notion of L-tileability coincides with the general-layer
    notion. -/
theorem tileable_iff (R : Set (ℤ × ℤ)) : LTileable R ↔ _root_.LTileable R := by
  constructor
  · rintro ⟨k, t, htrom, hdisj, hcover⟩
    choose pt hpt using fun i => exists_placedTile_of_isLTromino (htrom i)
    refine ⟨Fin k, inferInstance, ⟨pt⟩, ?_, ?_⟩
    · intro i j hij
      change Disjoint ((pt i).cells LProtoset) ((pt j).cells LProtoset)
      rw [hpt i, hpt j]
      exact hdisj i j hij
    · change (⋃ i, (pt i).cells LProtoset) = R
      rw [← hcover]
      exact Set.iUnion_congr hpt
  · rintro ⟨ιₜ, hft, t, hv⟩
    haveI := hft
    let e := Fintype.equivFin ιₜ
    refine ⟨Fintype.card ιₜ, fun i => t.cellsAt_finset (e.symm i),
      fun i => placedTile_cells_isLTromino (t.tiles (e.symm i)), ?_, ?_⟩
    · intro i j hij
      exact hv.disjoint _ _ fun h => hij (e.symm.injective h)
    · have hcov : (⋃ j, t.cellsAt_finset j) = R := hv.covers
      ext p
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        rw [← hcov]
        exact Set.mem_iUnion.mpr ⟨e.symm i, hi⟩
      · intro hp
        rw [← hcov] at hp
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
        exact ⟨e j, by simpa using hj⟩

private lemma rectangle_eq_rect (n m : ℤ) : rectangle n m = rect 0 0 n m := rfl

/-! ## Rotation by 180° -/

private lemma LTileable_rot180 {R : Set Cell} (n m : ℤ) (h : _root_.LTileable R) :
    _root_.LTileable (reflectYRegion m (reflectXRegion n R)) :=
  LTileable_reflectY m (LTileable_reflectX n h)

private lemma rot180_rot180 (n m : ℤ) (R : Set Cell) :
    reflectYRegion m (reflectXRegion n (reflectYRegion m (reflectXRegion n R))) = R := by
  ext ⟨x, y⟩
  simp only [mem_reflectYRegion, mem_reflectXRegion]
  rw [show n - 1 - (n - 1 - x) = x by ring, show m - 1 - (m - 1 - y) = y by ring]

private lemma LTileable_rot180_iff (n m : ℤ) (R : Set Cell) :
    _root_.LTileable (reflectYRegion m (reflectXRegion n R)) ↔ _root_.LTileable R := by
  refine ⟨fun h => ?_, LTileable_rot180 n m⟩
  rw [← rot180_rot180 n m R]
  exact LTileable_rot180 n m h

/-- Rotating by 180° carries the top-right dog-ear to the bottom-left one. -/
private lemma rot180_dogEar (n m : ℤ) :
    reflectYRegion m (reflectXRegion n (rect 0 0 n m \ {(n - 1, m - 1)})) =
      rect 0 0 n m \ {(0, 0)} := by
  ext ⟨x, y⟩
  simp only [mem_reflectYRegion, mem_reflectXRegion, Set.mem_diff, mem_rect,
    Set.mem_singleton_iff, Prod.mk.injEq]
  omega

/-- Rotating by 180° carries the top-right corner domino to the bottom-left one. -/
private lemma rot180_domino (n m : ℤ) :
    reflectYRegion m (reflectXRegion n
      (rect 0 0 n m \ ({(n - 1, m - 1)} ∪ {(n - 2, m - 1)}))) =
      rect 0 0 n m \ {(0, 0), (1, 0)} := by
  ext ⟨x, y⟩
  simp only [mem_reflectYRegion, mem_reflectXRegion, Set.mem_diff, mem_rect,
    Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff, Prod.mk.injEq]
  omega

/-! ## Cardinality of the corner-domino region -/

private lemma rect_ncard_nat (n m : ℕ) : (rect 0 0 (n : ℤ) m).ncard = n * m := by
  rw [rect_ncard]
  simp

private lemma domino_ncard (n m : ℕ) (hn : n ≥ 3) (hm : m ≥ 3) :
    (rect 0 0 (n : ℤ) m \
      ({((n : ℤ) - 1, (m : ℤ) - 1)} ∪ {((n : ℤ) - 2, (m : ℤ) - 1)})).ncard = n * m - 2 := by
  have hne : ((n : ℤ) - 1, (m : ℤ) - 1) ≠ ((n : ℤ) - 2, (m : ℤ) - 1) := by
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro h
    omega
  have hsub : ({((n : ℤ) - 1, (m : ℤ) - 1)} ∪ {((n : ℤ) - 2, (m : ℤ) - 1)} : Set Cell) ⊆
      rect 0 0 (n : ℤ) m := by
    intro p hp
    simp only [Set.mem_union, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> (simp [mem_rect]; omega)
  rw [Set.ncard_diff hsub ((Set.finite_singleton _).union (Set.finite_singleton _)),
    rect_ncard_nat, Set.singleton_union, Set.ncard_pair hne]

/-- The corner-domino region is a degenerate `rectMinusTwoCorners` (same corner
    twice), which gives the area-divisibility necessity for free. -/
private lemma rectMinusTwoCorners_TRTR (n m : ℤ) :
    rectMinusTwoCorners n m .TR .TR .horiz .horiz =
      rect 0 0 n m \ ({(n - 1, m - 1)} ∪ {(n - 2, m - 1)}) := by
  ext ⟨x, y⟩
  simp only [rectMinusTwoCorners, Corner.cells, Set.mem_diff, mem_rect, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  tauto

/-! ## The two-corner defect vocabulary -/

private def cornerPt (c : Corner) (n m : ℤ) : ℤ × ℤ :=
  match c with
  | .BL => (0, 0)
  | .BR => (n - 1, 0)
  | .TL => (0, m - 1)
  | .TR => (n - 1, m - 1)

private lemma exists_corner_of_isCornerDefect {n m : ℤ} {p : ℤ × ℤ} {D : Set (ℤ × ℤ)}
    (h : IsCornerDefect n m p D) :
    ∃ (c : Corner) (d : DefectType), p = cornerPt c n m ∧ D = c.cells d n m := by
  rcases h with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
    ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩
  exacts [⟨.BL, .single, rfl, rfl⟩, ⟨.BL, .horiz, rfl, rfl⟩, ⟨.BL, .vert, rfl, rfl⟩,
    ⟨.BR, .single, rfl, rfl⟩, ⟨.BR, .horiz, rfl, rfl⟩, ⟨.BR, .vert, rfl, rfl⟩,
    ⟨.TL, .single, rfl, rfl⟩, ⟨.TL, .horiz, rfl, rfl⟩, ⟨.TL, .vert, rfl, rfl⟩,
    ⟨.TR, .single, rfl, rfl⟩, ⟨.TR, .horiz, rfl, rfl⟩, ⟨.TR, .vert, rfl, rfl⟩]

/-! ## Proofs of the headline theorems -/

theorem LTileable_rectangle_iff (n m : ℕ) :
    LTileable (rectangle n m) ↔
      n = 0 ∨ m = 0 ∨
        (3 ∣ n * m ∧ n ≥ 2 ∧ m ≥ 2 ∧ ¬(n = 3 ∧ Odd m) ∧ ¬(Odd n ∧ m = 3)) := by
  have hdvd : 3 ∣ n * m ↔ n * m % 3 = 0 := by omega
  rw [tileable_iff, rectangle_eq_rect]
  exact (LTileable_rect_iff n m).trans (by simp only [RectTileableConditions, hdvd])

theorem LTileable_dogEaredRectangle_iff (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2) :
    LTileable (rectangle n m \ {(0, 0)}) ↔ 3 ∣ (n * m - 1) := by
  rw [tileable_iff, rectangle_eq_rect, ← rot180_dogEar (n : ℤ) m, LTileable_rot180_iff,
    LTileable_rectMinusCorner_iff n m hn hm]
  omega

theorem LTileable_cornerDomino_iff (n m : ℕ) (hn : n ≥ 3) (hm : m ≥ 3) :
    LTileable (rectangle n m \ {(0, 0), (1, 0)}) ↔ 3 ∣ (n * m - 2) := by
  have h9 : 9 ≤ n * m := Nat.mul_le_mul hn hm
  rw [tileable_iff, rectangle_eq_rect, ← rot180_domino (n : ℤ) m, LTileable_rot180_iff]
  constructor
  · intro h
    have harea := LTileable_rectMinusTwoCorners_area (n : ℤ) m .TR .TR .horiz .horiz
      (by rw [rectMinusTwoCorners_TRTR]; exact h)
    rw [rectMinusTwoCorners_TRTR, domino_ncard n m hn hm] at harea
    exact harea
  · intro h
    exact LTileable_rectMinus2Corner n m hn hm (by omega)

theorem LTileable_twoCornerDefects_iff (n m : ℤ) (hn : n ≥ 6) (hm : m ≥ 6)
    {p₁ p₂ : ℤ × ℤ} {D₁ D₂ : Set (ℤ × ℤ)}
    (h₁ : IsCornerDefect n m p₁ D₁) (h₂ : IsCornerDefect n m p₂ D₂)
    (hp : p₁ ≠ p₂) :
    LTileable (rectangle n m \ (D₁ ∪ D₂)) ↔
      3 ∣ (rectangle n m \ (D₁ ∪ D₂)).ncard := by
  rw [tileable_iff]
  obtain ⟨c₁, d₁, hp₁, rfl⟩ := exists_corner_of_isCornerDefect h₁
  obtain ⟨c₂, d₂, hp₂, rfl⟩ := exists_corner_of_isCornerDefect h₂
  have hc : c₁ ≠ c₂ := fun hcc => hp (by rw [hp₁, hp₂, hcc])
  exact LTileable_rectMinusTwoCorners_iff n m c₁ c₂ d₁ d₂ hn hm hc

end AbstractBridge
