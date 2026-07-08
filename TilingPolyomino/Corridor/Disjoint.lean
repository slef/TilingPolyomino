import TilingPolyomino.Corridor.EdgePiece

/-!
# Corridor rectangles of distinct edges are disjoint

`edgePiece_disjoint`: the corridor rectangles of two distinct boundary
edges of a 16-fat polyomino are disjoint.  A common cell would put the two
edges within the 8-thick band of each other; the ten `clash_*` lemmas rule
out every configuration of the two edge directions, using vertex isolation
(`sep16`) and the window bounds of the shared cell.
-/

open Set

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
