import TilingPolyomino.Corridor.Disjoint
import TilingPolyomino.Corridor.Cover

/-!
# The corridor carries a corner chain

`exists_corridorChain` — the assembly of the corridor decomposition:
iterate the boundary successor from any vertex; injectivity makes the orbit
periodic, the single-cycle theorem makes it exhaust the vertices, and the
corridor rectangles of the orbit's edges — pairwise disjoint, covering the
corridor, meeting at pushing corners — form the corner chain.
-/

open Set

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
