import TilingPolyomino.Polyomino.Decomposition.Vertical

/-!
# Spanning trees of the door graph

`PieceTree`: a rooted tree of decomposition pieces, each child hanging off
a door of its parent.  A finite connected polyomino carries a spanning tree
of its vertical decomposition (`exists_spanning_pieceTree`): pick any root,
split the remaining pieces into door-components, attach each component at a
piece adjacent to the root, and recurse.
-/

open Set

-- ============================================================
-- §7 Spanning trees of the door graph
-- ============================================================

/-- A rooted tree of decomposition pieces — the combinatorial object
    produced by choosing a spanning tree of the door graph and a root.
    The Euler tour of the corner-chain construction will recurse on it. -/
inductive PieceTree where
  | node (piece : VPiece) (children : List PieceTree)

namespace PieceTree

/-- The root piece. -/
def root : PieceTree → VPiece
  | node s _ => s

@[simp] lemma root_node (s : VPiece) (children : List PieceTree) :
    (node s children).root = s := rfl

mutual
  /-- All pieces of the tree, in preorder. -/
  def pieces : PieceTree → List VPiece
    | node s children => s :: piecesList children

  /-- All pieces of a forest, in preorder. -/
  def piecesList : List PieceTree → List VPiece
    | [] => []
    | c :: cs => c.pieces ++ piecesList cs
end

@[simp] lemma pieces_node (s : VPiece) (children : List PieceTree) :
    (node s children).pieces = s :: piecesList children := rfl

@[simp] lemma piecesList_nil : piecesList [] = [] := rfl

@[simp] lemma piecesList_cons (c : PieceTree) (cs : List PieceTree) :
    piecesList (c :: cs) = c.pieces ++ piecesList cs := rfl

mutual
  /-- Well-formedness over `P`: every node is a piece of the decomposition
      of `P`, and each child's root shares a door with its parent. -/
  def WF (P : Set Cell) : PieceTree → Prop
    | node s children => s.IsPieceOf P ∧ WFChildren P s children

  /-- The children of a node with piece `parent` are well-formed and hang
      off doors of `parent`. -/
  def WFChildren (P : Set Cell) (parent : VPiece) : List PieceTree → Prop
    | [] => True
    | c :: cs => parent.Adj c.root ∧ c.WF P ∧ WFChildren P parent cs
end

@[simp] lemma wf_node {P : Set Cell} (s : VPiece) (children : List PieceTree) :
    (node s children).WF P ↔ s.IsPieceOf P ∧ WFChildren P s children :=
  Iff.rfl

@[simp] lemma wfChildren_nil {P : Set Cell} (parent : VPiece) :
    WFChildren P parent [] := trivial

@[simp] lemma wfChildren_cons {P : Set Cell} (parent : VPiece)
    (c : PieceTree) (cs : List PieceTree) :
    WFChildren P parent (c :: cs) ↔
      parent.Adj c.root ∧ c.WF P ∧ WFChildren P parent cs :=
  Iff.rfl

/-- `T` is a **spanning tree** of the vertical decomposition of `P`: it is
    well-formed and its nodes are exactly the pieces, each occurring once. -/
structure IsSpanningTree (T : PieceTree) (P : Set Cell) : Prop where
  wf : T.WF P
  nodup : T.pieces.Nodup
  complete : ∀ s : VPiece, s.IsPieceOf P → s ∈ T.pieces

end PieceTree

/-- Reachability inside a set `S` of pieces, moving only through doors. -/
private def ReachIn (S : Set VPiece) : VPiece → VPiece → Prop :=
  Relation.ReflTransGen fun u v => u ∈ S ∧ v ∈ S ∧ u.Adj v

private lemma reachIn_mem {S : Set VPiece} {u v : VPiece} (hu : u ∈ S)
    (h : ReachIn S u v) : v ∈ S := by
  induction h with
  | refl => exact hu
  | tail _ hstep _ => exact hstep.2.1

private lemma reachIn_symm {S : Set VPiece} {u v : VPiece}
    (h : ReachIn S u v) : ReachIn S v u := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.head ⟨hstep.2.1, hstep.1, hstep.2.2.symm⟩ ih

/-- A door path in `S` starting at `u` is in fact a path *within* the
    door-component of `u` in `S`. -/
private lemma reachIn_component {S : Set VPiece} {u b : VPiece}
    (h : ReachIn S u b) :
    ReachIn {v | v ∈ S ∧ ReachIn S u v} u b := by
  induction h with
  | refl => exact .refl
  | @tail b' c hpath hstep ih =>
    exact ih.tail ⟨⟨hstep.1, hpath⟩, ⟨hstep.2.1, hpath.tail hstep⟩, hstep.2.2⟩

/-- Walking to `r` from elsewhere, one can stop just before `r`: some piece
    avoiding `r` throughout is reachable and door-adjacent to `r`. -/
private lemma exists_attach {S : Set VPiece} {u r : VPiece}
    (h : ReachIn S u r) :
    u ≠ r → ∃ w, ReachIn (S \ {r}) u w ∧ w.Adj r := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun h => absurd rfl h
  | @head a c hstep hrest ih =>
    intro hne
    by_cases hcr : c = r
    · subst hcr
      exact ⟨a, .refl, hstep.2.2⟩
    · obtain ⟨w, hw1, hw2⟩ := ih hcr
      exact ⟨w, Relation.ReflTransGen.head
        ⟨⟨hstep.1, by simpa using hne⟩, ⟨hstep.2.1, by simpa using hcr⟩,
          hstep.2.2⟩ hw1, hw2⟩

/-- Children construction: split a set `U` of pieces — closed under
    door-reachability in `S'` and with every piece linked to `r` through a
    door — into components, and build one subtree per component, each
    hanging off a door of `r`. -/
private theorem exists_children_aux (P : Set Cell) (r : VPiece)
    (S' : Set VPiece) (hS'fin : S'.Finite)
    (IH : ∀ C : Set VPiece, C ⊆ S' →
      (∀ a ∈ C, ∀ b ∈ C, ReachIn C a b) →
      ∀ w ∈ C, ∃ T : PieceTree, T.root = w ∧ T.WF P ∧ T.pieces.Nodup ∧
        ∀ s : VPiece, s ∈ T.pieces ↔ s ∈ C) :
    ∀ m : ℕ, ∀ U : Set VPiece, U ⊆ S' → U.ncard ≤ m →
      (∀ u ∈ U, ∀ v, ReachIn S' u v → v ∈ U) →
      (∀ u ∈ U, ∃ w, ReachIn S' u w ∧ w.Adj r) →
      ∃ L : List PieceTree, PieceTree.WFChildren P r L ∧
        (PieceTree.piecesList L).Nodup ∧
        ∀ s : VPiece, s ∈ PieceTree.piecesList L ↔ s ∈ U := by
  intro m
  induction m with
  | zero =>
    intro U hUsub hUcard _ _
    have hUfin : U.Finite := hS'fin.subset hUsub
    obtain rfl : U = ∅ := (Set.ncard_eq_zero hUfin).mp (by omega)
    exact ⟨[], PieceTree.wfChildren_nil r, List.nodup_nil, by simp⟩
  | succ m IHm =>
    intro U hUsub hUcard hUclosed hUattach
    rcases U.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · exact ⟨[], PieceTree.wfChildren_nil r, List.nodup_nil, by simp⟩
    have hUfin : U.Finite := hS'fin.subset hUsub
    have huS' : u ∈ S' := hUsub hu
    -- the component of `u`, and its attach point next to `r`
    set C := {v | v ∈ S' ∧ ReachIn S' u v} with hCdef
    have huC : u ∈ C := ⟨huS', .refl⟩
    have hCsub : C ⊆ S' := fun v hv => hv.1
    have hCU : C ⊆ U := fun v hv => hUclosed u hu v hv.2
    have hCconn : ∀ a ∈ C, ∀ b ∈ C, ReachIn C a b := fun a ha b hb =>
      (reachIn_symm (reachIn_component ha.2)).trans (reachIn_component hb.2)
    obtain ⟨w, hw_reach, hw_adj⟩ := hUattach u hu
    have hwC : w ∈ C := ⟨reachIn_mem huS' hw_reach, hw_reach⟩
    obtain ⟨T, hTroot, hTwf, hTnodup, hTmem⟩ := IH C hCsub hCconn w hwC
    -- recurse on what is left of `U`
    have hU'sub : U \ C ⊆ S' := fun v hv => hUsub hv.1
    have hU'card : (U \ C).ncard ≤ m := by
      have h1 : U \ C ⊆ U \ {u} :=
        Set.diff_subset_diff_right (Set.singleton_subset_iff.mpr huC)
      have h2 : (U \ C).ncard ≤ (U \ {u}).ncard :=
        Set.ncard_le_ncard h1 hUfin.diff
      have h3 : (U \ {u}).ncard = U.ncard - 1 :=
        Set.ncard_diff_singleton_of_mem hu
      have h4 : 0 < U.ncard := (Set.ncard_pos hUfin).mpr ⟨u, hu⟩
      omega
    have hU'closed : ∀ a ∈ U \ C, ∀ v, ReachIn S' a v → v ∈ U \ C := by
      rintro a ⟨haU, haC⟩ v hav
      refine ⟨hUclosed a haU v hav, fun hvC => haC ?_⟩
      exact ⟨hUsub haU, hvC.2.trans (reachIn_symm hav)⟩
    have hU'attach : ∀ a ∈ U \ C, ∃ w', ReachIn S' a w' ∧ w'.Adj r :=
      fun a ha => hUattach a ha.1
    obtain ⟨L', hL'wf, hL'nodup, hL'mem⟩ :=
      IHm (U \ C) hU'sub hU'card hU'closed hU'attach
    refine ⟨T :: L', ⟨by rw [hTroot]; exact hw_adj.symm, hTwf, hL'wf⟩, ?_, ?_⟩
    · simp only [PieceTree.piecesList_cons]
      exact hTnodup.append hL'nodup fun s hsT hsL' =>
        ((hL'mem s).mp hsL').2 ((hTmem s).mp hsT)
    · intro s
      simp only [PieceTree.piecesList_cons, List.mem_append, hTmem, hL'mem]
      constructor
      · rintro (h | h)
        · exact hCU h
        · exact h.1
      · intro hs
        by_cases hsC : s ∈ C
        · exact Or.inl hsC
        · exact Or.inr ⟨hs, hsC⟩

/-- Any internally door-connected finite set of decomposition pieces
    carries a spanning tree with prescribed root: remove the root, split
    the rest into components, attach each component at a piece adjacent to
    the root. -/
private theorem exists_rooted_tree_aux (P : Set Cell) :
    ∀ n : ℕ, ∀ S : Set VPiece, S.Finite → S.ncard ≤ n →
      (∀ s ∈ S, s.IsPieceOf P) →
      (∀ a ∈ S, ∀ b ∈ S, ReachIn S a b) →
      ∀ r ∈ S,
      ∃ T : PieceTree, T.root = r ∧ T.WF P ∧ T.pieces.Nodup ∧
        ∀ s : VPiece, s ∈ T.pieces ↔ s ∈ S := by
  intro n
  induction n with
  | zero =>
    intro S hSfin hScard _ _ r hr
    obtain rfl : S = ∅ := (Set.ncard_eq_zero hSfin).mp (by omega)
    simp at hr
  | succ n IHn =>
    intro S hSfin hScard hSpieces hSconn r hr
    have hS'fin : (S \ {r}).Finite := hSfin.diff
    have hS'card : (S \ {r}).ncard ≤ n := by
      have h3 : (S \ {r}).ncard = S.ncard - 1 :=
        Set.ncard_diff_singleton_of_mem hr
      have h4 : 0 < S.ncard := (Set.ncard_pos hSfin).mpr ⟨r, hr⟩
      omega
    have IH : ∀ C : Set VPiece, C ⊆ S \ {r} →
        (∀ a ∈ C, ∀ b ∈ C, ReachIn C a b) →
        ∀ w ∈ C, ∃ T : PieceTree, T.root = w ∧ T.WF P ∧ T.pieces.Nodup ∧
          ∀ s : VPiece, s ∈ T.pieces ↔ s ∈ C := by
      intro C hCsub hCconn w hw
      refine IHn C (hS'fin.subset hCsub) ?_
        (fun s hs => hSpieces s (hCsub hs).1) hCconn w hw
      calc C.ncard ≤ (S \ {r}).ncard := Set.ncard_le_ncard hCsub hS'fin
        _ ≤ n := hS'card
    have hclosed : ∀ u ∈ S \ {r}, ∀ v, ReachIn (S \ {r}) u v → v ∈ S \ {r} :=
      fun u hu v hv => reachIn_mem hu hv
    have hattach : ∀ u ∈ S \ {r}, ∃ w, ReachIn (S \ {r}) u w ∧ w.Adj r := by
      rintro u ⟨huS, hur⟩
      exact exists_attach (hSconn u huS r hr) (by simpa using hur)
    obtain ⟨L, hLwf, hLnodup, hLmem⟩ :=
      exists_children_aux P r (S \ {r}) hS'fin IH
        (S \ {r}).ncard (S \ {r}) subset_rfl le_rfl hclosed hattach
    refine ⟨.node r L, rfl, ⟨hSpieces r hr, hLwf⟩, ?_, ?_⟩
    · rw [PieceTree.pieces_node, List.nodup_cons]
      exact ⟨fun h => ((hLmem r).mp h).2 rfl, hLnodup⟩
    · intro s
      rw [PieceTree.pieces_node, List.mem_cons, hLmem s]
      constructor
      · rintro (rfl | h)
        · exact hr
        · exact h.1
      · intro hs
        by_cases hsr : s = r
        · exact Or.inl hsr
        · exact Or.inr ⟨hs, by simpa using hsr⟩

/-- **Spanning-tree existence.**  The door graph of a nonempty finite
    connected polyomino carries a spanning tree: pick any root, split the
    remaining pieces into door-components, attach each component at a piece
    adjacent to the root, and recurse. -/
theorem exists_spanning_pieceTree (P : Set Cell) (hfin : P.Finite)
    (hne : P.Nonempty) (hconn : CellConnected P) :
    ∃ T : PieceTree, T.IsSpanningTree P := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨r, hr, -⟩ := exists_vPiece_mem P hfin hp
  have hconn' : ∀ a ∈ vDecomp P, ∀ b ∈ vDecomp P, ReachIn (vDecomp P) a b :=
    fun a ha b hb => vPiece_reachable P hfin hconn ha hb
  obtain ⟨T, -, hwf, hnodup, hmem⟩ :=
    exists_rooted_tree_aux P (vDecomp P).ncard (vDecomp P)
      (vDecomp_finite P hfin) le_rfl (fun _ hs => hs) hconn' r hr
  exact ⟨T, hwf, hnodup, fun s hs => (hmem s).mpr hs⟩
