import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/- ## Basic Definitions -/

/- This file defines a general framework for polyomino tilings on the integer grid.
It is independent of any particular prototile (such as the L-tromino), and is
intended to be reusable for other tiling problems.

Main ingredients:

* `Cell`, `Region`
* `Prototile_finset`, `Protoset_finset`
* `PlacedTile_finset`
* `TileSet_finset` and `TileSet_finset.Valid_finset`
* Generic notions of `Tileable_finset`
* Rectangle regions and basic splitting lemmas
* Generic placement enumeration utilities
-/

/-- A cell on the integer grid -/
abbrev Cell := ℤ × ℤ

/-- A region is a finite set of cells -/
abbrev Region := Finset Cell

/- ## Prototile_finset and Protoset_finset -/

/- A prototile is the "shape" of a tile, represented as a list of cells with no
duplicates.  This design allows both:

* Computation: iterate over `p.cells` (the list)
* Proofs: use `(p : Finset Cell)` via coercion to access `Finset` lemmas

By convention, prototiles are normalized to have their anchor at the origin.
A protoset is an indexed family of prototiles - the allowed tile types.
-/

/-- A prototile is a polyomino shape (list of cells with no duplicates) -/
structure Prototile_finset where
  /-- The cells making up the tile -/
  cells : List Cell
  /-- No duplicate cells -/
  nodup : cells.Nodup := by decide
  deriving DecidableEq

/-- Coercion from `Prototile_finset` to `Finset Cell` -/
instance : Coe Prototile_finset (Finset Cell) where
  coe p := ⟨p.cells, p.nodup⟩

theorem Prototile_finset.coe_def (p : Prototile_finset) :
    (p : Finset Cell) = ⟨p.cells, p.nodup⟩ := rfl

theorem Prototile_finset.mem_coe (p : Prototile_finset) (c : Cell) :
    c ∈ (p : Finset Cell) ↔ c ∈ p.cells := by
  rw [Prototile_finset.coe_def]
  simp only [Finset.mem_mk, Multiset.mem_coe]

/-- Cardinality of a prototile -/
def Prototile_finset.card (p : Prototile_finset) : ℕ := p.cells.length

theorem Prototile_finset.card_eq (p : Prototile_finset) :
    p.card = (p : Finset Cell).card := by
  simp only [Prototile_finset.card, Finset.card_def]
  rfl

/-- A protoset is an indexed family of prototiles -/
structure Protoset_finset (ι : Type*) where
  /-- The tiles in the protoset -/
  tiles : ι → Prototile_finset

instance {ι : Type*} :
    CoeFun (Protoset_finset ι) (fun _ => ι → Prototile_finset) where
  coe := Protoset_finset.tiles

/- ## Rotations -/

/- We support 4 rotations (0°, 90°, 180°, 270° counterclockwise). -/

/-- Rotate a cell by 90° counterclockwise around the origin -/
def rotateCell90 (c : Cell) : Cell := (-c.2, c.1)

/-- Rotate a cell by a given number of 90° steps -/
def rotateCell (c : Cell) (r : Fin 4) : Cell :=
  match r with
  | 0 => c
  | 1 => rotateCell90 c
  | 2 => rotateCell90 (rotateCell90 c)
  | 3 => rotateCell90 (rotateCell90 (rotateCell90 c))

/-- Rotation by any amount is injective -/
theorem rotateCell_injective (r : Fin 4) :
    Function.Injective (rotateCell · r) := by
  intro ⟨x1, y1⟩ ⟨x2, y2⟩ h
  fin_cases r <;>
    simp only [rotateCell, rotateCell90, Prod.mk.injEq] at h <;>
    (ext <;> omega)

/-- Rotate all cells in a prototile (returns `Finset` for compatibility) -/
def rotateProto (p : Prototile_finset) (r : Fin 4) : Finset Cell :=
  (p : Finset Cell).image (rotateCell · r)

/-- Rotation preserves cardinality of a prototile -/
theorem rotateProto_card (p : Prototile_finset) (r : Fin 4) :
    (rotateProto p r).card = p.cells.length := by
  simp only [rotateProto]
  rw [Finset.card_image_of_injective _ (rotateCell_injective r)]
  rw [← p.card_eq]
  rfl

/- ## Placed Tiles -/

/-- A placed tile: prototile index + translation + rotation -/
structure PlacedTile_finset (ι : Type*) where
  /-- Index of the prototile in the protoset -/
  index : ι
  /-- Translation: where to place the tile -/
  translation : Cell
  /-- Rotation: 0, 1, 2, or 3 (multiples of 90°) -/
  rotation : Fin 4
  deriving DecidableEq, Repr

/-- Translate a cell by an offset -/
def translateCell (c : Cell) (offset : Cell) : Cell :=
  (c.1 + offset.1, c.2 + offset.2)

/-- Translation is injective -/
theorem translateCell_injective (offset : Cell) :
    Function.Injective (translateCell · offset) := by
  intro ⟨x1, y1⟩ ⟨x2, y2⟩ h
  simp only [translateCell, Prod.mk.injEq] at h
  ext <;> omega

/-- Translate a region by an offset -/
def translateRegion (r : Region) (offset : Cell) : Region :=
  r.image (translateCell · offset)

/-- Translation preserves cardinality of a region -/
theorem translateRegion_card (r : Region) (offset : Cell) :
    (translateRegion r offset).card = r.card := by
  simp only [translateRegion]
  exact Finset.card_image_of_injective _ (translateCell_injective offset)

/- ## Swap Transformation

Swapping x and y coordinates (reflection across the line `y = x`).
-/

/-- Swap x and y coordinates -/
def swapCell (c : Cell) : Cell := (c.2, c.1)

/-- Swap is an involution -/
theorem swapCell_involutive : Function.Involutive swapCell := fun _ => rfl

/-- Swap is injective -/
theorem swapCell_injective : Function.Injective swapCell :=
  swapCell_involutive.injective

/-- Apply swap to a region -/
def swapRegion (r : Region) : Region := r.image swapCell

/-- Get the cells covered by a placed tile -/
def PlacedTile_finset.cells {ι : Type*} (ps : Protoset_finset ι) (pt : PlacedTile_finset ι) :
    Finset Cell :=
  (rotateProto (ps pt.index) pt.rotation).image (translateCell · pt.translation)

/-- Translate a placed tile by an offset -/
def PlacedTile_finset.translate {ι : Type*} (pt : PlacedTile_finset ι) (offset : Cell) :
    PlacedTile_finset ι :=
  ⟨pt.index, (pt.translation.1 + offset.1, pt.translation.2 + offset.2),
    pt.rotation⟩

/-- Translation of a placed tile translates its cells -/
theorem PlacedTile_finset.translate_cells {ι : Type*}
    (ps : Protoset_finset ι) (pt : PlacedTile_finset ι) (offset : Cell) :
    (pt.translate offset).cells ps =
      translateRegion (pt.cells ps) offset := by
  simp only [PlacedTile_finset.cells, PlacedTile_finset.translate, translateRegion]
  ext c
  simp only [Finset.mem_image, translateCell]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact
      ⟨(b.1 + pt.translation.1, b.2 + pt.translation.2),
       ⟨b, hb, rfl⟩, by ring_nf⟩
  · rintro ⟨c', ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, by ring_nf⟩

/-- Placing a tile preserves the cardinality of the prototile -/
theorem PlacedTile_finset.cells_card {ι : Type*}
    (ps : Protoset_finset ι) (pt : PlacedTile_finset ι) :
    (pt.cells ps).card = (ps pt.index).cells.length := by
  simp only [PlacedTile_finset.cells]
  rw [Finset.card_image_of_injective _ (translateCell_injective pt.translation)]
  exact rotateProto_card (ps pt.index) pt.rotation

/- ## TileSet_finset: Indexed Family of Placed Tiles -/

/-- A `TileSet_finset` is an indexed family of placed tiles -/
structure TileSet_finset {ι : Type*} (ps : Protoset_finset ι) (ιₜ : Type*) where
  /-- The tiles in the family -/
  tiles : ιₜ → PlacedTile_finset ι

instance {ι : Type*} {ps : Protoset_finset ι} {ιₜ : Type*} :
    CoeFun (TileSet_finset ps ιₜ) (fun _ => ιₜ → PlacedTile_finset ι) where
  coe := TileSet_finset.tiles

namespace TileSet_finset

variable {ι : Type*} {ps : Protoset_finset ι} {ιₜ : Type*}

/-- The cells covered by a single tile in the tileset -/
def cellsAt_finset (t : TileSet_finset ps ιₜ) (i : ιₜ) : Finset Cell :=
  (t i).cells ps

/-- The union of all cells covered by the tileset (for finite index types) -/
def coveredCells_finset [Fintype ιₜ] (t : TileSet_finset ps ιₜ) : Finset Cell :=
  Finset.univ.biUnion t.cellsAt_finset

/-- Pairwise disjointness of tiles -/
def PairwiseDisjoint_finset [DecidableEq ιₜ] (t : TileSet_finset ps ιₜ) : Prop :=
  ∀ i j : ιₜ, i ≠ j → Disjoint (t.cellsAt_finset i) (t.cellsAt_finset j)

/-- If tiles are pairwise disjoint, the total area is the sum of individual areas -/
theorem card_coveredCells [Fintype ιₜ] [DecidableEq ιₜ]
    (t : TileSet_finset ps ιₜ) (hdisj : t.PairwiseDisjoint_finset) :
    t.coveredCells_finset.card = ∑ i : ιₜ, (t.cellsAt_finset i).card := by
  simp only [coveredCells_finset]
  rw [Finset.card_biUnion]
  intro i _ j _ hij
  exact hdisj i j hij

/-- A tileset is valid for a region if tiles are disjoint and exactly cover it -/
structure Valid_finset [Fintype ιₜ] [DecidableEq ιₜ]
    (t : TileSet_finset ps ιₜ) (region : Region) : Prop where
  /-- No two tiles overlap -/
  disjoint : t.PairwiseDisjoint_finset
  /-- The tiles exactly cover the region -/
  covers : t.coveredCells_finset = region

/-- Decidable pairwise disjointness for finite index types -/
instance instDecidablePairwiseDisjoint [Fintype ιₜ] [DecidableEq ιₜ]
    (t : TileSet_finset ps ιₜ) :
    Decidable t.PairwiseDisjoint_finset :=
  inferInstanceAs
    (Decidable (∀ i j : ιₜ, i ≠ j → Disjoint (t.cellsAt_finset i) (t.cellsAt_finset j)))

/-- Decidable validity for finite index types -/
instance instDecidableValid [Fintype ιₜ] [DecidableEq ιₜ]
    (t : TileSet_finset ps ιₜ) (region : Region) :
    Decidable (t.Valid_finset region) :=
  if hd : t.PairwiseDisjoint_finset then
    if hc : t.coveredCells_finset = region then
      isTrue ⟨hd, hc⟩
    else
      isFalse (fun h => hc h.covers)
  else
    isFalse (fun h => hd h.disjoint)

/-- Tiles at different indices are disjoint -/
theorem Valid_finset.disjoint_tiles [Fintype ιₜ] [DecidableEq ιₜ]
    {t : TileSet_finset ps ιₜ} {region : Region}
    (hv : t.Valid_finset region) (i j : ιₜ) (hij : i ≠ j) :
    Disjoint (t.cellsAt_finset i) (t.cellsAt_finset j) :=
  hv.disjoint i j hij

/-- Every tile's cells are contained in the region -/
theorem Valid_finset.tile_contained [Fintype ιₜ] [DecidableEq ιₜ]
    {t : TileSet_finset ps ιₜ} {region : Region}
    (hv : t.Valid_finset region) (i : ιₜ) :
    t.cellsAt_finset i ⊆ region := by
  rw [← hv.covers]
  intro c hc
  simp only [coveredCells_finset, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, hc⟩

/-- Translate a tileset by an offset -/
def translate (t : TileSet_finset ps ιₜ) (offset : Cell) : TileSet_finset ps ιₜ :=
  ⟨fun i => (t i).translate offset⟩

/-- Translation of a tileset preserves disjointness -/
theorem translate_preserves_disjoint [DecidableEq ιₜ]
    (t : TileSet_finset ps ιₜ) (offset : Cell)
    (hdisj : t.PairwiseDisjoint_finset) :
    (t.translate offset).PairwiseDisjoint_finset := by
  intro i j hij
  have hdisj_orig := hdisj i j hij
  rw [cellsAt_finset, cellsAt_finset, translate, PlacedTile_finset.translate_cells,
      PlacedTile_finset.translate_cells]
  rw [Finset.disjoint_iff_ne] at hdisj_orig ⊢
  intro c hc d hd heq
  simp only [translateRegion, Finset.mem_image, translateCell] at hc hd
  obtain ⟨c1, hc1, rfl⟩ := hc
  obtain ⟨c2, hc2, rfl⟩ := hd
  have h_eq : c1 = c2 := translateCell_injective offset heq
  subst h_eq
  exact hdisj_orig c1 hc1 c1 hc2 rfl

/-- Translation of a tileset translates coverage -/
theorem translate_coveredCells [Fintype ιₜ]
    (t : TileSet_finset ps ιₜ) (offset : Cell) :
    (t.translate offset).coveredCells_finset =
      translateRegion t.coveredCells_finset offset := by
  simp only [coveredCells_finset, translate]
  change
    Finset.univ.biUnion (fun i => ((t i).translate offset).cells ps) =
      translateRegion (Finset.univ.biUnion (fun i => (t i).cells ps)) offset
  rw [Finset.biUnion_congr rfl
        (fun i _ => PlacedTile_finset.translate_cells ps (t i) offset)]
  simp only [translateRegion]
  rw [← Finset.biUnion_image]

/-- Translation preserves validity -/
theorem translate_preserves_valid [Fintype ιₜ] [DecidableEq ιₜ]
    (t : TileSet_finset ps ιₜ) (offset : Cell) (region : Region)
    (hv : t.Valid_finset region) :
    (t.translate offset).Valid_finset (translateRegion region offset) := by
  constructor
  · exact translate_preserves_disjoint t offset hv.disjoint
  · rw [translate_coveredCells, hv.covers]

end TileSet_finset

/- ## General Tileability -/

/-- A region is tileable by a protoset if there exists a valid tiling -/
def Tileable_finset {ι : Type*} (ps : Protoset_finset ι) (r : Region) : Prop :=
  ∃ (ιₜ : Type) (_ : Fintype ιₜ) (_ : DecidableEq ιₜ)
    (t : TileSet_finset ps ιₜ), t.Valid_finset r

/-- The empty region is tileable by any protoset -/
theorem empty_tileable_finset {ι : Type*} (ps : Protoset_finset ι) :
    Tileable_finset ps ∅ :=
  ⟨Fin 0, inferInstance, inferInstance, ⟨Fin.elim0⟩,
    ⟨fun i _ _ => Fin.elim0 i, by simp [TileSet_finset.coveredCells_finset]⟩⟩

/-- A translated tileable region is tileable by any protoset -/
theorem Tileable_translate_finset {ι : Type*} (ps : Protoset_finset ι) {r : Region}
    (h : Tileable_finset ps r) (offset : Cell) :
    Tileable_finset ps (translateRegion r offset) := by
  obtain ⟨ιₜ, _, _, t, hv⟩ := h
  use ιₜ, inferInstance, inferInstance, t.translate offset
  exact t.translate_preserves_valid offset r hv

/-- If two disjoint regions are both tileable, their union is tileable -/
theorem Tileable_union_finset {ι : Type*} (ps : Protoset_finset ι)
    {r1 r2 : Region} (h1 : Tileable_finset ps r1) (h2 : Tileable_finset ps r2)
    (hdisj : Disjoint r1 r2) :
    Tileable_finset ps (r1 ∪ r2) := by
  obtain ⟨ι1, _, _, t1, hv1⟩ := h1
  obtain ⟨ι2, _, _, t2, hv2⟩ := h2
  -- Combine the two tilesets
  let t : TileSet_finset ps (ι1 ⊕ ι2) :=
    ⟨fun i =>
      match i with
      | Sum.inl i1 => t1 i1
      | Sum.inr i2 => t2 i2⟩
  use ι1 ⊕ ι2, inferInstance, inferInstance, t
  constructor
  · -- Pairwise disjoint
    intro i j hij
    match i, j with
    | Sum.inl i1, Sum.inl j1 =>
      simp only [TileSet_finset.cellsAt_finset]
      exact hv1.disjoint i1 j1 (fun h => hij (congrArg Sum.inl h))
    | Sum.inr i2, Sum.inr j2 =>
      simp only [TileSet_finset.cellsAt_finset]
      exact hv2.disjoint i2 j2 (fun h => hij (congrArg Sum.inr h))
    | Sum.inl i1, Sum.inr j2 =>
      simp only [TileSet_finset.cellsAt_finset, Finset.disjoint_iff_ne]
      intro c hc d hd
      have hc1 : c ∈ r1 := by
        rw [← hv1.covers]
        simp only [TileSet_finset.coveredCells_finset, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact ⟨i1, hc⟩
      have hd2 : d ∈ r2 := by
        rw [← hv2.covers]
        simp only [TileSet_finset.coveredCells_finset, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact ⟨j2, hd⟩
      exact Finset.disjoint_iff_ne.mp hdisj c hc1 d hd2
    | Sum.inr i2, Sum.inl j1 =>
      simp only [TileSet_finset.cellsAt_finset, Finset.disjoint_iff_ne]
      intro c hc d hd
      have hc2 : c ∈ r2 := by
        rw [← hv2.covers]
        simp only [TileSet_finset.coveredCells_finset, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact ⟨i2, hc⟩
      have hd1 : d ∈ r1 := by
        rw [← hv1.covers]
        simp only [TileSet_finset.coveredCells_finset, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact ⟨j1, hd⟩
      exact Finset.disjoint_iff_ne.mp hdisj d hd1 c hc2 ∘ Eq.symm
  · -- Covers
    simp only [TileSet_finset.coveredCells_finset, ← hv1.covers, ← hv2.covers]
    ext c
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
      true_and, TileSet_finset.cellsAt_finset]
    constructor
    · rintro ⟨i, hi⟩
      match i with
      | Sum.inl i1 => left; exact ⟨i1, hi⟩
      | Sum.inr i2 => right; exact ⟨i2, hi⟩
    · intro h
      rcases h with ⟨i1, hi1⟩ | ⟨i2, hi2⟩
      · exact ⟨Sum.inl i1, hi1⟩
      · exact ⟨Sum.inr i2, hi2⟩

/-- Finite union of pairwise-disjoint tileable regions is tileable. -/
theorem Tileable_biUnion_finset {ι : Type*} (ps : Protoset_finset ι)
    {ιₜ : Type*} [Fintype ιₜ]
    (Rk : ιₜ → Region)
    (hTile : ∀ k : ιₜ, Tileable_finset ps (Rk k))
    (hdisj : ∀ i j : ιₜ, i ≠ j → Disjoint (Rk i) (Rk j)) :
    Tileable_finset ps (Finset.univ.biUnion Rk) := by
  classical
  -- Prove the more general statement for an arbitrary finite set of indices.
  have h_general :
      ∀ (s : Finset ιₜ), Tileable_finset ps (s.biUnion Rk) := by
    intro s
    refine
      s.induction
        (by
          -- Empty union is the empty region.
          simpa using (empty_tileable_finset ps))
        ?step
    intro a s ha hIH
    -- `Rk a` is tileable by assumption.
    have hTa : Tileable_finset ps (Rk a) := hTile a
    -- The union over `s` is tileable by the induction hypothesis.
    have hTs : Tileable_finset ps (s.biUnion Rk) := hIH
    -- `Rk a` is disjoint from the union over `s`, using pairwise disjointness.
    have hdisj_as :
        Disjoint (Rk a) (s.biUnion Rk) := by
      -- Unfold disjointness via pointwise inequality.
      rw [Finset.disjoint_iff_ne]
      intro c hc d hd hcd
      -- `d` lies in some `Rk j` for `j ∈ s`.
      rcases Finset.mem_biUnion.mp hd with ⟨j, hj_s, hdj⟩
      -- Since `a ∉ s`, we know `a ≠ j`.
      have hne : a ≠ j := by
        intro h_eq
        subst h_eq
        exact ha hj_s
      -- Use disjointness of `Rk a` and `Rk j`.
      have hdisj_aj := hdisj a j hne
      exact Finset.disjoint_iff_ne.mp hdisj_aj c hc d hdj hcd
    -- Apply the two-region union lemma.
    have h_union : Tileable_finset ps (Rk a ∪ s.biUnion Rk) :=
      Tileable_union_finset ps hTa hTs hdisj_as
    -- Show that this union is exactly the biUnion over `insert a s`.
    have h_eq :
        (insert a s).biUnion Rk =
          Rk a ∪ s.biUnion Rk := by
      ext c
      constructor
      · intro hc
        rcases Finset.mem_biUnion.mp hc with ⟨j, hj_ins, hcj⟩
        by_cases hj : j = a
        · subst hj
          -- `c ∈ Rk a`, hence `c ∈ Rk a ∪ s.biUnion Rk`
          exact Finset.mem_union.mpr (Or.inl hcj)
        · -- `j ≠ a`, so `j ∈ s`
          have hj_s : j ∈ s := by
            -- Remove the `a`-case from membership in `insert a s`.
            simpa [Finset.mem_insert, hj] using hj_ins
          have hcS : c ∈ s.biUnion Rk :=
            Finset.mem_biUnion.mpr ⟨j, hj_s, hcj⟩
          exact Finset.mem_union.mpr (Or.inr hcS)
      · intro hc
        rcases Finset.mem_union.mp hc with hc_a | hc_s
        · -- `c ∈ Rk a`
          apply Finset.mem_biUnion.mpr
          refine ⟨a, ?_, hc_a⟩
          simp [Finset.mem_insert]
        · -- `c ∈ s.biUnion Rk`
          rcases Finset.mem_biUnion.mp hc_s with ⟨j, hj_s, hcj⟩
          apply Finset.mem_biUnion.mpr
          refine ⟨j, ?_, hcj⟩
          -- `j` is in `insert a s` but distinct from `a` since `a ∉ s`.
          have : j ≠ a := by
            intro h_eq
            subst h_eq
            exact ha hj_s
          simp [Finset.mem_insert, hj_s, this]
    simpa [h_eq] using h_union
  -- Specialize the general statement to `Finset.univ`.
  simpa using h_general Finset.univ

/-- Translating by offset and then by `-offset` gives the original region -/
theorem translateRegion_neg (r : Region) (offset : Cell) :
    translateRegion (translateRegion r offset) (-offset.1, -offset.2) = r := by
  simp only [translateRegion, Finset.image_image]
  have :
      ((fun x => translateCell x (-offset.1, -offset.2)) ∘
        (fun x => translateCell x offset)) =
        id := by
    funext ⟨x, y⟩
    simp only [translateCell, Function.comp_apply, id]
    ext <;> ring
  simp only [this, Finset.image_id]

/-- Composition of translations on a region adds their offsets. -/
theorem translateRegion_add (r : Region) (o₁ o₂ : Cell) :
    translateRegion (translateRegion r o₁) o₂ =
      translateRegion r (o₁.1 + o₂.1, o₁.2 + o₂.2) := by
  simp only [translateRegion, Finset.image_image]
  have :
      ((fun x => translateCell x o₂) ∘
        (fun x => translateCell x o₁)) =
        (fun x => translateCell x (o₁.1 + o₂.1, o₁.2 + o₂.2)) := by
    funext ⟨x, y⟩
    simp [translateCell, Function.comp_apply, add_left_comm, add_comm]
  simp [this]

/-- Erasing a point from a finite union distributes over both sides. -/
theorem erase_union_finset {α : Type*} [DecidableEq α]
    (A B : Finset α) (x : α) :
    (A ∪ B).erase x = A.erase x ∪ B.erase x := by
  classical
  ext c
  by_cases hcx : c = x
  · subst hcx
    simp [Finset.mem_union, Finset.mem_erase]
  · simp [Finset.mem_union, Finset.mem_erase, hcx]

/-- Erasing a translated point is the same as translating an erased region. -/
theorem translateRegion_erase_point (r : Region) (offset x : Cell) :
    (translateRegion r offset).erase (translateCell x offset) =
      translateRegion (r.erase x) offset := by
  classical
  unfold translateRegion
  ext c
  constructor
  · intro hc
    rcases Finset.mem_erase.mp hc with ⟨hc_ne, hc_img⟩
    rcases Finset.mem_image.mp hc_img with ⟨c₀, hc₀, rfl⟩
    have hc₀_ne : c₀ ≠ x := by
      intro h_eq
      apply hc_ne
      subst h_eq
      rfl
    have hc₀_erase : c₀ ∈ r.erase x :=
      Finset.mem_erase.mpr ⟨hc₀_ne, hc₀⟩
    exact Finset.mem_image.mpr ⟨c₀, hc₀_erase, rfl⟩
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨c₀, hc₀_erase, rfl⟩
    rcases Finset.mem_erase.mp hc₀_erase with ⟨hc₀_ne, hc₀⟩
    have hc_img :
        translateCell c₀ offset ∈
          Finset.image (translateCell · offset) r :=
      Finset.mem_image.mpr ⟨c₀, hc₀, rfl⟩
    have hc_ne :
        translateCell c₀ offset ≠ translateCell x offset := by
      intro h_eq
      apply hc₀_ne
      exact translateCell_injective offset h_eq
    exact Finset.mem_erase.mpr ⟨hc_ne, hc_img⟩

/-- Tileability is preserved by translation (both directions) -/
theorem Tileable_translate_iff_finset {ι : Type*} (ps : Protoset_finset ι)
    (r : Region) (offset : Cell) :
    Tileable_finset ps r ↔ Tileable_finset ps (translateRegion r offset) := by
  constructor
  · exact fun h => Tileable_translate_finset ps h offset
  · intro h
    have h' := Tileable_translate_finset ps h (-offset.1, -offset.2)
    rw [translateRegion_neg] at h'
    exact h'

/-- If `R = translateRegion S offset` and `R` is tileable, then `S` is tileable -/
theorem Tileable_of_translate_eq_finset {ι : Type*} (ps : Protoset_finset ι)
    {R S : Region} (offset : Cell)
    (heq : R = translateRegion S offset) (hR : Tileable_finset ps R) :
    Tileable_finset ps S := by
  rw [heq] at hR
  exact (Tileable_translate_iff_finset ps S offset).mpr hR

/- ## Helper for Creating TileSets -/

/-- Create a `TileSet_finset` from a function -/
def mkTileSet_finset {ι : Type*} (ps : Protoset_finset ι) (ιₜ : Type*)
    (f : ιₜ → PlacedTile_finset ι) : TileSet_finset ps ιₜ :=
  ⟨f⟩

/-- Create a placed tile -/
def mkPlacedTile_finset {ι : Type*} (i : ι) (x y : ℤ) (r : Fin 4) :
    PlacedTile_finset ι :=
  ⟨i, (x, y), r⟩

/- ## Generic Placement Enumeration -/

/-- A placed tile is contained in a region if all its cells are in the region -/
def PlacedTile_finset.containedIn {ι : Type*} (ps : Protoset_finset ι)
    (pt : PlacedTile_finset ι) (r : Region) : Prop :=
  pt.cells ps ⊆ r

instance {ι : Type*} (ps : Protoset_finset ι)
    (pt : PlacedTile_finset ι) (r : Region) :
    Decidable (pt.containedIn ps r) :=
  inferInstanceAs (Decidable (pt.cells ps ⊆ r))

/-- A placed tile covers a cell if the cell is in its cells -/
def PlacedTile_finset.coversCell {ι : Type*} (ps : Protoset_finset ι)
    (pt : PlacedTile_finset ι) (c : Cell) : Prop :=
  c ∈ pt.cells ps

instance {ι : Type*} (ps : Protoset_finset ι)
    (pt : PlacedTile_finset ι) (c : Cell) :
    Decidable (pt.coversCell ps c) :=
  inferInstanceAs (Decidable (c ∈ pt.cells ps))

/-- All placements of a single prototile that cover a given target cell.
For each cell `c` in the prototile and each rotation `r`, the unique
translation that maps `rotateCell c r` to `target` is:
`target - rotateCell c r`. -/
def allPlacementsCoveringProto_finset {ι : Type*}
    (i : ι) (proto : Prototile_finset) (target : Cell) :
    List (PlacedTile_finset ι) :=
  proto.cells.flatMap fun baseCell =>
    (List.finRange 4).map fun r =>
      let rotated := rotateCell baseCell r
      ⟨i, (target.1 - rotated.1, target.2 - rotated.2), r⟩

/-- All placements from a protoset that cover a given target cell -/
def allPlacementsCovering_finset {ι : Type*}
    (ps : Protoset_finset ι) (indices : List ι) (target : Cell) :
    List (PlacedTile_finset ι) :=
  indices.flatMap fun i => allPlacementsCoveringProto_finset i (ps i) target

/-- Every placement produced by `allPlacementsCoveringProto_finset`
actually covers the target -/
theorem allPlacementsCoveringProto_covers {ι : Type*}
    (ps : Protoset_finset ι) (i : ι) (target : Cell) (pt : PlacedTile_finset ι)
    (hpt : pt ∈ allPlacementsCoveringProto_finset i (ps i) target) :
    pt.coversCell ps target := by
  simp only [allPlacementsCoveringProto_finset, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hpt
  obtain ⟨baseCell, hbase, r, rfl⟩ := hpt
  simp only [PlacedTile_finset.coversCell, PlacedTile_finset.cells, Finset.mem_image,
    translateCell]
  refine ⟨rotateCell baseCell r, ?_, ?_⟩
  · simp only [rotateProto, Finset.mem_image]
    exact ⟨baseCell, Prototile_finset.mem_coe (ps i) baseCell |>.mpr hbase, rfl⟩
  · ext <;> ring

/-- `allPlacementsCoveringProto_finset` is complete: any placement with index `i`
covering `target` is in the list. -/
theorem allPlacementsCoveringProto_complete {ι : Type*}
    (ps : Protoset_finset ι) (i : ι) (target : Cell) (pt : PlacedTile_finset ι)
    (hidx : pt.index = i) (hcover : pt.coversCell ps target) :
    pt ∈ allPlacementsCoveringProto_finset i (ps i) target := by
  simp only [PlacedTile_finset.coversCell, PlacedTile_finset.cells] at hcover
  simp only [Finset.mem_image, translateCell] at hcover
  obtain ⟨rotatedCell, hrot, htrans⟩ := hcover
  simp only [rotateProto, Finset.mem_image] at hrot
  obtain ⟨origCell, horig, rfl⟩ := hrot
  simp only [allPlacementsCoveringProto_finset, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and]
  rw [hidx] at horig
  rw [(ps i).mem_coe] at horig
  refine ⟨origCell, horig, pt.rotation, ?_⟩
  rw [Prod.mk.injEq] at htrans
  obtain ⟨htx, hty⟩ := htrans
  obtain ⟨idx, trans, rot⟩ := pt
  simp only at hidx htx hty; subst hidx
  simp only [PlacedTile_finset.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  ext <;> omega

/-! Placements covering a cell and contained in a region -/
def placementsCoveringIn_finset {ι : Type*} (ps : Protoset_finset ι)
    (indices : List ι) (target : Cell) (region : Region) :
    List (PlacedTile_finset ι) :=
  (allPlacementsCovering_finset ps indices target).filter
    fun pt => pt.containedIn ps region


/- ## Protoset_finset Refinement -/

variable {ιA ιB : Type*}

/-- `psA` refines `psB` if every rotated prototile of `psB` is tileable by `psA`. -/
def Refines_finset (psA : Protoset_finset ιA) (psB : Protoset_finset ιB) : Prop :=
  ∀ (j : ιB) (r : Fin 4), Tileable_finset psA (rotateProto (psB j) r)

/-- If `psA` refines `psB` and `psB` tiles `R`, then `psA` tiles `R`.

Conceptually: replace each `psB`-tile in a tiling of `R` by a `psA`-tiling of
that tile's shape, using refinement. -/
theorem Tileable_refine_finset
    (psA : Protoset_finset ιA) (psB : Protoset_finset ιB) (R : Region)
    (hAB : Refines_finset psA psB) (hBR : Tileable_finset psB R) :
    Tileable_finset psA R := by
  classical
  -- Unpack a concrete tiling of `R` by `psB`.
  obtain ⟨ιₜB, hFB, hDB, tB, hBvalid⟩ := hBR
  letI : Fintype ιₜB := hFB
  letI : DecidableEq ιₜB := hDB
  -- The region covered by the `k`-th tile in the `psB`-tiling.
  let Rk : ιₜB → Region := fun k => tB.cellsAt_finset k
  -- Each such region is tileable by `psA`, using refinement and translation.
  have hTileA : ∀ k : ιₜB, Tileable_finset psA (Rk k) := by
    intro k
    -- The placed `psB`-tile at index `k`.
    let pt := tB k
    -- `psA` tiles the rotated prototile of `pt`.
    have h_shape :
        Tileable_finset psA (rotateProto (psB pt.index) pt.rotation) :=
      hAB pt.index pt.rotation
    -- Translate this tiling to the actual position of `pt`.
    have h_translated :
        Tileable_finset psA
          (translateRegion
            (rotateProto (psB pt.index) pt.rotation)
            pt.translation) :=
      Tileable_translate_finset psA h_shape pt.translation
    -- The region `Rk k` is exactly this translated rotated prototile.
    have h_eq :
        Rk k =
          translateRegion
            (rotateProto (psB pt.index) pt.rotation)
            pt.translation := by
      -- Unfold definitions.
      unfold Rk TileSet_finset.cellsAt_finset pt
      -- `PlacedTile_finset.cells` is defined as `translateRegion` of the rotated prototile.
      simp [PlacedTile_finset.cells, translateRegion]
    simpa [h_eq] using h_translated
  -- Regions corresponding to distinct tiles in the `psB`-tiling are disjoint.
  have hdisjA :
      ∀ i j : ιₜB, i ≠ j → Disjoint (Rk i) (Rk j) := by
    intro i j hij
    -- This is exactly the pairwise disjointness from validity of `tB`.
    have h := hBvalid.disjoint_tiles i j hij
    simpa [Rk, TileSet_finset.cellsAt_finset] using h
  -- The union of all these regions is `R` (since `tB` is a tiling of `R`).
  have h_union :
      Tileable_finset psA (Finset.univ.biUnion Rk) :=
    Tileable_biUnion_finset psA Rk hTileA hdisjA
  -- `tB.coveredCells_finset` is exactly this union.
  have h_cov :
      Finset.univ.biUnion Rk = tB.coveredCells_finset := by
    rfl
  -- Rewrite using the fact that `tB` covers `R`.
  have hA_R : Tileable_finset psA tB.coveredCells_finset := by
    simpa [h_cov] using h_union
  simpa [hBvalid.covers] using hA_R


/- ## Rectangle Definition and Tilings -/

/-- An `n × m` rectangle as a finite set of cells
from `(0,0)` to `(n-1, m-1)` -/
def rectangle (n m : ℕ) : Region :=
  (Finset.range n |>.map ⟨Int.ofNat, Int.ofNat_injective⟩) ×ˢ
  (Finset.range m |>.map ⟨Int.ofNat, Int.ofNat_injective⟩)

/-- The area of an `n × m` rectangle -/
@[simp] theorem rectangle_card (n m : ℕ) :
    (rectangle n m).card = n * m := by
  simp only [rectangle, Finset.card_product, Finset.card_map,
    Finset.card_range]

/-- Membership in a rectangle -/
theorem mem_rectangle {n m : ℕ} {c : Cell} :
    c ∈ rectangle n m ↔
      0 ≤ c.1 ∧ c.1 < n ∧ 0 ≤ c.2 ∧ c.2 < m := by
  simp only [rectangle, Finset.mem_product, Finset.mem_map,
    Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨x, hx, hxeq⟩, ⟨y, hy, hyeq⟩⟩
    simp only [← hxeq, ← hyeq]
    exact ⟨Int.natCast_nonneg x, Int.ofNat_lt.mpr hx,
      Int.natCast_nonneg y, Int.ofNat_lt.mpr hy⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine
      ⟨⟨c.1.toNat, by omega, by simp; omega⟩,
       ⟨c.2.toNat, by omega, by simp; omega⟩⟩

/-- Swapping an `n × m` rectangle gives an `m × n` rectangle -/
theorem swap_rectangle (n m : ℕ) :
    swapRegion (rectangle n m) = rectangle m n := by
  ext ⟨x, y⟩
  simp only [swapRegion, rectangle, Finset.mem_image, Finset.mem_product,
    Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk,
    swapCell]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨⟨j, hj, rfl⟩, ⟨i, hi, rfl⟩⟩
  · rintro ⟨⟨j, hj, rfl⟩, ⟨i, hi, rfl⟩⟩
    exact ⟨(i, j), ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩, rfl⟩

/- ## Rectangle Splitting and Combining -/

/-- A rectangle can be split horizontally -/
theorem rectangle_split_horizontal (a b m : ℕ) :
    rectangle (a + b) m =
      rectangle a m ∪
        translateRegion (rectangle b m) (a, 0) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_union, mem_rectangle, translateRegion,
    Finset.mem_image, translateCell]
  constructor
  · rintro ⟨hx0, hxab, hy0, hym⟩
    by_cases hxa : x < a
    · left; exact ⟨hx0, hxa, hy0, hym⟩
    · right
      push_neg at hxa
      refine ⟨(x - a, y), ⟨by omega, by omega, hy0, hym⟩, ?_⟩
      simp only [Prod.mk.injEq]; omega
  · rintro (⟨hx0, hxa, hy0, hym⟩ |
            ⟨⟨x', y'⟩, ⟨hx0', hxb, hy0', hym'⟩, heq⟩)
    · exact ⟨hx0, by omega, hy0, hym⟩
    · simp only [Prod.mk.injEq] at heq
      omega

/-- The two parts of a horizontal split are disjoint -/
theorem rectangle_split_horizontal_disjoint (a b m : ℕ) :
    Disjoint (rectangle a m)
      (translateRegion (rectangle b m) (a, 0)) := by
  rw [Finset.disjoint_iff_ne]
  intro c hc d hd heq
  simp only [mem_rectangle] at hc
  simp only [translateRegion, Finset.mem_image, translateCell,
    mem_rectangle] at hd
  obtain ⟨⟨x', y'⟩, ⟨hx0', hxb, _, _⟩, rfl⟩ := hd
  have hc1 : c.1 < ↑a := hc.2.1
  have hd1 : c.1 = x' + ↑a := by rw [heq]
  linarith

/-- A rectangle can be split vertically -/
theorem rectangle_split_vertical (n a b : ℕ) :
    rectangle n (a + b) =
      rectangle n a ∪
        translateRegion (rectangle n b) (0, a) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_union, mem_rectangle, translateRegion,
    Finset.mem_image, translateCell]
  constructor
  · rintro ⟨hx0, hxn, hy0, hyab⟩
    by_cases hya : y < a
    · left; exact ⟨hx0, hxn, hy0, hya⟩
    · right
      push_neg at hya
      refine ⟨(x, y - a), ⟨hx0, hxn, by omega, by omega⟩, ?_⟩
      simp only [Prod.mk.injEq]; omega
  · rintro (⟨hx0, hxn, hy0, hya⟩ |
            ⟨⟨x', y'⟩, ⟨hx0', hxn', hy0', hyb⟩, heq⟩)
    · exact ⟨hx0, hxn, hy0, by omega⟩
    · simp only [Prod.mk.injEq] at heq
      omega

/-- The two parts of a vertical split are disjoint -/
theorem rectangle_split_vertical_disjoint (n a b : ℕ) :
    Disjoint (rectangle n a)
      (translateRegion (rectangle n b) (0, a)) := by
  rw [Finset.disjoint_iff_ne]
  intro c hc d hd heq
  simp only [mem_rectangle] at hc
  simp only [translateRegion, Finset.mem_image, translateCell,
    mem_rectangle] at hd
  obtain ⟨⟨x', y'⟩, ⟨_, _, hy0', hyb⟩, rfl⟩ := hd
  have hc2 : c.2 < ↑a := hc.2.2.2
  have hd2 : c.2 = y' + ↑a := by rw [heq]
  linarith

/-- If we can tile two horizontally adjacent rectangles, we can tile their union -/
theorem Tileable_horizontal_union_finset {ι : Type*} (ps : Protoset_finset ι) (a b m : ℕ)
    (h1 : Tileable_finset ps (rectangle a m)) (h2 : Tileable_finset ps (rectangle b m)) :
    Tileable_finset ps (rectangle (a + b) m) := by
  rw [rectangle_split_horizontal]
  apply Tileable_union_finset ps h1
  · exact Tileable_translate_finset ps h2 (a, 0)
  · exact rectangle_split_horizontal_disjoint a b m

/-- If we can tile two vertically adjacent rectangles, we can tile their union -/
theorem Tileable_vertical_union_finset {ι : Type*} (ps : Protoset_finset ι) (n a b : ℕ)
    (h1 : Tileable_finset ps (rectangle n a)) (h2 : Tileable_finset ps (rectangle n b)) :
    Tileable_finset ps (rectangle n (a + b)) := by
  rw [rectangle_split_vertical]
  apply Tileable_union_finset ps h1
  · exact Tileable_translate_finset ps h2 (0, a)
  · exact rectangle_split_vertical_disjoint n a b
