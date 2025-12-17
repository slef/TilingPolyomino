/-
# Polyomino Tiling Proofs

This file defines a framework for polyomino tilings on the integer grid.
The design uses indexed families (functions `ιₜ → PlacedTile`) with typeclass
constraints for decidability when the index type is finite.

## Main Definitions
- `Prototile`: A polyomino shape (finite subset of ℤ²)
- `Protoset`: A collection of allowed tile shapes
- `PlacedTile`: A tile placed on the grid (prototile + translation + rotation)
- `TileSet`: An indexed family of placed tiles
- `TileSet.Valid`: A valid tiling of a region

## Design Notes
- When `[Fintype ιₜ] [DecidableEq ιₜ]`, decidability is automatic
- For infinite tilings, use `ιₜ = ℕ` (countable) or other index types
- This mirrors the AM library approach but maintains computability for finite cases

## Main Results
- `rect_tileable_iff`: Complete characterization of L-tileable rectangles.
- An n×m rectangle is L-tileable iff nm ≡ 0 (mod 3), n,m ≥ 2, and it's not 3×odd or odd×3.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! ## Basic Definitions -/

/-- A cell on the integer grid -/
abbrev Cell := ℤ × ℤ

/-- A region is a finite set of cells -/
abbrev Region := Finset Cell

/-! ## Prototile and Protoset

A prototile is the "shape" of a tile, represented as a list of cells with no duplicates.
This design allows both:
- Computation: iterate over `p.cells` (the list)
- Proofs: use `(p : Finset Cell)` via coercion to access Finset lemmas

By convention, prototiles are normalized to have their anchor at the origin.
A protoset is an indexed family of prototiles - the allowed tile types.
-/

/-- A prototile is a polyomino shape (list of cells with no duplicates) -/
structure Prototile where
  /-- The cells making up the tile -/
  cells : List Cell
  /-- No duplicate cells -/
  nodup : cells.Nodup := by decide
  deriving DecidableEq

/-- Coercion from Prototile to Finset Cell -/
instance : Coe Prototile (Finset Cell) where
  coe p := ⟨p.cells, p.nodup⟩

theorem Prototile.coe_def (p : Prototile) : (p : Finset Cell) = ⟨p.cells, p.nodup⟩ := rfl

theorem Prototile.mem_coe (p : Prototile) (c : Cell) : c ∈ (p : Finset Cell) ↔ c ∈ p.cells := by
  rw [Prototile.coe_def]
  simp only [Finset.mem_mk, Multiset.mem_coe]

/-- Cardinality of a prototile -/
def Prototile.card (p : Prototile) : ℕ := p.cells.length

theorem Prototile.card_eq (p : Prototile) : p.card = (p : Finset Cell).card := by
  simp only [Prototile.card, Finset.card_def]
  rfl

/-- A protoset is an indexed family of prototiles -/
structure Protoset (ι : Type*) where
  /-- The tiles in the protoset -/
  tiles : ι → Prototile

instance {ι : Type*} : CoeFun (Protoset ι) (fun _ => ι → Prototile) where
  coe := Protoset.tiles

/-! ## Rotations

We support 4 rotations (0°, 90°, 180°, 270° counterclockwise).
-/

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
theorem rotateCell_injective (r : Fin 4) : Function.Injective (rotateCell · r) := by
  intro ⟨x1, y1⟩ ⟨x2, y2⟩ h
  fin_cases r <;> simp only [rotateCell, rotateCell90, Prod.mk.injEq] at h <;> (ext <;> omega)

/-- Rotate all cells in a prototile (returns Finset for compatibility) -/
def rotateProto (p : Prototile) (r : Fin 4) : Finset Cell :=
  (p : Finset Cell).image (rotateCell · r)

/-- Rotation preserves cardinality of a prototile -/
theorem rotateProto_card (p : Prototile) (r : Fin 4) : (rotateProto p r).card = p.cells.length := by
  simp only [rotateProto]
  rw [Finset.card_image_of_injective _ (rotateCell_injective r)]
  rw [← p.card_eq]
  rfl

/-! ## Placed Tiles

A placed tile consists of:
- Which prototile (index into the protoset)
- A translation (where to place it)
- A rotation (which orientation)
-/

/-- A placed tile: prototile index + translation + rotation -/
structure PlacedTile (ι : Type*) where
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
theorem translateCell_injective (offset : Cell) : Function.Injective (translateCell · offset) := by
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

/-! ## Swap Transformation

Swapping x and y coordinates (reflection across the line y=x).
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
def PlacedTile.cells {ι : Type*} (ps : Protoset ι) (pt : PlacedTile ι) : Finset Cell :=
  (rotateProto (ps pt.index) pt.rotation).image (translateCell · pt.translation)

/-- Translate a placed tile by an offset -/
def PlacedTile.translate {ι : Type*} (pt : PlacedTile ι) (offset : Cell) : PlacedTile ι :=
  ⟨pt.index, (pt.translation.1 + offset.1, pt.translation.2 + offset.2), pt.rotation⟩

/-- Translation of a placed tile translates its cells -/
theorem PlacedTile.translate_cells {ι : Type*} (ps : Protoset ι) (pt : PlacedTile ι)
    (offset : Cell) : (pt.translate offset).cells ps = translateRegion (pt.cells ps) offset := by
  simp only [PlacedTile.cells, PlacedTile.translate, translateRegion]
  ext c
  simp only [Finset.mem_image, translateCell]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨(b.1 + pt.translation.1, b.2 + pt.translation.2), ⟨b, hb, rfl⟩, by ring_nf⟩
  · rintro ⟨c', ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, by ring_nf⟩

/-- Placing a tile preserves the cardinality of the prototile -/
theorem PlacedTile.cells_card {ι : Type*} (ps : Protoset ι) (pt : PlacedTile ι) :
    (pt.cells ps).card = (ps pt.index).cells.length := by
  simp only [PlacedTile.cells]
  rw [Finset.card_image_of_injective _ (translateCell_injective pt.translation)]
  exact rotateProto_card (ps pt.index) pt.rotation

/-! ## TileSet: Indexed Family of Placed Tiles

A `TileSet` is a function from an index type to placed tiles.
This is the same approach as the AM library, but we add typeclass
constraints for decidability when needed.
-/

/-- A TileSet is an indexed family of placed tiles -/
structure TileSet {ι : Type*} (ps : Protoset ι) (ιₜ : Type*) where
  /-- The tiles in the family -/
  tiles : ιₜ → PlacedTile ι

instance {ι : Type*} {ps : Protoset ι} {ιₜ : Type*} :
    CoeFun (TileSet ps ιₜ) (fun _ => ιₜ → PlacedTile ι) where
  coe := TileSet.tiles

namespace TileSet

variable {ι : Type*} {ps : Protoset ι} {ιₜ : Type*}

/-- The cells covered by a single tile in the tileset -/
def cellsAt (t : TileSet ps ιₜ) (i : ιₜ) : Finset Cell :=
  (t i).cells ps

/-- The union of all cells covered by the tileset (for finite index types) -/
def coveredCells [Fintype ιₜ] (t : TileSet ps ιₜ) : Finset Cell :=
  Finset.univ.biUnion t.cellsAt

/-- Pairwise disjointness of tiles -/
def PairwiseDisjoint [DecidableEq ιₜ] (t : TileSet ps ιₜ) : Prop :=
  ∀ i j : ιₜ, i ≠ j → Disjoint (t.cellsAt i) (t.cellsAt j)

/-- If tiles are pairwise disjoint, the total area is the sum of individual areas -/
theorem card_coveredCells [Fintype ιₜ] [DecidableEq ιₜ] (t : TileSet ps ιₜ)
    (hdisj : t.PairwiseDisjoint) : t.coveredCells.card = ∑ i : ιₜ, (t.cellsAt i).card := by
  simp only [coveredCells]
  rw [Finset.card_biUnion]
  intro i _ j _ hij
  exact hdisj i j hij

/-- A tileset is valid for a region if tiles are disjoint and exactly cover it -/
structure Valid [Fintype ιₜ] [DecidableEq ιₜ] (t : TileSet ps ιₜ) (region : Region) : Prop where
  /-- No two tiles overlap -/
  disjoint : t.PairwiseDisjoint
  /-- The tiles exactly cover the region -/
  covers : t.coveredCells = region

/-- Decidable pairwise disjointness for finite index types -/
instance instDecidablePairwiseDisjoint [Fintype ιₜ] [DecidableEq ιₜ] (t : TileSet ps ιₜ) :
    Decidable t.PairwiseDisjoint :=
  inferInstanceAs (Decidable (∀ i j : ιₜ, i ≠ j → Disjoint (t.cellsAt i) (t.cellsAt j)))

/-- Decidable validity for finite index types -/
instance instDecidableValid [Fintype ιₜ] [DecidableEq ιₜ] (t : TileSet ps ιₜ) (region : Region) :
    Decidable (t.Valid region) :=
  if hd : t.PairwiseDisjoint then
    if hc : t.coveredCells = region then
      isTrue ⟨hd, hc⟩
    else
      isFalse (fun h => hc h.covers)
  else
    isFalse (fun h => hd h.disjoint)

/-- Tiles at different indices are disjoint -/
theorem Valid.disjoint_tiles [Fintype ιₜ] [DecidableEq ιₜ] {t : TileSet ps ιₜ} {region : Region}
    (hv : t.Valid region) (i j : ιₜ) (hij : i ≠ j) :
    Disjoint (t.cellsAt i) (t.cellsAt j) :=
  hv.disjoint i j hij

/-- Every tile's cells are contained in the region -/
theorem Valid.tile_contained [Fintype ιₜ] [DecidableEq ιₜ] {t : TileSet ps ιₜ} {region : Region}
    (hv : t.Valid region) (i : ιₜ) : t.cellsAt i ⊆ region := by
  rw [← hv.covers]
  intro c hc
  simp only [coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, hc⟩

/-- Translate a tileset by an offset -/
def translate (t : TileSet ps ιₜ) (offset : Cell) : TileSet ps ιₜ :=
  ⟨fun i => (t i).translate offset⟩

/-- Translation of a tileset preserves disjointness -/
theorem translate_preserves_disjoint [DecidableEq ιₜ] (t : TileSet ps ιₜ) (offset : Cell)
    (hdisj : t.PairwiseDisjoint) : (t.translate offset).PairwiseDisjoint := by
  intro i j hij
  have hdisj_orig := hdisj i j hij
  rw [cellsAt, cellsAt, translate, PlacedTile.translate_cells, PlacedTile.translate_cells]
  rw [Finset.disjoint_iff_ne] at hdisj_orig ⊢
  intro c hc d hd heq
  simp only [translateRegion, Finset.mem_image, translateCell] at hc hd
  obtain ⟨c1, hc1, rfl⟩ := hc
  obtain ⟨c2, hc2, rfl⟩ := hd
  -- c = translateCell c1 offset = translateCell c2 offset, so c1 = c2 by injectivity
  have h_eq : c1 = c2 := translateCell_injective offset heq
  subst h_eq
  exact hdisj_orig c1 hc1 c1 hc2 rfl

/-- Translation of a tileset translates coverage -/
theorem translate_coveredCells [Fintype ιₜ] (t : TileSet ps ιₜ) (offset : Cell) :
    (t.translate offset).coveredCells = translateRegion t.coveredCells offset := by
  simp only [coveredCells, translate]
  change Finset.univ.biUnion (fun i => ((t i).translate offset).cells ps) =
    translateRegion (Finset.univ.biUnion (fun i => (t i).cells ps)) offset
  rw [Finset.biUnion_congr rfl fun i _ => PlacedTile.translate_cells ps (t i) offset]
  simp only [translateRegion]
  -- Need: biUnion (image f) = image f (biUnion)
  -- This follows from image distributing over biUnion
  rw [← Finset.biUnion_image]

/-- Translation preserves validity -/
theorem translate_preserves_valid [Fintype ιₜ] [DecidableEq ιₜ] (t : TileSet ps ιₜ) (offset : Cell)
    (region : Region) (hv : t.Valid region) :
    (t.translate offset).Valid (translateRegion region offset) := by
  constructor
  · exact translate_preserves_disjoint t offset hv.disjoint
  · rw [translate_coveredCells, hv.covers]

end TileSet

/-! ## General Tileability -/

/-- A region is tileable by a protoset if there exists a valid tiling -/
def Tileable {ι : Type*} (ps : Protoset ι) (r : Region) : Prop :=
  ∃ (ιₜ : Type) (_ : Fintype ιₜ) (_ : DecidableEq ιₜ) (t : TileSet ps ιₜ), t.Valid r

/-- The empty region is tileable by any protoset -/
theorem empty_tileable {ι : Type*} (ps : Protoset ι) : Tileable ps ∅ :=
  ⟨Fin 0, inferInstance, inferInstance, ⟨Fin.elim0⟩,
    ⟨fun i _ _ => Fin.elim0 i, by simp [TileSet.coveredCells]⟩⟩

/-- A translated tileable region is tileable by any protoset -/
theorem Tileable_translate {ι : Type*} (ps : Protoset ι) {r : Region} (h : Tileable ps r)
    (offset : Cell) : Tileable ps (translateRegion r offset) := by
  obtain ⟨ιₜ, _, _, t, hv⟩ := h
  use ιₜ, inferInstance, inferInstance, t.translate offset
  exact t.translate_preserves_valid offset r hv

/-- If two disjoint regions are both tileable, their union is tileable -/
theorem Tileable_union {ι : Type*} (ps : Protoset ι) {r1 r2 : Region} (h1 : Tileable ps r1)
    (h2 : Tileable ps r2) (hdisj : Disjoint r1 r2) : Tileable ps (r1 ∪ r2) := by
  obtain ⟨ι1, _, _, t1, hv1⟩ := h1
  obtain ⟨ι2, _, _, t2, hv2⟩ := h2
  -- Combine the two tilesets
  let t : TileSet ps (ι1 ⊕ ι2) := ⟨fun i =>
    match i with
    | Sum.inl i1 => t1 i1
    | Sum.inr i2 => t2 i2⟩
  use ι1 ⊕ ι2, inferInstance, inferInstance, t
  constructor
  · -- Pairwise disjoint
    intro i j hij
    match i, j with
    | Sum.inl i1, Sum.inl j1 =>
      simp only [TileSet.cellsAt]
      exact hv1.disjoint i1 j1 (fun h => hij (congrArg Sum.inl h))
    | Sum.inr i2, Sum.inr j2 =>
      simp only [TileSet.cellsAt]
      exact hv2.disjoint i2 j2 (fun h => hij (congrArg Sum.inr h))
    | Sum.inl i1, Sum.inr j2 =>
      simp only [TileSet.cellsAt, Finset.disjoint_iff_ne]
      intro c hc d hd
      have hc1 : c ∈ r1 := by
        rw [← hv1.covers]
        simp only [TileSet.coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i1, hc⟩
      have hd2 : d ∈ r2 := by
        rw [← hv2.covers]
        simp only [TileSet.coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨j2, hd⟩
      exact Finset.disjoint_iff_ne.mp hdisj c hc1 d hd2
    | Sum.inr i2, Sum.inl j1 =>
      simp only [TileSet.cellsAt, Finset.disjoint_iff_ne]
      intro c hc d hd
      have hc2 : c ∈ r2 := by
        rw [← hv2.covers]
        simp only [TileSet.coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i2, hc⟩
      have hd1 : d ∈ r1 := by
        rw [← hv1.covers]
        simp only [TileSet.coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨j1, hd⟩
      exact Finset.disjoint_iff_ne.mp hdisj d hd1 c hc2 ∘ Eq.symm
  · -- Covers
    simp only [TileSet.coveredCells, ← hv1.covers, ← hv2.covers]
    ext c
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, TileSet.cellsAt]
    constructor
    · rintro ⟨i, hi⟩
      match i with
      | Sum.inl i1 => left; exact ⟨i1, hi⟩
      | Sum.inr i2 => right; exact ⟨i2, hi⟩
    · intro h
      rcases h with ⟨i1, hi1⟩ | ⟨i2, hi2⟩
      · exact ⟨Sum.inl i1, hi1⟩
      · exact ⟨Sum.inr i2, hi2⟩

/-- Translating by offset and then by -offset gives the original region -/
theorem translateRegion_neg (r : Region) (offset : Cell) :
    translateRegion (translateRegion r offset) (-offset.1, -offset.2) = r := by
  simp only [translateRegion, Finset.image_image]
  have : ((fun x => translateCell x (-offset.1, -offset.2)) ∘
          (fun x => translateCell x offset)) = id := by
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
theorem Tileable_translate_iff {ι : Type*} (ps : Protoset ι) (r : Region) (offset : Cell) :
    Tileable ps r ↔ Tileable ps (translateRegion r offset) := by
  constructor
  · exact fun h => Tileable_translate ps h offset
  · intro h
    have h' := Tileable_translate ps h (-offset.1, -offset.2)
    rw [translateRegion_neg] at h'
    exact h'

/-- If R = S.image(translate by offset) and R is tileable, then S is tileable -/
theorem Tileable_of_translate_eq {ι : Type*} (ps : Protoset ι) {R S : Region} (offset : Cell)
    (heq : R = translateRegion S offset) (hR : Tileable ps R) : Tileable ps S := by
  rw [heq] at hR
  exact (Tileable_translate_iff ps S offset).mpr hR

/-! ## Helper for Creating TileSets -/

/-- Create a TileSet from a function -/
def mkTileSet {ι : Type*} (ps : Protoset ι) (ιₜ : Type*) (f : ιₜ → PlacedTile ι) :
    TileSet ps ιₜ := ⟨f⟩

/-- Create a placed tile -/
def mkPlacedTile {ι : Type*} (i : ι) (x y : ℤ) (r : Fin 4) : PlacedTile ι :=
  ⟨i, (x, y), r⟩

/-! ## Rectangle Definition and Tilings -/

/-- An n×m rectangle as a finite set of cells from (0,0) to (n-1, m-1) -/
def rectangle (n m : ℕ) : Region :=
  (Finset.range n |>.map ⟨Int.ofNat, Int.ofNat_injective⟩) ×ˢ
  (Finset.range m |>.map ⟨Int.ofNat, Int.ofNat_injective⟩)

/-- The area of an n×m rectangle -/
@[simp] theorem rectangle_card (n m : ℕ) : (rectangle n m).card = n * m := by
  simp only [rectangle, Finset.card_product, Finset.card_map, Finset.card_range]

/-- Membership in a rectangle -/
theorem mem_rectangle {n m : ℕ} {c : Cell} :
    c ∈ rectangle n m ↔ 0 ≤ c.1 ∧ c.1 < n ∧ 0 ≤ c.2 ∧ c.2 < m := by
  simp only [rectangle, Finset.mem_product, Finset.mem_map, Finset.mem_range,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨x, hx, hxeq⟩, ⟨y, hy, hyeq⟩⟩
    simp only [← hxeq, ← hyeq]
    exact ⟨Int.natCast_nonneg x, Int.ofNat_lt.mpr hx, Int.natCast_nonneg y, Int.ofNat_lt.mpr hy⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨c.1.toNat, by omega, by simp; omega⟩, ⟨c.2.toNat, by omega, by simp; omega⟩⟩

/-- Swapping an n×m rectangle gives an m×n rectangle -/
theorem swap_rectangle (n m : ℕ) : swapRegion (rectangle n m) = rectangle m n := by
  ext ⟨x, y⟩
  simp only [swapRegion, rectangle, Finset.mem_image, Finset.mem_product, Finset.mem_map,
    Finset.mem_range, Function.Embedding.coeFn_mk, swapCell]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨⟨j, hj, rfl⟩, ⟨i, hi, rfl⟩⟩
  · rintro ⟨⟨j, hj, rfl⟩, ⟨i, hi, rfl⟩⟩
    exact ⟨(i, j), ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩, rfl⟩

/-! ## Rectangle Splitting and Combining -/

/-- A rectangle can be split horizontally -/
theorem rectangle_split_horizontal (a b m : ℕ) :
    rectangle (a + b) m = rectangle a m ∪ translateRegion (rectangle b m) (a, 0) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_union, mem_rectangle, translateRegion, Finset.mem_image, translateCell]
  constructor
  · rintro ⟨hx0, hxab, hy0, hym⟩
    by_cases hxa : x < a
    · left; exact ⟨hx0, hxa, hy0, hym⟩
    · right
      push_neg at hxa
      refine ⟨(x - a, y), ⟨by omega, by omega, hy0, hym⟩, ?_⟩
      simp only [Prod.mk.injEq]; omega
  · rintro (⟨hx0, hxa, hy0, hym⟩ | ⟨⟨x', y'⟩, ⟨hx0', hxb, hy0', hym'⟩, heq⟩)
    · exact ⟨hx0, by omega, hy0, hym⟩
    · simp only [Prod.mk.injEq] at heq
      omega

/-- The two parts of a horizontal split are disjoint -/
theorem rectangle_split_horizontal_disjoint (a b m : ℕ) :
    Disjoint (rectangle a m) (translateRegion (rectangle b m) (a, 0)) := by
  rw [Finset.disjoint_iff_ne]
  intro c hc d hd heq
  simp only [mem_rectangle] at hc
  simp only [translateRegion, Finset.mem_image, translateCell, mem_rectangle] at hd
  obtain ⟨⟨x', y'⟩, ⟨hx0', hxb, _, _⟩, rfl⟩ := hd
  -- d = (x' + a, y' + 0), c ∈ rectangle a m, c = d
  -- c.1 < a (from hc) but c.1 = x' + a ≥ a
  have hc1 : c.1 < ↑a := hc.2.1
  have hd1 : c.1 = x' + ↑a := by rw [heq]
  linarith

/-- A rectangle can be split vertically -/
theorem rectangle_split_vertical (n a b : ℕ) :
    rectangle n (a + b) = rectangle n a ∪ translateRegion (rectangle n b) (0, a) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_union, mem_rectangle, translateRegion, Finset.mem_image, translateCell]
  constructor
  · rintro ⟨hx0, hxn, hy0, hyab⟩
    by_cases hya : y < a
    · left; exact ⟨hx0, hxn, hy0, hya⟩
    · right
      push_neg at hya
      refine ⟨(x, y - a), ⟨hx0, hxn, by omega, by omega⟩, ?_⟩
      simp only [Prod.mk.injEq]; omega
  · rintro (⟨hx0, hxn, hy0, hya⟩ | ⟨⟨x', y'⟩, ⟨hx0', hxn', hy0', hyb⟩, heq⟩)
    · exact ⟨hx0, hxn, hy0, by omega⟩
    · simp only [Prod.mk.injEq] at heq
      omega

/-- The two parts of a vertical split are disjoint -/
theorem rectangle_split_vertical_disjoint (n a b : ℕ) :
    Disjoint (rectangle n a) (translateRegion (rectangle n b) (0, a)) := by
  rw [Finset.disjoint_iff_ne]
  intro c hc d hd heq
  simp only [mem_rectangle] at hc
  simp only [translateRegion, Finset.mem_image, translateCell, mem_rectangle] at hd
  obtain ⟨⟨x', y'⟩, ⟨_, _, hy0', hyb⟩, rfl⟩ := hd
  -- d = (x' + 0, y' + a), c ∈ rectangle n a, c = d
  -- c.2 < a but c.2 = y' + a ≥ a
  have hc2 : c.2 < ↑a := hc.2.2.2
  have hd2 : c.2 = y' + ↑a := by rw [heq]
  linarith

/-- If we can tile two horizontally adjacent rectangles, we can tile their union -/
theorem Tileable_horizontal_union {ι : Type*} (ps : Protoset ι) (a b m : ℕ)
    (h1 : Tileable ps (rectangle a m)) (h2 : Tileable ps (rectangle b m)) :
    Tileable ps (rectangle (a + b) m) := by
  rw [rectangle_split_horizontal]
  apply Tileable_union ps h1
  · exact Tileable_translate ps h2 (a, 0)
  · exact rectangle_split_horizontal_disjoint a b m

/-- If we can tile two vertically adjacent rectangles, we can tile their union -/
theorem Tileable_vertical_union {ι : Type*} (ps : Protoset ι) (n a b : ℕ)
    (h1 : Tileable ps (rectangle n a)) (h2 : Tileable ps (rectangle n b)) :
    Tileable ps (rectangle n (a + b)) := by
  rw [rectangle_split_vertical]
  apply Tileable_union ps h1
  · exact Tileable_translate ps h2 (0, a)
  · exact rectangle_split_vertical_disjoint n a b

/-! ## Generic Placement Enumeration

For any protoset, we can enumerate all placements that cover a given cell.
The key insight: for each (index, base cell, rotation), there's exactly one
translation that makes the rotated base cell land on the target.
-/

/-- A placed tile is contained in a region if all its cells are in the region -/
def PlacedTile.containedIn {ι : Type*} (ps : Protoset ι) (pt : PlacedTile ι) (r : Region) : Prop :=
  pt.cells ps ⊆ r

instance {ι : Type*} (ps : Protoset ι) (pt : PlacedTile ι) (r : Region) :
    Decidable (pt.containedIn ps r) :=
  inferInstanceAs (Decidable (pt.cells ps ⊆ r))

/-- A placed tile covers a cell if the cell is in its cells -/
def PlacedTile.coversCell {ι : Type*} (ps : Protoset ι) (pt : PlacedTile ι) (c : Cell) : Prop :=
  c ∈ pt.cells ps

instance {ι : Type*} (ps : Protoset ι) (pt : PlacedTile ι) (c : Cell) :
    Decidable (pt.coversCell ps c) :=
  inferInstanceAs (Decidable (c ∈ pt.cells ps))

/-- All placements of a single prototile that cover a given target cell.
    For each cell c in the prototile and each rotation r, the unique translation
    that maps rotateCell(c, r) to target is: target - rotateCell(c, r) -/
def allPlacementsCoveringProto {ι : Type*} (i : ι) (proto : Prototile) (target : Cell) :
    List (PlacedTile ι) :=
  proto.cells.flatMap fun baseCell =>
    (List.finRange 4).map fun r =>
      let rotated := rotateCell baseCell r
      ⟨i, (target.1 - rotated.1, target.2 - rotated.2), r⟩

/-- All placements from a protoset that cover a given target cell -/
def allPlacementsCovering {ι : Type*} (ps : Protoset ι) (indices : List ι) (target : Cell) :
    List (PlacedTile ι) :=
  indices.flatMap fun i => allPlacementsCoveringProto i (ps i) target

/-- Every placement produced by allPlacementsCoveringProto actually covers the target -/
theorem allPlacementsCoveringProto_covers {ι : Type*} (ps : Protoset ι) (i : ι)
    (target : Cell) (pt : PlacedTile ι)
    (hpt : pt ∈ allPlacementsCoveringProto i (ps i) target) :
    pt.coversCell ps target := by
  simp only [allPlacementsCoveringProto, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hpt
  obtain ⟨baseCell, hbase, r, rfl⟩ := hpt
  simp only [PlacedTile.coversCell, PlacedTile.cells, Finset.mem_image, translateCell]
  refine ⟨rotateCell baseCell r, ?_, ?_⟩
  · simp only [rotateProto, Finset.mem_image]
    exact ⟨baseCell, Prototile.mem_coe (ps i) baseCell |>.mpr hbase, rfl⟩
  · ext <;> ring

/-- allPlacementsCoveringProto is complete: any placement with index i covering target
    is in the list -/
theorem allPlacementsCoveringProto_complete {ι : Type*} (ps : Protoset ι) (i : ι)
    (target : Cell) (pt : PlacedTile ι) (hidx : pt.index = i)
    (hcover : pt.coversCell ps target) :
    pt ∈ allPlacementsCoveringProto i (ps i) target := by
  simp only [PlacedTile.coversCell, PlacedTile.cells] at hcover
  simp only [Finset.mem_image, translateCell] at hcover
  obtain ⟨rotatedCell, hrot, htrans⟩ := hcover
  simp only [rotateProto, Finset.mem_image] at hrot
  obtain ⟨origCell, horig, rfl⟩ := hrot
  simp only [allPlacementsCoveringProto, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and]
  -- origCell ∈ ps pt.index = ps i (by hidx)
  rw [hidx] at horig
  rw [(ps i).mem_coe] at horig
  refine ⟨origCell, horig, pt.rotation, ?_⟩
  -- Show pt equals the constructed placement
  rw [Prod.mk.injEq] at htrans
  obtain ⟨htx, hty⟩ := htrans
  obtain ⟨idx, trans, rot⟩ := pt
  simp only at hidx htx hty; subst hidx
  simp only [PlacedTile.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  ext <;> omega

/-- Placements covering a cell and contained in a region -/
def placementsCoveringIn {ι : Type*} (ps : Protoset ι) (indices : List ι)
    (target : Cell) (region : Region) : List (PlacedTile ι) :=
  (allPlacementsCovering ps indices target).filter fun pt => pt.containedIn ps region

/-! ## L-Tromino Protoset

The L-tromino is a single prototile that looks like:
```
  □
  □ □   (cells: (0,0), (0,1), (1,0))
```
-/

/-- The L-tromino shape, anchored at origin -/
def lTromino : Prototile := ⟨[(0, 0), (0, 1), (1, 0)], by decide⟩

/-- A protoset containing just the L-tromino -/
def lTrominoSet : Protoset Unit := ⟨fun _ => lTromino⟩

/-! ## Utility Lemmas -/

/-- Each L-tromino covers exactly 3 cells -/
theorem lTromino_covers_3 (pt : PlacedTile Unit) :
    (pt.cells lTrominoSet).card = 3 :=
  PlacedTile.cells_card lTrominoSet pt

/-! ## Existential Tileability -/

/-- A region is tileable by L-trominoes if there exists a valid tiling -/
def LTileable (r : Region) : Prop := Tileable lTrominoSet r

/-- 2×3 rectangle tiling -/
def tiling_2x3 : TileSet lTrominoSet (Fin 2) := ⟨![
  ⟨(), (0, 0), 0⟩,
  ⟨(), (1, 2), 2⟩
]⟩

theorem tiling_2x3_valid : tiling_2x3.Valid (rectangle 2 3) := by decide

/-- The 2×3 rectangle is tileable (basic example) -/
example : LTileable (rectangle 2 3) :=
  ⟨Fin 2, inferInstance, inferInstance, tiling_2x3, tiling_2x3_valid⟩

/-! ## Impossibility Results -/

/-- If a region is tileable, its area is divisible by 3 -/
theorem LTileable.area_div_3 {r : Region} (h : LTileable r) : r.card % 3 = 0 := by
  obtain ⟨ιₜ, _, _, t, hvalid⟩ := h
  rw [← hvalid.covers]
  rw [t.card_coveredCells hvalid.disjoint]
  have h3 : ∀ i : ιₜ, (t.cellsAt i).card = 3 := fun i => lTromino_covers_3 (t i)
  simp only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

/-- A 2×2 rectangle is not tileable (area 4 not divisible by 3) -/
example : ¬LTileable (rectangle 2 2) := by
  intro h
  have := h.area_div_3
  simp at this

/-- Any rotated L-tromino has two cells with different x-coordinates -/
theorem rotateProto_lTromino_x_span (r : Fin 4) :
    ∃ c1 c2 : Cell, c1 ∈ rotateProto lTromino r ∧
      c2 ∈ rotateProto lTromino r ∧ c1.1 ≠ c2.1 := by
  use rotateCell (0, 1) r, rotateCell (1, 0) r
  constructor
  · simp only [rotateProto, Finset.mem_image]
    exact ⟨(0, 1), by simp [lTromino], rfl⟩
  constructor
  · simp only [rotateProto, Finset.mem_image]
    exact ⟨(1, 0), by simp [lTromino], rfl⟩
  · fin_cases r <;> simp [rotateCell, rotateCell90]

/-- Any placed L-tromino has cells with different x-coordinates -/
theorem lTromino_placed_x_span (pt : PlacedTile Unit) :
    ∃ c1 c2 : Cell, c1 ∈ pt.cells lTrominoSet ∧ c2 ∈ pt.cells lTrominoSet ∧ c1.1 ≠ c2.1 := by
  obtain ⟨c1, c2, h1, h2, hne⟩ := rotateProto_lTromino_x_span pt.rotation
  simp only [PlacedTile.cells, lTrominoSet, Finset.mem_image, translateCell]
  exact ⟨(c1.1 + pt.translation.1, c1.2 + pt.translation.2),
         (c2.1 + pt.translation.1, c2.2 + pt.translation.2),
         ⟨c1, h1, rfl⟩, ⟨c2, h2, rfl⟩, by omega⟩

/-- A 1×n rectangle only has cells with x = 0 -/
theorem rectangle_1_n_x_eq_0 {n : ℕ} {c : Cell} (h : c ∈ rectangle 1 n) : c.1 = 0 := by
  simp only [rectangle, Finset.mem_product, Finset.mem_map, Finset.mem_range,
    Function.Embedding.coeFn_mk] at h
  obtain ⟨⟨x, hx, hx'⟩, _⟩ := h
  simp only [Int.ofNat_eq_natCast] at hx'
  omega

/-- A 1×n rectangle (n ≥ 1) is not tileable by L-trominoes -/
theorem not_tileable_1_by_n {n : ℕ} (hn : n ≥ 1) : ¬LTileable (rectangle 1 n) := by
  intro ⟨ιₜ, hfin, _, t, hvalid⟩
  -- Any placed L-tromino has cells with different x-coordinates
  -- But rectangle 1×n only has cells with x = 0
  -- So no L-tromino can fit
  by_cases hempty : IsEmpty ιₜ
  · -- No tiles means empty coverage, but rectangle is non-empty
    haveI := hempty
    have hcov : t.coveredCells = ∅ := by
      simp only [TileSet.coveredCells]
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro ⟨i, _⟩
      exact IsEmpty.false i
    rw [hvalid.covers] at hcov
    have : (rectangle 1 n).card ≥ 1 := by simp; omega
    simp [hcov] at this
  · -- There's at least one tile
    rw [not_isEmpty_iff] at hempty
    obtain ⟨i⟩ := hempty
    -- That tile has two cells with different x-coordinates
    obtain ⟨c1, c2, hc1, hc2, hne⟩ := lTromino_placed_x_span (t i)
    -- Both must be in the rectangle
    have hc1_rect : c1 ∈ rectangle 1 n := by
      rw [← hvalid.covers]
      simp only [TileSet.coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, hc1⟩
    have hc2_rect : c2 ∈ rectangle 1 n := by
      rw [← hvalid.covers]
      simp only [TileSet.coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, hc2⟩
    -- But both have x = 0
    have h1 := rectangle_1_n_x_eq_0 hc1_rect
    have h2 := rectangle_1_n_x_eq_0 hc2_rect
    omega

/-- A 1×3 rectangle is not tileable (special case) -/
theorem not_tileable_1x3 : ¬LTileable (rectangle 1 3) := not_tileable_1_by_n (by omega)

/-! ## Transformation Invariance

L-tileability is preserved under transformations of regions.
This lets us reduce symmetric cases (e.g., n×1 to 1×n).
-/

/-- The rotation that corresponds to applying swap before/after -/
def swapRotation : Fin 4 → Fin 4 := ![0, 3, 2, 1]

/-- Key lemma: swapping a rotated L-tromino gives another rotation -/
theorem swap_rotateProto_lTromino (r : Fin 4) :
    (rotateProto lTromino r).image swapCell = rotateProto lTromino (swapRotation r) := by
  fin_cases r <;> decide

/-- Swapping cells commutes with translation (with swapped offset) -/
theorem swapCell_translateCell (c offset : Cell) :
    swapCell (translateCell c offset) = translateCell (swapCell c) (swapCell offset) := by
  simp only [swapCell, translateCell]

/-- If a region is L-tileable, so is its swap -/
theorem LTileable_swap {r : Region} (h : LTileable r) : LTileable (swapRegion r) := by
  obtain ⟨ιₜ, _, _, t, hvalid⟩ := h
  -- Transform each placed tile: swap translation, adjust rotation
  let t' : TileSet lTrominoSet ιₜ := ⟨fun i =>
    ⟨(), swapCell (t i).translation, swapRotation (t i).rotation⟩⟩
  use ιₜ, inferInstance, inferInstance, t'
  -- Key: show that (t' i).cells = (t i).cells.image swapCell
  have cells_eq : ∀ i, t'.cellsAt i = (t.cellsAt i).image swapCell := by
    intro i
    simp only [TileSet.cellsAt, PlacedTile.cells, lTrominoSet]
    -- t'.translation = swapCell (t.translation), so t'.translation.1 = t.translation.2
    have htrans : (t' i).translation = swapCell ((t i).translation) := rfl
    ext c
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      -- b is in rotateProto lTromino (swapRotation (t i).rotation)
      have hswap := swap_rotateProto_lTromino (t i).rotation
      rw [← hswap] at hb
      simp only [Finset.mem_image] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      use translateCell b' (t i).translation
      refine ⟨⟨b', hb', rfl⟩, ?_⟩
      simp only [translateCell, swapCell]
      -- Need: (b'.2 + t.trans.2, b'.1 + t.trans.1) = (b'.2 + t'.trans.1, b'.1 + t'.trans.2)
      -- Since t'.trans = swapCell t.trans, t'.trans.1 = t.trans.2 and t'.trans.2 = t.trans.1
      rfl
    · rintro ⟨c', ⟨b, hb, rfl⟩, rfl⟩
      use swapCell b
      have hswap := swap_rotateProto_lTromino (t i).rotation
      rw [← hswap]
      refine ⟨Finset.mem_image_of_mem _ hb, ?_⟩
      simp only [translateCell, swapCell]
      rfl
  constructor
  · -- Disjointness preserved (swap is injective)
    intro i j hij
    rw [cells_eq, cells_eq]
    have hdisj := hvalid.disjoint i j hij
    rw [Finset.disjoint_iff_ne] at hdisj ⊢
    intro c hc d hd
    simp only [Finset.mem_image] at hc hd
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨d', hd', rfl⟩ := hd
    intro heq
    have : c' = d' := swapCell_injective heq
    exact hdisj c' hc' d' hd' this
  · -- Coverage: show t'.coveredCells = swapRegion r
    simp only [TileSet.coveredCells, swapRegion, ← hvalid.covers]
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨i, hci⟩
      rw [cells_eq] at hci
      simp only [Finset.mem_image] at hci
      obtain ⟨c', hc', rfl⟩ := hci
      exact ⟨c', ⟨i, hc'⟩, rfl⟩
    · rintro ⟨c', ⟨i, hi⟩, rfl⟩
      use i
      rw [cells_eq]
      exact Finset.mem_image_of_mem _ hi

/-- An n×1 rectangle (n ≥ 1) is not tileable by L-trominoes -/
theorem not_tileable_n_by_1 {n : ℕ} (hn : n ≥ 1) : ¬LTileable (rectangle n 1) := by
  intro h
  have h' := LTileable_swap h
  rw [swap_rectangle] at h'
  exact not_tileable_1_by_n hn h'

/-! ## 3×odd Impossibility -/

/-- The 3×2 rectangle used in the 3×odd impossibility proof -/
def rect3x2 : Region := rectangle 3 2

/-! ## Key Lemmas for the 3×odd Impossibility Proof -/

/-- An L-tromino has y-span at most 1: all cells have y-coordinates within 1 of each other -/
theorem lTromino_y_span_2 (pt : PlacedTile Unit) (c1 c2 : Cell)
    (h1 : c1 ∈ pt.cells lTrominoSet) (h2 : c2 ∈ pt.cells lTrominoSet) :
    (c1.2 - c2.2).natAbs ≤ 1 := by
  simp only [PlacedTile.cells, Finset.mem_image] at h1 h2
  obtain ⟨r1, hr1, hc1⟩ := h1
  obtain ⟨r2, hr2, hc2⟩ := h2
  simp only [rotateProto, Finset.mem_image] at hr1 hr2
  obtain ⟨o1, ho1, hro1⟩ := hr1
  obtain ⟨o2, ho2, hro2⟩ := hr2
  -- o1, o2 ∈ lTromino.cells = [(0,0), (0,1), (1,0)]
  simp only [lTrominoSet, lTromino] at ho1 ho2
  subst hc1 hc2 hro1 hro2
  simp only [translateCell]
  -- Now do case analysis on o1, o2, and rotation
  obtain ⟨_, _, rot⟩ := pt
  have h1' : o1 ∈ ([(0, 0), (0, 1), (1, 0)] : List Cell) := ho1
  have h2' : o2 ∈ ([(0, 0), (0, 1), (1, 0)] : List Cell) := ho2
  fin_cases rot <;> fin_cases h1' <;> fin_cases h2' <;> simp [rotateCell, rotateCell90]

/-- A tile covering (0,0) has all cells with y < 2 (assuming y ≥ 0) -/
theorem tile_covering_00_y_bound (pt : PlacedTile Unit)
    (hcover : pt.coversCell lTrominoSet (0, 0))
    (c : Cell) (hc : c ∈ pt.cells lTrominoSet) (_hy_nonneg : c.2 ≥ 0) :
    c.2 < 2 := by
  have hspan := lTromino_y_span_2 pt (0, 0) c hcover hc
  omega

/-- A tile covering (2,0) has all cells with y < 2 (assuming y ≥ 0) -/
theorem tile_covering_20_y_bound (pt : PlacedTile Unit)
    (hcover : pt.coversCell lTrominoSet (2, 0))
    (c : Cell) (hc : c ∈ pt.cells lTrominoSet) (_hy_nonneg : c.2 ≥ 0) :
    c.2 < 2 := by
  have hspan := lTromino_y_span_2 pt (2, 0) c hcover hc
  omega

/-- An L-tromino has x-span at most 1: all cells have x-coordinates within 1 of each other -/
theorem lTromino_x_span_2 (pt : PlacedTile Unit) (c1 c2 : Cell)
    (h1 : c1 ∈ pt.cells lTrominoSet) (h2 : c2 ∈ pt.cells lTrominoSet) :
    (c1.1 - c2.1).natAbs ≤ 1 := by
  simp only [PlacedTile.cells, Finset.mem_image] at h1 h2
  obtain ⟨r1, hr1, hc1⟩ := h1
  obtain ⟨r2, hr2, hc2⟩ := h2
  simp only [rotateProto, Finset.mem_image] at hr1 hr2
  obtain ⟨o1, ho1, hro1⟩ := hr1
  obtain ⟨o2, ho2, hro2⟩ := hr2
  simp only [lTrominoSet, lTromino] at ho1 ho2
  subst hc1 hc2 hro1 hro2
  simp only [translateCell]
  obtain ⟨_, _, rot⟩ := pt
  have h1' : o1 ∈ ([(0, 0), (0, 1), (1, 0)] : List Cell) := ho1
  have h2' : o2 ∈ ([(0, 0), (0, 1), (1, 0)] : List Cell) := ho2
  fin_cases rot <;> fin_cases h1' <;> fin_cases h2' <;> simp [rotateCell, rotateCell90]

/-- If a tile covers (0,0) and is contained in rectangle 3 n (n ≥ 2),
    then it's contained in rect3x2 -/
theorem tile_covering_00_in_3x2 (n : ℕ) (_hn : n ≥ 2)
    (pt : PlacedTile Unit)
    (hcover : pt.coversCell lTrominoSet (0, 0))
    (hcontained : pt.containedIn lTrominoSet (rectangle 3 n)) :
    pt.containedIn lTrominoSet rect3x2 := by
  intro c hc
  have hc_rect := hcontained hc
  rw [mem_rectangle] at hc_rect
  simp only [rect3x2]
  rw [mem_rectangle]
  refine ⟨hc_rect.1, hc_rect.2.1, hc_rect.2.2.1, ?_⟩
  exact tile_covering_00_y_bound pt hcover c hc hc_rect.2.2.1

/-- If a tile covers (2,0) and is contained in rectangle 3 n (n ≥ 2),
    then it's contained in rect3x2 -/
theorem tile_covering_20_in_3x2 (n : ℕ) (_hn : n ≥ 2)
    (pt : PlacedTile Unit)
    (hcover : pt.coversCell lTrominoSet (2, 0))
    (hcontained : pt.containedIn lTrominoSet (rectangle 3 n)) :
    pt.containedIn lTrominoSet rect3x2 := by
  intro c hc
  have hc_rect := hcontained hc
  rw [mem_rectangle] at hc_rect
  simp only [rect3x2]
  rw [mem_rectangle]
  refine ⟨hc_rect.1, hc_rect.2.1, hc_rect.2.2.1, ?_⟩
  exact tile_covering_20_y_bound pt hcover c hc hc_rect.2.2.1

/-- Tiles covering (0,0) and (2,0) in a 3×n tiling (n≥2) must be disjoint -/
theorem tiles_00_20_disjoint {ιₜ : Type*} [Fintype ιₜ] [DecidableEq ιₜ]
    (ts : TileSet lTrominoSet ιₜ) (n : ℕ) (_hn : n ≥ 2)
    (hvalid : ts.Valid (rectangle 3 n))
    (i j : ιₜ) (_hi : (ts i).coversCell lTrominoSet (0, 0))
    (_hj : (ts j).coversCell lTrominoSet (2, 0)) (hij : i ≠ j) :
    Disjoint ((ts i).cells lTrominoSet) ((ts j).cells lTrominoSet) :=
  hvalid.disjoint_tiles i j hij

/-- The two tiles covering (0,0) and (2,0) cover exactly rect3x2 -/
theorem tiles_00_20_cover_3x2 {ιₜ : Type*} [Fintype ιₜ] [DecidableEq ιₜ]
    (ts : TileSet lTrominoSet ιₜ) (n : ℕ) (hn : n ≥ 2)
    (hvalid : ts.Valid (rectangle 3 n))
    (i j : ιₜ) (hi : (ts i).coversCell lTrominoSet (0, 0))
    (hj : (ts j).coversCell lTrominoSet (2, 0)) (hij : i ≠ j) :
    ((ts i).cells lTrominoSet) ∪ ((ts j).cells lTrominoSet) = rect3x2 := by
  -- Both tiles are contained in rect3x2
  have hci : (ts i).containedIn lTrominoSet (rectangle 3 n) := hvalid.tile_contained i
  have hcj : (ts j).containedIn lTrominoSet (rectangle 3 n) := hvalid.tile_contained j
  have hi_3x2 := tile_covering_00_in_3x2 n hn (ts i) hi hci
  have hj_3x2 := tile_covering_20_in_3x2 n hn (ts j) hj hcj
  -- They are disjoint
  have hdisj := tiles_00_20_disjoint ts n hn hvalid i j hi hj hij
  -- Each has 3 cells (L-tromino has 3 cells)
  have hcard_i : ((ts i).cells lTrominoSet).card = 3 := lTromino_covers_3 (ts i)
  have hcard_j : ((ts j).cells lTrominoSet).card = 3 := lTromino_covers_3 (ts j)
  have hcard_rect : rect3x2.card = 6 := by simp [rect3x2]
  -- Union is subset of rect3x2
  have hunion_sub : (ts i).cells lTrominoSet ∪ (ts j).cells lTrominoSet ⊆ rect3x2 :=
    Finset.union_subset hi_3x2 hj_3x2
  -- Union has 6 cells (3 + 3 since disjoint)
  have hcard_union : ((ts i).cells lTrominoSet ∪ (ts j).cells lTrominoSet).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisj, hcard_i, hcard_j]
  -- Equal by cardinality
  exact Finset.eq_of_subset_of_card_le hunion_sub (by omega)

/-- The remaining tiles (excluding i and j) cover exactly rectangle 3 n minus rect3x2 -/
theorem remaining_tiles_cover {ιₜ : Type*} [Fintype ιₜ] [DecidableEq ιₜ]
    (ts : TileSet lTrominoSet ιₜ) (n : ℕ) (hn : n ≥ 2)
    (hvalid : ts.Valid (rectangle 3 n))
    (i j : ιₜ) (hi : (ts i).coversCell lTrominoSet (0, 0))
    (hj : (ts j).coversCell lTrominoSet (2, 0)) (hij : i ≠ j) :
    (Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j)).biUnion (fun k => (ts k).cells lTrominoSet) =
    rectangle 3 n \ rect3x2 := by
  -- The two tiles cover rect3x2
  have hcover_ij := tiles_00_20_cover_3x2 ts n hn hvalid i j hi hj hij
  -- The full tiling covers rectangle 3 n
  have hcover_all : ts.coveredCells = rectangle 3 n := hvalid.covers
  -- The remaining tiles cover the complement
  ext c
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff]
  constructor
  · -- If c is covered by some tile k ≠ i, j, then c ∈ rectangle 3 n \ rect3x2
    rintro ⟨k, ⟨hki, hkj⟩, hck⟩
    constructor
    · -- c ∈ rectangle 3 n (from validity)
      rw [← hcover_all]
      simp only [TileSet.coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨k, hck⟩
    · -- c ∉ rect3x2 (disjoint from tiles i and j)
      intro hc_rect
      rw [← hcover_ij] at hc_rect
      simp only [Finset.mem_union] at hc_rect
      rcases hc_rect with hci | hcj
      · -- c ∈ (ts i).cells, but k ≠ i and tiles are disjoint
        have hdisj := hvalid.disjoint_tiles k i hki
        exact Finset.disjoint_left.mp hdisj hck hci
      · -- c ∈ (ts j).cells, but k ≠ j and tiles are disjoint
        have hdisj := hvalid.disjoint_tiles k j hkj
        exact Finset.disjoint_left.mp hdisj hck hcj
  · -- If c ∈ rectangle 3 n \ rect3x2, then c is covered by some tile k ≠ i, j
    rintro ⟨hc_rect, hc_not_3x2⟩
    -- c must be covered by some tile
    rw [← hcover_all] at hc_rect
    simp only [TileSet.coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and] at hc_rect
    obtain ⟨k, hck⟩ := hc_rect
    -- k cannot be i or j (since c ∉ rect3x2 but tiles i,j cover rect3x2)
    refine ⟨k, ⟨?_, ?_⟩, hck⟩
    · -- k ≠ i
      intro heq; subst heq
      rw [← hcover_ij] at hc_not_3x2
      exact hc_not_3x2 (Finset.mem_union_left _ hck)
    · -- k ≠ j
      intro heq; subst heq
      rw [← hcover_ij] at hc_not_3x2
      exact hc_not_3x2 (Finset.mem_union_right _ hck)

/-- rectangle 3 n minus rect3x2 equals the translated rectangle 3 (n-2) -/
theorem rectangle_minus_3x2 (n : ℕ) (hn : n ≥ 2) :
    rectangle 3 n \ rect3x2 = translateRegion (rectangle 3 (n - 2)) (0, 2) := by
  ext ⟨x, y⟩
  simp only [Finset.mem_sdiff, mem_rectangle, rect3x2, translateRegion, Finset.mem_image,
    translateCell, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hx0, hxn, hy0, hyn⟩, hnotin⟩
    -- y must be ≥ 2 (otherwise would be in rect3x2)
    have hy2 : y ≥ 2 := by
      by_contra h
      push_neg at h
      exact hnotin ⟨hx0, hxn, hy0, h⟩
    refine ⟨(x, y - 2), ⟨by omega, by omega, by omega, by omega⟩, by omega, by omega⟩
  · rintro ⟨⟨x', y'⟩, ⟨hx0', hxn', hy0', hyn'⟩, hxeq, hyeq⟩
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, ?_⟩
    intro ⟨_, _, _, hy2⟩
    omega

/-! ## Full Rectangle Characterization -/

/-- The conditions for a non-trivial n×m rectangle to be tileable by L-trominoes.
    Note: The empty rectangle (n=0 or m=0) is always tileable by 0 tiles.
    For n,m ≥ 1, the conditions are:
    - Area divisible by 3
    - Neither dimension is 1
    - Not 3×odd or odd×3 -/
def RectTileableConditions (n m : ℕ) : Prop :=
  n = 0 ∨ m = 0 ∨ (                      -- Empty is tileable
    n * m % 3 = 0 ∧                       -- Area divisible by 3
    n ≥ 2 ∧ m ≥ 2 ∧                       -- Neither dimension is 1
    ¬(n = 3 ∧ Odd m) ∧                    -- Not 3×odd
    ¬(Odd n ∧ m = 3))                     -- Not odd×3

/-- The empty region is L-tileable -/
theorem empty_LTileable : LTileable ∅ :=
  empty_tileable lTrominoSet

/-! ## Combining Tilings -/

/-- A translated L-tileable region is L-tileable -/
theorem LTileable_translate {r : Region} (h : LTileable r) (offset : Cell) :
    LTileable (translateRegion r offset) :=
  Tileable_translate lTrominoSet h offset

/-- L-tileability is preserved by translation (both directions) -/
theorem LTileable_translate_iff (r : Region) (offset : Cell) :
    LTileable r ↔ LTileable (translateRegion r offset) :=
  Tileable_translate_iff lTrominoSet r offset

/-- If R = S.image(translate by offset) and R is L-tileable, then S is L-tileable -/
theorem LTileable_of_translate_eq {R S : Region} (offset : Cell)
    (heq : R = translateRegion S offset) (hR : LTileable R) : LTileable S :=
  Tileable_of_translate_eq lTrominoSet offset heq hR

/-! ## 3×odd Impossibility (requires translation invariance) -/

/-- A 3×(2k+1) rectangle is not tileable by L-trominoes.

Proof by induction on k:
- Base case (k=0): 3×1 is not tileable (too thin)
- Inductive step (k' → k'+1): For 3×(2k'+3), if it were tileable,
  the first 3×2 strip must be exactly covered by 2 tiles (case analysis
  on how to cover corners (0,0) and (2,0)), leaving 3×(2k'+1).
  But 3×(2k'+1) is not tileable by IH, contradiction.
-/
theorem not_tileable_3_by_odd (k : ℕ) : ¬LTileable (rectangle 3 (2 * k + 1)) := by
  induction k with
  | zero =>
    -- Base case: 3×1 is not tileable (height 1)
    simp only [Nat.mul_zero, Nat.zero_add]
    exact not_tileable_n_by_1 (by omega)
  | succ k' ih =>
    -- Inductive step: 3×(2k'+3) is not tileable, assuming 3×(2k'+1) is not
    have heq : 2 * (k' + 1) + 1 = 2 * k' + 3 := by omega
    rw [heq]
    intro ⟨ιₜ, hfin, hdec, ts, hvalid⟩
    -- The rectangle 3×(2k'+3) contains (0,0) and (2,0), which must be covered
    have h00_in : (0, 0) ∈ rectangle 3 (2 * k' + 3) := by rw [mem_rectangle]; omega
    have h20_in : (2, 0) ∈ rectangle 3 (2 * k' + 3) := by rw [mem_rectangle]; omega
    rw [← hvalid.covers] at h00_in h20_in
    simp only [TileSet.coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and] at h00_in h20_in
    obtain ⟨i, hi⟩ := h00_in
    obtain ⟨j, hj⟩ := h20_in
    -- i ≠ j because tiles covering (0,0) and (2,0) are distinct (x-span is ≤ 1)
    have hij : i ≠ j := by
      intro h; subst h
      have hspan := lTromino_x_span_2 (ts i) (0, 0) (2, 0) hi hj
      simp at hspan
    -- The remaining tiles (excluding i and j) cover rectangle 3 (2k'+3) \ rect3x2
    have hremain := remaining_tiles_cover ts (2 * k' + 3) (by omega) hvalid i j hi hj hij
    -- This region equals rectangle 3 (2k'+1) translated by (0, 2)
    have hminus := rectangle_minus_3x2 (2 * k' + 3) (by omega)
    have h2k1 : 2 * k' + 3 - 2 = 2 * k' + 1 := by omega
    rw [h2k1] at hminus
    -- The remaining region is L-tileable (by the remaining tiles)
    have hremain_tileable : LTileable (rectangle 3 (2 * k' + 3) \ rect3x2) := by
      let remaining := Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j)
      let ts_remain : TileSet lTrominoSet remaining := ⟨fun ⟨k, _⟩ => ts k⟩
      refine ⟨remaining, inferInstance, inferInstance, ts_remain, ?_⟩
      constructor
      · -- Pairwise disjoint
        intro ⟨a, _⟩ ⟨b, _⟩ hab
        simp only [ne_eq, Subtype.mk.injEq] at hab
        exact hvalid.disjoint_tiles a b hab
      · -- Covers the remaining region
        rw [← hremain]
        ext c
        simp only [TileSet.coveredCells, TileSet.cellsAt, Finset.mem_biUnion,
          Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨k, hk⟩, hc⟩
          simp only [remaining, Finset.mem_filter, Finset.mem_univ, true_and] at hk
          exact ⟨k, hk, hc⟩
        · rintro ⟨k, hk, hc⟩
          refine ⟨⟨k, ?_⟩, hc⟩
          simp only [remaining, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hk
    -- So rectangle 3 (2k'+1) is L-tileable (by translation invariance), contradicting IH
    apply ih
    exact LTileable_of_translate_eq (0, 2) hminus hremain_tileable

/-- A (2k+1)×3 rectangle is not tileable by L-trominoes -/
theorem not_tileable_odd_by_3 (k : ℕ) : ¬LTileable (rectangle (2 * k + 1) 3) := by
  -- Use symmetry: if (2k+1)×3 is tileable, then 3×(2k+1) would be tileable
  intro h
  have h' := LTileable_swap h
  rw [swap_rectangle] at h'
  exact not_tileable_3_by_odd k h'

/-- rectangle 0 m = ∅ -/
theorem rectangle_0_m (m : ℕ) : rectangle 0 m = ∅ := by
  simp [rectangle]

/-- rectangle n 0 = ∅ -/
theorem rectangle_n_0 (n : ℕ) : rectangle n 0 = ∅ := by
  simp [rectangle]

/-! ## Rectangle Decomposition Lemmas -/

/-- Swapping dimensions preserves tileability (90° rotation) -/
theorem LTileable_swap_rectangle (n m : ℕ) :
    LTileable (rectangle n m) ↔ LTileable (rectangle m n) := by
  constructor
  · intro h
    have h' := LTileable_swap h
    rwa [swap_rectangle] at h'
  · intro h
    have h' := LTileable_swap h
    rwa [swap_rectangle] at h'

/-- If we can tile two horizontally adjacent rectangles, we can tile their union -/
theorem LTileable_horizontal_union (a b m : ℕ)
    (h1 : LTileable (rectangle a m)) (h2 : LTileable (rectangle b m)) :
    LTileable (rectangle (a + b) m) :=
  Tileable_horizontal_union lTrominoSet a b m h1 h2

/-- If we can tile two vertically adjacent rectangles, we can tile their union -/
theorem LTileable_vertical_union (n a b : ℕ)
    (h1 : LTileable (rectangle n a)) (h2 : LTileable (rectangle n b)) :
    LTileable (rectangle n (a + b)) :=
  Tileable_vertical_union lTrominoSet n a b h1 h2

/-! ## Base Case Tilings -/

/-- 2×3 is tileable -/
theorem tileable_2x3 : LTileable (rectangle 2 3) :=
  ⟨Fin 2, inferInstance, inferInstance, tiling_2x3, tiling_2x3_valid⟩

/-- 3×2 is tileable -/
theorem tileable_3x2 : LTileable (rectangle 3 2) := by
  rw [← LTileable_swap_rectangle]
  exact tileable_2x3

/-- 3×6 is tileable (3 copies of 3×2) -/
theorem tileable_3x6 : LTileable (rectangle 3 6) := by
  have h1 := tileable_3x2
  have h12 := LTileable_vertical_union 3 2 2 h1 h1
  exact LTileable_vertical_union 3 4 2 h12 h1

/-- 2×6 is tileable (2 copies of 2×3) -/
theorem tileable_2x6 : LTileable (rectangle 2 6) :=
  LTileable_vertical_union 2 3 3 tileable_2x3 tileable_2x3

/-- 5×6 is tileable (2×6 + 3×6) -/
theorem tileable_5x6 : LTileable (rectangle 5 6) :=
  LTileable_horizontal_union 2 3 6 tileable_2x6 tileable_3x6

/-- 6×5 is tileable (by swap) -/
theorem tileable_6x5 : LTileable (rectangle 6 5) := by
  rw [← LTileable_swap_rectangle]
  exact tileable_5x6

/-- 2×9 is tileable (3 copies of 2×3) -/
theorem tileable_2x9 : LTileable (rectangle 2 9) := by
  have h1 := tileable_2x3
  have h12 := LTileable_vertical_union 2 3 3 h1 h1
  exact LTileable_vertical_union 2 6 3 h12 h1

/-- Explicit tiling of the 5×9 rectangle with 15 L-trominoes.
This is a special base case that needs an irregular tiling.
The key insight is that 5×9 cannot be decomposed into rectangular pieces
that are all individually L-tileable. We need tiles that cross boundaries. -/
def tiling_5x9 : TileSet lTrominoSet (Fin 15) := ⟨![
  ⟨(), (1, 0), 1⟩,   -- Tile 0: covers (0,0), (1,0), (1,1)
  ⟨(), (0, 2), 3⟩,   -- Tile 1: covers (0,1), (0,2), (1,2)
  ⟨(), (0, 4), 3⟩,   -- Tile 2: covers (0,3), (0,4), (1,4)
  ⟨(), (2, 3), 2⟩,   -- Tile 3: covers (1,3), (2,2), (2,3)
  ⟨(), (0, 6), 3⟩,   -- Tile 4: covers (0,5), (0,6), (1,6)
  ⟨(), (2, 5), 2⟩,   -- Tile 5: covers (1,5), (2,4), (2,5)
  ⟨(), (0, 8), 3⟩,   -- Tile 6: covers (0,7), (0,8), (1,8)
  ⟨(), (2, 7), 1⟩,   -- Tile 7: covers (1,7), (2,7), (2,8)
  ⟨(), (3, 6), 1⟩,   -- Tile 8: covers (2,6), (3,6), (3,7)
  ⟨(), (4, 8), 2⟩,   -- Tile 9: covers (3,8), (4,7), (4,8)
  ⟨(), (4, 5), 1⟩,   -- Tile 10: covers (3,5), (4,5), (4,6)
  ⟨(), (2, 1), 3⟩,   -- Tile 11: covers (2,0), (2,1), (3,1)
  ⟨(), (4, 0), 1⟩,   -- Tile 12: covers (3,0), (4,0), (4,1)
  ⟨(), (4, 2), 1⟩,   -- Tile 13: covers (3,2), (4,2), (4,3)
  ⟨(), (3, 4), 3⟩    -- Tile 14: covers (3,3), (3,4), (4,4)
]⟩

theorem tiling_5x9_valid : tiling_5x9.Valid (rectangle 5 9) := by decide

theorem tileable_5x9 : LTileable (rectangle 5 9) :=
  ⟨Fin 15, inferInstance, inferInstance, tiling_5x9, tiling_5x9_valid⟩

/-- 9×5 is tileable (by swap) -/
theorem tileable_9x5 : LTileable (rectangle 9 5) := by
  rw [← LTileable_swap_rectangle]
  exact tileable_5x9

/-- 6×3 is tileable (3 copies of 2×3) -/
theorem tileable_6x3 : LTileable (rectangle 6 3) := by
  have h1 := tileable_2x3
  have h12 := LTileable_horizontal_union 2 2 3 h1 h1
  exact LTileable_horizontal_union 4 2 3 h12 h1

/-- 3×(2k) is tileable for k ≥ 1 -/
theorem tileable_3x_even (k : ℕ) (hk : k ≥ 1) : LTileable (rectangle 3 (2 * k)) := by
  induction k with
  | zero => omega
  | succ k' ih =>
    cases Nat.eq_zero_or_pos k' with
    | inl hzero =>
      subst hzero
      exact tileable_3x2
    | inr hpos =>
      have hk' : k' ≥ 1 := hpos
      have h1 := ih hk'
      have h2 := tileable_3x2
      have heq : 2 * (k' + 1) = 2 * k' + 2 := by ring
      rw [heq]
      exact LTileable_vertical_union 3 (2 * k') 2 h1 h2

/-- (2k)×3 is tileable for k ≥ 1 -/
theorem tileable_even_x3 (k : ℕ) (hk : k ≥ 1) : LTileable (rectangle (2 * k) 3) := by
  rw [← LTileable_swap_rectangle]
  exact tileable_3x_even k hk

/-- 2×(3k) is tileable for any k -/
theorem tileable_2x_mult3 (k : ℕ) : LTileable (rectangle 2 (3 * k)) := by
  induction k with
  | zero => simp only [Nat.mul_zero, rectangle_n_0]; exact empty_LTileable
  | succ k' ih =>
    have heq : 3 * (k' + 1) = 3 * k' + 3 := by ring
    rw [heq]
    exact LTileable_vertical_union 2 (3 * k') 3 ih tileable_2x3

/-- (3k)×2 is tileable for any k -/
theorem tileable_mult3_x2 (k : ℕ) : LTileable (rectangle (3 * k) 2) := by
  rw [← LTileable_swap_rectangle]
  exact tileable_2x_mult3 k

/-- If n is even (n = 2j, j ≥ 1) and m is a multiple of 3, then n × m is tileable -/
theorem tileable_even_mult3 (j k : ℕ) (hj : j ≥ 1) :
    LTileable (rectangle (2 * j) (3 * k)) := by
  -- n = 2j, so rectangle (2j) (3k) = j copies of 2 × (3k)
  -- Each 2 × (3k) is tileable
  induction j with
  | zero => omega
  | succ j' ih =>
    cases Nat.eq_zero_or_pos j' with
    | inl hzero =>
      subst hzero
      exact tileable_2x_mult3 k
    | inr hpos' =>
      have h1 := ih hpos'
      have h2 := tileable_2x_mult3 k
      have heq : 2 * (j' + 1) = 2 * j' + 2 := by ring
      rw [heq]
      exact LTileable_horizontal_union (2 * j') 2 (3 * k) h1 h2

/-- 3 × (6j) is tileable for any j -/
theorem tileable_3x6j (j : ℕ) : LTileable (rectangle 3 (6 * j)) := by
  induction j with
  | zero => simp only [Nat.mul_zero, rectangle_n_0]; exact empty_LTileable
  | succ j' ih =>
    have heq : 6 * (j' + 1) = 6 * j' + 6 := by ring
    rw [heq]
    exact LTileable_vertical_union 3 (6 * j') 6 ih tileable_3x6

/-- 5 × (6j) is tileable for any j -/
theorem tileable_5x6j (j : ℕ) : LTileable (rectangle 5 (6 * j)) := by
  induction j with
  | zero => simp only [Nat.mul_zero, rectangle_n_0]; exact empty_LTileable
  | succ j' ih =>
    have heq : 6 * (j' + 1) = 6 * j' + 6 := by ring
    rw [heq]
    exact LTileable_vertical_union 5 (6 * j') 6 ih tileable_5x6

/-- 5 × (9 + 6j) is tileable: 5×9 base case plus j copies of 5×6 -/
theorem tileable_5x_9plus6j (j : ℕ) : LTileable (rectangle 5 (9 + 6 * j)) :=
  LTileable_vertical_union 5 9 (6 * j) tileable_5x9 (tileable_5x6j j)

/-- n × (6j) is tileable for odd n ≥ 3, any j ≥ 0 (simple induction on n) -/
theorem tileable_odd_x_6j (n j : ℕ) (hn : n ≥ 3) (hodd : Odd n) :
    LTileable (rectangle n (6 * j)) := by
  obtain ⟨i, hi⟩ := hodd  -- n = 2i + 1
  induction i using Nat.strong_induction_on generalizing n with
  | _ i ih =>
    match i with
    | 0 => simp only [Nat.mul_zero, Nat.zero_add] at hi hn; omega
    | 1 => subst hi; exact tileable_3x6j j  -- n = 3
    | 2 => subst hi; exact tileable_5x6j j  -- n = 5
    | Nat.succ (Nat.succ (Nat.succ i')) =>
      -- n = 2(i'+3) + 1 ≥ 7: strip 2 × 6j
      have h2 : LTileable (rectangle 2 (6 * j)) := by
        convert tileable_2x_mult3 (2 * j) using 2; ring
      have hn2_eq : n - 2 = 2 * (i' + 2) + 1 := by omega
      have h_rest := ih (i' + 2) (by omega) (n - 2) (by omega) hn2_eq
      convert LTileable_horizontal_union (n - 2) 2 (6 * j) h_rest h2 using 2; omega

/-- 5 × (6i + 3) is tileable for i ≥ 1 (equals 5 × (9 + 6(i-1))) -/
theorem tileable_5x_6iplus3 (i : ℕ) (hi : i ≥ 1) : LTileable (rectangle 5 (6 * i + 3)) := by
  have heq : 6 * i + 3 = 9 + 6 * (i - 1) := by omega
  rw [heq]
  exact tileable_5x_9plus6j (i - 1)

/-- n × (6i + 3) is tileable for odd n ≥ 5, i ≥ 1 -/
theorem tileable_odd_ge5_x_6iplus3 (n i : ℕ) (hn : n ≥ 5) (hodd : Odd n) (hi : i ≥ 1) :
    LTileable (rectangle n (6 * i + 3)) := by
  obtain ⟨k, hk⟩ := hodd  -- n = 2k + 1
  induction k using Nat.strong_induction_on generalizing n with
  | _ k ih =>
    match k with
    | 0 => simp only [Nat.mul_zero, Nat.zero_add] at hk hn; omega
    | 1 => simp only [hk] at hn; omega  -- n = 3 < 5
    | 2 => subst hk; exact tileable_5x_6iplus3 i hi  -- n = 5
    | Nat.succ (Nat.succ (Nat.succ k')) =>
      -- n = 2(k'+3) + 1 ≥ 7: strip 2 × (6i + 3)
      have h2 : LTileable (rectangle 2 (6 * i + 3)) := by
        convert tileable_2x_mult3 (2 * i + 1) using 2; ring
      have hn2_eq : n - 2 = 2 * (k' + 2) + 1 := by omega
      have h_rest := ih (k' + 2) (by omega) (n - 2) (by omega) hn2_eq
      convert LTileable_horizontal_union (n - 2) 2 (6 * i + 3) h_rest h2 using 2; omega

/-- n × (3k) is tileable for odd n ≥ 3, k ≥ 2, with n ≠ 3 when k is odd -/
theorem tileable_odd_x_mult3 (n k : ℕ) (hn : n ≥ 3) (hodd : Odd n) (hk : k ≥ 2)
    (h_not_3_odd : ¬(n = 3 ∧ Odd k)) : LTileable (rectangle n (3 * k)) := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · -- k = 2j even, so 3k = 6j
    convert tileable_odd_x_6j n j hn hodd using 2; ring
  · -- k = 2j + 1 odd ≥ 3, so 3k = 6j + 3, need j ≥ 1 (since k = 2j+1 ≥ 2 means j ≥ 1)
    have hj : j ≥ 1 := by
      by_contra hlt; push_neg at hlt
      have hj0 : j = 0 := by omega
      rw [hj0] at hk; omega  -- k = 1 contradicts k ≥ 2
    -- Since k is odd and h_not_3_odd, n ≠ 3, so n ≥ 5
    have hn5 : n ≥ 5 := by
      by_contra hlt; push_neg at hlt
      obtain ⟨i, hi⟩ := hodd  -- n = 2i + 1
      have hn3 : n = 3 := by omega
      exact h_not_3_odd ⟨hn3, j, rfl⟩
    convert tileable_odd_ge5_x_6iplus3 n j hn5 hodd hj using 2; ring

/-- Sufficiency: if conditions hold, the rectangle is tileable -/
theorem rect_tileable_of_conditions (n m : ℕ) (h : RectTileableConditions n m) :
    LTileable (rectangle n m) := by
  rcases h with rfl | rfl | ⟨harea, hn, hm, hnodd3, hnodd3'⟩
  · -- n = 0
    rw [rectangle_0_m]; exact empty_LTileable
  · -- m = 0
    rw [rectangle_n_0]; exact empty_LTileable
  · -- Main case: n ≥ 2, m ≥ 2, n*m divisible by 3, not 3×odd or odd×3
    -- Since n*m divisible by 3, either 3 | n or 3 | m
    have h3div : 3 ∣ n ∨ 3 ∣ m := Nat.Prime.dvd_mul Nat.prime_three |>.mp
      (Nat.dvd_of_mod_eq_zero harea)
    rcases h3div with hn3 | hm3
    · -- 3 | n: swap and use the 3|m case
      rw [← LTileable_swap_rectangle]
      -- Now need rectangle m (3k) where n = 3k
      obtain ⟨k, rfl⟩ := hn3
      have hk : k ≥ 1 := by omega
      rcases Nat.even_or_odd m with ⟨j, rfl⟩ | hodd
      · -- m = 2j even
        have hj : j ≥ 1 := by omega
        convert tileable_even_mult3 j k hj using 2; ring
      · -- m odd: need n = 3k ≥ 6 (since 3×odd excluded means k ≥ 2)
        have hk2 : k ≥ 2 := by
          by_contra hlt; push_neg at hlt
          have hk1 : k = 1 := by omega
          subst hk1
          exact hnodd3 ⟨rfl, hodd⟩
        -- m odd ≥ 3, 3k ≥ 6
        have hm3' : m ≥ 3 := by obtain ⟨j, rfl⟩ := hodd; omega
        -- Need to show ¬(m = 3 ∧ Odd k) for tileable_odd_x_mult3
        have h_not : ¬(m = 3 ∧ Odd k) := by
          intro ⟨hm_eq, hk_odd⟩
          -- If m = 3, then by hnodd3': ¬(Odd (3k) ∧ m = 3)
          -- Odd (3k) ↔ Odd k, so hnodd3' becomes ¬(Odd k ∧ m = 3)
          have h3k_odd : Odd (3 * k) := by
            obtain ⟨i, rfl⟩ := hk_odd; use 3 * i + 1; ring
          exact hnodd3' ⟨h3k_odd, hm_eq⟩
        exact tileable_odd_x_mult3 m k hm3' hodd hk2 h_not
    · -- 3 | m
      obtain ⟨k, rfl⟩ := hm3
      have hk : k ≥ 1 := by omega
      rcases Nat.even_or_odd n with ⟨j, rfl⟩ | hodd
      · -- n = 2j even
        have hj : j ≥ 1 := by omega
        convert tileable_even_mult3 j k hj using 2; ring
      · -- n odd: need m = 3k ≥ 6 (since odd×3 excluded means k ≥ 2)
        have hk2 : k ≥ 2 := by
          by_contra hlt; push_neg at hlt
          have hk1 : k = 1 := by omega
          subst hk1
          exact hnodd3' ⟨hodd, rfl⟩
        -- n odd ≥ 3, 3k ≥ 6
        have hn3' : n ≥ 3 := by obtain ⟨j, rfl⟩ := hodd; omega
        -- Need to show ¬(n = 3 ∧ Odd k) for tileable_odd_x_mult3
        have h_not : ¬(n = 3 ∧ Odd k) := by
          intro ⟨hn_eq, hk_odd⟩
          subst hn_eq
          -- hnodd3 : ¬(3 = 3 ∧ Odd (3k))
          -- Odd (3k) ↔ Odd k
          have h3k_odd : Odd (3 * k) := by
            obtain ⟨i, rfl⟩ := hk_odd; use 3 * i + 1; ring
          exact hnodd3 ⟨rfl, h3k_odd⟩
        exact tileable_odd_x_mult3 n k hn3' hodd hk2 h_not

/-- Necessity: if tileable, the conditions hold -/
theorem conditions_of_rect_tileable (n m : ℕ) (h : LTileable (rectangle n m)) :
    RectTileableConditions n m := by
  unfold RectTileableConditions
  -- Handle trivial cases first
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · left; rfl
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · right; left; rfl
  -- Now n, m ≥ 1
  right; right
  have harea : n * m % 3 = 0 := by simpa using h.area_div_3
  refine ⟨harea, ?_, ?_, ?_, ?_⟩
  · -- n ≥ 2
    by_contra hlt; push_neg at hlt
    have : n = 1 := by omega
    subst this
    exact not_tileable_1_by_n hm h
  · -- m ≥ 2
    by_contra hlt; push_neg at hlt
    have : m = 1 := by omega
    subst this
    exact not_tileable_n_by_1 hn h
  · -- ¬(n = 3 ∧ Odd m)
    intro ⟨hn3, hmodd⟩
    subst hn3
    obtain ⟨k, rfl⟩ := hmodd
    exact not_tileable_3_by_odd k h
  · -- ¬(Odd n ∧ m = 3)
    intro ⟨hnodd, hm3⟩
    subst hm3
    obtain ⟨k, rfl⟩ := hnodd
    exact not_tileable_odd_by_3 k h

/-- **Main Theorem**: Complete characterization of L-tileable rectangles -/
theorem rect_tileable_iff (n m : ℕ) :
    LTileable (rectangle n m) ↔ RectTileableConditions n m :=
  ⟨conditions_of_rect_tileable n m, rect_tileable_of_conditions n m⟩

/-! ## Deficient Rectangles (Three-Cornered) -/

/-- The top-right corner cell of an `n × m` rectangle (0-based coordinates). -/
def cornerTR (n m : ℕ) : Cell :=
  (Int.ofNat (n - 1), Int.ofNat (m - 1))

/-- A three-cornered `n × m` rectangle: `rectangle n m` with its top-right corner removed.

We implement this as `erase` of the top-right corner from the full rectangle, so
cardinality lemmas are immediate from `Finset.card_erase`. -/
def rectangleMinusCorner (n m : ℕ) : Region :=
  (rectangle n m).erase (cornerTR n m)

/-- The top-right corner is indeed in the rectangle when `n,m ≥ 1`. -/
theorem cornerTR_mem_rectangle {n m : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) :
    cornerTR n m ∈ rectangle n m := by
  -- Reduce to linear arithmetic in ℤ and discharge with `omega`.
  have hineq :
      0 ≤ (cornerTR n m).1 ∧ (cornerTR n m).1 < n ∧
      0 ≤ (cornerTR n m).2 ∧ (cornerTR n m).2 < m := by
    dsimp [cornerTR]
    omega
  exact (mem_rectangle.mpr hineq)

/-- Cardinality of a three-cornered rectangle: one less than the full rectangle. -/
theorem rectangleMinusCorner_card {n m : ℕ} (hn : n ≥ 1) (hm : m ≥ 1) :
    (rectangleMinusCorner n m).card = n * m - 1 := by
  have hcorner : cornerTR n m ∈ rectangle n m :=
    cornerTR_mem_rectangle hn hm
  -- `erase` removes exactly one element from the rectangle.
  simp [rectangleMinusCorner, rectangle_card, hcorner]

/-- Swapping the top-right corner of an `n × m` rectangle gives the
top-right corner of the `m × n` rectangle. -/
theorem swapCell_cornerTR (n m : ℕ) :
    swapCell (cornerTR n m) = cornerTR m n := by
  simp [cornerTR, swapCell]

/-- Swapping a three-cornered `n × m` rectangle yields the `m × n` one. -/
theorem swap_rectangleMinusCorner (n m : ℕ) :
    swapRegion (rectangleMinusCorner n m) = rectangleMinusCorner m n := by
  -- Work elementwise, using the characterization of `erase` and `swap_rectangle`.
  unfold rectangleMinusCorner swapRegion
  -- `swapRegion r = r.image swapCell`
  ext c
  constructor
  · -- → direction
    intro hc
    -- `c ∈ image swapCell ((rectangle n m).erase (cornerTR n m))`
    rcases Finset.mem_image.mp hc with ⟨a, ha_erase, rfl⟩
    rcases Finset.mem_erase.mp ha_erase with ⟨ha_ne_corner, ha_rect⟩
    -- `swapCell a` lies in `swapRegion (rectangle n m) = rectangle m n`
    have h_in_rect_mn : swapCell a ∈ rectangle m n := by
      -- First, show `swapCell a ∈ swapRegion (rectangle n m)`
      have h_in_swap : swapCell a ∈ swapRegion (rectangle n m) := by
        -- membership in `image swapCell (rectangle n m)`
        exact Finset.mem_image.mpr ⟨a, ha_rect, rfl⟩
      -- then rewrite using `swap_rectangle`
      simpa [swap_rectangle] using h_in_swap
    -- and it is not the swapped corner
    have h_ne_cornerTR_mn : swapCell a ≠ cornerTR m n := by
      intro h_eq
      -- compare with `swapCell (cornerTR n m)` using injectivity
      have h' : a = cornerTR n m := by
        apply swapCell_injective
        simpa [swapCell_cornerTR] using h_eq
      exact ha_ne_corner h'
    -- So `swapCell a` lies in `erase (cornerTR m n) (rectangle m n)`.
    exact Finset.mem_erase.mpr ⟨h_ne_cornerTR_mn, h_in_rect_mn⟩
  · -- ← direction
    intro hc
    -- `c ∈ erase (cornerTR m n) (rectangle m n)`
    rcases Finset.mem_erase.mp hc with ⟨hc_ne_corner, hc_rect_mn⟩
    -- Find a preimage `a` in `rectangle n m` with `swapCell a = c`
    have h_in_swap : c ∈ swapRegion (rectangle n m) := by
      -- rewrite membership using `swap_rectangle`
      simpa [swap_rectangle] using hc_rect_mn
    rcases Finset.mem_image.mp h_in_swap with ⟨a, ha_rect, h_eq⟩
    subst h_eq
    -- Show `a ≠ cornerTR n m`
    have ha_ne_corner : a ≠ cornerTR n m := by
      intro h_eq
      -- Then `swapCell a = swapCell (cornerTR n m) = cornerTR m n`,
      -- contradicting `hc_ne_corner`.
      have : swapCell a = cornerTR m n := by
        simp [h_eq, swapCell_cornerTR]
      exact hc_ne_corner this
    -- Thus `swapCell a` lies in the image of the erased rectangle.
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_erase.mpr ⟨ha_ne_corner, ha_rect⟩, rfl⟩

/-- L-tileability of three-cornered rectangles is symmetric in the dimensions. -/
theorem LTileable_swap_rectangleMinusCorner (n m : ℕ) :
    LTileable (rectangleMinusCorner n m) ↔
      LTileable (rectangleMinusCorner m n) := by
  constructor
  · intro h
    have h' := LTileable_swap h
    simpa [swap_rectangleMinusCorner] using h'
  · intro h
    have h' := LTileable_swap h
    simpa [swap_rectangleMinusCorner] using h'

/-! ### Splitting three-cornered rectangles -/

/-- Horizontal split of a three-cornered rectangle.

If we cut an `(a+b) × m` three-cornered rectangle at `x = a` with `b ≥ 1`,
the missing corner lies in the right part.  The shape decomposes as a union of:

- the full `a × m` rectangle on the left, and
- a translated copy of `rectangleMinusCorner b m` on the right. -/
theorem rectangleMinusCorner_split_horizontal (a b m : ℕ) (hb : 0 < b) :
    rectangleMinusCorner (a + b) m =
      rectangle a m ∪ translateRegion (rectangleMinusCorner b m) (a, 0) := by
  classical
  have hsplit := rectangle_split_horizontal a b m
  -- First, rewrite the deficient rectangle using the horizontal split.
  have hL :
      rectangleMinusCorner (a + b) m =
        (rectangle a m ∪ translateRegion (rectangle b m) (a, 0)).erase
          (cornerTR (a + b) m) := by
    unfold rectangleMinusCorner
    simp [hsplit]
  -- Now use the generic `erase_union_finset` lemma on the right-hand side.
  have h₁ :
      (rectangle a m ∪ translateRegion (rectangle b m) (a, 0)).erase
          (cornerTR (a + b) m) =
        (rectangle a m).erase (cornerTR (a + b) m) ∪
          (translateRegion (rectangle b m) (a, 0)).erase (cornerTR (a + b) m) := by
    simpa using
      (erase_union_finset (rectangle a m)
        (translateRegion (rectangle b m) (a, 0)) (cornerTR (a + b) m))
  -- The missing corner is not in the left `a × m` rectangle when `b ≥ 1`.
  have hcorner_not_left :
      cornerTR (a + b) m ∉ rectangle a m := by
    -- A point in `rectangle a m` must have x-coordinate `< a`,
    -- but the corner has x-coordinate `a + b - 1 ≥ a` when `b ≥ 1`.
    intro h
    rcases (mem_rectangle.mp h) with ⟨_, hx_lt_a, _, _⟩
    -- x-coordinate of the corner
    have hx_corner :
        (cornerTR (a + b) m).1 = Int.ofNat (a + b - 1) := rfl
    -- From `hb : 0 < b` we get `a ≤ a + b - 1`.
    have hx_nat : a ≤ a + b - 1 := by
      omega
    -- Compare in ℤ using monotonicity of `Int.ofNat`.
    have hx_le : (a : ℤ) ≤ (cornerTR (a + b) m).1 := by
      have hx_le' : a ≤ a + b - 1 := hx_nat
      exact Int.ofNat_le.mpr hx_le'
    have hx_lt : (cornerTR (a + b) m).1 < a := by
      simpa [hx_corner] using hx_lt_a
    have : (cornerTR (a + b) m).1 < (cornerTR (a + b) m).1 :=
      lt_of_lt_of_le hx_lt hx_le
    exact lt_irrefl _ this
  -- Identify the erased right part with a translated three-cornered rectangle.
  have hcorner_translate :
      translateCell (cornerTR b m) (a, 0) = cornerTR (a + b) m := by
    -- Compute coordinates explicitly.
    dsimp [cornerTR, translateCell]
    ext
    · -- x-coordinate
      -- Goal: `↑a + ↑(b - 1) = ↑(a + b - 1)` in ℤ; this is linear arithmetic.
      have : (↑a + ↑(b - 1) : ℤ) = ↑(a + b - 1) := by
        omega
      simpa [add_comm, add_left_comm, add_assoc] using this
    · -- y-coordinate
      simp
  have h₂ :
      (translateRegion (rectangle b m) (a, 0)).erase (cornerTR (a + b) m) =
        translateRegion (rectangleMinusCorner b m) (a, 0) := by
    -- Use the translation/erase lemma with `x = cornerTR b m`.
    have := translateRegion_erase_point (rectangle b m) (a, 0) (cornerTR b m)
    -- Rewrite the erased point using `hcorner_translate`.
    simpa [rectangleMinusCorner, hcorner_translate] using this
  -- Combine `erase_union_finset`, `hcorner_not_left`, and `h₂` to rewrite the RHS.
  have hR :
      (rectangle a m ∪ translateRegion (rectangle b m) (a, 0)).erase
          (cornerTR (a + b) m) =
        rectangle a m ∪ translateRegion (rectangleMinusCorner b m) (a, 0) := by
    have hA :
        (rectangle a m).erase (cornerTR (a + b) m) = rectangle a m :=
      Finset.erase_eq_of_notMem hcorner_not_left
    simp [h₁, hA, h₂]
  -- Finally, combine the left and right descriptions.
  calc
    rectangleMinusCorner (a + b) m
        = (rectangle a m ∪ translateRegion (rectangle b m) (a, 0)).erase
            (cornerTR (a + b) m) := hL
    _ = rectangle a m ∪ translateRegion (rectangleMinusCorner b m) (a, 0) := hR

/-- Vertical split of a three-cornered rectangle.

If we cut an `n × (a+b)` three-cornered rectangle at `y = a` with `b ≥ 1`,
the missing corner lies in the top part.  The shape decomposes as a union of:

- the full `n × a` rectangle at the bottom, and
- a translated copy of `rectangleMinusCorner n b` above it. -/
theorem rectangleMinusCorner_split_vertical (n a b : ℕ) (hb : 0 < b) :
    rectangleMinusCorner n (a + b) =
      rectangle n a ∪ translateRegion (rectangleMinusCorner n b) (0, a) := by
  classical
  -- Start from the definition via `erase` and the vertical split of rectangles.
  have hsplit := rectangle_split_vertical n a b
  -- First, rewrite the deficient rectangle using the vertical split.
  have hL :
      rectangleMinusCorner n (a + b) =
        (rectangle n a ∪ translateRegion (rectangle n b) (0, a)).erase
          (cornerTR n (a + b)) := by
    unfold rectangleMinusCorner
    simp [hsplit]
  -- Distribute `erase` over the union.
  have h₁ :
      (rectangle n a ∪ translateRegion (rectangle n b) (0, a)).erase
          (cornerTR n (a + b)) =
        (rectangle n a).erase (cornerTR n (a + b)) ∪
          (translateRegion (rectangle n b) (0, a)).erase
            (cornerTR n (a + b)) := by
    simpa using
      (erase_union_finset (rectangle n a)
        (translateRegion (rectangle n b) (0, a)) (cornerTR n (a + b)))
  -- The missing corner does not lie in the bottom `n × a` rectangle.
  have hcorner_not_bottom :
      cornerTR n (a + b) ∉ rectangle n a := by
    intro h
    rcases (mem_rectangle.mp h) with ⟨_, _, _, hy_lt_a⟩
    -- y-coordinate of the corner is `a + b - 1 ≥ a`, contradiction.
    have hy_corner :
        (cornerTR n (a + b)).2 = Int.ofNat (a + b - 1) := rfl
    -- From `hb : 0 < b` we get `a ≤ a + b - 1`.
    have hy_nat : a ≤ a + b - 1 := by
      omega
    have hy_le : (a : ℤ) ≤ (cornerTR n (a + b)).2 := by
      have hy_le' : a ≤ a + b - 1 := hy_nat
      exact Int.ofNat_le.mpr hy_le'
    have hy_lt : (cornerTR n (a + b)).2 < a := by
      simpa [hy_corner] using hy_lt_a
    have : (cornerTR n (a + b)).2 < (cornerTR n (a + b)).2 :=
      lt_of_lt_of_le hy_lt hy_le
    exact lt_irrefl _ this
  -- Identify the erased top part with a translated three-cornered rectangle.
  have hcorner_translate :
      translateCell (cornerTR n b) (0, a) = cornerTR n (a + b) := by
    dsimp [cornerTR, translateCell]
    ext
    · -- x-coordinate
      simp
    · -- y-coordinate
      -- Goal: `↑a + ↑(b - 1) = ↑(a + b - 1)` in ℤ.
      have : (↑a + ↑(b - 1) : ℤ) = ↑(a + b - 1) := by
        omega
      simpa [add_comm, add_left_comm, add_assoc] using this
  have h₂ :
      (translateRegion (rectangle n b) (0, a)).erase (cornerTR n (a + b)) =
        translateRegion (rectangleMinusCorner n b) (0, a) := by
    have := translateRegion_erase_point (rectangle n b) (0, a) (cornerTR n b)
    simpa [rectangleMinusCorner, hcorner_translate] using this
  -- Put everything together on the right-hand side.
  have hR :
      (rectangle n a ∪ translateRegion (rectangle n b) (0, a)).erase
          (cornerTR n (a + b)) =
        rectangle n a ∪ translateRegion (rectangleMinusCorner n b) (0, a) := by
    have hA :
        (rectangle n a).erase (cornerTR n (a + b)) = rectangle n a :=
      Finset.erase_eq_of_notMem hcorner_not_bottom
    simp [h₁, hA, h₂]
  -- Finally, combine the left and right descriptions.
  calc
    rectangleMinusCorner n (a + b)
        = (rectangle n a ∪ translateRegion (rectangle n b) (0, a)).erase
            (cornerTR n (a + b)) := hL
    _ = rectangle n a ∪ translateRegion (rectangleMinusCorner n b) (0, a) := hR

/-! ### Simple mod-3 helper lemmas -/

/-- If `(n * m) % 3 ≠ 0`, then in particular `n % 3 ≠ 0`.

Equivalently (by contrapositive): if `n % 3 = 0`, then `(n * m) % 3 = 0`. -/
theorem mod3_ne_zero_of_mul_mod3_ne_zero_left {n m : ℕ}
    (h : (n * m) % 3 ≠ 0) :
    n % 3 ≠ 0 := by
  intro hn0
  -- From `n % 3 = 0` we get `3 ∣ n`, hence `3 ∣ n * m`, so `(n * m) % 3 = 0`.
  have h3_div_n : 3 ∣ n := Nat.dvd_of_mod_eq_zero hn0
  have h3_div_nm : 3 ∣ n * m := dvd_mul_of_dvd_left h3_div_n m
  have hzero : (n * m) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3_div_nm
  exact h hzero

/-! A number modulo `3` is either `0`, `1`, or `2`.  If it is not `0`, it must
be `1` or `2`. -/
theorem mod3_eq_one_or_two_of_ne_zero {n : ℕ} (h : n % 3 ≠ 0) :
    n % 3 = 1 ∨ n % 3 = 2 := by
  -- First, `n % 3` lies in `{0,1,2}` since it is strictly less than `3`.
  have hlt3 : n % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
  -- From `n % 3 ≠ 0` we get `0 < n % 3` and hence `1 ≤ n % 3`.
  have hpos : 0 < n % 3 := Nat.pos_of_ne_zero h
  have hge1 : 1 ≤ n % 3 := Nat.succ_le_of_lt hpos
  -- Rewrite `< 3` as `≤ 2`.
  have hle2 : n % 3 ≤ 2 := by
    have : n % 3 < (2 : ℕ).succ := by simpa using hlt3
    exact Nat.lt_succ_iff.mp this
  -- So either `n % 3 < 2` or `n % 3 = 2`.
  have hlt2_or_eq2 : n % 3 < 2 ∨ n % 3 = 2 := lt_or_eq_of_le hle2
  rcases hlt2_or_eq2 with hlt2 | heq2
  · -- Case `n % 3 < 2`: then in fact `n % 3 ≤ 1`, and together with `1 ≤ n % 3`
    -- we get `n % 3 = 1`.
    have hle1 : n % 3 ≤ 1 := by
      have : n % 3 < (1 : ℕ).succ := by simpa using hlt2
      exact Nat.lt_succ_iff.mp this
    have : n % 3 = 1 := le_antisymm hle1 hge1
    exact Or.inl this
  · -- Case `n % 3 = 2`.
    exact Or.inr heq2

/- If `(n * m) % 3 = 1`, then the residues of `n` and `m` modulo 3 are
either both `1` or both `2`. Mixed congruence classes `{1,2}` give
product ≡ 2 (mod 3), not 1.

This lemma is currently left as a placeholder; the intended proof follows
the standard modular arithmetic argument sketched in the comments above. -/
theorem mod3_both_one_or_two_of_area_mod3_zero
    {n m : ℕ}
    (h : (n * m) % 3 = 1) :
    (n % 3 = 1 ∧ m % 3 = 1) ∨ (n % 3 = 2 ∧ m % 3 = 2) := by
  -- From `(n * m) % 3 = 1` we know the product is not divisible by 3.
  have hnm_ne0 : (n * m) % 3 ≠ 0 := by
    simp [h]
  -- Hence neither factor is `0` mod `3`.
  have hn_ne0 : n % 3 ≠ 0 :=
    mod3_ne_zero_of_mul_mod3_ne_zero_left (n := n) (m := m) hnm_ne0
  have hm_ne0 : m % 3 ≠ 0 := by
    have hmn_ne0 : (m * n) % 3 ≠ 0 := by
      simpa [Nat.mul_comm] using hnm_ne0
    exact mod3_ne_zero_of_mul_mod3_ne_zero_left (n := m) (m := n) hmn_ne0
  -- Each residue modulo `3` is therefore either `1` or `2`.
  have hn_res : n % 3 = 1 ∨ n % 3 = 2 :=
    mod3_eq_one_or_two_of_ne_zero hn_ne0
  have hm_res : m % 3 = 1 ∨ m % 3 = 2 :=
    mod3_eq_one_or_two_of_ne_zero hm_ne0
  -- Analyze the four possible combinations of residues.
  rcases hn_res with hn1 | hn2
  · -- Case `n % 3 = 1`.
    rcases hm_res with hm1 | hm2
    · -- Subcase `m % 3 = 1`: this is one of the desired alternatives.
      left
      exact ⟨hn1, hm1⟩
    · -- Subcase `m % 3 = 2`: then `(n * m) % 3 = 2`, contradicting `h`.
      have hnm2 : (n * m) % 3 = 2 := by
        have hcalc : (n * m) % 3 = (1 * 2) % 3 := by
          simpa [hn1, hm2] using (Nat.mul_mod n m 3)
        simpa using hcalc
      have : (1 : ℕ) ≠ 2 := by decide
      have hf : False := this (h.symm.trans hnm2)
      exact hf.elim
  · -- Case `n % 3 = 2`.
    rcases hm_res with hm1 | hm2
    · -- Subcase `m % 3 = 1`: symmetric to the previous contradictory case.
      have hnm2 : (n * m) % 3 = 2 := by
        have hcalc : (n * m) % 3 = (2 * 1) % 3 := by
          simpa [hn2, hm1] using (Nat.mul_mod n m 3)
        simpa using hcalc
      have : (1 : ℕ) ≠ 2 := by decide
      have hf : False := this (h.symm.trans hnm2)
      exact hf.elim
    · -- Subcase `m % 3 = 2`: this is the other desired alternative.
      right
      exact ⟨hn2, hm2⟩

/-- If a three-cornered rectangle is L-tileable, then its area is divisible by 3. -/
theorem rectMinusCorner_tileable_area_div_3 {n m : ℕ}
    (hn : n ≥ 1) (hm : m ≥ 1)
    (h : LTileable (rectangleMinusCorner n m)) :
    (n * m - 1) % 3 = 0 := by
  have hcard : (rectangleMinusCorner n m).card % 3 = 0 := by
    simpa using h.area_div_3
  simpa [rectangleMinusCorner_card hn hm] using hcard

/-- A tiling of the 2×2 rectangle with its top-right corner removed. -/
def tiling_2x2_minus : TileSet lTrominoSet Unit :=
  mkTileSet lTrominoSet Unit (fun _ => mkPlacedTile () 0 0 0)

theorem tiling_2x2_minus_valid :
    tiling_2x2_minus.Valid (rectangleMinusCorner 2 2) := by
  decide

/-- The 2×2 rectangle with a missing top-right corner is L-tileable. -/
theorem tileable_2x2_minus : LTileable (rectangleMinusCorner 2 2) :=
  ⟨Unit, inferInstance, inferInstance, tiling_2x2_minus, tiling_2x2_minus_valid⟩

/-- Explicit tiling of the 4×4 rectangle with its top-right corner removed.
This is the `2² × 2²` deficiency-1 square used in Ash–Golomb's Theorem 2. -/
def tiling_4x4_minus : TileSet lTrominoSet (Fin 5) := ⟨![
  ⟨(), (0, 0), 0⟩,  -- bottom-left quadrant
  ⟨(), (3, 0), 1⟩,  -- bottom-right quadrant
  ⟨(), (0, 3), 3⟩,  -- top-left quadrant
  ⟨(), (2, 2), 0⟩,  -- top-right quadrant (except the missing corner)
  ⟨(), (1, 1), 0⟩   -- central tromino
]⟩

theorem tiling_4x4_minus_valid :
    tiling_4x4_minus.Valid (rectangleMinusCorner 4 4) := by
  decide

/-- The 4×4 rectangle with a missing top-right corner is L-tileable. -/
theorem tileable_4x4_minus : LTileable (rectangleMinusCorner 4 4) :=
  ⟨Fin 5, inferInstance, inferInstance, tiling_4x4_minus, tiling_4x4_minus_valid⟩

/-- Explicit tiling of the 5×5 rectangle with its top-right corner removed.

We follow the Ash–Golomb decomposition:
- a 2×3 rectangle `A` at the bottom-left,
- a 3×2 rectangle `B` at the bottom-right,
- and four L-trominoes near the top boundary.

The eight tiles (0–7) are:
- tiles 0–1: a copy of `tiling_2x3` covering `A = {(x,y) | x ∈ {0,1}, y ∈ {0,1,2}}`,
- tiles 2–3: a tiling of `B = {(x,y) | x ∈ {2,3,4}, y ∈ {0,1}}`,
- tiles 4–7: the four L-trominoes:
  - `T₁ = {(0,3),(0,4),(1,4)}`,
  - `T₂ = {(1,3),(2,3),(2,2)}`,
  - `T₃ = {(2,4),(3,4),(3,3)}`,
  - `T₄ = {(3,2),(4,2),(4,3)}`.
-/
def tiling_5x5_minus : TileSet lTrominoSet (Fin 8) := ⟨![
  -- A: 2×3 rectangle at bottom-left (copy of tiling_2x3)
  ⟨(), (0, 0), 0⟩,
  ⟨(), (1, 2), 2⟩,
  -- B: 3×2 rectangle at bottom-right
  ⟨(), (2, 0), 0⟩,
  ⟨(), (4, 1), 2⟩,
  -- T₁: {(0,3),(0,4),(1,4)}
  ⟨(), (0, 4), 3⟩,
  -- T₂: {(1,3),(2,3),(2,2)}
  ⟨(), (2, 3), 2⟩,
  -- T₃: {(2,4),(3,4),(3,3)}
  ⟨(), (3, 4), 2⟩,
  -- T₄: {(3,2),(4,2),(4,3)}
  ⟨(), (4, 2), 1⟩
]⟩

theorem tiling_5x5_minus_valid :
    tiling_5x5_minus.Valid (rectangleMinusCorner 5 5) := by
  decide

/-- The 5×5 rectangle with a missing top-right corner is L-tileable. -/
theorem tileable_5x5_minus : LTileable (rectangleMinusCorner 5 5) :=
  ⟨Fin 8, inferInstance, inferInstance, tiling_5x5_minus, tiling_5x5_minus_valid⟩

/-- Explicit tiling of the 7×7 rectangle with its top-right corner removed.

We use the user-specified partition of `R(7,7)⁻` into 16 disjoint L-trominoes,
converted to 0-based coordinates.

In 0-based `(x,y)` coordinates (with `0 ≤ x,y ≤ 6`, missing `(6,6)`), the 16
L-trominoes are:
- `T₁  = {(0,0),(0,1),(1,1)}`
- `T₂  = {(1,0),(2,0),(2,1)}`
- `T₃  = {(0,2),(0,3),(1,3)}`
- `T₄  = {(1,2),(2,2),(2,3)}`
- `T₅  = {(0,4),(1,4),(1,5)}`
- `T₆  = {(0,5),(0,6),(1,6)}`
- `T₇  = {(2,6),(3,5),(3,6)}`
- `T₈  = {(2,4),(2,5),(3,4)}`
- `T₉  = {(3,0),(4,0),(4,1)}`
- `T₁₀ = {(3,1),(3,2),(4,2)}`
- `T₁₁ = {(3,3),(4,3),(4,4)}`
- `T₁₂ = {(4,5),(4,6),(5,6)}`
- `T₁₃ = {(5,0),(6,0),(6,1)}`
- `T₁₄ = {(5,1),(5,2),(6,2)}`
- `T₁₅ = {(5,3),(6,3),(6,4)}`
- `T₁₆ = {(5,4),(5,5),(6,5)}`.
-/
def tiling_7x7_minus : TileSet lTrominoSet (Fin 16) := ⟨![
  -- T₁
  ⟨(), (0, 1), 3⟩,
  -- T₂
  ⟨(), (2, 0), 1⟩,
  -- T₃
  ⟨(), (0, 3), 3⟩,
  -- T₄
  ⟨(), (2, 2), 1⟩,
  -- T₅
  ⟨(), (1, 4), 1⟩,
  -- T₆
  ⟨(), (0, 6), 3⟩,
  -- T₇
  ⟨(), (3, 6), 2⟩,
  -- T₈
  ⟨(), (2, 4), 0⟩,
  -- T₉
  ⟨(), (4, 0), 1⟩,
  -- T₁₀
  ⟨(), (3, 2), 3⟩,
  -- T₁₁
  ⟨(), (4, 3), 1⟩,
  -- T₁₂
  ⟨(), (4, 6), 3⟩,
  -- T₁₃
  ⟨(), (6, 0), 1⟩,
  -- T₁₄
  ⟨(), (5, 2), 3⟩,
  -- T₁₅
  ⟨(), (6, 3), 1⟩,
  -- T₁₆
  ⟨(), (5, 5), 3⟩
]⟩

theorem tiling_7x7_minus_valid :
    tiling_7x7_minus.Valid (rectangleMinusCorner 7 7) := by
  decide

/-- The 7×7 rectangle with a missing top-right corner is L-tileable. -/
theorem tileable_7x7_minus : LTileable (rectangleMinusCorner 7 7) :=
  ⟨Fin 16, inferInstance, inferInstance, tiling_7x7_minus, tiling_7x7_minus_valid⟩

/-- Sufficiency direction assuming `m ≤ n` (Ash–Golomb Theorem 2, one-sided).

If `n,m ≥ 2`, `m ≤ n`, and the deficient rectangle area `(n*m - 1)` is divisible
by `3`, then `rectangleMinusCorner n m` is L-tileable.

This lemma corresponds to the `m ≤ n` branch of the main theorem, where
the full Ash–Golomb case analysis (mod 3) will be carried out. -/
theorem rectMinusCorner_tileable_of_area_m_le_n
    (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2) (hmn : m ≤ n)
    (harea : (n * m - 1) % 3 = 0) :
    LTileable (rectangleMinusCorner n m) := by
  -- `n,m ≥ 2` implies `1 ≤ n * m`, used to rewrite `(n*m - 1) + 1`.
  have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
  have hm1 : 1 ≤ m := le_trans (by decide : 1 ≤ 2) hm
  have hnm_ge1 : 1 ≤ n * m := by
    -- Since `n,m ≥ 1`, we have `1 * 1 ≤ n * m`.
    have h : 1 * 1 ≤ n * m := Nat.mul_le_mul hn1 hm1
    simpa using h
  -- Use the area condition to compute `(n * m) % 3`, then apply the
  -- modular-arithmetic classification lemma.
  have h_add := Nat.add_mod (n * m - 1) 1 3
  have h_step :
      (n * m) % 3 =
        ((n * m - 1) % 3 + 1 % 3) % 3 := by
    -- `h_add` has left side `((n*m - 1) + 1) % 3`; rewrite it as `(n*m) % 3`.
    have h1 : ((n * m - 1) + 1) % 3 = (n * m) % 3 := by
      simp [Nat.sub_add_cancel hnm_ge1]
    -- From `h1 : LHS = (n*m)%3` and `h_add : LHS = RHS`, deduce `(n*m)%3 = RHS`.
    exact h1.symm.trans h_add
  have hnm_mod1 : (n * m) % 3 = 1 := by
    have : (n * m) % 3 = ((0 : ℕ) + 1) % 3 := by
      simpa [harea, Nat.one_mod] using h_step
    simpa [Nat.one_mod] using this
  -- Now apply the mod-3 helper lemma: only two residue patterns are possible.
  have hres :
      (n % 3 = 1 ∧ m % 3 = 1) ∨ (n % 3 = 2 ∧ m % 3 = 2) :=
    mod3_both_one_or_two_of_area_mod3_zero (n := n) (m := m) hnm_mod1
  rcases hres with h11 | h22
  · -- Case `n ≡ m ≡ 1 (mod 3)`: Ash–Golomb Case 1, to be filled.
    have hn1_mod : n % 3 = 1 := h11.1
    have hm1_mod : m % 3 = 1 := h11.2
    -- TODO: use `hn1_mod`, `hm1_mod`, `hn`, `hm`, and `hmn` to build a tiling.
    sorry
  · -- Case `n ≡ m ≡ 2 (mod 3)`: Ash–Golomb Case 2, to be filled.
    have hn2_mod : n % 3 = 2 := h22.1
    have hm2_mod : m % 3 = 2 := h22.2
    -- TODO: use `hn2_mod`, `hm2_mod`, `hn`, `hm`, and `hmn` to build a tiling.
    sorry

/-- **Ash–Golomb Theorem 2 (statement)**:
An `n × m` rectangle with one corner removed is L-tileable iff its area is a multiple of 3.

We assume `n,m ≥ 2` so the shape is non-degenerate. -/
theorem rectMinusCorner_tileable_iff (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2) :
    LTileable (rectangleMinusCorner n m) ↔ (n * m - 1) % 3 = 0 := by
  constructor
  · -- Necessity: tileable ⇒ area divisible by 3
    intro h
    exact rectMinusCorner_tileable_area_div_3 (by omega) (by omega) h
  · -- Sufficiency: area divisible by 3 ⇒ tileable.
    intro harea
    -- Without loss of generality, assume `m ≤ n`. If not, we can swap the axes:
    -- L-tileability of `rectangleMinusCorner` is invariant under swapping x,y.
    by_cases hmn : m ≤ n
    · -- Main branch: `m ≤ n`
      exact rectMinusCorner_tileable_of_area_m_le_n n m hn hm hmn harea
    · -- Symmetric branch: `¬(m ≤ n)` i.e. `n < m`.
      -- Use symmetry: first obtain a tiling for `rectangleMinusCorner m n`
      -- (where `n ≤ m` holds), then swap back.
      have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
      -- Area condition is symmetric in `n` and `m`.
      have harea' : (m * n - 1) % 3 = 0 := by
        simpa [Nat.mul_comm] using harea
      -- Apply the one-sided lemma to the swapped pair `(m,n)`.
      have h_swapped : LTileable (rectangleMinusCorner m n) :=
        rectMinusCorner_tileable_of_area_m_le_n m n hm hn hnm harea'
      -- Transport the tiling back using symmetry of three-cornered rectangles.
      exact (LTileable_swap_rectangleMinusCorner m n).mp h_swapped
