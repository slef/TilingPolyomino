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
* `Prototile`, `Protoset`
* `PlacedTile`
* `TileSet` and `TileSet.Valid`
* Generic notions of `Tileable`
* Rectangle regions and basic splitting lemmas
* Generic placement enumeration utilities
-/

/-- A cell on the integer grid -/
abbrev Cell := ℤ × ℤ

/-- A region is a finite set of cells -/
abbrev Region := Finset Cell

/- ## Prototile and Protoset -/

/- A prototile is the "shape" of a tile, represented as a list of cells with no
duplicates.  This design allows both:

* Computation: iterate over `p.cells` (the list)
* Proofs: use `(p : Finset Cell)` via coercion to access `Finset` lemmas

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

/-- Coercion from `Prototile` to `Finset Cell` -/
instance : Coe Prototile (Finset Cell) where
  coe p := ⟨p.cells, p.nodup⟩

theorem Prototile.coe_def (p : Prototile) :
    (p : Finset Cell) = ⟨p.cells, p.nodup⟩ := rfl

theorem Prototile.mem_coe (p : Prototile) (c : Cell) :
    c ∈ (p : Finset Cell) ↔ c ∈ p.cells := by
  rw [Prototile.coe_def]
  simp only [Finset.mem_mk, Multiset.mem_coe]

/-- Cardinality of a prototile -/
def Prototile.card (p : Prototile) : ℕ := p.cells.length

theorem Prototile.card_eq (p : Prototile) :
    p.card = (p : Finset Cell).card := by
  simp only [Prototile.card, Finset.card_def]
  rfl

/-- A protoset is an indexed family of prototiles -/
structure Protoset (ι : Type*) where
  /-- The tiles in the protoset -/
  tiles : ι → Prototile

instance {ι : Type*} :
    CoeFun (Protoset ι) (fun _ => ι → Prototile) where
  coe := Protoset.tiles

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
def rotateProto (p : Prototile) (r : Fin 4) : Finset Cell :=
  (p : Finset Cell).image (rotateCell · r)

/-- Rotation preserves cardinality of a prototile -/
theorem rotateProto_card (p : Prototile) (r : Fin 4) :
    (rotateProto p r).card = p.cells.length := by
  simp only [rotateProto]
  rw [Finset.card_image_of_injective _ (rotateCell_injective r)]
  rw [← p.card_eq]
  rfl

/- ## Placed Tiles -/

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
def PlacedTile.cells {ι : Type*} (ps : Protoset ι) (pt : PlacedTile ι) :
    Finset Cell :=
  (rotateProto (ps pt.index) pt.rotation).image (translateCell · pt.translation)

/-- Translate a placed tile by an offset -/
def PlacedTile.translate {ι : Type*} (pt : PlacedTile ι) (offset : Cell) :
    PlacedTile ι :=
  ⟨pt.index, (pt.translation.1 + offset.1, pt.translation.2 + offset.2),
    pt.rotation⟩

/-- Translation of a placed tile translates its cells -/
theorem PlacedTile.translate_cells {ι : Type*}
    (ps : Protoset ι) (pt : PlacedTile ι) (offset : Cell) :
    (pt.translate offset).cells ps =
      translateRegion (pt.cells ps) offset := by
  simp only [PlacedTile.cells, PlacedTile.translate, translateRegion]
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
theorem PlacedTile.cells_card {ι : Type*}
    (ps : Protoset ι) (pt : PlacedTile ι) :
    (pt.cells ps).card = (ps pt.index).cells.length := by
  simp only [PlacedTile.cells]
  rw [Finset.card_image_of_injective _ (translateCell_injective pt.translation)]
  exact rotateProto_card (ps pt.index) pt.rotation

/- ## TileSet: Indexed Family of Placed Tiles -/

/-- A `TileSet` is an indexed family of placed tiles -/
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
theorem card_coveredCells [Fintype ιₜ] [DecidableEq ιₜ]
    (t : TileSet ps ιₜ) (hdisj : t.PairwiseDisjoint) :
    t.coveredCells.card = ∑ i : ιₜ, (t.cellsAt i).card := by
  simp only [coveredCells]
  rw [Finset.card_biUnion]
  intro i _ j _ hij
  exact hdisj i j hij

/-- A tileset is valid for a region if tiles are disjoint and exactly cover it -/
structure Valid [Fintype ιₜ] [DecidableEq ιₜ]
    (t : TileSet ps ιₜ) (region : Region) : Prop where
  /-- No two tiles overlap -/
  disjoint : t.PairwiseDisjoint
  /-- The tiles exactly cover the region -/
  covers : t.coveredCells = region

/-- Decidable pairwise disjointness for finite index types -/
instance instDecidablePairwiseDisjoint [Fintype ιₜ] [DecidableEq ιₜ]
    (t : TileSet ps ιₜ) :
    Decidable t.PairwiseDisjoint :=
  inferInstanceAs
    (Decidable (∀ i j : ιₜ, i ≠ j → Disjoint (t.cellsAt i) (t.cellsAt j)))

/-- Decidable validity for finite index types -/
instance instDecidableValid [Fintype ιₜ] [DecidableEq ιₜ]
    (t : TileSet ps ιₜ) (region : Region) :
    Decidable (t.Valid region) :=
  if hd : t.PairwiseDisjoint then
    if hc : t.coveredCells = region then
      isTrue ⟨hd, hc⟩
    else
      isFalse (fun h => hc h.covers)
  else
    isFalse (fun h => hd h.disjoint)

/-- Tiles at different indices are disjoint -/
theorem Valid.disjoint_tiles [Fintype ιₜ] [DecidableEq ιₜ]
    {t : TileSet ps ιₜ} {region : Region}
    (hv : t.Valid region) (i j : ιₜ) (hij : i ≠ j) :
    Disjoint (t.cellsAt i) (t.cellsAt j) :=
  hv.disjoint i j hij

/-- Every tile's cells are contained in the region -/
theorem Valid.tile_contained [Fintype ιₜ] [DecidableEq ιₜ]
    {t : TileSet ps ιₜ} {region : Region}
    (hv : t.Valid region) (i : ιₜ) :
    t.cellsAt i ⊆ region := by
  rw [← hv.covers]
  intro c hc
  simp only [coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i, hc⟩

/-- Translate a tileset by an offset -/
def translate (t : TileSet ps ιₜ) (offset : Cell) : TileSet ps ιₜ :=
  ⟨fun i => (t i).translate offset⟩

/-- Translation of a tileset preserves disjointness -/
theorem translate_preserves_disjoint [DecidableEq ιₜ]
    (t : TileSet ps ιₜ) (offset : Cell)
    (hdisj : t.PairwiseDisjoint) :
    (t.translate offset).PairwiseDisjoint := by
  intro i j hij
  have hdisj_orig := hdisj i j hij
  rw [cellsAt, cellsAt, translate, PlacedTile.translate_cells,
      PlacedTile.translate_cells]
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
    (t : TileSet ps ιₜ) (offset : Cell) :
    (t.translate offset).coveredCells =
      translateRegion t.coveredCells offset := by
  simp only [coveredCells, translate]
  change
    Finset.univ.biUnion (fun i => ((t i).translate offset).cells ps) =
      translateRegion (Finset.univ.biUnion (fun i => (t i).cells ps)) offset
  rw [Finset.biUnion_congr rfl
        (fun i _ => PlacedTile.translate_cells ps (t i) offset)]
  simp only [translateRegion]
  rw [← Finset.biUnion_image]

/-- Translation preserves validity -/
theorem translate_preserves_valid [Fintype ιₜ] [DecidableEq ιₜ]
    (t : TileSet ps ιₜ) (offset : Cell) (region : Region)
    (hv : t.Valid region) :
    (t.translate offset).Valid (translateRegion region offset) := by
  constructor
  · exact translate_preserves_disjoint t offset hv.disjoint
  · rw [translate_coveredCells, hv.covers]

end TileSet

/- ## General Tileability -/

/-- A region is tileable by a protoset if there exists a valid tiling -/
def Tileable {ι : Type*} (ps : Protoset ι) (r : Region) : Prop :=
  ∃ (ιₜ : Type) (_ : Fintype ιₜ) (_ : DecidableEq ιₜ)
    (t : TileSet ps ιₜ), t.Valid r

/-- The empty region is tileable by any protoset -/
theorem empty_tileable {ι : Type*} (ps : Protoset ι) :
    Tileable ps ∅ :=
  ⟨Fin 0, inferInstance, inferInstance, ⟨Fin.elim0⟩,
    ⟨fun i _ _ => Fin.elim0 i, by simp [TileSet.coveredCells]⟩⟩

/-- A translated tileable region is tileable by any protoset -/
theorem Tileable_translate {ι : Type*} (ps : Protoset ι) {r : Region}
    (h : Tileable ps r) (offset : Cell) :
    Tileable ps (translateRegion r offset) := by
  obtain ⟨ιₜ, _, _, t, hv⟩ := h
  use ιₜ, inferInstance, inferInstance, t.translate offset
  exact t.translate_preserves_valid offset r hv

/-- If two disjoint regions are both tileable, their union is tileable -/
theorem Tileable_union {ι : Type*} (ps : Protoset ι)
    {r1 r2 : Region} (h1 : Tileable ps r1) (h2 : Tileable ps r2)
    (hdisj : Disjoint r1 r2) :
    Tileable ps (r1 ∪ r2) := by
  obtain ⟨ι1, _, _, t1, hv1⟩ := h1
  obtain ⟨ι2, _, _, t2, hv2⟩ := h2
  -- Combine the two tilesets
  let t : TileSet ps (ι1 ⊕ ι2) :=
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
        simp only [TileSet.coveredCells, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact ⟨i1, hc⟩
      have hd2 : d ∈ r2 := by
        rw [← hv2.covers]
        simp only [TileSet.coveredCells, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact ⟨j2, hd⟩
      exact Finset.disjoint_iff_ne.mp hdisj c hc1 d hd2
    | Sum.inr i2, Sum.inl j1 =>
      simp only [TileSet.cellsAt, Finset.disjoint_iff_ne]
      intro c hc d hd
      have hc2 : c ∈ r2 := by
        rw [← hv2.covers]
        simp only [TileSet.coveredCells, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact ⟨i2, hc⟩
      have hd1 : d ∈ r1 := by
        rw [← hv1.covers]
        simp only [TileSet.coveredCells, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact ⟨j1, hd⟩
      exact Finset.disjoint_iff_ne.mp hdisj d hd1 c hc2 ∘ Eq.symm
  · -- Covers
    simp only [TileSet.coveredCells, ← hv1.covers, ← hv2.covers]
    ext c
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
      true_and, TileSet.cellsAt]
    constructor
    · rintro ⟨i, hi⟩
      match i with
      | Sum.inl i1 => left; exact ⟨i1, hi⟩
      | Sum.inr i2 => right; exact ⟨i2, hi⟩
    · intro h
      rcases h with ⟨i1, hi1⟩ | ⟨i2, hi2⟩
      · exact ⟨Sum.inl i1, hi1⟩
      · exact ⟨Sum.inr i2, hi2⟩

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
theorem Tileable_translate_iff {ι : Type*} (ps : Protoset ι)
    (r : Region) (offset : Cell) :
    Tileable ps r ↔ Tileable ps (translateRegion r offset) := by
  constructor
  · exact fun h => Tileable_translate ps h offset
  · intro h
    have h' := Tileable_translate ps h (-offset.1, -offset.2)
    rw [translateRegion_neg] at h'
    exact h'

/-- If `R = translateRegion S offset` and `R` is tileable, then `S` is tileable -/
theorem Tileable_of_translate_eq {ι : Type*} (ps : Protoset ι)
    {R S : Region} (offset : Cell)
    (heq : R = translateRegion S offset) (hR : Tileable ps R) :
    Tileable ps S := by
  rw [heq] at hR
  exact (Tileable_translate_iff ps S offset).mpr hR

/- ## Helper for Creating TileSets -/

/-- Create a `TileSet` from a function -/
def mkTileSet {ι : Type*} (ps : Protoset ι) (ιₜ : Type*)
    (f : ιₜ → PlacedTile ι) : TileSet ps ιₜ :=
  ⟨f⟩

/-- Create a placed tile -/
def mkPlacedTile {ι : Type*} (i : ι) (x y : ℤ) (r : Fin 4) :
    PlacedTile ι :=
  ⟨i, (x, y), r⟩

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



/- ## Generic Placement Enumeration -/

/-- A placed tile is contained in a region if all its cells are in the region -/
def PlacedTile.containedIn {ι : Type*} (ps : Protoset ι)
    (pt : PlacedTile ι) (r : Region) : Prop :=
  pt.cells ps ⊆ r

instance {ι : Type*} (ps : Protoset ι)
    (pt : PlacedTile ι) (r : Region) :
    Decidable (pt.containedIn ps r) :=
  inferInstanceAs (Decidable (pt.cells ps ⊆ r))

/-- A placed tile covers a cell if the cell is in its cells -/
def PlacedTile.coversCell {ι : Type*} (ps : Protoset ι)
    (pt : PlacedTile ι) (c : Cell) : Prop :=
  c ∈ pt.cells ps

instance {ι : Type*} (ps : Protoset ι)
    (pt : PlacedTile ι) (c : Cell) :
    Decidable (pt.coversCell ps c) :=
  inferInstanceAs (Decidable (c ∈ pt.cells ps))

/-- All placements of a single prototile that cover a given target cell.
For each cell `c` in the prototile and each rotation `r`, the unique
translation that maps `rotateCell c r` to `target` is:
`target - rotateCell c r`. -/
def allPlacementsCoveringProto {ι : Type*}
    (i : ι) (proto : Prototile) (target : Cell) :
    List (PlacedTile ι) :=
  proto.cells.flatMap fun baseCell =>
    (List.finRange 4).map fun r =>
      let rotated := rotateCell baseCell r
      ⟨i, (target.1 - rotated.1, target.2 - rotated.2), r⟩

/-- All placements from a protoset that cover a given target cell -/
def allPlacementsCovering {ι : Type*}
    (ps : Protoset ι) (indices : List ι) (target : Cell) :
    List (PlacedTile ι) :=
  indices.flatMap fun i => allPlacementsCoveringProto i (ps i) target

/-- Every placement produced by `allPlacementsCoveringProto`
actually covers the target -/
theorem allPlacementsCoveringProto_covers {ι : Type*}
    (ps : Protoset ι) (i : ι) (target : Cell) (pt : PlacedTile ι)
    (hpt : pt ∈ allPlacementsCoveringProto i (ps i) target) :
    pt.coversCell ps target := by
  simp only [allPlacementsCoveringProto, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hpt
  obtain ⟨baseCell, hbase, r, rfl⟩ := hpt
  simp only [PlacedTile.coversCell, PlacedTile.cells, Finset.mem_image,
    translateCell]
  refine ⟨rotateCell baseCell r, ?_, ?_⟩
  · simp only [rotateProto, Finset.mem_image]
    exact ⟨baseCell, Prototile.mem_coe (ps i) baseCell |>.mpr hbase, rfl⟩
  · ext <;> ring

/-- `allPlacementsCoveringProto` is complete: any placement with index `i`
covering `target` is in the list. -/
theorem allPlacementsCoveringProto_complete {ι : Type*}
    (ps : Protoset ι) (i : ι) (target : Cell) (pt : PlacedTile ι)
    (hidx : pt.index = i) (hcover : pt.coversCell ps target) :
    pt ∈ allPlacementsCoveringProto i (ps i) target := by
  simp only [PlacedTile.coversCell, PlacedTile.cells] at hcover
  simp only [Finset.mem_image, translateCell] at hcover
  obtain ⟨rotatedCell, hrot, htrans⟩ := hcover
  simp only [rotateProto, Finset.mem_image] at hrot
  obtain ⟨origCell, horig, rfl⟩ := hrot
  simp only [allPlacementsCoveringProto, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and]
  rw [hidx] at horig
  rw [(ps i).mem_coe] at horig
  refine ⟨origCell, horig, pt.rotation, ?_⟩
  rw [Prod.mk.injEq] at htrans
  obtain ⟨htx, hty⟩ := htrans
  obtain ⟨idx, trans, rot⟩ := pt
  simp only at hidx htx hty; subst hidx
  simp only [PlacedTile.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  ext <;> omega

/-! Placements covering a cell and contained in a region -/
def placementsCoveringIn {ι : Type*} (ps : Protoset ι)
    (indices : List ι) (target : Cell) (region : Region) :
    List (PlacedTile ι) :=
  (allPlacementsCovering ps indices target).filter
    fun pt => pt.containedIn ps region
