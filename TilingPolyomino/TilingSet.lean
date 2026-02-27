import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic
import TilingPolyomino.RectOmega

open Set Function

-- ============================================================
-- Core hierarchy (mirrors Tiling.lean with Set Cell)
-- ============================================================

/-- A set-based prototile: a finite nonempty set of cells -/
structure SetPrototile where
  cells : Set Cell
  finite : cells.Finite
  nonempty : cells.Nonempty

/-- A protoset is an indexed family of set-based prototiles -/
def SetProtoset (ι : Type*) := ι → SetPrototile

instance {ι : Type*} : CoeFun (SetProtoset ι) (fun _ => ι → SetPrototile) where
  coe ps := ps

/-- A placed tile: index into protoset, translation, and rotation -/
structure SetPlacedTile (ι : Type*) where
  index : ι
  translation : Cell
  rotation : Fin 4

/-- The cells covered by a placed tile under protoset ps -/
def SetPlacedTile.cells {ι : Type*} (ps : SetProtoset ι) (pt : SetPlacedTile ι) : Set Cell :=
  translate pt.translation.1 pt.translation.2 (rotate pt.rotation (ps pt.index).cells)

/-- An indexed family of placed tiles -/
structure SetTileSet {ι : Type*} (ps : SetProtoset ι) (ιₜ : Type*) where
  tiles : ιₜ → SetPlacedTile ι

namespace SetTileSet

variable {ι : Type*} {ps : SetProtoset ι} {ιₜ : Type*}

def cellsAt (t : SetTileSet ps ιₜ) (i : ιₜ) : Set Cell :=
  (t.tiles i).cells ps

/-- All cells covered by the tiling (finite union over all tiles) -/
def coveredCells (t : SetTileSet ps ιₜ) : Set Cell :=
  ⋃ i : ιₜ, t.cellsAt i

/-- A valid tiling: pairwise disjoint tiles that exactly cover R -/
structure Valid (t : SetTileSet ps ιₜ) (R : Set Cell) : Prop where
  disjoint : ∀ i j : ιₜ, i ≠ j → Disjoint (t.cellsAt i) (t.cellsAt j)
  covers : t.coveredCells = R

end SetTileSet

/-- R is tileable by protoset ps if there exists a finite valid tiling -/
def SetTileable (R : Set Cell) {ι : Type*} (ps : SetProtoset ι) : Prop :=
  ∃ (ιₜ : Type) (_ : Fintype ιₜ) (t : SetTileSet ps ιₜ), t.Valid R

-- ============================================================
-- Finite lemmas for transformations
-- ============================================================

theorem translate_finite (dx dy : ℤ) (s : Set Cell) (h : s.Finite) :
    (translate dx dy s).Finite := by
  have h_inj : Function.Injective (fun p : Cell => (p.1 - dx, p.2 - dy)) := by
    intro ⟨x1, y1⟩ ⟨x2, y2⟩ heq
    simp only [Prod.mk.injEq] at heq
    ext <;> omega
  dsimp [translate]; exact h.preimage h_inj.injOn

theorem rotate_finite (r : Fin 4) (s : Set Cell) (h : s.Finite) :
    (rotate r s).Finite :=
  h.preimage (rotateCell_injective (inverseRot r)).injOn

namespace SetPlacedTile

variable {ι : Type*} {ps : SetProtoset ι} (pt : SetPlacedTile ι)

theorem cells_finite : (pt.cells ps).Finite :=
  translate_finite _ _ _ (rotate_finite _ _ (ps pt.index).finite)

theorem cells_ncard_eq : (pt.cells ps).ncard = (ps pt.index).cells.ncard := by
  simp only [cells]
  rw [translate_ncard _ _ _ (rotate_finite _ _ (ps pt.index).finite),
      rotate_ncard _ _ (ps pt.index).finite]

end SetPlacedTile

-- ============================================================
-- Translation helper lemmas
-- ============================================================

private theorem translate_compose (dx dy dx' dy' : ℤ) (S : Set Cell) :
    translate dx dy (translate dx' dy' S) = translate (dx + dx') (dy + dy') S := by
  ext ⟨x, y⟩; simp only [mem_translate]
  rw [show x - dx - dx' = x - (dx + dx') from by omega,
      show y - dy - dy' = y - (dy + dy') from by omega]

private theorem translate_iUnion_eq {α : Type*} (dx dy : ℤ) (A : α → Set Cell) :
    translate dx dy (⋃ i, A i) = ⋃ i, translate dx dy (A i) := by
  ext p
  simp [mem_translate]

private theorem translate_disjoint_iff (dx dy : ℤ) {A B : Set Cell} :
    Disjoint (translate dx dy A) (translate dx dy B) ↔ Disjoint A B := by
  constructor
  · intro h
    rw [Set.disjoint_left] at h ⊢
    intro p hpA hpB
    have hpA' : (p.1 + dx, p.2 + dy) ∈ translate dx dy A := by
      simpa [mem_translate] using hpA
    have hpB' : (p.1 + dx, p.2 + dy) ∈ translate dx dy B := by
      simpa [mem_translate] using hpB
    exact h hpA' hpB'
  · intro h
    rw [Set.disjoint_left] at h ⊢
    intro p hpA hpB
    have hpA' : (p.1 - dx, p.2 - dy) ∈ A := by
      simpa [mem_translate] using hpA
    have hpB' : (p.1 - dx, p.2 - dy) ∈ B := by
      simpa [mem_translate] using hpB
    exact h hpA' hpB'

-- ============================================================
-- Cardinality necessary condition
-- ============================================================

theorem SetTileable.ncard_dvd {R : Set Cell} {ι : Type*} {ps : SetProtoset ι}
    [Subsingleton ι] (_hR : R.Finite) (ht : SetTileable R ps) :
    ∀ i : ι, (ps i).cells.ncard ∣ R.ncard := by
  obtain ⟨ιₜ, hft, t, hv⟩ := ht
  haveI : Fintype ιₜ := hft
  haveI : Finite ιₜ := inferInstance
  intro i
  have h_card_eq : ∀ j : ιₜ, (t.cellsAt j).ncard = (ps i).cells.ncard := fun j => by
    rw [SetTileSet.cellsAt, SetPlacedTile.cells_ncard_eq]
    rw [show (t.tiles j).index = i from Subsingleton.elim _ _]
  have h_tile_fin : ∀ j : ιₜ, (t.cellsAt j).Finite := fun _ => SetPlacedTile.cells_finite _
  have h_union : (⋃ j : ιₜ, t.cellsAt j).ncard = ∑ᶠ j : ιₜ, (t.cellsAt j).ncard :=
    Set.ncard_iUnion_of_finite h_tile_fin (fun j k hjk => hv.disjoint j k hjk)
  have h_R : R.ncard = ∑ᶠ j : ιₜ, (t.cellsAt j).ncard := by
    have hcov : (⋃ j : ιₜ, t.cellsAt j) = R := by
      have := hv.covers; simp only [SetTileSet.coveredCells] at this; exact this
    exact (congrArg Set.ncard hcov).symm.trans h_union
  rw [h_R, finsum_eq_sum_of_fintype,
      Finset.sum_congr rfl (fun j _ => h_card_eq j),
      Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact dvd_mul_left _ _

-- ============================================================
-- Empty region
-- ============================================================

theorem SetTileable.empty {ι : Type*} (ps : SetProtoset ι) :
    SetTileable (∅ : Set Cell) ps :=
  ⟨Empty, inferInstance, ⟨Empty.elim⟩,
    ⟨fun i => i.elim, by simp [SetTileSet.coveredCells]⟩⟩

-- ============================================================
-- Translation
-- ============================================================

theorem SetTileable.translate {ι : Type*} {ps : SetProtoset ι} {R : Set Cell}
    (h : SetTileable R ps) (dx dy : ℤ) :
    SetTileable (_root_.translate dx dy R) ps := by
  obtain ⟨ιₜ, hft, t, hv⟩ := h
  let t' : SetTileSet ps ιₜ := ⟨fun i => {
    index := (t.tiles i).index
    translation := (dx + (t.tiles i).translation.1, dy + (t.tiles i).translation.2)
    rotation := (t.tiles i).rotation }⟩
  have h_eq : ∀ j : ιₜ, t'.cellsAt j = _root_.translate dx dy (t.cellsAt j) := fun j => by
    simp only [SetTileSet.cellsAt, SetPlacedTile.cells, t']
    rw [← translate_compose]
  have h_cov : ∀ j, t.cellsAt j ⊆ R := fun j p hp => by
    have : p ∈ t.coveredCells := Set.mem_iUnion.mpr ⟨j, hp⟩
    rwa [hv.covers] at this
  refine ⟨ιₜ, hft, t', ⟨?_, ?_⟩⟩
  · intro i j hij
    rw [h_eq i, h_eq j]
    exact (translate_disjoint_iff dx dy).mpr (hv.disjoint i j hij)
  · simp only [SetTileSet.coveredCells]
    calc
      (⋃ j : ιₜ, t'.cellsAt j) = ⋃ j : ιₜ, _root_.translate dx dy (t.cellsAt j) := by
        simpa using iUnion_congr h_eq
      _ = _root_.translate dx dy (⋃ j : ιₜ, t.cellsAt j) := by
        symm
        exact translate_iUnion_eq dx dy (fun j => t.cellsAt j)
      _ = _root_.translate dx dy R := by
        simpa [SetTileSet.coveredCells] using congrArg (_root_.translate dx dy) hv.covers

theorem SetTileable_translate {ι : Type*} {ps : SetProtoset ι} {R : Set Cell}
    (h : SetTileable R ps) (dx dy : ℤ) :
    SetTileable (_root_.translate dx dy R) ps := h.translate dx dy

/-- Alias -/
theorem setTileable_translate {ι : Type*} {ps : SetProtoset ι} {R : Set Cell}
    (h : SetTileable R ps) (dx dy : ℤ) :
    SetTileable (_root_.translate dx dy R) ps := h.translate dx dy

-- ============================================================
-- Union
-- ============================================================

theorem SetTileable.union {ι : Type*} {ps : SetProtoset ι} {R S : Set Cell}
    (hR : SetTileable R ps) (hS : SetTileable S ps) (hdisj : Disjoint R S) :
    SetTileable (R ∪ S) ps := by
  obtain ⟨ιR, hfR, tR, hvR⟩ := hR
  obtain ⟨ιS, hfS, tS, hvS⟩ := hS
  haveI : Fintype ιR := hfR; haveI : Fintype ιS := hfS
  let t : SetTileSet ps (ιR ⊕ ιS) := ⟨Sum.elim tR.tiles tS.tiles⟩
  have covR : (⋃ i : ιR, (tR.tiles i).cells ps) = R := by
    have := hvR.covers; simp only [SetTileSet.coveredCells, SetTileSet.cellsAt] at this; exact this
  have covS : (⋃ i : ιS, (tS.tiles i).cells ps) = S := by
    have := hvS.covers; simp only [SetTileSet.coveredCells, SetTileSet.cellsAt] at this; exact this
  refine ⟨ιR ⊕ ιS, inferInstance, t, ⟨?_, ?_⟩⟩
  · intro i j hij
    simp only [SetTileSet.cellsAt, t]
    cases i <;> cases j <;> simp only [Sum.elim]
    · exact hvR.disjoint _ _ (fun h => hij (congrArg Sum.inl h))
    · apply Set.disjoint_left.mpr
      intro p h1 h2
      have hpR : p ∈ R := covR ▸ Set.mem_iUnion.mpr ⟨_, h1⟩
      have hpS : p ∈ S := covS ▸ Set.mem_iUnion.mpr ⟨_, h2⟩
      exact absurd hpS (Set.disjoint_left.mp hdisj hpR)
    · apply Set.disjoint_left.mpr
      intro p h1 h2
      have hpS : p ∈ S := covS ▸ Set.mem_iUnion.mpr ⟨_, h1⟩
      have hpR : p ∈ R := covR ▸ Set.mem_iUnion.mpr ⟨_, h2⟩
      exact absurd hpS (Set.disjoint_left.mp hdisj hpR)
    · exact hvS.disjoint _ _ (fun h => hij (congrArg Sum.inr h))
  · simp only [SetTileSet.coveredCells, SetTileSet.cellsAt, t]
    ext p
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      cases i with
      | inl i => exact Or.inl (covR ▸ Set.mem_iUnion.mpr ⟨i, hi⟩)
      | inr i => exact Or.inr (covS ▸ Set.mem_iUnion.mpr ⟨i, hi⟩)
    · rintro (hpR | hpS)
      · rw [← covR] at hpR
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpR
        exact ⟨Sum.inl i, hi⟩
      · rw [← covS] at hpS
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpS
        exact ⟨Sum.inr i, hi⟩

-- ============================================================
-- Remove two tiles
-- ============================================================

theorem SetTileable.remove_two {ι : Type*} {ps : SetProtoset ι} {R S : Set Cell} {ιₜ : Type}
    [Fintype ιₜ] (t : SetTileSet ps ιₜ) (hv : t.Valid R)
    (i₀ i₁ : ιₜ) (_hi : i₀ ≠ i₁) (hS : t.cellsAt i₀ ∪ t.cellsAt i₁ = S) :
    SetTileable (R \ S) ps := by
  let ιₜ' : Type := {j : ιₜ // j ≠ i₀ ∧ j ≠ i₁}
  haveI : DecidableEq ιₜ := Classical.decEq _
  haveI : Fintype ιₜ' := inferInstance
  let t' : SetTileSet ps ιₜ' := ⟨fun ⟨j, _⟩ => t.tiles j⟩
  -- t'.cellsAt ⟨j, _⟩ = t.cellsAt j
  have h_cell : ∀ j (hj : j ≠ i₀ ∧ j ≠ i₁), t'.cellsAt ⟨j, hj⟩ = t.cellsAt j := fun _ _ => rfl
  have h_cov : (⋃ j : ιₜ, t.cellsAt j) = R := by
    have := hv.covers; simp only [SetTileSet.coveredCells] at this; exact this
  exact ⟨ιₜ', inferInstance, t', ⟨
    (fun ⟨i, hi_ne⟩ ⟨j, hj_ne⟩ hne => by
      simp only [h_cell]
      exact hv.disjoint i j (fun h => hne (Subtype.ext h))),
    (by
      simp only [SetTileSet.coveredCells]
      ext p
      constructor
      · intro hp
        rcases Set.mem_iUnion.mp hp with ⟨⟨j, ⟨hj0, hj1⟩⟩, hpj⟩
        have hpj' : p ∈ t.cellsAt j := by
          simpa [h_cell] using hpj
        refine ⟨h_cov ▸ Set.mem_iUnion.mpr ⟨j, hpj'⟩, fun hs => ?_⟩
        rw [← hS] at hs
        rcases hs with h0 | h1
        · exact absurd h0 (Set.disjoint_left.mp (hv.disjoint j i₀ hj0) hpj')
        · exact absurd h1 (Set.disjoint_left.mp (hv.disjoint j i₁ hj1) hpj')
      · rintro ⟨hpR, hpnS⟩
        rw [← h_cov] at hpR
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hpR
        have hj0 : j ≠ i₀ := fun h => hpnS (hS ▸ Or.inl (h ▸ hj))
        have hj1 : j ≠ i₁ := fun h => hpnS (hS ▸ Or.inr (h ▸ hj))
        exact Set.mem_iUnion.mpr ⟨⟨j, ⟨hj0, hj1⟩⟩, by simpa [h_cell] using hj⟩)
  ⟩⟩

-- ============================================================
-- Refinement theorem
-- ============================================================

/-- If R is tiled by psP, and each psP-placed-tile region can be tiled by psQ,
    then R is tiled by psQ -/
theorem SetTileable.refine {R : Set Cell} {ιP ιQ : Type*} {psP : SetProtoset ιP}
    {psQ : SetProtoset ιQ}
    (hR : SetTileable R psP)
    (hpieces : ∀ (pt : SetPlacedTile ιP), SetTileable (pt.cells psP) psQ) :
    SetTileable R psQ := by
  obtain ⟨ιₜP, hfP, tP, hvP⟩ := hR
  haveI : Fintype ιₜP := hfP
  choose ιₜQ hfQ tQ hvQ using fun j : ιₜP => hpieces (tP.tiles j)
  haveI := fun j => hfQ j
  let t : SetTileSet psQ (Σ j : ιₜP, ιₜQ j) := ⟨fun ⟨j, k⟩ => (tQ j).tiles k⟩
  -- cells of t at (j, k) = cells of tQ j at k
  have h_cell : ∀ j k, t.cellsAt ⟨j, k⟩ = (tQ j).cellsAt k := fun _ _ => rfl
  -- cell coverage for each sub-tiling
  have h_cov_Q : ∀ j, (⋃ k : ιₜQ j, (tQ j).cellsAt k) = (tP.tiles j).cells psP := fun j => by
    have := (hvQ j).covers; simp only [SetTileSet.coveredCells] at this; exact this
  have h_cov_P : (⋃ j : ιₜP, (tP.tiles j).cells psP) = R := by
    have := hvP.covers; simp only [SetTileSet.coveredCells, SetTileSet.cellsAt] at this; exact this
  refine ⟨_, inferInstance, t, ⟨?_, ?_⟩⟩
  · intro ⟨j₁, k₁⟩ ⟨j₂, k₂⟩ hne
    simp only [h_cell]
    by_cases hj : j₁ = j₂
    · subst hj
      exact (hvQ j₁).disjoint k₁ k₂ (fun h => hne (Sigma.ext rfl (heq_of_eq h)))
    · apply Set.disjoint_of_subset
        (fun p hp => h_cov_Q j₁ ▸ Set.mem_iUnion.mpr ⟨k₁, hp⟩)
        (fun p hp => h_cov_Q j₂ ▸ Set.mem_iUnion.mpr ⟨k₂, hp⟩)
      exact hvP.disjoint j₁ j₂ hj
  · simp only [SetTileSet.coveredCells]
    ext p
    simp only [h_cell, Set.mem_iUnion, Sigma.exists]
    constructor
    · rintro ⟨j, k, hp⟩
      have : p ∈ (tP.tiles j).cells psP := h_cov_Q j ▸ Set.mem_iUnion.mpr ⟨k, hp⟩
      exact h_cov_P ▸ Set.mem_iUnion.mpr ⟨j, this⟩
    · intro hp
      rw [← h_cov_P] at hp
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
      rw [← h_cov_Q j] at hj
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hj
      exact ⟨j, k, hk⟩

-- ============================================================
-- Partition-based refinement
-- ============================================================

/-- Partition-based refinement (Fintype index) -/
theorem SetTileable.refine_partition {ι : Type} [Fintype ι] {ιQ : Type*} {R : Set Cell}
    {psQ : SetProtoset ιQ}
    (pieces : ι → Set Cell)
    (hcover : ⋃ i, pieces i = R)
    (hdisj : Pairwise (Disjoint on pieces))
    (htile : ∀ i, SetTileable (pieces i) psQ) :
    SetTileable R psQ := by
  choose ιₜ hft t hv using htile
  haveI := fun i => hft i
  let t' : SetTileSet psQ (Σ i : ι, ιₜ i) := ⟨fun ⟨i, j⟩ => (t i).tiles j⟩
  have h_cell : ∀ i j, t'.cellsAt ⟨i, j⟩ = (t i).cellsAt j := fun _ _ => rfl
  have h_cov : ∀ i, (⋃ j : ιₜ i, (t i).cellsAt j) = pieces i := fun i => by
    have := (hv i).covers; simp only [SetTileSet.coveredCells] at this; exact this
  refine ⟨_, inferInstance, t', ⟨?_, ?_⟩⟩
  · intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hne
    simp only [h_cell]
    by_cases hi : i₁ = i₂
    · subst hi
      exact (hv i₁).disjoint j₁ j₂ (fun h => hne (Sigma.ext rfl (heq_of_eq h)))
    · apply Set.disjoint_of_subset
        (fun p hp => h_cov i₁ ▸ Set.mem_iUnion.mpr ⟨j₁, hp⟩)
        (fun p hp => h_cov i₂ ▸ Set.mem_iUnion.mpr ⟨j₂, hp⟩)
      exact hdisj hi
  · simp only [SetTileSet.coveredCells]
    ext p
    simp only [h_cell, Set.mem_iUnion, Sigma.exists]
    constructor
    · rintro ⟨i, j, hp⟩
      exact hcover ▸ Set.mem_iUnion.mpr ⟨i, h_cov i ▸ Set.mem_iUnion.mpr ⟨j, hp⟩⟩
    · intro hp
      rw [← hcover] at hp
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
      rw [← h_cov i] at hi
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
      exact ⟨i, j, hj⟩

-- ============================================================
-- Swap region
-- ============================================================

protected def Set.swapRegion (R : Set Cell) : Set Cell := {p | (p.2, p.1) ∈ R}

@[simp] theorem mem_swapRegion (R : Set Cell) (p : Cell) :
    p ∈ Set.swapRegion R ↔ (p.2, p.1) ∈ R := Iff.rfl

-- ============================================================
-- Horizontal and vertical union
-- ============================================================

theorem SetTileable.horizontal_union {ι : Type*} {ps : SetProtoset ι} {a b m : ℤ}
    (ha_pos : 0 ≤ a) (hb_pos : 0 ≤ b)
    (ha : SetTileable (rect 0 0 a m) ps)
    (hb : SetTileable (rect a 0 (a + b) m) ps) :
    SetTileable (rect 0 0 (a + b) m) ps := by
  have h_eq : rect 0 0 (a + b) m = rect 0 0 a m ∪ rect a 0 (a + b) m := by
    ext p; simp only [mem_rect, Set.mem_union]; omega
  have h_disj : Disjoint (rect 0 0 a m) (rect a 0 (a + b) m) := by
    rw [Set.disjoint_left]; intro p h1 h2
    simp only [mem_rect] at h1 h2; omega
  rw [h_eq]; exact SetTileable.union ha hb h_disj

theorem SetTileable.vertical_union {ι : Type*} {ps : SetProtoset ι} {n a b : ℤ}
    (ha_pos : 0 ≤ a) (hb_pos : 0 ≤ b)
    (ha : SetTileable (rect 0 0 n a) ps)
    (hb : SetTileable (rect 0 a n (a + b)) ps) :
    SetTileable (rect 0 0 n (a + b)) ps := by
  have h_eq : rect 0 0 n (a + b) = rect 0 0 n a ∪ rect 0 a n (a + b) := by
    ext p; simp only [mem_rect, Set.mem_union]; omega
  have h_disj : Disjoint (rect 0 0 n a) (rect 0 a n (a + b)) := by
    rw [Set.disjoint_left]; intro p h1 h2
    simp only [mem_rect] at h1 h2; omega
  rw [h_eq]; exact SetTileable.union ha hb h_disj

-- ============================================================
-- Scale rect: tiling a×b implies tiling (n·a)×(m·b)
-- ============================================================

/-- If ps tiles an a×b rectangle (a > 0), it tiles an (n·a)×b rectangle (n ≥ 1). -/
theorem SetTileable.scale_rect_horiz {ι : Type*} {ps : SetProtoset ι} {a b : ℤ}
    (h : SetTileable (rect 0 0 a b) ps) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) :
    SetTileable (rect 0 0 ((n : ℤ) * a) b) ps := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  clear hn
  induction k with
  | zero => norm_num; exact h
  | succ k ih =>
    have h_left : SetTileable (rect 0 0 ((↑(k + 1) : ℤ) * a) b) ps := ih
    have h_right : SetTileable (rect ((↑(k + 1) : ℤ) * a) 0 ((↑(k + 1) : ℤ) * a + a) b) ps := by
      have translate_eq : rect ((↑(k + 1) : ℤ) * a) 0 ((↑(k + 1) : ℤ) * a + a) b =
                         _root_.translate ((↑(k + 1) : ℤ) * a) 0 (rect 0 0 a b) := by
        ext ⟨x, y⟩; simp only [mem_rect, mem_translate]; constructor
        · intro ⟨h1, h2, h3, h4⟩; exact ⟨by omega, by omega, by omega, by omega⟩
        · intro ⟨h1, h2, h3, h4⟩; exact ⟨by omega, by omega, by omega, by omega⟩
      rw [translate_eq]
      exact setTileable_translate h _ _
    have ha_nonneg : 0 ≤ (↑(k + 1) : ℤ) * a := mul_nonneg (Nat.cast_nonneg _) (le_of_lt ha)
    have ha_pos : 0 ≤ a := le_of_lt ha
    have succ_eq : (↑(k + 1).succ : ℤ) * a = (↑(k + 1) : ℤ) * a + a := by
      simp only [Nat.cast_succ]; ring
    rw [succ_eq]
    exact SetTileable.horizontal_union ha_nonneg ha_pos h_left h_right

/-- If ps tiles an a×b rectangle (b > 0), it tiles a c×(m·b) rectangle (m ≥ 1). -/
theorem SetTileable.scale_rect_vert {ι : Type*} {ps : SetProtoset ι} {c b : ℤ}
    (h : SetTileable (rect 0 0 c b) ps) (hb : 0 < b) (hc : 0 ≤ c)
    (m : ℕ) (hm : 1 ≤ m) :
    SetTileable (rect 0 0 c ((m : ℤ) * b)) ps := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  clear hm
  induction k with
  | zero => norm_num; exact h
  | succ k ih =>
    have h_left : SetTileable (rect 0 0 c ((↑(k + 1) : ℤ) * b)) ps := ih
    have h_right : SetTileable (rect 0 ((↑(k + 1) : ℤ) * b) c ((↑(k + 1) : ℤ) * b + b)) ps := by
      have translate_eq : rect 0 ((↑(k + 1) : ℤ) * b) c ((↑(k + 1) : ℤ) * b + b) =
                         _root_.translate 0 ((↑(k + 1) : ℤ) * b) (rect 0 0 c b) := by
        ext ⟨x, y⟩; simp only [mem_rect, mem_translate]; constructor
        · intro ⟨h1, h2, h3, h4⟩; exact ⟨by omega, by omega, by omega, by omega⟩
        · intro ⟨h1, h2, h3, h4⟩; exact ⟨by omega, by omega, by omega, by omega⟩
      rw [translate_eq]
      exact setTileable_translate h _ _
    have hb_nonneg : 0 ≤ (↑(k + 1) : ℤ) * b := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hb)
    have hb_pos : 0 ≤ b := le_of_lt hb
    have succ_eq : (↑(k + 1).succ : ℤ) * b = (↑(k + 1) : ℤ) * b + b := by
      simp only [Nat.cast_succ]; ring
    rw [succ_eq]
    exact SetTileable.vertical_union hb_nonneg hb_pos h_left h_right

/-- If ps tiles an a×b rectangle (a,b > 0), it tiles any (n·a)×(m·b) rectangle (n,m ≥ 1). -/
theorem SetTileable.scale_rect {ι : Type*} {ps : SetProtoset ι} {a b : ℤ}
    (h : SetTileable (rect 0 0 a b) ps) (ha : 0 < a) (hb : 0 < b)
    (n m : ℕ) (_hn : 1 ≤ n) (_hm : 1 ≤ m) :
    SetTileable (rect 0 0 ((n : ℤ) * a) ((m : ℤ) * b)) ps :=
  (h.scale_rect_horiz ha n _hn).scale_rect_vert hb (mul_nonneg (Nat.cast_nonneg _) (le_of_lt ha)) m _hm

-- ============================================================
-- Empty rectangle
-- ============================================================

theorem rect_empty_of_eq (x0 x1 y : ℤ) : rect x0 y x1 y = ∅ := by
  ext p; simp only [mem_rect, Set.mem_empty_iff_false, iff_false]; omega

-- ============================================================
-- Rotation cancellation lemmas (used by generic bridge)
-- ============================================================

/-- Rotating then applying the inverse rotation gives the identity. -/
theorem rotateCell_inverseRot_cancel (c : Cell) (r : Fin 4) :
    rotateCell (rotateCell c r) (inverseRot r) = c := by
  fin_cases r <;>
  simp only [inverseRot, rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3] <;>
  ext <;> simp [rotateCell_1, rotateCell_2, rotateCell_3]

/-- Applying the inverse rotation then rotating gives the identity. -/
theorem rotateCell_inverseRot_cancel' (c : Cell) (r : Fin 4) :
    rotateCell (rotateCell c (inverseRot r)) r = c := by
  fin_cases r <;>
  simp only [inverseRot, rotateCell_0, rotateCell_1, rotateCell_2, rotateCell_3] <;>
  ext <;> simp [rotateCell_1, rotateCell_2, rotateCell_3]

-- ============================================================
-- SetPrototile extensionality
-- ============================================================

/-- Two `SetPrototile` values are equal iff their `cells` fields are equal.
    (The `finite` and `nonempty` fields are propositions, hence proof-irrelevant.) -/
@[ext]
theorem SetPrototile.ext {a b : SetPrototile} (h : a.cells = b.cells) : a = b := by
  obtain ⟨c₁, _, _⟩ := a; obtain ⟨c₂, _, _⟩ := b; simp only at h; subst h; rfl

-- ============================================================
-- Generic Finset ↔ Set bridge
-- ============================================================

/-- A `SetProtoset sps` is *compatible* with a `Protoset ps` if their cell sets agree:
    for all `i`, `(sps i).cells = ↑(ps i : Finset Cell)`. -/
def ProtosetCompatible {ι : Type*} (ps : Protoset ι) (sps : SetProtoset ι) : Prop :=
  ∀ i : ι, (sps i).cells = ↑(ps i : Finset Cell)

/-- `rotateProto p r` coerced to `Set Cell` equals `rotate r ↑p`. -/
private lemma coe_rotateProto_eq (p : Prototile) (r : Fin 4) :
    ↑(rotateProto p r : Finset Cell) = rotate r ↑(p : Finset Cell) := by
  ext c
  simp only [Finset.mem_coe, rotateProto, Finset.mem_image, mem_rotate]
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [rotateCell_inverseRot_cancel]; exact he
  · intro h
    exact ⟨rotateCell c (inverseRot r), h, rotateCell_inverseRot_cancel' c r⟩

/-- `Finset.image (translateCell · t)` coerced to `Set Cell` equals `translate t.1 t.2 ↑S`. -/
private lemma coe_image_translateCell_eq (S : Finset Cell) (t : Cell) :
    ↑(S.image (translateCell · t) : Finset Cell) = translate t.1 t.2 ↑S := by
  ext ⟨cx, cy⟩
  simp only [Finset.mem_coe, Finset.mem_image, translateCell, mem_translate, Finset.mem_coe]
  constructor
  · rintro ⟨⟨ex, ey⟩, he, hce⟩
    simp only [Prod.mk.injEq] at hce
    have h1 : cx - t.1 = ex := by omega
    have h2 : cy - t.2 = ey := by omega
    rwa [show (cx - t.1, cy - t.2) = (ex, ey) from Prod.ext h1 h2]
  · intro h
    exact ⟨(cx - t.1, cy - t.2), h, by ext <;> simp⟩

/-- **Key lemma**: cells of a Finset-based `PlacedTile`, coerced to `Set Cell`, equal the cells
    of the corresponding `SetPlacedTile` under any compatible `SetProtoset`. -/
lemma placedTile_cells_compat {ι : Type*} (ps : Protoset ι) (sps : SetProtoset ι)
    (hc : ProtosetCompatible ps sps) (pt : PlacedTile ι) :
    ↑(pt.cells ps : Finset Cell) =
    SetPlacedTile.cells sps ⟨pt.index, pt.translation, pt.rotation⟩ := by
  simp only [PlacedTile.cells, SetPlacedTile.cells]
  rw [coe_image_translateCell_eq, coe_rotateProto_eq, hc]

/-- **Generic bridge theorem**: `Tileable ps R` (Finset) ↔ `SetTileable ↑R sps` (Set)
    for any compatible pair of protosets. -/
theorem Tileable_iff_set {ι : Type*} (ps : Protoset ι) (sps : SetProtoset ι)
    (hc : ProtosetCompatible ps sps) (R : Finset Cell) :
    Tileable ps R ↔ SetTileable (↑R : Set Cell) sps := by
  constructor
  · -- Forward: Finset tiling → Set tiling
    -- hFin, hDec become local typeclass instances from the intro pattern
    intro ⟨ιₜ, hFin, hDec, t, hValid⟩
    let t' : SetTileSet sps ιₜ :=
      ⟨fun i => ⟨(t.tiles i).index, (t.tiles i).translation, (t.tiles i).rotation⟩⟩
    -- t' is a let-binding, so t' can be used to unfold via simp
    have h_cells : ∀ i : ιₜ, t'.cellsAt i = ↑(t.cellsAt i : Finset Cell) := fun i =>
      (placedTile_cells_compat ps sps hc (t.tiles i)).symm
    refine ⟨ιₜ, hFin, t', ⟨?_, ?_⟩⟩
    · intro i j hij
      rw [h_cells i, h_cells j]
      exact Finset.disjoint_coe.mpr (hValid.disjoint i j hij)
    · -- Show ⋃ i, t'.cellsAt i = ↑R
      simp only [SetTileSet.coveredCells]
      have h_eq : (⋃ i : ιₜ, t'.cellsAt i) = ↑(t.coveredCells) := by
        ext p
        simp only [Set.mem_iUnion, h_cells, Finset.mem_coe,
                   TileSet.coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and]
      rw [h_eq, hValid.covers]
  · -- Backward: Set tiling → Finset tiling
    -- hFin becomes a local typeclass instance from the intro pattern
    intro ⟨ιₜ, hFin, t', hValid⟩
    haveI hDec : DecidableEq ιₜ := Classical.decEq _
    let t : TileSet ps ιₜ :=
      ⟨fun i => ⟨(t'.tiles i).index, (t'.tiles i).translation, (t'.tiles i).rotation⟩⟩
    -- h_cells: t'.cellsAt i = ↑(t.cellsAt i)
    -- Both sides unfold via placedTile_cells_compat applied to t.tiles i
    -- (t.tiles i is a let-def of ⟨(t'.tiles i).index, ...⟩, definitionally equal)
    have h_cells : ∀ i : ιₜ, t'.cellsAt i = ↑(t.cellsAt i : Finset Cell) := fun i =>
      (placedTile_cells_compat ps sps hc (t.tiles i)).symm
    refine ⟨ιₜ, hFin, hDec, t, ⟨?_, ?_⟩⟩
    · intro i j hij
      have hdisj := hValid.disjoint i j hij
      rw [h_cells i, h_cells j] at hdisj
      exact Finset.disjoint_coe.mp hdisj
    · -- Prove t.coveredCells = R
      have hcov := hValid.covers
      simp only [SetTileSet.coveredCells] at hcov
      -- hcov : ⋃ i, t'.cellsAt i = ↑R
      apply Finset.ext; intro p
      simp only [TileSet.coveredCells, Finset.mem_biUnion, Finset.mem_univ, true_and]
      -- Goal: (∃ i, p ∈ t.cellsAt i) ↔ p ∈ R
      constructor
      · rintro ⟨i, hi⟩
        -- p ∈ t.cellsAt i → p ∈ ↑(t.cellsAt i) → p ∈ t'.cellsAt i → p ∈ ↑R → p ∈ R
        have h1 : p ∈ (↑(t.cellsAt i) : Set Cell) := Finset.mem_coe.mpr hi
        rw [← h_cells i] at h1
        have h2 : p ∈ (↑R : Set Cell) := hcov ▸ Set.mem_iUnion.mpr ⟨i, h1⟩
        exact Finset.mem_coe.mp h2
      · intro hp
        -- p ∈ R → p ∈ ↑R = ⋃ i, t'.cellsAt i → p ∈ t'.cellsAt i → p ∈ t.cellsAt i
        have h1 : p ∈ (↑R : Set Cell) := Finset.mem_coe.mpr hp
        rw [← hcov] at h1
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
        rw [h_cells i] at hi
        exact ⟨i, Finset.mem_coe.mp hi⟩

-- ============================================================
-- Canonical Protoset → SetProtoset conversion
-- ============================================================

/-- Convert a Finset-based `Prototile` to a `SetPrototile`.
    Requires the underlying Finset to be nonempty. -/
def toSetPrototile (p : Prototile) (h : (p : Finset Cell).Nonempty) : SetPrototile where
  cells    := ↑(p : Finset Cell)
  finite   := Finset.finite_toSet _
  nonempty := Finset.coe_nonempty.mpr h

/-- Convert a `Protoset ι` to a `SetProtoset ι` via `toSetPrototile`.
    Requires every prototile in the protoset to be nonempty. -/
def toSetProtoset {ι : Type*} (ps : Protoset ι)
    (h : ∀ i, (ps i : Finset Cell).Nonempty) : SetProtoset ι :=
  fun i => toSetPrototile (ps i) (h i)

/-- `toSetProtoset ps h` is automatically compatible with `ps`:
    `(toSetProtoset ps h i).cells = ↑(ps i)` holds by `rfl`. -/
theorem toSetProtoset_compat {ι : Type*} (ps : Protoset ι)
    (h : ∀ i, (ps i : Finset Cell).Nonempty) :
    ProtosetCompatible ps (toSetProtoset ps h) :=
  fun _ => rfl

/-- **Generic bridge (canonical form)**: `Tileable ps R ↔ SetTileable ↑R (toSetProtoset ps h)`.
    No manual compatibility proof required — use this when you have a `Protoset` and want
    the canonical `SetProtoset`. -/
theorem Tileable_iff_toSet {ι : Type*} (ps : Protoset ι) (R : Finset Cell)
    (h : ∀ i, (ps i : Finset Cell).Nonempty) :
    Tileable ps R ↔ SetTileable (↑R : Set Cell) (toSetProtoset ps h) :=
  Tileable_iff_set ps (toSetProtoset ps h) (toSetProtoset_compat ps h) R
