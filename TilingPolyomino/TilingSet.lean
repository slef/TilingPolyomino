import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic
import TilingPolyomino.RectOmega

open Set Function

-- ============================================================
-- Step 1 — Core definitions (generic, shape-independent)
-- ============================================================

/-- A "shape" is a finite non-empty set of cells (the prototile) -/
structure Shape where
  cells : Set Cell
  finite : cells.Finite
  nonempty : cells.Nonempty

/-- A placed copy is a translate + rotate of a shape -/
def placedCopy (s : Shape) (dx dy : ℤ) (r : Fin 4) : Set Cell :=
  translate dx dy (rotate r s.cells)

/-- A tiling of a region R by a shape s is a family of placed copies that
(a) covers R exactly, and (b) are pairwise disjoint -/
structure Tiling (R : Set Cell) (s : Shape) where
  ι : Type        -- index type
  tile : ι → Set Cell
  covers : ⋃ i, tile i = R
  disjoint : ∀ i j, i ≠ j → Disjoint (tile i) (tile j)
  is_placed : ∀ i, ∃ dx dy r, tile i = placedCopy s dx dy r

/-- Tileability -/
def SetTileable (R : Set Cell) (s : Shape) : Prop :=
  Nonempty (Tiling R s)

-- ============================================================
-- Step 2 — Connection to RExp
-- ============================================================

def rexpTileable (e : RExp) (s : Shape) : Prop := SetTileable (e.eval) s

-- ============================================================
-- Step 3 — Finite lemmas for transformations
-- ============================================================

theorem translate_finite (dx dy : ℤ) (s : Set Cell) (h : s.Finite) :
    (translate dx dy s).Finite := by
  dsimp [translate]
  have h_inj : Function.Injective (fun (p : Cell) => (p.1 - dx, p.2 - dy)) := by
    intro p1 p2 heq
    ext
    · have h1 : p1.1 - dx = p2.1 - dx := by injection heq
      omega
    · have h2 : p1.2 - dy = p2.2 - dy := by injection heq
      omega
  exact h.preimage h_inj.injOn

theorem rotate_finite (r : Fin 4) (s : Set Cell) (h : s.Finite) :
    (rotate r s).Finite := by
  dsimp [rotate]
  exact h.preimage (rotateCell_injective (inverseRot r)).injOn

theorem ncard_placedCopy (s : Shape) (dx dy : ℤ) (r : Fin 4) :
    (placedCopy s dx dy r).ncard = s.cells.ncard := by
  dsimp [placedCopy]
  rw [translate_ncard dx dy (rotate r s.cells) (rotate_finite r s.cells s.finite)]
  rw [rotate_ncard r s.cells s.finite]

theorem finite_placedCopy (s : Shape) (dx dy : ℤ) (r : Fin 4) :
    (placedCopy s dx dy r).Finite := by
  dsimp [placedCopy]
  exact translate_finite dx dy (rotate r s.cells) (rotate_finite r s.cells s.finite)

-- ============================================================
-- Step 4 — Cardinality necessary condition
-- ============================================================

theorem SetTileable.ncard_dvd {R : Set Cell} {s : Shape} (hR : R.Finite) (ht : SetTileable R s) :
    s.cells.ncard ∣ R.ncard := by
  rcases ht with ⟨t⟩
  have h_nonempty : ∀ i, (t.tile i).Nonempty := by
    intro i
    rcases t.is_placed i with ⟨dx, dy, r, heq⟩
    rw [heq]
    have h_card : (placedCopy s dx dy r).ncard = s.cells.ncard := ncard_placedCopy s dx dy r
    have h_s_pos : 0 < s.cells.ncard := (Set.ncard_pos s.finite).mpr s.nonempty
    rw [← h_card] at h_s_pos
    exact (Set.ncard_pos (finite_placedCopy s dx dy r)).mp h_s_pos
  have h_fin_ι : Finite t.ι := by
    let f : t.ι → R := fun i => ⟨(h_nonempty i).some, by
      have h1 : (h_nonempty i).some ∈ t.tile i := (h_nonempty i).some_mem
      have h2 : t.tile i ⊆ ⋃ j, t.tile j := Set.subset_iUnion _ _
      rw [t.covers] at h2
      exact h2 h1⟩
    have f_inj : f.Injective := by
      intro i j hij
      by_contra hne
      have h_dj := t.disjoint i j hne
      have h1 : (h_nonempty i).some ∈ t.tile i := (h_nonempty i).some_mem
      have h2 : (h_nonempty j).some ∈ t.tile j := (h_nonempty j).some_mem
      have eq_val : (h_nonempty i).some = (h_nonempty j).some := congr_arg Subtype.val hij
      rw [eq_val] at h1
      exact Set.disjoint_left.mp h_dj h1 h2
    haveI : Finite R := hR
    exact Finite.of_injective f f_inj
  have h_tile_fin : ∀ i, (t.tile i).Finite := by
    intro i
    rcases t.is_placed i with ⟨dx, dy, r, heq⟩
    rw [heq]
    exact finite_placedCopy s dx dy r
  have h_union_ncard : (⋃ i, t.tile i).ncard = ∑ᶠ (i : t.ι), (t.tile i).ncard := by
    apply Set.ncard_iUnion_of_finite h_tile_fin
    intro i j hij
    exact t.disjoint i j hij
  have h_R_ncard : R.ncard = ∑ᶠ (i : t.ι), (t.tile i).ncard := by
    rw [← h_union_ncard, t.covers]
  have h_sum : ∑ᶠ (i : t.ι), (t.tile i).ncard = ∑ᶠ (i : t.ι), s.cells.ncard := by
    congr 1
    ext i
    rcases t.is_placed i with ⟨dx, dy, r, heq⟩
    rw [heq]
    exact ncard_placedCopy s dx dy r
  rw [h_R_ncard, h_sum]
  haveI : Fintype t.ι := Fintype.ofFinite t.ι
  rw [finsum_eq_sum_of_fintype]
  rw [Finset.sum_const]
  simp only [nsmul_eq_mul, Finset.card_univ]
  exact dvd_mul_left _ _

-- ============================================================
-- Step 5 — Tiling constructors
-- ============================================================

def Tiling.of_one (R : Set Cell) (s : Shape)
    (dx dy : ℤ) (r : Fin 4)
    (h_cover : placedCopy s dx dy r = R) :
    Tiling R s where
  ι := Fin 1
  tile _ := placedCopy s dx dy r
  covers := by
    rw [← h_cover]
    ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨_, hp⟩; exact hp
    · intro hp; exact ⟨0, hp⟩
  disjoint i j hij := by
    fin_cases i; fin_cases j
    contradiction
  is_placed _ := ⟨dx, dy, r, rfl⟩

def Tiling.of_two (R : Set Cell) (s : Shape)
    (dx1 dy1 : ℤ) (r1 : Fin 4)
    (dx2 dy2 : ℤ) (r2 : Fin 4)
    (h_cover : placedCopy s dx1 dy1 r1 ∪ placedCopy s dx2 dy2 r2 = R)
    (h_disj : Disjoint (placedCopy s dx1 dy1 r1) (placedCopy s dx2 dy2 r2)) :
    Tiling R s where
  ι := Fin 2
  tile i := if i.val = 0 then placedCopy s dx1 dy1 r1 else placedCopy s dx2 dy2 r2
  covers := by
    rw [← h_cover]
    ext p
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · left; simpa [Fin.isValue] using hi
      · right; simpa [Fin.isValue] using hi
    · intro h
      rcases h with h | h
      · exact ⟨0, by simpa [Fin.isValue] using h⟩
      · exact ⟨1, by simpa [Fin.isValue] using h⟩
  disjoint i j hij := by
    fin_cases i <;> fin_cases j
    · contradiction
    · simp only [ite_true]
      exact h_disj
    · simp only [ite_true]
      exact h_disj.symm
    · contradiction
  is_placed i := by
    fin_cases i
    · exact ⟨dx1, dy1, r1, by rfl⟩
    · exact ⟨dx2, dy2, r2, by rfl⟩

-- ============================================================
-- Step 6 — Union and refinement
-- ============================================================

def Tiling.union {R S : Set Cell} {s : Shape} (tR : Tiling R s) (tS : Tiling S s)
    (hdisj : Disjoint R S) : Tiling (R ∪ S) s where
  ι := tR.ι ⊕ tS.ι
  tile := Sum.elim tR.tile tS.tile
  covers := by
    have h1 : ⋃ i, tR.tile i = R := tR.covers
    have h2 : ⋃ i, tS.tile i = S := tS.covers
    ext p
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      cases i
      · left; rw [← h1]; exact Set.mem_iUnion.mpr ⟨_, hi⟩
      · right; rw [← h2]; exact Set.mem_iUnion.mpr ⟨_, hi⟩
    · intro h
      rcases h with h | h
      · have ⟨i, hi⟩ : ∃ i, p ∈ tR.tile i := Set.mem_iUnion.mp (by rw [h1]; exact h)
        exact ⟨Sum.inl i, hi⟩
      · have ⟨i, hi⟩ : ∃ i, p ∈ tS.tile i := Set.mem_iUnion.mp (by rw [h2]; exact h)
        exact ⟨Sum.inr i, hi⟩
  disjoint i j hij := by
    cases i <;> cases j
    · apply tR.disjoint
      intro heq; apply hij; rw [heq]
    · apply Set.disjoint_left.mpr
      intro p h1 h2
      have hpR : p ∈ R := by rw [← tR.covers]; exact Set.mem_iUnion.mpr ⟨_, h1⟩
      have hpS : p ∈ S := by rw [← tS.covers]; exact Set.mem_iUnion.mpr ⟨_, h2⟩
      exact Set.disjoint_left.mp hdisj hpR hpS
    · apply Set.disjoint_left.mpr
      intro p h1 h2
      have hpS : p ∈ S := by rw [← tS.covers]; exact Set.mem_iUnion.mpr ⟨_, h1⟩
      have hpR : p ∈ R := by rw [← tR.covers]; exact Set.mem_iUnion.mpr ⟨_, h2⟩
      exact Set.disjoint_left.mp hdisj hpR hpS
    · apply tS.disjoint
      intro heq; apply hij; rw [heq]
  is_placed i := by
    cases i
    · exact tR.is_placed _
    · exact tS.is_placed _

theorem SetTileable.union {R S : Set Cell} {s : Shape} (hR : SetTileable R s) (hS : SetTileable S s)
    (hdisj : Disjoint R S) : SetTileable (R ∪ S) s :=
  ⟨Tiling.union hR.some hS.some hdisj⟩

/-- General refinement: if R is partitioned into pieces each tileable by s,
    then R itself is tileable by s. -/
theorem SetTileable.refine {ι : Type} {R : Set Cell} {s : Shape}
    (pieces : ι → Set Cell)
    (hcover : ⋃ i, pieces i = R)
    (hdisj : Pairwise (Disjoint on pieces))
    (hfin : ∀ i, (pieces i).Finite)
    (htile : ∀ i, SetTileable (pieces i) s) :
    SetTileable R s := by
  apply Nonempty.intro
  have _ := hfin
  exact {
    ι := Σ i, (htile i).some.ι
    tile := fun ⟨i, j⟩ => (htile i).some.tile j
    covers := by
      rw [← hcover]
      ext p
      simp only [Set.mem_iUnion, Sigma.exists]
      constructor
      · rintro ⟨i, j, hp⟩
        exact ⟨i, by rw [← (htile i).some.covers]; exact Set.mem_iUnion.mpr ⟨j, hp⟩⟩
      · rintro ⟨i, hp⟩
        have : p ∈ ⋃ j, (htile i).some.tile j := by rw [(htile i).some.covers]; exact hp
        rcases Set.mem_iUnion.mp this with ⟨j, hj⟩
        exact ⟨i, j, hj⟩
    disjoint := by
      intro x y hxy
      by_cases hfst : x.fst = y.fst
      · rcases x with ⟨x_fst, x_snd⟩
        rcases y with ⟨y_fst, y_snd⟩
        dsimp at hfst
        subst hfst
        have hsnd : x_snd ≠ y_snd := by
          intro heq
          apply hxy
          congr
        exact (htile x_fst).some.disjoint x_snd y_snd hsnd
      · have hdisj_pieces : Disjoint (pieces x.fst) (pieces y.fst) := hdisj hfst
        have hsubx : (htile x.fst).some.tile x.snd ⊆ pieces x.fst := by
          intro p hp
          rw [← (htile x.fst).some.covers]
          exact Set.mem_iUnion.mpr ⟨x.snd, hp⟩
        have hsuby : (htile y.fst).some.tile y.snd ⊆ pieces y.fst := by
          intro p hp
          rw [← (htile y.fst).some.covers]
          exact Set.mem_iUnion.mpr ⟨y.snd, hp⟩
        exact Set.disjoint_of_subset hsubx hsuby hdisj_pieces
    is_placed := fun ⟨i, j⟩ => (htile i).some.is_placed j
  }

-- ============================================================
-- Step 7 — Swap region (generic)
-- ============================================================

protected def Set.swapRegion (R : Set Cell) : Set Cell := {p | (p.2, p.1) ∈ R}

@[simp] theorem mem_swapRegion (R : Set Cell) (p : Cell) :
  p ∈ Set.swapRegion R ↔ (p.2, p.1) ∈ R := by rfl

-- ============================================================
-- Step 8 — Generic translation lemma
-- ============================================================

private theorem translate_placedCopy_eq (s : Shape) (dx dy dx' dy' : ℤ) (r : Fin 4) :
    translate dx dy (placedCopy s dx' dy' r) = placedCopy s (dx + dx') (dy + dy') r := by
  ext ⟨x, y⟩
  simp only [placedCopy, mem_translate]
  constructor
  · intro h
    have h1 : x - dx - dx' = x - (dx + dx') := by omega
    have h2 : y - dy - dy' = y - (dy + dy') := by omega
    rwa [← h1, ← h2]
  · intro h
    have h1 : x - dx - dx' = x - (dx + dx') := by omega
    have h2 : y - dy - dy' = y - (dy + dy') := by omega
    rwa [h1, h2]

/-- Translation preserves tileability (generic, works for any Shape) -/
theorem setTileable_translate {R : Set Cell} {s : Shape} (h : SetTileable R s) (dx dy : ℤ) :
    SetTileable (translate dx dy R) s := by
  rcases h with ⟨t⟩
  apply Nonempty.intro
  refine {
    ι := t.ι
    tile := fun i => translate dx dy (t.tile i)
    covers := by
      ext ⟨x, y⟩
      simp only [Set.mem_iUnion, mem_translate]
      constructor
      · rintro ⟨i, hi⟩
        have hmem : (x - dx, y - dy) ∈ ⋃ j, t.tile j := Set.mem_iUnion.mpr ⟨i, hi⟩
        rwa [t.covers] at hmem
      · intro h
        have hmem : (x - dx, y - dy) ∈ ⋃ j, t.tile j := by rw [t.covers]; exact h
        exact Set.mem_iUnion.mp hmem
    disjoint := by
      intro i j hij
      have hd := t.disjoint i j hij
      rw [Set.disjoint_iff_inter_eq_empty] at hd ⊢
      ext ⟨x, y⟩
      simp only [mem_translate, Set.mem_inter_iff, Set.mem_empty_iff_false]
      have := Set.ext_iff.mp hd (x - dx, y - dy)
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false] at this
      exact this
    is_placed := by
      intro i
      rcases t.is_placed i with ⟨dx', dy', r, hr⟩
      refine ⟨dx + dx', dy + dy', r, ?_⟩
      rw [hr]
      exact translate_placedCopy_eq s dx dy dx' dy' r
  }

-- ============================================================
-- Step 9 — Vacuous tileability + empty rectangles
-- ============================================================

/-- The empty region is vacuously tileable by any shape -/
theorem SetTileable.empty (s : Shape) : SetTileable (∅ : Set Cell) s :=
  ⟨{  ι := Empty
      tile := Empty.elim
      covers := by simp
      disjoint := fun i => i.elim
      is_placed := fun i => i.elim }⟩

/-- rect with zero height is empty -/
theorem rect_empty_of_eq (x0 x1 y : ℤ) : rect x0 y x1 y = ∅ := by
  ext p; simp only [mem_rect, Set.mem_empty_iff_false, iff_false]; omega

-- ============================================================
-- Step 10 — Horizontal and vertical union lemmas
-- ============================================================

theorem SetTileable.horizontal_union {s : Shape} {a b m : ℤ} (ha_pos : 0 ≤ a) (hb_pos : 0 ≤ b)
    (ha : SetTileable (rect 0 0 a m) s)
    (hb : SetTileable (rect a 0 (a+b) m) s) :
    SetTileable (rect 0 0 (a+b) m) s := by
  have h_eq : rect 0 0 (a+b) m = rect 0 0 a m ∪ rect a 0 (a+b) m := by
    ext ⟨x, y⟩
    simp only [mem_rect, mem_union]
    omega
  have h_disj : Disjoint (rect 0 0 a m) (rect a 0 (a+b) m) := by
    rw [Set.disjoint_left]
    intro p h1 h2
    simp only [mem_rect] at h1 h2
    omega
  rw [h_eq]
  exact SetTileable.union ha hb h_disj

theorem SetTileable.vertical_union {s : Shape} {n a b : ℤ} (ha_pos : 0 ≤ a) (hb_pos : 0 ≤ b)
    (ha : SetTileable (rect 0 0 n a) s)
    (hb : SetTileable (rect 0 a n (a+b)) s) :
    SetTileable (rect 0 0 n (a+b)) s := by
  have h_eq : rect 0 0 n (a+b) = rect 0 0 n a ∪ rect 0 a n (a+b) := by
    ext ⟨x, y⟩
    simp only [mem_rect, mem_union]
    omega
  have h_disj : Disjoint (rect 0 0 n a) (rect 0 a n (a+b)) := by
    rw [Set.disjoint_left]
    intro p h1 h2
    simp only [mem_rect] at h1 h2
    omega
  rw [h_eq]
  exact SetTileable.union ha hb h_disj
