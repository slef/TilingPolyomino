import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic
import TilingPolyomino.RectOmega

open Set

-- Step 1 — Core definitions

/-- A "shape" is a finite non-empty set of cells (the prototile) -/
structure Shape where
  cells : Set Cell
  finite : cells.Finite
  nonempty : cells.Nonempty

/-- The L-tromino shape (standard orientation): {(0,0),(0,1),(1,0)} -/
def lShape_cells : Set Cell := {(0,0), (0,1), (1,0)}

def lShape : Shape := ⟨
  lShape_cells,
  by simp [Set.finite_insert, lShape_cells],
  ⟨(0,0), by simp [lShape_cells]⟩
⟩

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

-- Finite lemmas for transformations

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

-- Step 2 — Cardinality necessary condition

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

-- Step 3 — Connection to RExp

def rexpTileable (e : RExp) (s : Shape) : Prop := SetTileable (e.eval) s

-- Step 5 — Union lemma

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

-- Step 4 — Base case proofs

theorem lShape_eq_rects : lShape.cells = rect 0 0 1 2 ∪ rect 1 0 2 1 := by
  ext ⟨x, y⟩
  simp [lShape, lShape_cells]
  omega

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

theorem setTileable_2x3 : SetTileable (rect 0 0 2 3) lShape := by
  apply Nonempty.intro
  refine Tiling.of_two _ lShape 0 0 0 1 2 2 ?_ ?_
  · dsimp [placedCopy]
    rw [lShape_eq_rects]
    rect_omega
  · dsimp [placedCopy]
    rw [lShape_eq_rects, Set.disjoint_iff_inter_eq_empty]
    rect_omega

theorem setTileable_3x2 : SetTileable (rect 0 0 3 2) lShape := by
  apply Nonempty.intro
  refine Tiling.of_two _ lShape 0 0 0 2 1 2 ?_ ?_
  · dsimp [placedCopy]
    rw [lShape_eq_rects]
    rect_omega
  · dsimp [placedCopy]
    rw [lShape_eq_rects, Set.disjoint_iff_inter_eq_empty]
    rect_omega

theorem setTileable_2x2_minus : SetTileable (rect 0 0 2 2 \ {(1,1)}) lShape := by
  apply Nonempty.intro
  refine Tiling.of_one _ lShape 0 0 0 ?_
  have h_sing : ({(1,1)} : Set Cell) = rect 1 1 2 2 := by
    ext ⟨x, y⟩
    simp
    omega
  dsimp [placedCopy]
  rw [lShape_eq_rects, h_sing]
  rect_omega

