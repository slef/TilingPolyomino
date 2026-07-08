import Mathlib.Data.Int.LeastGreatest
import Mathlib.Tactic

/-!
# Ray-crossing parity: the abstract toolkit

For a set `V` of vertical unit segments (encoded by their upper-right grid
point) and a cell `(a, b)`, `rayCross V a b` is the set of segments of `V`
in the cell's row, strictly to its right.  The parity of its cardinality is
the discrete winding-parity of the rightward ray; this file proves the two
invariance lemmas of the parity argument: moving right past a non-segment
(`even_rayCross_add_right`) and moving up across a family whose grid points
all have even degree (`even_rayCross_add_up`).

Fully abstract: no polyomino, no fatness — just finite sets of segments.
-/

open Set

-- ============================================================
-- §6 Ray-crossing parity: the abstract toolkit
-- ============================================================
--
-- For the single-boundary-cycle theorem.  A *curve* is presented by two
-- sets of unit segments: `V ⊆ ℤ × ℤ` (the pair `(x, y)` denotes the
-- vertical segment on the grid line `x` between the cells `(x-1, y)` and
-- `(x, y)`) and `H` (the pair `(x, y)` denotes the horizontal segment on
-- the grid row `y` between the cells `(x, y-1)` and `(x, y)`).  The only
-- global hypothesis is the **even-degree identity** at every grid point.
-- The parity of the number of crossings of the rightward ray from a cell
-- then changes exactly when the cell moves across a segment of the curve.

/-- The crossings of the rightward ray from the cell `(a, b)` with the
    vertical segments `V`: the abscissas `x > a` with `(x, b) ∈ V`. -/
def rayCross (V : Set (ℤ × ℤ)) (a b : ℤ) : Set ℤ :=
  {x : ℤ | a < x ∧ (x, b) ∈ V}

lemma rayCross_finite {V : Set (ℤ × ℤ)} (hV : V.Finite) (a b : ℤ) :
    (rayCross V a b).Finite := by
  apply Set.Finite.subset ((hV.inter_of_left {t | t.2 = b}).image Prod.fst)
  rintro x ⟨h1, h2⟩
  exact ⟨(x, b), ⟨h2, rfl⟩, rfl⟩

/-- The crossings within the window `(a, t]`. -/
private def raySeg (V : Set (ℤ × ℤ)) (a t r : ℤ) : Set ℤ :=
  {x : ℤ | a < x ∧ x ≤ t ∧ (x, r) ∈ V}

private lemma raySeg_finite (V : Set (ℤ × ℤ)) (a t r : ℤ) :
    (raySeg V a t r).Finite := by
  apply (Set.finite_Icc (a + 1) t).subset
  rintro x ⟨h1, h2, -⟩
  exact Set.mem_Icc.mpr ⟨by omega, h2⟩

private lemma raySeg_base (V : Set (ℤ × ℤ)) (a r : ℤ) :
    raySeg V a a r = ∅ := by
  ext x
  simp only [raySeg, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2, -⟩
  omega

private lemma raySeg_succ_mem {V : Set (ℤ × ℤ)} {a t r : ℤ} (hat : a ≤ t)
    (h : (t + 1, r) ∈ V) :
    (raySeg V a (t + 1) r).ncard = (raySeg V a t r).ncard + 1 := by
  have heq : raySeg V a (t + 1) r = insert (t + 1) (raySeg V a t r) := by
    ext x
    simp only [raySeg, Set.mem_setOf_eq, Set.mem_insert_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hx : x = t + 1
      · exact Or.inl hx
      · exact Or.inr ⟨h1, by omega, h3⟩
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨by omega, le_rfl, h⟩
      · exact ⟨h1, by omega, h3⟩
  rw [heq, Set.ncard_insert_of_notMem
    (fun hx => by simp only [raySeg, Set.mem_setOf_eq] at hx; omega)
    (raySeg_finite _ _ _ _)]

private lemma raySeg_succ_not_mem {V : Set (ℤ × ℤ)} {a t r : ℤ}
    (h : (t + 1, r) ∉ V) :
    raySeg V a (t + 1) r = raySeg V a t r := by
  ext x
  simp only [raySeg, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    by_cases hx : x = t + 1
    · subst hx
      exact absurd h3 h
    · omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by omega, h3⟩

private lemma rayCross_eq_raySeg {V : Set (ℤ × ℤ)} {a b M : ℤ}
    (hM : ∀ t ∈ V, t.1 ≤ M) :
    rayCross V a b = raySeg V a M b := by
  ext x
  simp only [rayCross, raySeg, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, hM _ h2, h2⟩
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩

/-- **Horizontal parity step.**  The crossing counts of two horizontally
    adjacent cells have even sum iff the vertical segment between the two
    cells is not on the curve. -/
lemma even_rayCross_add_right {V : Set (ℤ × ℤ)} (hV : V.Finite) (a b : ℤ) :
    (Even ((rayCross V a b).ncard + (rayCross V (a + 1) b).ncard)) ↔
      (a + 1, b) ∉ V := by
  by_cases h : (a + 1, b) ∈ V
  · have heq : rayCross V a b = insert (a + 1) (rayCross V (a + 1) b) := by
      ext x
      simp only [rayCross, Set.mem_setOf_eq, Set.mem_insert_iff]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hx : x = a + 1
        · exact Or.inl hx
        · exact Or.inr ⟨by omega, h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨by omega, h⟩
        · exact ⟨by omega, h2⟩
    refine iff_of_false (fun hev => ?_) (not_not_intro h)
    rw [heq, Set.ncard_insert_of_notMem
      (fun hx => by simp only [rayCross, Set.mem_setOf_eq] at hx; omega)
      (rayCross_finite hV _ _)] at hev
    rw [Nat.even_iff] at hev
    omega
  · have heq : rayCross V a b = rayCross V (a + 1) b := by
      ext x
      simp only [rayCross, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        by_cases hx : x = a + 1
        · subst hx
          exact absurd h2 h
        · omega
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    refine iff_of_true ?_ h
    rw [heq]
    exact ⟨(rayCross V (a + 1) b).ncard, rfl⟩

/-- **Vertical parity step.**  Under the even-degree identity, the
    crossing counts of two vertically adjacent cells have even sum iff the
    horizontal segment between the two cells is not on the curve.  Proved
    by telescoping the even-degree identity along the row. -/
lemma even_rayCross_add_up {V H : Set (ℤ × ℤ)} (hV : V.Finite) (hH : H.Finite)
    (hdeg : ∀ x y : ℤ, (((x, y) ∈ V) ↔ ((x, y - 1) ∈ V)) ↔
      (((x, y) ∈ H) ↔ ((x - 1, y) ∈ H)))
    (a b : ℤ) :
    (Even ((rayCross V a b).ncard + (rayCross V a (b + 1)).ncard)) ↔
      (a, b + 1) ∉ H := by
  obtain ⟨M0, hM0⟩ := ((hV.union hH).image Prod.fst).bddAbove
  have hMV : ∀ t ∈ V, t.1 ≤ max a M0 + 1 := fun t ht => by
    have h' : t.1 ≤ M0 := hM0 ⟨t, Or.inl ht, rfl⟩
    omega
  have hMnotH : (max a M0 + 1, b + 1) ∉ H := fun hmem => by
    have h' : max a M0 + 1 ≤ M0 := hM0 ⟨_, Or.inr hmem, rfl⟩
    omega
  -- the invariant, telescoped from `a` to the end of the support
  have key : ∀ t, a ≤ t →
      ((Even ((raySeg V a t b).ncard + (raySeg V a t (b + 1)).ncard)) ↔
        (((a, b + 1) ∈ H) ↔ ((t, b + 1) ∈ H))) := by
    intro t ht
    induction t, ht using Int.le_induction with
    | base =>
      rw [raySeg_base, raySeg_base]
      simp
    | succ n hn ih =>
      have hdeg' := hdeg (n + 1) (b + 1)
      rw [show b + 1 - 1 = b from by ring,
        show n + 1 - 1 = n from by ring] at hdeg'
      by_cases h1 : (n + 1, b) ∈ V <;> by_cases h2 : (n + 1, b + 1) ∈ V
      · have hHiff : ((n + 1, b + 1) ∈ H ↔ (n, b + 1) ∈ H) :=
          hdeg'.mp (iff_of_true h2 h1)
        have hpar : Even ((raySeg V a (n + 1) b).ncard +
              (raySeg V a (n + 1) (b + 1)).ncard) ↔
            Even ((raySeg V a n b).ncard + (raySeg V a n (b + 1)).ncard) := by
          rw [raySeg_succ_mem hn h1, raySeg_succ_mem hn h2,
            Nat.even_iff, Nat.even_iff]
          omega
        rw [hpar, ih]
        clear hpar ih
        tauto
      · have hHiff : ¬((n + 1, b + 1) ∈ H ↔ (n, b + 1) ∈ H) :=
          fun hiff => h2 ((hdeg'.mpr hiff).mpr h1)
        have hpar : Even ((raySeg V a (n + 1) b).ncard +
              (raySeg V a (n + 1) (b + 1)).ncard) ↔
            ¬Even ((raySeg V a n b).ncard + (raySeg V a n (b + 1)).ncard) := by
          rw [raySeg_succ_mem hn h1, raySeg_succ_not_mem h2,
            Nat.even_iff, Nat.even_iff]
          omega
        rw [hpar, ih]
        clear hpar ih
        tauto
      · have hHiff : ¬((n + 1, b + 1) ∈ H ↔ (n, b + 1) ∈ H) :=
          fun hiff => h1 ((hdeg'.mpr hiff).mp h2)
        have hpar : Even ((raySeg V a (n + 1) b).ncard +
              (raySeg V a (n + 1) (b + 1)).ncard) ↔
            ¬Even ((raySeg V a n b).ncard + (raySeg V a n (b + 1)).ncard) := by
          rw [raySeg_succ_not_mem h1, raySeg_succ_mem hn h2,
            Nat.even_iff, Nat.even_iff]
          omega
        rw [hpar, ih]
        clear hpar ih
        tauto
      · have hHiff : ((n + 1, b + 1) ∈ H ↔ (n, b + 1) ∈ H) :=
          hdeg'.mp (iff_of_false h2 h1)
        have hpar : Even ((raySeg V a (n + 1) b).ncard +
              (raySeg V a (n + 1) (b + 1)).ncard) ↔
            Even ((raySeg V a n b).ncard + (raySeg V a n (b + 1)).ncard) := by
          rw [raySeg_succ_not_mem h1, raySeg_succ_not_mem h2]
        rw [hpar, ih]
        clear hpar ih
        tauto
  have hfin := key (max a M0 + 1) (by have := le_max_left a M0; omega)
  rw [rayCross_eq_raySeg hMV, rayCross_eq_raySeg hMV, hfin]
  exact ⟨fun hiff hmem => hMnotH (hiff.mp hmem),
    fun hn => iff_of_false hn hMnotH⟩

