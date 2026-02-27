# TilingPolyomino — To-Do List

## In Progress
- (nothing active)

## Up Next
- [ ] **Genuine Set proofs for corner theorems**: `LTileable_rectMinusCorner_iff_set` and
      `LTileable_rectMinus2Corner_set` are currently bridge-based (via `LTileable_iff_set`).
      Goal: replace with independent Set proofs (no bridge), mirroring the structure of
      `not_LTileable_3x_odd_set` and `LTileable_3xn_iff_set`.

## Backlog
- [ ] **rect_omega for Set.mem_diff goals**: `h_diff_eq` style proofs now use
      `ext ⟨x,y⟩; simp only [...]; omega` — consider adding this as a `rect_omega` extension.
- [ ] **TilingSet.lean structural linter warnings** (pre-existing, unfixable without restructure):
      `remove_two` and `refine_partition` have `[Fintype ι]` hypotheses not appearing in their
      return types. Fixing requires switching to `Finite` + `Fintype.ofFinite` in the proofs.
      Leave as-is unless doing a structural refactor.

## Done (recent)
- [x] **Lint cleanup pass 3 — disjointness simp warnings** (`feat/set-tiling`, 3e665a0):
      - `LTileable_2x3_set` / `LTileable_3x2_set` disjointness: switched from
        `simp_all [...]` to `simp_all only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
        Set.disjoint_iff_inter_eq_empty, SetTileSet.cellsAt, SetPlacedTile.cells,
        LProtoset_set, LPrototile_set, LShape_cells]` — eliminates all 'flexible tactic'
        and 'unused simp arg' linter warnings for these theorems.
      - Coverage simp: removed `rotateCell_1`, `rotateCell_3` (unused; tiles use only rot-0
        and rot-2, so only `rotateCell_0` and `rotateCell_2` are needed).
      - Key insight: `rect_omega` already includes `mem_translate`, `mem_rotate`,
        `rotateCell_*` internally — those were redundant in the `simp_all` list.
      - LTrominoSet.lean: 466 → 464 lines (−2). 0 sorries. Build clean.
      - **Remaining warnings** (unavoidable without structural changes):
          * TilingSet.lean `[Fintype ι]` warnings in `remove_two`/`refine_partition`
          * LTromino.lean line 1832: `info: ring_nf` suggestion (info only, not a warning)
- [x] **Lint cleanup pass 2** (`feat/set-tiling`, 021ca62):
      - `LTileable_2x2_minus_set` simp call: removed `Fin.exists_fin_one`, `rotateCell_1/2/3`
        (all unused — single tile at rotation 0, only `rotateCell_0` needed).
      - 4 family theorems (`LTileable_2x_mult3_set`, `LTileable_3x_even_set`,
        `LTileable_mult3_x_2_set`, `LTileable_even_x_3_set`):
        `convert h using 2 <;> ring` → `convert h using 2; ring`
        (linter: `unnecessarySeqFocus` — `convert` leaves exactly 1 goal here).
      - **Note**: `LTileable_rect_area_dvd_set` cron claim of "27L" confirmed stale.
        Current proof: 4L (single `simpa [rect_ncard, ...]`), well under 15L target.
      - **Priority 2 check**: `LTileable_rect_iff_set` vs `rect_tileable_iff` — no discrepancy.
        Bridge reuses `RectTileableConditions` directly; conditions identical by construction.
      - Remaining pre-existing warnings (unfixable without structural changes):
          * Unused simp args in `LTileable_2x3/3x2_set` disjointness (see Backlog)
          * `[Fintype ...]` typeclass not in return type of `remove_two`/`refine_partition`
      - LTrominoSet.lean: 466L (unchanged — edits within existing lines). 0 sorries.
- [x] **Lint cleanup + area-dvd compression** (`feat/set-tiling`):
      - `LTileable_rect_area_dvd_set`: 7L → 4L (single `simpa [rect_ncard, ...]`).
        **Note**: cron claim of "27L" was stale; prior passes already reduced it to 7L.
        Now at 4L, comfortably below the 15L Finset comparison.
      - 6 concrete base-case theorems (`LTileable_2x6_set` etc.): removed dead `<;> ring`
        (linter: `ring` never executed since `convert h using 2` already closes).
      - `push_cast` in `LTileable_6x_of_ge2_set` removed (linter: tactic does nothing).
      - 2 long theorem signatures split to stay under 100-char limit.
      - `TilingSet.lean`: fixed deprecated `Int.ediv_add_emod` → `Int.mul_ediv_add_emod`;
        removed unused `_hR`/`_hi`/`_hn`/`_hm` variable prefixes; dropped unused `Set.mem_diff`
        simp arg in `remove_two`.
      - Remaining warnings (pre-existing, not fixable without structural changes):
          * Unused simp args in `LTileable_2x3/3x2_set` disjointness (see Backlog below)
          * `[Fintype ...]` typeclass not in return type of `remove_two`/`refine_partition`
          * `unnecessarySeqFocus` for `convert <;> ring` in 4 family theorems
            (FIXED in lint cleanup pass 2)
      - LTrominoSet.lean 467 → 466L (−1). TilingSet.lean 675L (no line change). 0 sorries.
- [x] **`LTileable_nx2_iff_set`** added (`feat/set-tiling`):
      5 lines via swap + `LTileable_2xn_iff_set` (mirrors `LTileable_nx3_iff_set` pattern).
      LTrominoSet.lean 462 → 467 lines (+5). 0 sorries.
- [x] **Fair line-count comparison** completed (`feat/set-tiling`):
      11 matched theorem pairs (Set vs Finset framework, same theorems):
        Set total: 201L | Finset total: 245L | Ratio: 0.82x (Set 18% shorter overall)
      Excluding Finset `decide`-shortcut base cases (tileable_2x3, tileable_3x2):
        Set: 167L | Finset: 236L | Ratio: 0.71x (Set 29% shorter on non-trivial proofs)
      Key wins for Set: LTileable_swap_set 27L vs 63L (0.43x),
        LTileable_3x_even_set 5L vs 17L (0.29x), LTileable_mult3_mult2_set 6L vs 19L (0.32x).
      Key losses for Set: LTileable_rect_area_dvd_set 27L vs 15L (1.8x — ncard harder than card).
- [x] **Deleted `LTrominoSet_original.lean`** scratch file (616L, pre-refactor old-naming copy).
      Added `*.lean.bak` and `*_original.lean` to `.gitignore`.
- [x] **Fifth simplification pass** (`feat/set-tiling`):
      - `not_LTileable_1xn_set`: 23 → 19 lines (−4): merged intro+haveI, compressed hcell
        to `by simp [mem_rect]; omega`, collapsed h_sub inner have to 1 line.
      - `not_LTileable_3x_odd_set`: 68 → 67 lines (−1): merged hgoal+rw into single
        `rw [show ... from by push_cast; omega]`.
      - Total: LTrominoSet.lean 466 → 462 lines (−4). 0 sorries.
      - **Note**: Linter suggests `LTileable_2x3_set`/`LTileable_3x2_set` disjointness
        case can use `simp_all only [Fin.isValue, Fin.zero_eta, Fin.mk_one]` — future pass.
- [x] **Fourth simplification pass** (`feat/set-tiling`):
      - Merged `lPlaced_set_ybnd_of_cover_00` + `lPlaced_set_ybnd_of_cover_20` into a single
        `lPlaced_set_ybnd_of_y0` (generalised hypothesis: `∃ cx, (cx,0) ∈ tile`).
      - Dropped the now-unused `hq_nn` parameter (revealed by the merge; omega never needed it).
      - Total: LTrominoSet.lean 475 → 466 lines (−9). 0 sorries.
- [x] **Third simplification pass** (`feat/set-tiling`):
      - `not_LTileable_3x_odd_set`: 75 → 68 lines (−7): removed `hi_sub_full`/`hj_sub_full`
        helpers (inlined via reshaped `sub_full`), eliminated `h_rect_card` variable
        (merged into `ncard` inequality via simp), compressed `h_back` with `convert`.
      - `LTileable_6x_of_ge2_set`, `LTileable_odd_x_6_set`: replaced `induction'`
        (style warning) with `revert … ; induction … using Nat.strong_induction_on;
        rename_i … ; intro …` (no line change, correct Lean 4 idiom).
      - Total: LTrominoSet.lean 482 → 475 lines (−7). 0 sorries.
- [x] **Second simplification pass** (`feat/set-tiling`):
      - `LTileable_2x2_minus_set`: 21 → 14 lines (−7): removed `h_sing` subproof, let `simp+Prod.mk.injEq+omega` close.
      - `LTileable_6x_of_ge2_set`: 26 → 15 lines (−11): merged Nat→ℤ cast via `convert+push_cast+omega`; `h_stripe` compressed to 2 lines.
      - `LTileable_odd_x_6_set`: 21 → 15 lines (−6): same pattern as above.
      - `lPlaced_set_x_span`: removed dead `<;> omega` (simp now closes all branches).
      - Total: LTrominoSet.lean 507 → 482 lines (−25). 0 sorries.
- [x] **Proof simplification audit** (`feat/set-tiling`):
      - `LTileable_swap_set`: 36 → 24 lines (−12)
      - `not_LTileable_1xn_set`: 33 → 25 lines (−8)
      - `not_LTileable_3x_odd_set`: 122 → 75 lines (−47): extracted `sub_full` helper,
        compressed `h_diff_eq` to 3 lines via `simp+omega`, inlined 3-arg lambdas.
      - `LTileable_nx3_iff_set`: 17 → 5 lines (−12): `constructor <;> simpa [swapRegion_rect]`.
      - Total: LTrominoSet.lean 579 → 507 lines (−72).  0 sorries throughout.
- [x] **NAMING_CONVENTIONS.md** created (`feat/set-tiling`).
- [x] **Port `rectMinusCorner_tileable_iff` to Set** (bridge-based, `LTrominoSetBridge.lean`):
      `LTileable_rectMinusCorner_iff_set (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2)`.
      Condition: `(n * m - 1) % 3 = 0`. Via `coe_rectangleMinusCorner_eq` + `LTileable_iff_set`.
- [x] **Port `rectMinus2Corner_tileable_of_area_mod2` to Set** (bridge-based, `LTrominoSetBridge.lean`):
      `LTileable_rectMinus2Corner_set (n m : ℕ) (hn : n ≥ 3) (hm : m ≥ 3) (hmod : n * m % 3 = 2)`.
      Via `coe_rectangleMinus2Corner_eq` + `LTileable_iff_set`.
      Bridge.lean: 59 → 119 lines. 0 sorries.
- [x] **Canonical conversion + simplified bridge** (`feat/set-tiling`):
      Added `SetPrototile.ext`, `toSetPrototile`, `toSetProtoset`, `toSetProtoset_compat`,
      and `Tileable_iff_toSet` (2-arg, no manual compat proof) to `TilingSet.lean`.
      `LTrominoSetBridge.lean` refactored: `LProtoset_set_eq_toSet` + `Tileable_iff_toSet`
      replace `lTrominoSet_compat`; bridge proves `LProtoset_set = toSetProtoset lTrominoSet`.
      Line counts: TilingSet 633→675, Bridge 52→59. 0 sorries.
- [x] **Generic bridge theorem** (`feat/set-tiling`):
      `ProtosetCompatible` predicate + `placedTile_cells_compat` key lemma +
      `Tileable_iff_set` in `TilingSet.lean` (generic, works for any protoset).
      `LTrominoSetBridge.lean` collapsed from 172 → 52 lines via one-liner corollary.
      `lTrominoSet_compat` proves `LProtoset_set` compatible with `lTrominoSet`.
- [x] All `sorry`s proved in `LTromino.lean`
- [x] `rectMinus2Corner_tileable_of_area_mod2` complete
- [x] Blueprint (`leanblueprint web`) with 288 declarations, dependency graph, TikZ figures
- [x] `TilingSet.lean`: full `SetPrototile → SetProtoset → SetPlacedTile → SetTileSet → SetTileable` hierarchy
- [x] `LTrominoSet.lean`: all L-tromino base cases, families, impossibility theorems
- [x] `not_LTileable_3x_odd_set` proved via corner-forcing induction
- [x] `SetTileable.scale_rect` generic theorem
- [x] Fat proofs collapsed (2x_mult3, 3x_even, etc. → 2 lines each)
- [x] Bridge theorem `LTileable_iff_set` + `rect_setTileable_iff_set`
