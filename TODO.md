# TilingPolyomino — To-Do List

## ⚠️ TOP PRIORITY — Strategic Goal: Native Set Proofs (No Bridge Shortcuts)

The purpose of the Set framework (`TilingSet.lean` / `LTrominoSet.lean`) is to provide
**simpler, independent proofs** of all major L-tromino theorems — not to delegate back to
the Finset framework via the bridge.

The bridge (`LTrominoSetBridge.lean`) is a **two-way compatibility layer** for later use:
if some theorem is easier to prove in one framework, the bridge lets you transport it.
But using the bridge to prove Set theorems defeats the entire point.

**Status** (ALL DONE):
1. ~~`LTileable_rect_iff_set`~~ — **DONE**: native proof in LTrominoSet.lean (f62afd4)
2. ~~`LTileable_rectMinusCorner_iff_set`~~ — **DONE**: native proof in LTrominoSet.lean (ce3b2f0, 2026-02-27 15:10)
3. ~~`LTileable_rectMinus2Corner_set`~~ — **DONE**: native proof in LTrominoSet.lean (`5f82e19`, 2026-02-27 16:10)

All three major Set-framework theorems are now proved natively. Bridge.lean retains only
conversion helpers (`LTileable_iff_set`, coercions) — no theorem delegation to bridge.

## ✅ RESOLVED — LTileable_5x9_set heartbeat fix confirmed working
`set_option maxHeartbeats 20000000` per-theorem budget applied (commit ce3b2f0 working tree, now committed).
Build passed cleanly — 0 errors, 0 warnings, 0 sorries. Verified 2026-02-27 15:10 cron.

## In Progress

_Nothing in progress. P4 just completed (2026-02-27 16:10). Next up: P5 or P6._

## Up Next

### P5 (NEW TOP PRIORITY) — General Two-Corner Defects Theorem (new work, new file)

See `FUTURE_PLANS.md` Extension 1 for full statement, proof sketch, and diagrams.

**Informal statement**: Every n×m rectangle (n,m ≥ 9) with at most two corner defects
(each defect removing 1 or 2 adjacent cells from a corner) and area ≡ 0 (mod 3) is
L-tromino tileable.

**New file**: `LTrominoDefects.lean` (imports `LTrominoSet.lean`; Set framework throughout).

**Proof strategy** (Stefan's sketch, 2026-02-27):
- Strong induction on m, case split on `m % 3`:
  - `m % 3 ≠ 0`: vertical cut — each piece gets one defect and area ≡ 0 (mod 3);
    apply `LTileable_rectMinusCorner_iff_set` (size-1) or Remark 2 analogue (size-2).
  - `m % 3 = 0`: strip a 2-row band covering both defects, recurse on remaining
    (m-2 ≢ 0 mod 3 → falls to Case 1). The band has 3×3 = 9 configurations.

**Prerequisites (all done)**:
- `LTileable_rectMinusCorner_iff_set` ✓
- `LTileable_rectMinus2Corner_set` ✓ (size-2 defect analogue)
- `SetTileable.horizontal_union`, `vertical_union`, `scale_rect` ✓
- `LTileable_2xn_iff_set` ✓

**Sub-tasks**:
- [ ] Define `rectMinus2Corners_set` (region with two arbitrary corner defects d1,d2 ∈ {1,2})
- [ ] Prove the 2-row band lemma (9 configurations: 3 left-defect × 3 right-defect shapes)
- [ ] Prove the vertical-cut lemma (Case 1)
- [ ] Prove the main theorem by induction
- [ ] Verify / tighten bound B = 9

### P6 — Auto-tactic for explicit tiling verification (side project — do only if more explicit tilings needed)
- Pattern: all explicit tiling proofs have the same structure: provide tile list, prove pairwise
  disjointness by `fin_cases` + `rect_omega`, prove coverage by `interval_cases` + witnesses
- Idea: a `decide_tiling` tactic (or `norm_num` extension) that takes a tile list and a region
  and automatically generates + checks the proof, so explicit tilings become 1-liners
- Motivation: 5×9 took 45 lines; with more base cases for deficient rectangles (4×4, 5×5, 7×7,
  5×2 minus corner), we'll need several more — an auto-tactic would collapse all to ~3 lines each
- Only worth building if we need ≥4 more explicit tiling base cases; assess after deficient rect work

### P7 — RExp experiment: redefine `LShape_cells` as `rect 0 0 1 2 ∪ rect 1 0 2 1`
- Question: does this collapse the `simp [LShape_cells, mem_translate, ...]; omega` blocks
  in coverage proofs to single `rexp_omega` calls?
- Cost: `LPrototile_set_ncard` becomes harder (ncard of a union); bridge proofs may need updating
- Try on a branch; measure before committing

### P7 — Blueprint for the Set framework (do when out of proof tasks)
- Extend the existing blueprint (`blueprint/` dir) to cover the Set framework theorems
- Add dependency nodes for: `SetTileable`, `scale_rect`, `LTileable_rect_iff_set`,
  `LTileable_rectMinusCorner_iff_set`, `LTileable_rectMinus2Corner_set`
- Add TikZ figures for the new theorems where useful
- Update `\uses{}` entries in blueprint `.tex` files for the new dep graph edges
- Goal: the blueprint should cover the full arc from Set primitives to the final characterization

## Backlog

## Backlog
- [ ] **rect_omega for Set.mem_diff goals**: `h_diff_eq` style proofs now use
      `ext ⟨x,y⟩; simp only [...]; omega` — consider adding this as a `rect_omega` extension.
- [ ] **TilingSet.lean structural linter warnings** (pre-existing, unfixable without restructure):
      `remove_two` and `refine_partition` have `[Fintype ι]` hypotheses not appearing in their
      return types. Fixing requires switching to `Finite` + `Fintype.ofFinite` in the proofs.
      Leave as-is unless doing a structural refactor.

## Done (recent)
- [x] **P4 COMPLETE — Native `LTileable_rectMinus2Corner_set` in LTrominoSet.lean** (`feat/set-tiling`, `5f82e19`, 2026-02-27 16:10):
      - Full native Set-framework proof; no bridge delegation. 0 sorries. Build clean.
      - `rectMinus2Corner_set` defined as `rect 0 0 n m \ ({(n-1, m-1)} ∪ {(n-2, m-1)})`.
      - Helper lemmas: `LTileable_piece2_base_set`, `LTileable_piece2_set` (4×(3k+1) minus corner).
      - Family lemmas: `LTileable_4x_3kplus2_minus_2corner_set`, `LTileable_3jplus2_x_3kplus1_minus_2corner_set`,
        `LTileable_3jplus1_x_3kplus2_minus_2corner_set`.
      - Main theorem at LTrominoSet.lean line 1637: case split on (n≡1,m≡2) vs (n≡2,m≡1) mod 3.
      - Bridge copy removed. LTrominoSet.lean: 1295 → 1658L (+363). Bridge: 108 → 84L (−24).
      - All three TOP PRIORITY native Set proofs complete. Branch is PR-ready.
- [x] **P3 COMPLETE — Native `LTileable_rectMinusCorner_iff_set` in LTrominoSet.lean** (`feat/set-tiling`, `ce3b2f0`, 2026-02-27 15:10):
      - All 7 steps complete, 0 sorries, build clean (verified by cron 15:10).
      - STEP 6: `LTileable_rectMinusCorner_ncard_set` (necessity via ncard divisibility).
      - STEP 7: Full iff assembled from mod-1 and mod-2 cases:
        `LTileable_4x_3kplus1_minus_corner_set`, `LTileable_rectMinusCorner_mod1_jk_ge_set`,
        `LTileable_rectMinusCorner_mod1_recurrence_k_ge3_set`, `LTileable_rectMinusCorner_mod1_set`,
        `LTileable_mod2_minus_corner_set_all`, `LTileable_rectMinusCorner_iff_set`.
      - Bridge copy removed. LTrominoSet.lean: 1057 → 1295L (+238). Bridge: 119 → 108L (−11).
      - `LTileable_5x9_set` heartbeat blocker resolved: `set_option maxHeartbeats 20000000`.
- [x] **P3 STEPS 1–5 — Native rectMinusCorner work in LTrominoSet.lean** (`feat/set-tiling`, `a466cf0`..`46fee68`, 2026-02-27 10:48):
      - `rectMinusCorner_set` defined as `rect 0 0 n m \ {(n-1, m-1)}` in Set framework.
      - Split/union lemmas, swap, ncard proved.
      - 5 explicit base cases: 2×2, 5×2, 4×4, 5×5, 7×7.
      - 4 family lemmas: (3k+2)×2, 4×(7+6k), 5×(6k+2), 5×(6k+5).
      - Main mod-2 case: `LTileable_rectMinusCorner_mod2_set` (both dims ≡ 2 mod 3).
      - LTrominoSet.lean: 679 → 1057L (+378). 0 sorries. Build clean.
      - Remaining: STEP 6 (forward/impossibility) + STEP 7 (full iff assembly) — see In Progress.
- [x] **P2b — Bridge copy of `LTileable_rect_iff_set` removed** (cron check 2026-02-27 09:40):
      - Inspection confirmed: `theorem LTileable_rect_iff_set` is NOT present in Bridge.lean.
      - Only a 2-line NOTE comment remains at lines 56-57 (cosmetic; can be deleted at will).
      - Bridge.lean stays at 115L (the ~100L target was based on a larger expected proof;
        actual bridge proof was short, so the headroom was always smaller than estimated).
      - No downstream breakage: `LTileable_rect_iff_set` in LTrominoSet.lean is the canonical
        definition; nothing imports it from Bridge.lean.
      - **Header doc block still lists it** (line 11): update when doing next Bridge.lean pass.
- [x] **P2 — Native `LTileable_rect_iff_set` in LTrominoSet.lean (no bridge)** (`feat/set-tiling`, `f62afd4`, 2026-02-27):
      - All 5 sorry lemmas proved. LTrominoSet.lean: 483 → 679L (+196). 0 sorries. Build clean.
      - `LTileable_5x9_set`: explicit 15-tile disjoint cover.
      - `LTileable_5x_6iplus3_set`: induction via vertical_union of 5×9 and 5×(6i) blocks.
      - `LTileable_odd_ge5_x_6iplus3_set`: strong induction stripping 2-col slabs.
      - `LTileable_odd_x_mult3_set`: case split k even / k odd (6i+3 lemma).
      - `LTileable_rect_iff_set` (line 677): main iff, wired to ncard_dvd + not_LTileable_3x_odd_set.
      - **Note**: Bridge copy in LTrominoSetBridge.lean (line 56) annotated "now proved natively" but
        not yet removed (bridge still 115L). Remove it in next cleanup pass.
- [x] **P1 — `LTileable_3x2_set` as 1-liner via swap** (`feat/set-tiling`, `dd1ffba`, 2026-02-27):
      - Unprivated `swapRegion_rect`; replaced 14-line proof with:
        `swapRegion_rect 2 3 ▸ LTileable_swap_set LTileable_2x3_set`
      - LTrominoSet.lean: 466 → 464 lines (−2 net after P1 + blueprint TODO docs commit).
      - 0 sorries. Build clean.
- [x] **Lint fix: scale_rect_vert unused var + line-too-long** (`feat/set-tiling`, 25343f7):
      - `scale_rect_vert`: renamed `hc` → `_hc` (unused variable warning).
      - `scale_rect`: split long one-liner (line 476) across two lines (100-char limit).
      - These were introduced by the `scale_rect_horiz + scale_rect_vert` decomposition commit.
      - TilingSet.lean: 649 → 650 lines (+1). Build clean, 0 sorries. Pushed to fork.
- [x] **PR-readiness pass** (`feat/set-tiling`, 775fc1f):
      - Removed stale `TASK_next.md` (131L scratch planning file; all 4 tasks it described
        are long complete in LTrominoSet.lean and LTrominoSetBridge.lean).
      - **Priority 1 already done** (`5ee8c77`): `LTileable_rect_area_dvd_set` is 4L
        (single `simpa [rect_ncard, ...]`), well below the 15L target. Cron claim of "27L" was stale.
      - **Priority 2 already done** (`021ca62`): `LTileable_rect_iff_set` exactly matches
        `rect_tileable_iff` conditions via `RectTileableConditions` — no discrepancy.
      - Remaining linter warnings (pre-existing, documented in Backlog):
          * `TilingSet.lean` `[Fintype ι]` not-in-return-type for `remove_two`/`refine_partition`
          * `LTromino.lean:1832` `ring_nf` info suggestion (info only, not an error)
      - Build: clean, 0 sorries. Branch is synced with fork/feat/set-tiling.
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
- [x] **Inline LTileable_2x2_minus_set** (`main`):
      - Moved inline into `LTileable_2x2_minus_corner_set`.
      - Used `by simp` to automatically close the first disjointness goal instead of `fin_cases`.
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
      replace `LTrominoSet_compat`; bridge proves `LProtoset_set = toSetProtoset LTrominoSet`.
      Line counts: TilingSet 633→675, Bridge 52→59. 0 sorries.
- [x] **Generic bridge theorem** (`feat/set-tiling`):
      `ProtosetCompatible` predicate + `placedTile_cells_compat` key lemma +
      `Tileable_iff_set` in `TilingSet.lean` (generic, works for any protoset).
      `LTrominoSetBridge.lean` collapsed from 172 → 52 lines via one-liner corollary.
      `LTrominoSet_compat` proves `LProtoset_set` compatible with `LTrominoSet`.
- [x] All `sorry`s proved in `LTromino.lean`
- [x] `rectMinus2Corner_tileable_of_area_mod2` complete
- [x] Blueprint (`leanblueprint web`) with 288 declarations, dependency graph, TikZ figures
- [x] `TilingSet.lean`: full `SetPrototile → SetProtoset → SetPlacedTile → SetTileSet → SetTileable` hierarchy
- [x] `LTrominoSet.lean`: all L-tromino base cases, families, impossibility theorems
- [x] `not_LTileable_3x_odd_set` proved via corner-forcing induction
- [x] `SetTileable.scale_rect` generic theorem
- [x] Fat proofs collapsed (2x_mult3, 3x_even, etc. → 2 lines each)
- [x] Bridge theorem `LTileable_iff_set` + `rect_setTileable_iff_set`
