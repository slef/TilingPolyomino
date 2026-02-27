# TilingPolyomino — To-Do List

## In Progress
- (nothing active)

## Up Next
- [ ] **Genuine Set proofs for corner theorems**: `LTileable_rectMinusCorner_iff_set` and
      `LTileable_rectMinus2Corner_set` are currently bridge-based (via `LTileable_iff_set`).
      Goal: replace with independent Set proofs (no bridge), mirroring the structure of
      `not_LTileable_3x_odd_set` and `LTileable_3xn_iff_set`.
- [ ] **Fair line-count comparison**: compare `LTrominoSet.lean` + `LTrominoSetBridge.lean`
      against `LTromino.lean` for matching theorem sets.
- [ ] **`induction'` → `induction`**: Replace `induction'` (style warning) in
      `LTileable_6x_of_ge2_set` and `LTileable_odd_x_6_set` with `induction ... using`.
- [ ] **`LTileable_2xn_iff_set` and `LTileable_nx2_iff_set`** companion symmetry (only `2xn`/`3xn`
      are biconditionals; `nx2` and `nx3` directions are missing or need checking).

## Backlog
- [ ] **rect_omega for Set.mem_diff goals**: `h_diff_eq` style proofs now use
      `ext ⟨x,y⟩; simp only [...]; omega` — consider adding this as a `rect_omega` extension.
- [ ] **`LTileable_nx2_iff_set`** and **`LTileable_2xn_iff_set`** companion symmetry theorems
      (currently only `2xn` and `3xn` are biconditionals).

## Done (recent)
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
