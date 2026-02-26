# TilingPolyomino — To-Do List

## In Progress
- [ ] **Naming cleanup** (`feat/set-tiling`): fix `LSet*` prefix → `LTileable_*_set` suffix everywhere;
      create `NAMING_CONVENTIONS.md`; full coherence audit across all Set files.

## Up Next

## Backlog
- [ ] **Proof simplification**: audit every proof in `LTrominoSet.lean` / `TilingSet.lean`,
      target ≤15 lines per theorem; use `scale_rect`, `refine`, `rect_omega`.
      No bridge shortcuts — Set proofs should be independently clean.
- [ ] **Port remaining major theorems** to Set framework (currently only `rect_setTileable_iff`):
      - `rectMinusCorner_tileable_iff_set`
      - `rectMinus2Corner_tileable_of_area_mod2_set`
      These would make the Set framework a full peer to `LTromino.lean` (all 3 major theorems).
- [ ] **Fair line-count comparison**: once all 3 major theorems are ported,
      compare line counts for matching theorem sets only.

## Done
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
