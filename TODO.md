# TilingPolyomino — To-Do List

## In Progress
- [ ] **Naming cleanup** (`feat/set-tiling`): fix `LSet*` prefix → `LTileable_*_set` suffix everywhere;
      create `NAMING_CONVENTIONS.md`; full coherence audit across all Set files.

## Up Next
- [ ] **Generic bridge theorem** (in `TilingSet.lean`):
      add `toSetPrototile`, `toSetProtoset` conversion functions, then prove
      `Tileable_iff_set : Tileable ps R ↔ SetTileable (↑R) (toSetProtoset ps)`.
      Then `LTrominoSetBridge.lean` collapses to a one-liner corollary;
      `LProtoset_set` becomes `toSetProtoset lTrominoSet`.

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
- [x] All `sorry`s proved in `LTromino.lean`
- [x] `rectMinus2Corner_tileable_of_area_mod2` complete
- [x] Blueprint (`leanblueprint web`) with 288 declarations, dependency graph, TikZ figures
- [x] `TilingSet.lean`: full `SetPrototile → SetProtoset → SetPlacedTile → SetTileSet → SetTileable` hierarchy
- [x] `LTrominoSet.lean`: all L-tromino base cases, families, impossibility theorems
- [x] `not_LTileable_3x_odd_set` proved via corner-forcing induction
- [x] `SetTileable.scale_rect` generic theorem
- [x] Fat proofs collapsed (2x_mult3, 3x_even, etc. → 2 lines each)
- [x] Bridge theorem `LTileable_iff_set` + `rect_setTileable_iff_set`
