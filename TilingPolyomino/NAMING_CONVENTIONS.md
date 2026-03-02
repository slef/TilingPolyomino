# Naming Conventions

## Tiling Framework

### Generic (TilingSet.lean)
All generic Set-framework names follow this scheme:

**Rule 1**: `_set` is always a **suffix**, always **lowercase**.
  Correct: `Prototile`, `Protoset`, `PlacedTile`, `TileSet`, `Tileable`
  Wrong: `SetPrototile`, `setTileable`, `SetTileSet`

- Lemmas: `Tileable.refine`, `Tileable.scale_rect`, `Tileable.translate`, etc.

### L-Tromino Specific (LTrominoSet.lean, LTrominoSetBridge.lean)
All L-tromino-specific names follow this scheme:

**Rule 1**: `_set` is always a **suffix**, always **lowercase**.
  Correct: `LTileable_2x3`, `LPrototile`, `LProtoset`
  Wrong: `LSetTileable_2x3`, `lSetPrototile`, `setTileable_2x3`

**Rule 2**: `LTileable` prefix for all L-tromino tileability theorems.
  Correct: `LTileable_2x3`, `LTileable_swap`, `not_LTileable_3x_odd`
  Wrong: `tileable_2x3`, `setTileable_2x3`

**Rule 3**: No `lPlacedCopy` or equivalent helper — use `SetPlacedTile.cells LProtoset` directly.
  Private implementation helpers (e.g. `private def lPlaced`) are acceptable when they
  meaningfully simplify proof terms, but must not appear in the public API.

### Finset Framework (LTromino.lean) — Reference
For comparison, the Finset framework uses:
- Objects: `LTromino : Prototile`, `LTrominoSet : Protoset Unit`
- Property: `LTileable` (uppercase L)
- Base case lemmas: `tileable_2x3`, `tileable_3x2` (no L prefix)
- Generic lemmas: `LTileable_swap`, `LTileable_translate` (uppercase L)
- Impossibility: `not_tileable_3_by_odd`, `not_tileable_1_by_n`

The Set framework mirrors this with `_set` suffix:
- Objects: `LPrototile`, `LProtoset`
- Property: `LTileable` (def alias)
- All lemmas: `LTileable_2x3`, `LTileable_swap`, `not_LTileable_3x_odd`

### Complete Name Mapping (Set framework)

| Concept | Name |
|---|---|
| L-tromino prototile | `LPrototile` |
| L-tromino protoset | `LProtoset` |
| ncard of prototile | `LPrototile_set_ncard` |
| Tileability predicate | `LTileable` |
| Swap symmetry | `LTileable_swap` |
| Base: 2×3 | `LTileable_2x3` |
| Base: 3×2 | `LTileable_3x2` |
| Base: 2×2 minus corner | `LTileable_2x2_minus_corner` |
| Inductive: 2×(3k) | `LTileable_2x_mult3` |
| Inductive: 3×(2k) | `LTileable_3x_even` |
| Inductive: (3k)×2 | `LTileable_mult3_x_2` |
| Inductive: (2k)×3 | `LTileable_even_x_3` |
| Inductive: 6×k (k≥2) | `LTileable_6x_of_ge2` |
| Inductive: k×6 (k≥2) | `LTileable_kx6_of_ge2` |
| Area divisibility | `LTileable_rect_area_dvd` |
| Impossibility: 1×n | `not_LTileable_1xn` |
| Impossibility: n×1 | `not_LTileable_nx1` |
| Impossibility: 3×odd | `not_LTileable_3x_odd` |
| Iff: 2×n | `LTileable_2xn_iff` |
| Iff: 3×n | `LTileable_3xn_iff` |
| Iff: n×3 | `LTileable_nx3_iff` |
| General: (3a)×(2b) | `LTileable_mult3_mult2` |
| General: (2a)×(3b) | `LTileable_mult2_mult3` |
| General: odd×6 | `LTileable_odd_x_6` |
| General: 6×odd | `LTileable_6x_odd` |
| General: odd×(6k) | `LTileable_odd_x_mult6` |
| Bridge: LTileable ↔ Tileable | `LTileable_iff` |
| Bridge: rect iff | `LTileable_rect_iff` |
| LTromino coercion to LShape_cells | `LTromino_coe_eq_LShape` |
