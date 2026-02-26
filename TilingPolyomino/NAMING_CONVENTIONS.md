# Naming Conventions

## Tiling Framework

### Generic (TilingSet.lean)
Structures and predicates with no specific tile shape use plain names:
- `SetPrototile`, `SetProtoset`, `SetPlacedTile`, `SetTileSet`, `SetTileable`
- Lemmas: `SetTileable.refine`, `SetTileable.scale_rect`, `SetTileable.translate`, etc.

### L-Tromino Specific (LTrominoSet.lean, LTrominoSetBridge.lean)
All L-tromino-specific names follow this scheme:

**Rule 1**: `_set` is always a **suffix**, always **lowercase**.
  Correct: `LTileable_2x3_set`, `LPrototile_set`, `LProtoset_set`
  Wrong: `LSetTileable_2x3`, `lSetPrototile`, `setTileable_2x3`

**Rule 2**: `LTileable` prefix for all L-tromino tileability theorems.
  Correct: `LTileable_2x3_set`, `LTileable_swap_set`, `not_LTileable_3x_odd_set`
  Wrong: `tileable_2x3_set`, `setTileable_2x3`

**Rule 3**: No `lPlacedCopy` or equivalent helper — use `SetPlacedTile.cells LProtoset_set` directly.
  Private implementation helpers (e.g. `private def lPlaced_set`) are acceptable when they
  meaningfully simplify proof terms, but must not appear in the public API.

### Finset Framework (LTromino.lean) — Reference
For comparison, the Finset framework uses:
- Objects: `lTromino : Prototile`, `lTrominoSet : Protoset Unit` (lowercase l)
- Property: `LTileable` (uppercase L)
- Base case lemmas: `tileable_2x3`, `tileable_3x2` (no L prefix)
- Generic lemmas: `LTileable_swap`, `LTileable_translate` (uppercase L)
- Impossibility: `not_tileable_3_by_odd`, `not_tileable_1_by_n`

The Set framework mirrors this with `_set` suffix:
- Objects: `LPrototile_set`, `LProtoset_set`
- Property: `LTileable_set` (def alias)
- All lemmas: `LTileable_2x3_set`, `LTileable_swap_set`, `not_LTileable_3x_odd_set`

### Complete Name Mapping (Set framework)

| Concept | Name |
|---|---|
| L-tromino prototile | `LPrototile_set` |
| L-tromino protoset | `LProtoset_set` |
| ncard of prototile | `LPrototile_set_ncard` |
| Tileability predicate | `LTileable_set` |
| Swap symmetry | `LTileable_swap_set` |
| Base: 2×3 | `LTileable_2x3_set` |
| Base: 3×2 | `LTileable_3x2_set` |
| Base: 2×2 minus corner | `LTileable_2x2_minus_set` |
| Inductive: 2×(3k) | `LTileable_2x_mult3_set` |
| Inductive: 3×(2k) | `LTileable_3x_even_set` |
| Inductive: (3k)×2 | `LTileable_mult3_x_2_set` |
| Inductive: (2k)×3 | `LTileable_even_x_3_set` |
| Inductive: 6×k (k≥2) | `LTileable_6x_of_ge2_set` |
| Inductive: k×6 (k≥2) | `LTileable_kx6_of_ge2_set` |
| Area divisibility | `LTileable_rect_area_dvd_set` |
| Impossibility: 1×n | `not_LTileable_1xn_set` |
| Impossibility: n×1 | `not_LTileable_nx1_set` |
| Impossibility: 3×odd | `not_LTileable_3x_odd_set` |
| Iff: 2×n | `LTileable_2xn_iff_set` |
| Iff: 3×n | `LTileable_3xn_iff_set` |
| Iff: n×3 | `LTileable_nx3_iff_set` |
| General: (3a)×(2b) | `LTileable_mult3_mult2_set` |
| General: (2a)×(3b) | `LTileable_mult2_mult3_set` |
| General: odd×6 | `LTileable_odd_x_6_set` |
| General: 6×odd | `LTileable_6x_odd_set` |
| General: odd×(6k) | `LTileable_odd_x_mult6_set` |
| Bridge: LTileable ↔ SetTileable | `LTileable_iff_set` |
| Bridge: rect iff | `LTileable_rect_iff_set` |
| lTromino coercion to LShape_cells | `lTromino_coe_eq_LShape_set` |
