# Naming Conventions — TilingPolyomino

This document codifies the naming conventions used across all files.
Follow these when adding new definitions or theorems.

---

## Core Definitions

### Set framework (`TilingSet.lean`, `LTromino.lean`) — **Primary Framework**

All generic Set-framework names have no suffix:

| Name | Convention |
|------|-----------|
| `Prototile` | CamelCase, no suffix |
| `Protoset` | CamelCase, no suffix |
| `Tileable R` | CamelCase, no suffix |
| `LShape_cells : Set Cell` | `L` prefix + `_cells` suffix |
| `LPrototile : SetPrototile` | `L` prefix |
| `LProtoset : SetProtoset Unit` | `L` prefix |
| `LTileable R` | `L` prefix = L-tromino, no suffix |
| `lPlaced dx dy r` | lowercase `l`, private helper |

### Finset framework (`Tiling.lean`, `LTrominoBase.lean`) — **Legacy / Computable Framework**

All finset-specific concepts use the `_finset` suffix:

| Name | Convention |
|------|-----------|
| `Prototile_finset` | `_finset` suffix |
| `Protoset_finset` | `_finset` suffix |
| `Tileable_finset` | `_finset` suffix |
| `LTromino_finset` | `_finset` suffix, uppercase L |
| `LTrominoSet_finset` | `_finset` suffix |
| `LTileable_finset R` | `L` prefix, `_finset` suffix |
| `rectangle n m : Finset Cell` | lowercase |
| `rectangleMinusCorner n m` | camelCase |
| `rectangleMinus2Corner n m` | camelCase |
| `RectTileableConditions n m` | CamelCase predicate |

---

## Theorem Naming

### Tileability theorems (positive)

Pattern: `LTileable_<shape>`

```
LTileable_2x3
LTileable_2xn_iff      -- biconditional: iff
LTileable_3xn_iff
LTileable_rectMinusCorner_iff
LTileable_rectMinus2Corner    -- positive only (no iff)
LTileable_mult3_mult2
LTileable_odd_x_6
LTileable_swap
```

### Impossibility theorems (negative)

Pattern: `not_LTileable_<shape>`

```
not_LTileable_1xn
not_LTileable_nx1
not_LTileable_3x_odd
```

### Complete Name Mapping (Set framework)

| Concept | Name |
|---|---|
| L-tromino prototile | `LPrototile` |
| L-tromino protoset | `LProtoset` |
| ncard of prototile | `LPrototile_ncard` |
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

### Helper / private lemmas

- Private proof helpers: lowercase `l` prefix, e.g., `lPlaced_ncard`
- Private rotation helpers: e.g., `swapRot`
- Public support lemmas: camelCase or descriptive, e.g., `swapRegion_rect`, `LPrototile_ncard`
- No `lPlacedCopy` or equivalent helper — use `PlacedTile.cells LProtoset` directly in the public API.

---

## Bridge Conventions (`LTrominoSetBridge.lean`)

Coercion lemmas: `coe_<source>_eq_<target>`

```
coe_rectangle_eq_rect        -- ↑(rectangle n m) = rect 0 0 n m
coe_rectangleMinusCorner_eq  -- ↑(rectangleMinusCorner n m) = rect \ {corner}
coe_rectangleMinus2Corner_eq -- ↑(rectangleMinus2Corner n m) = rect \ {two corners}
```

Bridge theorem: `Tileable_iff_to_set` — the generic Finset↔Set equivalence.

---

## File Organization

| File | Contents |
|------|----------|
| `Basic.lean` | Cell type, PlacedTile, Protoset |
| `TilingSet.lean` | Set-based tiling hierarchy (Primary) |
| `Tiling.lean` | Finset-based tiling (Legacy/Computable Base Cases) |
| `RectOmega.lean` | `rect`, `translate`, `rotate`, `rect_omega` tactic |
| `LTromino.lean` | L-tromino Set framework: shapes, families, impossibility, main theorems |
| `LTrominoBase.lean` | L-tromino Finset definitions + explicit `decide` base cases |
| `LTrominoSetBridge.lean` | Bridge lemmas to move Finset base cases to the Set framework |
| `Mod3.lean` | Utility lemmas for modular arithmetic |

---

## Style Guidelines

1. **Suffix `_finset`** on Finset-framework versions of definitions/theorems (the legacy/computable framework).
2. **Set framework is default**: Primary proofs and structures in `TilingSet.lean` and `LTromino.lean` should not have framework-specific suffixes.
3. **Bridge usage**: Use `Tileable_iff_to_set` + coercion to promote explicit Finset base cases to Set theorems.
4. **Target ≤15 lines** per theorem where possible; use `scale_rect`, `refine`, `rect_omega`.
