# Naming Conventions — TilingPolyomino

This document codifies the naming conventions used across all files.
Follow these when adding new definitions or theorems.

---

## Core Definitions

### Finset framework (`LTromino.lean`)

| Name | Convention |
|------|-----------|
| `lTromino : Finset Cell` | lowercase, matches Prototile name |
| `lTrominoSet : Protoset Unit` | camelCase, `Set` suffix refers to Protoset not `Set Cell` |
| `rectangle n m : Finset Cell` | lowercase |
| `rectangleMinusCorner n m` | camelCase |
| `rectangleMinus2Corner n m` | camelCase |
| `LTileable R` | `L` prefix = L-tromino, no suffix |
| `RectTileableConditions n m` | CamelCase predicate |

### Set framework (`TilingSet.lean`, `LTrominoSet.lean`)

| Name | Convention |
|------|-----------|
| `LShape_cells : Set Cell` | `L` prefix + `_cells` suffix |
| `LPrototile_set : SetPrototile` | `L` prefix + `_set` suffix (= Set-based prototile) |
| `LProtoset_set : SetProtoset Unit` | `L` prefix + `_set` suffix |
| `LTileable_set R` | `L` prefix + `_set` suffix |
| `lPlaced_set dx dy r` | lowercase `l`, private helper |

---

## Theorem Naming

### Tileability theorems (positive)

Pattern: `LTileable_<shape>_set`

```
LTileable_2x3_set
LTileable_2xn_iff_set      -- biconditional: iff + _set
LTileable_3xn_iff_set
LTileable_rectMinusCorner_iff_set
LTileable_rectMinus2Corner_set    -- positive only (no iff)
LTileable_mult3_mult2_set
LTileable_odd_x_6_set
LTileable_swap_set
```

### Impossibility theorems (negative)

Pattern: `not_LTileable_<shape>_set`

```
not_LTileable_1xn_set
not_LTileable_nx1_set
not_LTileable_3x_odd_set
```

### Helper / private lemmas

- Private proof helpers: lowercase `l` prefix + `_set` suffix, e.g., `lPlaced_set_ncard`
- Private rotation helpers: e.g., `swapRot`
- Public support lemmas: camelCase or descriptive, e.g., `swapRegion_rect`, `LPrototile_set_ncard`

---

## Bridge Conventions (`LTrominoSetBridge.lean`)

Coercion lemmas: `coe_<source>_eq_<target>`

```
coe_rectangle_eq_rect        -- ↑(rectangle n m) = rect 0 0 n m
coe_rectangleMinusCorner_eq  -- ↑(rectangleMinusCorner n m) = rect \ {corner}
coe_rectangleMinus2Corner_eq -- ↑(rectangleMinus2Corner n m) = rect \ {two corners}
```

Bridge theorem: `LTileable_iff_set` — the generic Finset↔Set equivalence.

---

## File Organization

| File | Contents |
|------|----------|
| `Basic.lean` | Cell type, PlacedTile, Protoset |
| `Tiling.lean` | Finset-based tiling (Prototile, TileSet, Tileable) |
| `RectOmega.lean` | `rect`, `translate`, `rotate`, `rect_omega` tactic |
| `TilingSet.lean` | Set-based tiling hierarchy + generic bridge |
| `LTromino.lean` | L-tromino definitions + all Finset theorems |
| `LTrominoSet.lean` | L-tromino Set framework: shapes, families, impossibility |
| `LTrominoSetBridge.lean` | Bridge + Set corollaries of major Finset theorems |

---

## Style Guidelines

1. **Suffix `_set`** on Set-framework versions of definitions/theorems (not on Set Cell types themselves)
2. **Bridge first pass**: use `LTileable_iff_set` + coercion for initial ports; add genuine Set proofs later
3. **No bridge shortcuts in LTrominoSet.lean** — all proofs there should be independent Set proofs
4. **Private helpers**: prefix `private` + use `lPlaced_set`-style naming
5. **Target ≤15 lines** per theorem where possible; use `scale_rect`, `refine`, `rect_omega`
