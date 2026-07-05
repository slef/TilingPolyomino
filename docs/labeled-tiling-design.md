# Labeled Tiling Design

## Goal

Extend the tiling framework with edge labels and matching rules. A valid labeled tiling requires: (1) no overlap, (2) covers the region, (3) adjacent edges between different tiles satisfy matching rules, (4) boundary edges of the region satisfy matching rules.

## New Types

### Direction

```
inductive Dir | N | E | S | W

Dir.opposite : Dir → Dir        -- N↔S, E↔W
Dir.step : Cell → Dir → Cell    -- neighbor cell in that direction
rotateDir : Dir → Fin 4 → Dir   -- 90° CCW: N→W→S→E→N
```

### Labeled Prototile (Set-based)

```
structure LabeledPrototile (L : Type*) where
  cells    : Set Cell
  finite   : cells.Finite
  nonempty : cells.Nonempty
  edgeLabel : Cell → Dir → L
  -- edgeLabel is meaningful only for (c, d) where c ∈ cells
  -- and d points outside the tile (i.e., Dir.step c d ∉ cells)
```

Only boundary edges carry meaningful labels. An edge `(c, d)` is a boundary edge when `c ∈ cells` and `Dir.step c d ∉ cells`.

### Labeled Protoset

```
def LabeledProtoset (ι : Type*) (L : Type*) := ι → LabeledPrototile L
```

### Matching Rule

```
structure MatchingRule (L : Type*) where
  allowed : L → L → Prop
```

Direction-independent. For Wang tiles: `allowed = Eq`.

## Placed Tile Labels Under Rotation + Translation

A placed tile has index `i`, rotation `r : Fin 4`, translation `t : Cell`.

The placed cell corresponding to proto-cell `c₀` is:
```
c = translate t (rotateCell c₀ r)
```

The boundary edge `(c₀, d₀)` in the prototile becomes `(c, rotateDir d₀ r)` in the placed tile, with the same label `edgeLabel c₀ d₀`.

Conversely, given a placed cell `c` and direction `d`:
```
original cell:      rotateCell (untranslate t c) (inverseRot r)
original direction: rotateDir d (inverseRot r)
label:              edgeLabel (original cell) (original direction)
```

## Valid Labeled Tiling

Layers on top of the existing `TileSet`/`Valid` framework:

```
structure LabeledTileSet (lps : LabeledProtoset ι L) (ιₜ : Type*) where
  tileSet : TileSet (unlabel lps) ιₜ   -- underlying unlabeled tiling
  -- (unlabel just forgets labels, projecting to Protoset ι)
```

Validity:

```
structure LabeledValid (lt : LabeledTileSet lps ιₜ) (R : Set Cell) (mr : MatchingRule L) where
  base_valid : lt.tileSet.Valid R           -- no overlap + covers R
  interior_matching : ∀ (i j : ιₜ), i ≠ j →
    ∀ c d, c ∈ cellsOf i → Dir.step c d ∈ cellsOf j →
      mr.allowed (labelOf i c d) (labelOf j (Dir.step c d) d.opposite)
  boundary_matching : ∀ (i : ιₜ),
    ∀ c d, c ∈ cellsOf i → Dir.step c d ∉ R →
      mr.allowed (labelOf i c d) ???
    -- boundary version TBD: could require a designated boundary label,
    -- or a separate boundary predicate
```

### Boundary edges — open question

Two options:
- **Boundary label**: `MatchingRule` includes a distinguished boundary label; boundary edges must carry it.
- **Boundary predicate**: A separate `boundaryOk : L → Prop` for edges at the region boundary.
- **Free boundary**: No constraint on boundary edges (simplest, may suffice for many problems).

Decide per use case. Can start with free boundary and add constraints later.

## Target Examples

### Wang Tiles

- `ι = Fin n` (n tile types)
- Each prototile has `cells = {(0,0)}`
- `edgeLabel (0,0) d` gives the color on each of the 4 edges
- `MatchingRule` with `allowed = Eq`
- Rotation: typically disabled (restrict to `r = 0`), or allow all 4

### 1×n Labeled Rectangles

- Prototile `cells = {(0,0), (1,0), ..., (n-1,0)}`
- Internal edges (horizontal, between consecutive cells) are not boundary edges — ignored
- Boundary edges: top/bottom of each cell, left of (0,0), right of (n-1,0)
- Labels on these boundary edges
- Rotation supported (a 1×n becomes n×1 under 90° rotation)

## Relationship to Existing Code

- `LabeledPrototile L` extends `Prototile` with `edgeLabel`
- `LabeledTileSet` wraps `TileSet` — all existing theorems (union, translation, cardinality, refinement) apply to the underlying unlabeled tiling
- Matching is a purely additional constraint on top
- Lives in `TilingPolyomino/LabeledTiling.lean` (new file, Set-based only)

## Key helpers to implement

1. `Dir` type with `opposite`, `step`, `rotateDir`
2. `boundaryEdges : Set Cell → Set (Cell × Dir)` — edges pointing outside
3. `placedLabel : LabeledProtoset → PlacedTile → Cell → Dir → L` — label lookup accounting for rotation + translation
4. `unlabel : LabeledProtoset ι L → Protoset ι` — forget labels
5. Decidable/computable variants if needed later
