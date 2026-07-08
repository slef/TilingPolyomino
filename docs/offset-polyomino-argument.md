# Fat polyominoes are L-tileable, via the inward offset — the argument

Source: SL's verbal sketch + whiteboard drawing, 2026-07-07; construction
refined and scoping decisions fixed by SL later the same day.  This note
records the argument as the agent understands it, the formal definitions,
and the constant accounting.  Skeleton: `TilingPolyomino/OffsetPolyomino.lean`
(green, one `sorry`: `exists_corridorChain`).

## 1. Statement

> **Theorem (target).**  Every finite, connected, simply connected
> (`Pᶜ` connected), 16-fat polyomino whose area is a multiple of 3 is
> L-tileable.

*λ-fat* (SL): every vertex of the boundary is at `L∞`-distance ≥ λ from
every non-incident edge.  A *local* property, unlike the global grid
alignment of `LTileable_of_vertexAligned`.

Scoping decisions (SL, 2026-07-07):

- **No holes for now** (`CellConnected Pᶜ` hypothesis): with a hole, the
  corridor gets one annulus per boundary component, the inner annulus has
  area ≡ −|hole| (mod 6) regardless of snapping, and defects cannot cross
  the offset region.  Holes are future work.
- **Diagonal (pinch) vertices are excluded by fatness** — automatic in the
  quadrant formulation below (no quadrant has the diagonal 2×2 pattern).
  Necessary: two rectangles joined at a corner can satisfy the
  distance-only reading of fatness but need not be tileable.
- **The constant is 16 = 2·8**: 8 = 6 (corridor thickness needed by the
  two-corner-defect theorem) + 2 (snap), doubled so that two offset edges
  never *cross* (touching is fine: `offsetCore` may degenerate or
  disconnect, and the 3×2-grid result needs no connectivity).

## 2. Fatness, formally

`Fat l P` (in the skeleton): **for every vertex `v` of `P`, inside the
square of `L∞`-radius `l` centered at `v`, `P` coincides with a quarter
plane cornered at `v`, or with the complement of one**:

```
∃ c : Corner, P ∩ box v l = quadrant v c ∩ box v l
            ∨ P ∩ box v l = (quadrant v c)ᶜ ∩ box v l
```

(`quadrant v .BL` = the quarter plane up-right of `v`, etc.; convex corner
= quadrant, reflex corner = complement.)  Equivalence with the distance
formulation: if no foreign edge comes within `l` of `v`, the only boundary
in the square is the two incident edges, which run straight through it, so
`P` is a quadrant there; conversely a quadrant's square contains no
foreign boundary.  Useful consequences (to be proved when needed):

- every maximal edge has length ≥ `l` (arms of the quadrant run through
  the square);
- two boundary edges facing each other are ≥ `l` apart (at an endpoint of
  the overlap of their spans sits a vertex of one whose square would see
  the other).

## 3. The offset polyomino

*(SL: "offset every edge inwards by at least 6, then further until it
snaps on the 3×2 grid.")*

Formal construction (per-cell, hypothesis-free):

> `offBox c` = the 3×2 grid cell at `c` inflated by 6 in all directions;
> `offsetCore P` = the union of the complete 3×2 grid cells with
> `offBox ⊆ P`.

- `offsetCore P ⊆ P`, finite; **all its vertices lie on the 3×2 grid, for
  any `P` whatsoever** (membership is constant on grid cells) — so by
  `LTileable_of_vertexOnGrid3x2` it is L-tileable with *no* connectivity
  or area hypothesis.  In particular the degeneracies at 16-fatness
  (offset edges touching, `offsetCore` disconnected or locally empty) are
  harmless.
- `|offsetCore P| ≡ 0 (mod 6)`, so `corridor P = P \ offsetCore P` has
  area ≡ |P| (mod 3).

For a fat `P` this erosion **is** edge-offset-and-snap: along a boundary
edge the offset boundary is the first grid line at distance ≥ 6 inside,
i.e. at distance `∈ {6,7,8}` (vertical edges, pitch 3) or `∈ {6,7}`
(horizontal edges, pitch 2).  Each vertex `uᵢ` of `P` yields a vertex
`vᵢ` of the offset boundary, displaced 6–8 in both coordinates, direction
determined by the corner's quadrant and type (convex/reflex).

## 4. The corridor chain (SL's ray construction, 2026-07-07)

The boundary of `P` is a single cycle (§5).  Walk it (say ccw, so the
offset polygon `u₀u₁…` ↦ `v₀v₁…` is walked in parallel; edges alternate
horizontal/vertical, and offset edges may have length 0 — fine).  Draw one
cut per vertex, always *forward* in the walk direction:

- at a **convex** vertex `uᵢ`: the ray from `vᵢ₋₁` through `vᵢ`, extended
  past `vᵢ` until it hits `∂P` at `v'ᵢ` — a cut of length 6–8 from the
  offset corner to the boundary;
- at a **reflex** vertex `uᵢ`: the ray from `uᵢ₋₁` through `uᵢ`, extended
  past `uᵢ` until it hits the offset boundary at `u'ᵢ` — again length
  6–8.

These cuts partition the corridor into **one rectangle per boundary
edge**, with dimensions:

- thickness 6–8 (the offset distance of that edge);
- length = edge length (≥ 16), −(6–8) if the *entry* vertex is convex
  (the rectangle starts at the offset corner line), +(6–8) if the *exit*
  vertex is reflex (the rectangle absorbs the corner block) — in the worst
  case ≥ 16 − 8 = 8 ≥ 6.  ✓

Consecutive rectangles share the cut endpoint `v'ᵢ` (on `∂P`, convex
case) or `u'ᵢ` (on the offset boundary, reflex case) as a **common
corner** with edge-adjacent corner cells — exactly `PushAdj`.  So the
rectangles form a cyclic corner chain; cutting the cycle at one link gives
the `IsCornerChain` list (no defect needs to cross the cut: the corridor
area is already ≡ 0 mod 3).  `IsCornerChain.tileable` finishes the
corridor, and `P = offsetCore ⊔ corridor` finishes the theorem.

Formalization choice: walk the **vertices `uᵢ` of `P`** as the primary
object and *define* `vᵢ` by the snap formula; prove `offsetCore` coincides
locally with the band description.  The weakly-simple degeneracies of the
offset polygon (pinches, zero-length edges) then never need their own
combinatorics.

## 5. The boundary is a single cycle

Two parts:

1. **Local (easy, from fatness):** each vertex has exactly two incident
   maximal edges, each running straight for ≥ 16 to the next vertex; with
   an interior-on-the-left orientation, "next vertex" is a function, and
   the finite vertex set splits into disjoint cycles.
2. **Global (the real content, but elementary — no Jordan curve needed):**
   *ray-crossing parity.*  For a boundary cycle `C` and a cell `q`, let
   `π(q)` = parity of the number of vertical edges of `C` crossed by the
   rightward ray from `q` (i.e. vertical `C`-edges in `q`'s row, strictly
   to its right).  Then:
   - `π` is invariant along horizontal steps between two cells of `P`, or
     two cells of `Pᶜ` (such a step crosses no boundary edge, and a
     vertical `C`-edge occupies the only relevant position);
   - `π` is invariant along vertical steps (every grid point has even
     degree in the closed cycle `C` — a discrete Green's-theorem count);
   - so by `CellConnected P` and `CellConnected Pᶜ`, `π` is constant on
     `P` and constant on `Pᶜ`;
   - across an edge **of `C`** the two sides differ in `π`, so the two
     constants differ; but across a boundary edge **not in `C`** the two
     sides agree — contradiction if any such edge exists.  Hence every
     boundary edge lies on `C`: one cycle.

## 6. Status / next steps

**THEOREM COMPLETE (2026-07-09): `LTileable_of_fat` is fully proved,
zero sorries project-wide, standard axioms only.  The plan below was
carried out as written; the three final lemmas
(`edgePiece_subset_corridor`, `edgePiece_disjoint`, `corridor_covered`)
were proved by three parallel subagents and spliced back.  Remaining
follow-ups: the `LTileable ⇒ 3 ∣ area` converse, holes, abstract-layer
exposure, and splitting `OffsetPolyomino.lean` into per-topic modules.**

Done (all green in `OffsetPolyomino.lean`): `Fat` + `Fat.mono` + rectangle
sanity check; `offsetCore` with unconditional `VertexOnGrid 3 2`,
`LTileable_offsetCore`, `6 ∣ ncard`; corridor area/disjointness/
nonemptiness; assembly `LTileable_of_fat` from the one `sorry`
`exists_corridorChain`.

Plan for `exists_corridorChain`:

- §A maximal edges & the vertex successor function (local consequences of
  `Fat 16`);
- §B single cycle via the parity argument (§5.2);
- §C the rectangles by explicit formula from consecutive vertices
  (`uᵢ₋₁, uᵢ, uᵢ₊₁` + snap), with: sides ≥ 6, ⊆ corridor, pairwise
  disjoint, cover, consecutive `PushAdj`;
- §D listing the cycle as a `List ChainLink` (cut open), `IsCornerChain`.
