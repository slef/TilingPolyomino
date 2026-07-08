# LOG.md — running project log

(Started 2026-07-04, when `AGENTS.md` was adopted; earlier history is in git.)

## Session log

- **2026-07-08/09 (Offset polyomino — THEOREM COMPLETE, zero sorries).**
  `LTileable_of_fat` — a finite, connected, simply connected, 16-fat
  polyomino with `3 ∣ area` is L-tileable — is fully proved; whole
  project builds green with zero sorries; standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`).
  The last three lemmas were proved by **three parallel subagents**,
  each in its own scratch file against the built oleans, then spliced
  back into `OffsetPolyomino.lean` (final size ~4960 lines):
  - `edgePiece_subset_corridor` (315 lines, first try): bands in-span;
    reflex-end extension via the endpoint's quadrant (the surviving
    corner is exactly the forward-cut reflex corner); poke witness for
    non-membership in the core.  Finding: the predecessor hypothesis is
    unused — start-side trims only shrink within the span.
  - `corridor_covered` (662 lines): witness cell in the safety box,
    first-flip L-path chase, oriented governing edges, snap-criterion
    lemmas (box-poke bounds ⟺ strict strip bounds), strip lemmas with
    convex-trim → predecessor-rectangle handoff, and the four reflex
    corner-block cases.  Finding: a span-miss endpoint is *always*
    reflex (a convex quadrant would exclude the cell from `P`), so the
    classification has no convex branch.  Predecessor existence in five
    lines: injective successor on a finite type is surjective.
  - `edgePiece_disjoint` (565 lines): sep16 (vertex-isolation
    packaging), per-direction windows, ten clash lemmas (same-axis via
    endpoint_of_vertex*/perp/bands; facing via in-band vs run — the N/S
    facing case needs the mod-3 divisibility of the snaps; perpendicular
    via run/band clashes, out-band corner cells, and shared-corner
    identification through pred_unique).  Finding: the successor
    hypotheses h3/h3' are unused — all corner cases resolve through
    predecessors.
  Agent-ops lessons (recorded in memory): two agents died emitting one
  giant Write (64k output cap) — every brief must mandate
  skeleton-with-sorries-then-small-fills; a transcript poisoned by a
  failed giant write is not worth resuming — restart fresh; scratch
  files against built oleans give conflict-free parallelism, but
  integration must wait until no agent still imports the library.
  Remaining (future work): the `LTileable ⇒ 3 ∣ area` converse
  (routine), holes, abstract-layer exposure (Phase 5), and splitting the
  file into per-topic modules per SL's granularity directive.

- **2026-07-08 (methodology note, SL).**  While three parallel agents
  work on the last three corridor lemmas: the bottleneck is that each
  agent must first digest the ~3400-line `OffsetPolyomino.lean` before
  contributing.  Directive for future proofs: decompose into smaller,
  self-contained chunks (many minimal-hypothesis leaf lemmas, smaller
  per-topic files, briefs listing only the few needed API signatures) so
  individual agents can work with far less background.  What worked
  well: one lemma ≈ one agent ≈ one scratch file compiled against the
  built oleans — zero build contention, zero file conflicts.

- **2026-07-09 (Offset polyomino — the CHAIN IS ASSEMBLED).**  Build
  green; the single `exists_corridorChain` sorry is now replaced by
  three *focused* geometric sorries, everything else proved:
  `exists_corridorChain` is fully assembled from (i) a vertex found at
  the max-abscissa cell, (ii) the successor as a choice function on the
  finite vertex subtype, injective by `pred_unique`, hence periodic
  (pigeonhole + iterate cancellation), with `k := Nat.find` the least
  period; (iii) the orbit `orb i := (f^[i] v₀).1` with `horb`
  (consecutive edges), `hperiod`, `horbpred` (wrap-around predecessor),
  `horbinj` (Nodup below `k`); (iv) totality via `vertex_mem_of_closed`
  applied to `S = {orb i | i < k}` (closures by unique/pred_unique and
  index wrap); (v) the link list `(range k).map (fun i => ⟨edgePiece
  (orb (i+k-1)) (orb i) (orb (i+1)) (orb (i+2)), eEntry …, eExit …⟩)`:
  nonempty (k > 0), chain via `List.isChain_iff_getElem` +
  `edgePiece_pushAdj` (after index-arithmetic rewrites and one
  `hperiod` fold), pairwise disjointness via `List.pairwise_lt_range`
  + `edgePiece_disjoint`, covers by antisymmetry
  (`edgePiece_subset_corridor` one way; `corridor_covered` + the orbit
  identifications `hw'`/`hz'`/`hp'` the other), `entry_ne_exit` via
  `eEntry_ne_eExit`.  REMAINING (the last mathematics): the three
  sorried lemmas `edgePiece_subset_corridor` (bands + snap arithmetic),
  `edgePiece_disjoint`, `corridor_covered` (strip/corner-block
  classification).

- **2026-07-08 night (Offset polyomino — rectangles and their chain
  adjacency PROVED).**  All green, one `sorry`.  New in
  `OffsetPolyomino.lean` (~700 lines; now imports `EulerTour`):
  (1) `Fat.vertex_isolated` — no second vertex inside a vertex's box
  (same-side-of-quadrant trick, casing only on which coordinate
  differs).  (2) `NextVtx.perp` — consecutive edges are perpendicular
  (16-case grid: same-axis pairs violate a clause of `IsVertex` at the
  shared vertex or clash on a cell).  (3) Snap functions
  `snapE/W/N/S` (nearest grid line at distance ≥ 6, specs by omega).
  (4) The **corridor rectangle** of an edge: coordinate functions
  `eX0/eX1/eY0/eY1 p u w z` implementing SL's forward-cut rule (convex
  start trims to the incoming offset line, reflex end absorbs the corner
  block to the outgoing offset line; convexity = left turn, read off the
  neighbour coordinates), `eEntry`/`eExit` corner tables,
  `eEntry_ne_eExit` (unconditional, `split_ifs <;> decide`), the total
  `edgePiece : RectPiece` (via `max`-clamping; collapsed by
  `edgePiece_x1/y1` under `eBounds`, which gets all four side bounds by
  `split_ifs <;> omega` from `NextVtx.far` + snap specs).
  (5) **`edgePiece_pushAdj`** — consecutive rectangles meet at a pushing
  corner: the 8 real (direction × turn) combos each verified by
  computing both rectangles' corner coordinates (deterministic `if_pos`/
  `if_neg` chains) + `CellAdj` by omega; the 8 same-axis combos die by
  `NextVtx.perp`.  Exit/entry tables: E cvx TR/rfl BR, N cvx TL/rfl TR,
  W cvx BL/rfl TL, S cvx BR/rfl BL (exits); entries are the matching
  partners.  Lesson: keep the per-combo simp lists uniform and disable
  `linter.unusedSimpArgs` locally.
  Remaining for `exists_corridorChain`: (a) the cyclic orbit list
  (iterate the successor on the finite vertex subtype, minimal period,
  `vertex_mem_of_closed` for totality); (b) `edgePiece ⊆ corridor`
  (bands + snap arithmetic); (c) cover + pairwise disjointness (the
  strip/corner-block classification); (d) assembly.

- **2026-07-08 later (Offset polyomino — §C locality layer PROVED).**
  All green, still one `sorry`.  New in `OffsetPolyomino.lean` (~600
  lines): (1) `Fat.column_no_dip/_no_bump`, `Fat.row_no_dip/_no_bump` —
  inside a vertex's box, membership along a fixed column/row changes at
  most once (∈,∉,∈ and ∉,∈,∉ impossible; 8 quadrant cases, omega);
  these four small lemmas turn out to carry ALL the remaining fatness
  geometry.  (2) `NextVtx.far` — every edge has length ≥ 16: a turn
  inside the box is impossible because both cell columns beside it lie
  on the same side of the quadrant (uniform over the 8 cases — no
  quadrant enumeration).  (3) Oriented governing edges
  `govern_H_above/below`, `govern_V_left/right` (edge + run + both
  endpoint coordinates).  (4) The eight **band lemmas**:
  `band_in_east/west/north/south` (the 15 cells on the interior side of
  every edge cell are in `P`) and `band_out_*` (the 15 exterior cells
  are out).  Proof pattern: least offending depth k′, the offending
  boundary segment's governing edge runs parallel; comparing run ends,
  either the edge's own vertex or the offending edge's vertex sees an
  impossible column/row dip/bump.  Plan for the corridor decomposition
  (worked out, recorded in memory): corridor = per-edge snap strips ∪
  reflex corner blocks; strip membership ⟺ box-poke criterion is
  *arithmetic* (corner-distance < 6 to the edge line), `∉ core` follows
  from `band_out`, `⊆ P` from `band_in`; the cover direction chases the
  first membership flip along an in-box L-path (poke criterion is then
  automatic since the flip lies inside the box); if the flip's edge span
  misses the cell's projection, the edge's endpoint vertex is within
  (8,7) and its quadrant classifies the cell into an arm strip or a
  reflex corner block (8 cases).  Next: snap functions, strip/corner
  rectangle definitions, the classification lemma, then §D chain
  assembly.

- **2026-07-08 (Offset polyomino — §B PROVED: the boundary is one
  cycle).**  All green, still exactly one `sorry`
  (`exists_corridorChain`).  New §7 of `OffsetPolyomino.lean` (~700
  lines): `curveV`/`curveH` (segments of the edges `(u, next u)` for `u`
  in a vertex family `S`; the interval conditions void themselves on the
  wrong orientation, so no direction guards needed), curve ⊆ boundary,
  `govern_V`/`govern_H` (every boundary segment lies on a walk edge —
  paired forward/reverse walks), `endpoint_of_vertexV/H` (edge interiors
  carry no vertex, so a vertex on an edge span is an endpoint),
  `vertex_mem_S_of_curveV/H`, **`curve_local`** (at any grid point the
  curve of a succ+pred-closed family is absent or agrees with the whole
  boundary — vertex case via governing edges + closure, non-vertex case
  via the straight run through the point), `curve_degree` (even degree,
  inherited from the free boundary identity), `par_const_of_path`
  (parity invariant on `P`-paths and `Pᶜ`-paths), **`curve_covers`**
  (parity: flip across one curve segment vs. no flip across an uncovered
  boundary segment + the two connectivities ⇒ the curve covers the whole
  boundary) and **`vertex_mem_of_closed`** — a nonempty succ+pred-closed
  vertex family of a connected, simply connected, 16-fat polyomino
  contains every vertex: the single-cycle theorem, no Jordan machinery.
  Note: `curve_local`/`curve_degree` need no fatness at all — only the
  walk-edge structure; `Fat 16` enters solely through
  `exists_nextVtx` in `curve_covers`.
  Next (§C): edge length ≥ 16 (`NextVtx.far`), the local description of
  `offsetCore` along an edge (snapped band), the per-edge corridor
  rectangle (SL's forward-cut formula), cover/disjointness/PushAdj; then
  (§D) the orbit as a cyclic list → `IsCornerChain`.

- **2026-07-07 night (Offset polyomino — §A completed, parity toolkit
  PROVED).**  All green, still exactly one `sorry`
  (`exists_corridorChain`).  New in `OffsetPolyomino.lean`:
  (1) `NextVtx.pred_unique` — injectivity of the successor (16-case
  mirror of `unique`); (2) `vertexSet_finite`; (3) walk lemmas
  **refactored** to single-cell hypotheses (`∃` first turn from one
  boundary cell — the 16-run version was only needed for the now-dropped
  length bound, to be recovered later as `NextVtx.far` from the box);
  `exists_nextVtx` simplified accordingly; (4) the four **reverse-end**
  walk lemmas (`walk_west'`, `walk_east'`, `walk_south'`, `walk_north'`)
  — both ends of every oriented run, for the governing-edge construction;
  (5) boundary segments `bndV`/`bndH` + finiteness + `bnd_degree` (the
  even-degree identity of the full boundary — a free mod-2 tautology of
  the 2×2 pattern, `tauto`); (6) §6 **ray-crossing parity toolkit**,
  fully abstract in curve data `V H : Set (ℤ × ℤ)`: `rayCross`,
  windowed counts `raySeg` with insert/step lemmas,
  `even_rayCross_add_right` (parity flips across a vertical curve
  segment) and `even_rayCross_add_up` (flips across a horizontal one,
  by telescoping the even-degree identity along the row with
  `Int.le_induction`).  Lesson: `tauto` must not see `Even (….ncard)`
  hypotheses (it destructures the `∃` and whnf-unfolds `ncard` →
  deterministic timeout); rewrite the goal down to small propositional
  atoms first and `clear` the heavy hypotheses.
  Next: governing edge of a boundary segment (existence via the paired
  walk lemmas, uniqueness), curve of a successor-closed vertex set,
  locally-closed ⇒ even degree, single-cycle theorem.

- **2026-07-07 evening (Offset polyomino — §A boundary walk PROVED).**
  New §5 of `OffsetPolyomino.lean` (~450 lines, all green, no new
  sorries): straight-run predicates (`HRunAbove/Below`, `VRunLeft/Right`,
  named by interior side), `NextVtx P u w` (successor vertex on the
  interior-on-the-left walk; 4-direction disjunction), `Fat.mem_iff`
  (pointwise quadrant form), `Fat.not_diagonal`, the four
  no-vertex-inside-a-run lemmas, the four walk lemmas (least/greatest
  turn point via `Int.exists_least/greatest_of_bdd`, first turn is a
  vertex), `exists_nextVtx` (8 quadrant cases → outgoing direction:
  convex BL→E, BR→N, TL→S, TR→W; reflex BL→N, BR→W, TL→E, TR→S) and
  `NextVtx.unique` (16-case grid; same-direction via first-turn
  uniqueness, E/W and N/S clashes via `Fat.not_diagonal`, the rest by
  first-step cell contradictions).  Lessons: avoid `(xf+1)-1` defeq traps
  (rewrite with `show … from by ring` first); keep `u w : Cell`
  undestructured so `omega` sees `u.1`-atoms consistently.
  Next: successor injectivity / predecessor, orbit machinery, then the
  ray-crossing parity single-cycle lemma (§B).

- **2026-07-07 later (Offset polyomino — checkpoint answers, Fat
  reworked).**  SL's decisions: (1) no holes for now (`CellConnected Pᶜ`
  stays); (2) diagonal vertices excluded — ok; (3) the constant is **16**
  (= 2·8: thickness 6 + snap 2, doubled so offset edges never cross;
  touching is fine since the 3×2-grid result tolerates a degenerate or
  disconnected `offsetCore`); (4) simpler corridor decomposition than my
  strips+blocks: ONE rectangle per boundary edge, with forward cuts at
  each vertex (convex: from the offset vertex `vᵢ` out to `∂P` at `v'ᵢ`;
  reflex: from `uᵢ` to the offset boundary at `u'ᵢ`) — cut endpoints are
  the chain corners; worst rectangle (6–8) × (≥ 16−8 = 8).  `Fat`
  redefined readably per SL: at every vertex, `P ∩ box v l` equals
  `quadrant v c ∩ box v l` or its complement's (∃ c : Corner) — diagonal
  exclusion now automatic; `Fat.mono` and the rectangle example redone;
  constants 24→16.  Single-cycle plan: local successor from fatness +
  ray-crossing parity invariant on `P` and `Pᶜ` (no Jordan machinery).
  Build green, still exactly one `sorry` (`exists_corridorChain`).
  Argument doc rewritten accordingly.

- **2026-07-07 (Offset polyomino — true fatness, Phase 1–3 skeleton).**
  New target (SL, verbal sketch + whiteboard drawing): a *fat* polyomino
  (every vertex at `L∞`-distance ≥ λ from every non-incident edge — a
  local condition) with `3 ∣ area` is L-tileable, by offsetting every
  edge inwards by ≥ 6 snapped onto the 3×2 grid, tiling the offset by
  `LTileable_of_vertexOnGrid3x2`, and tiling the 6–8-thick corridor by a
  corner chain along the boundary cycle. Argument written down in
  `docs/offset-polyomino-argument.md`; skeleton in new
  `TilingPolyomino/OffsetPolyomino.lean` — everything proved except the
  geometric core `exists_corridorChain` (one `sorry`). Proved now:
  `Fat` (local clean-corner formalization) + monotonicity + rectangle
  sanity check; `offsetCore` (per-grid-cell erosion by an inflated-box
  test) with `VertexOnGrid 3 2 (offsetCore P)` *unconditionally*, hence
  `LTileable_offsetCore`; `6 ∣ |offsetCore P|`; corridor area/disjointness/
  nonemptiness; assembly `LTileable_of_fat`. De-privatized
  `mem_gridCell_cornerOf` / `cornerOf_of_mem_gridCell` in
  `AlignedPolyomino.lean` for reuse. Build green (one intended `sorry`).
  **Stop-and-ask issues surfaced** (details in the doc, §6): (1) holes
  break the sketch — inner-annulus area ≡ −|hole| (mod 6) can't be fixed
  by snapping and defects can't cross the offset region, so the skeleton
  assumes simple connectivity (`CellConnected Pᶜ`); (2) diagonal
  (pinch) vertices must be excluded by the fatness definition (two
  rectangles joined at a corner give a fat non-tileable configuration);
  (3) constant accounting says λ ≈ 22, skeleton uses `Fat 24`
  provisionally (SL had guessed λ > 8); (4) proposed 4-stage plan for
  the corridor machinery (≈ VerticalDecomposition + EulerTour in size).

- **2026-07-06 (Euler tour — the fat-polyomino main lemma is PROVED).**
  New file `TilingPolyomino/EulerTour.lean` (~1500 lines) completes
  `exists_cornerChain`; the whole project now builds with **zero `sorry`
  and zero warnings**, and `LTileable_of_vertexAligned` (a finite
  connected 20-aligned polyomino with `3 ∣ area` is L-tileable) is
  verified with standard axioms only. Design decisions (approved /
  delegated by SL):
  - **Uniform split rule**: every piece with ≥ 1 door is split at its
    vertical midline (SL simplified my "≥ 2 doors" correction further);
    the sub-piece cycle (west column up, east column down) makes any
    entry point work, so the root is arbitrary — no re-rooting.
  - **No separator cuts**: the only horizontal cuts are door midpoints;
    the sub-piece between two consecutive same-side midpoints serves as
    landing area of one door and take-off area of the next. Same-side
    door midpoints are ≥ 40 apart, door halves ≥ 10, so all sub-pieces
    have sides ≥ 10 ≥ 6.
  - Crossings: west→east through the pieces with *bottom* edges at the
    midpoint (config `(BR,BL)`), east→west through those with *top*
    edges there (`(TL,TR)`); turns `(TR,TL)`/`(BL,BR)` — the four
    `PushAdj` lemmas are one-line `omega` proofs.
  Structure: `WestTour`/`EastTour` (spliceable-chain interfaces with
  head/last corner data), `SegUp`/`SegDown` column folds over sorted
  door-event lists (bespoke insertion-sort existence lemma; separations
  from run-disjointness of same-strip pieces), and one big induction on
  the tree producing West/East/root chains simultaneously; the root
  chain breaks the cycle at the top turn. `exists_cornerChain` and the
  main lemma moved from `FatPolyomino.lean` (which is now sorry-free) to
  `EulerTour.lean`, since they need the whole stack. Remaining for the
  full fat-polyomino theorem: replace `VertexAligned` by true fatness,
  and the converse direction (both recorded in FUTURE_PLANS/earlier
  notes).

- **2026-07-05 (Fat polyominoes — vertical decomposition, steps 1–2).**
  SL sketched the `exists_cornerChain` proof (vertical decomposition →
  door graph + spanning tree rooted at a leaf → subdivide slabs at door
  midpoints → clockwise Euler tour with door-midpoint entry/exit corners).
  New file `TilingPolyomino/VerticalDecomposition.lean`, **no `sorry`**:
  - Boundary-walk lemmas (`isCutLine_of_horiz_discont`,
    `exists_vertex_row_of_vert_discont`): a membership discontinuity
    between adjacent cells yields a vertex on the line/row between them —
    walk along the boundary edge to its first end (an
    `Int.exists_least_of_bdd` extraction; finiteness bounds the walk);
    at the end the two "constant-pattern" conjuncts of `IsVertex` fail for
    complementary reasons, so the proof is 4 lines per conjunct.
  - `Slab`, `Slab.IsSlabOf` (strip between consecutive cut lines × maximal
    vertical run): pairwise disjoint (`eq_of_mem`), cover
    (`exists_slab_mem` — run/strip extraction plus column propagation
    `mem_iff_of_no_cut`), aligned coordinates (`IsSlabOf.aligned`) and
    sides ≥ f (`side_ge`).
  - Doors (`DoorBetween`, `Slab.Adj`) and **connectivity of the door
    graph** (`slab_reachable`): follow a cell path, slab changes happen
    only through doors (`eq_or_adj_of_cellAdj`; vertical neighbours share
    their run, so all slab transitions are horizontal).
  Remaining for `exists_cornerChain`: the tree/tour layer (spanning tree
  rooted at a leaf, slab subdivision, clockwise Euler tour). Design
  question for SL recorded in the session summary: custom rooted-tree
  inductive vs Mathlib `SimpleGraph` spanning trees.

- **2026-07-05 (Vertical decomposition — reframed per SL, tree layer set
  up).** SL's review: the deliverable is a decomposition of `P` into
  disjoint rectangles (`RectPiece`-compatible), stated as such — the
  `Slab` naming had suggested full strips. The definition was already
  per-component (strip × maximal run); renamed `Slab` → `VPiece`,
  `IsSlabOf` → `VPiece.IsPieceOf`, and added the explicit packaging:
  `vDecomp P` (the set of pieces), `vDecomp_isDecomposition` (rectangles
  ⊆ `P`, pairwise disjoint, union = `P`), `vDecomp_finite` (inject a
  piece into its bottom-left cell), and `VPiece.toRectPiece` (for
  20-aligned `P`; sides ≥ 20 ≥ 6). Spanning-tree layer per SL's
  delegation ("whatever works best"): custom rose tree `PieceTree`
  (mutual `pieces`/`piecesList`, `WF`/`WFChildren` — the nested-inductive
  mutual pattern), `IsSpanningTree` (well-formed, nodup, complete);
  `exists_spanning_pieceTree` was the file's one `sorry`, closed the same
  day (see next entry). Whole project green.

- **2026-07-05 (Spanning tree proved — VerticalDecomposition sorry-free).**
  SL asked whether the direct construction beats invoking Mathlib's
  `SimpleGraph.Connected.exists_isTree_le`; answer: yes, because the tour
  needs a *rooted rose tree with a recursion principle*, and extracting
  that from an abstract `IsTree` costs the same induction again through a
  heavier API. Direct proof, ~200 lines, no `sorry`:
  - `ReachIn S` (door-reachability within a piece set) with `mem`/`symm`/
    `component` lemmas — `reachIn_component` upgrades a path in `S` to a
    path *within* the component of its start;
  - `exists_attach`: stop a door path one step before `r` (head induction);
  - `exists_children_aux`: inner induction — peel off the component of an
    arbitrary uncovered piece, build its subtree via the outer IH rooted
    at the attach point, recurse on the rest (closure under reachability
    is the maintained invariant);
  - `exists_rooted_tree_aux`: outer induction on `≤ n` (plain `Nat`
    induction on an upper bound, avoiding strong-induction eliminators);
  - `exists_spanning_pieceTree` assembles them on `vDecomp P`.
  Both `FatPolyomino` sub-goals delegated so far are done; the single
  remaining `sorry` in the project is `exists_cornerChain`, whose missing
  ingredient is now only the subdivision + Euler tour layer (step 4 of the
  plan).

- **2026-07-05 (Fat polyominoes — tiling half proved).** Per SL's review of
  the skeleton: `isVertex_rect_iff` demoted to an `example`; infinite-`P`
  conjecture recorded in `FUTURE_PLANS.md`. Then closed three of the four
  `sorry`s, leaf-first, build green after each:
  (1) `RectPiece.tileable_optDefects` — translation to the origin plus the
  existing rectangle/one-corner/two-corner theorems; needed the `cells_*`
  helper lemmas of `TwoCornerDefects.lean` de-privatized (renamed into the
  `Corner` namespace: `Corner.cells_finite/ncard/subset_rect/disjoint`).
  (2) `exists_pushTromino` — statement change surfaced: dropped the
  `Disjoint R.cells S.cells` hypothesis (a `PushAdj` configuration forces
  the pieces onto opposite sides of the contact line, so it was redundant).
  Proof: 4 core geometric configurations (`BR–BL`, `TR–TL`, `TL–BL`,
  `TR–BR`) × 2 export sizes with explicit trominoes (each set fact by
  `simp only` + `omega`), the 4 mirrored configurations by swapping `R`/`S`
  (`s ↔ 3 − s`), the 8 impossible corner pairs killed by `omega`. A case
  enumeration, but each case is 3 one-line-ish goals; a symmetry-machinery
  reduction to 2 configurations was considered and rejected as no shorter.
  (3) `chainCells_tileable` — induction along the chain: if the head's
  residue mod 3 is 0, tile it and recurse defect-free; otherwise get the
  straddling tromino from (2), tile the head minus both defects via (1),
  and recurse with the inherited defect. Set bookkeeping via
  `Set.ncard_diff`/`ncard_union_eq` and a final `omega` per area goal.
  Remaining `sorry`: only `exists_cornerChain` (the geometric decomposition,
  steps 1–4 of the sketch) — deferred per SL, to be worked jointly.
  Whole project builds green.

- **2026-07-05 (Fat polyominoes — Phases 1–3 skeleton).** New target theorem
  (SL): every fat connected polyomino with area ≡ 0 (mod 3) is L-tileable;
  first lemma uses the *vertex-aligned* weakening (all vertex coordinates
  multiples of 20). Created `TilingPolyomino/FatPolyomino.lean` with:
  polyomino notions (`CellAdj`, `CellConnected`, `IsVertex`,
  `VertexAligned`); the corner-chain interface between the geometric
  decomposition and the tiling argument (`RectPiece` — sides ≥ 6 —,
  `PushAdj`, `ChainLink`, `IsCornerChain`); four `sorry`ed skeleton lemmas
  (`exists_cornerChain` = vertical decomposition + spanning tree + Euler
  tour; `exists_pushTromino` = one defect push; `RectPiece.tileable_optDefects`
  = one piece via the existing rectangle/one-corner/two-corner theorems;
  `chainCells_tileable` = induction along the chain); and the main lemma
  `LTileable_of_vertexAligned` proved from these (no `sorry` in the glue).
  `IsVertex` defined as "membership pattern around the grid point constant
  neither row- nor column-wise"; sanity lemma `isVertex_rect_iff` (vertices
  of a rectangle = its 4 corners) proved by `omega`. Awaiting SL's review of
  the definitions and lemma statements (Checkpoints 1–3 for this theorem).

- **2026-07-05 (AGENTS.md policy update — layout & attribution).** Per SL's
  revised `AGENTS.md`: moved the abstract layer into the library folder
  (`TilingPolyomino/Abstract.lean`, `TilingPolyomino/AbstractBridge.lean`,
  imported as `TilingPolyomino.Abstract`/`.AbstractBridge`). The root
  `TilingPolyomino.lean` does not import them; the lakefile lists
  `TilingPolyomino.Abstract` as an extra `roots` entry of the library so the
  default `lake build` still enforces the sorry-free contract. Added the
  newly required "Sources and attribution" section to `Abstract.lean`
  (Ash–Golomb 2004; two-corner theorem: MIT-ULB CompGeom Group, 2026).
  Open question for SL: precise source locations (theorem numbers/pages) for
  the rectangle, dog-eared, and corner-domino theorems in Ash–Golomb, and
  whether the rectangle characterization should carry an earlier citation.

- **2026-07-05 (Phase 5 — final polish).** Per SL: hypotheses of the
  two-corner theorem restyled `n ≥ 6` (matching the other theorems), and the
  exposed bridge statement `LTileable_iff_tileable` dropped from
  `Abstract.lean` — the abstract layer is now fully self-contained (only
  elementary vocabulary appears in its definitions and statements); the
  layer-equivalence lemma survives as `AbstractBridge.tileable_iff`.

- **2026-07-05 (Phase 5 — Checkpoint 5 revisions).** Per SL's review:
  (1) dog-ear and corner-domino defects moved from the top-right corner to
  `(0,0)` / `{(0,0),(1,0)}` — bridged via a 180°-rotation lemma built on the
  existing `LTileable_reflectX`/`LTileable_reflectY`; (2) the corner-domino
  theorem upgraded from mod-3 hypothesis to a full iff (`↔ 3 ∣ n·m − 2`) —
  necessity via `LTileable_rectMinusTwoCorners_area` applied to the
  degenerate `rectMinusTwoCorners n m TR TR horiz horiz` plus a direct
  `ncard` computation; (3) file split for reading flow: `Abstract.lean` is
  now definitions + statements only, each proved by one-line delegation to
  `AbstractBridge.lean`, which restates the elementary definitions verbatim
  and holds all machinery — the delegation type-checks by definitional
  equality, so any drift between the copies fails to compile. Whole project
  builds green; all four headline theorems re-verified (standard axioms only).
- **2026-07-04 (Phase 5 — Abstract layer).** Created `Abstract.lean` at the
  project root: elementary definitions (`IsLTromino`, `LTileable`,
  `rectangle`, `IsCornerDefect`), four headline theorems, and sorry-free
  bridges to the general layer. Added an `Abstract` lean_lib to
  `lakefile.toml`. File compiles with zero errors/warnings; all four headline
  theorems verified via `#print axioms` (only `propext`, `Classical.choice`,
  `Quot.sound`). Awaiting Checkpoint 5 review of the theorem selection.

## Definition choices (abstract layer)

- **`Abstract.IsLTromino`**: explicit disjunction of the four translated
  rotations of `{(0,0),(0,1),(1,0)}` (equivalently, a 2×2 square minus one
  cell). Chosen over reusing `LProtoset`/`PlacedTile` so that the reader
  needs no placed-tile machinery. Reflections are not listed: the L-tromino's
  reflections coincide with its rotations.
- **`Abstract.LTileable`**: `∃ k (t : Fin k → Set (ℤ × ℤ))`, all tiles
  L-trominoes, pairwise disjoint, union = R. Chosen over a
  `Finset (Finset Cell)` partition as the quantifier structure is closest to
  "finitely many pairwise disjoint tiles" and bridges cleanly to the
  general `Tileable` (arbitrary `Fintype` index).
- **`Abstract.rectangle`**: set-builder `[0,n) × [0,m)`; definitionally equal
  to the general layer's `rect 0 0 n m` (bridge is `rfl`).
- **`Abstract.IsCornerDefect`**: a flat 12-case disjunction (4 corners × 3
  defect shapes) with explicit cell sets, anchored at the corner *cell*
  `p : ℤ × ℤ` rather than an inductive `Corner` type. Chosen so the abstract
  layer introduces no new inductive types; the sets mirror `Corner.cells`
  literally, so the bridge is a 12-way `rfl` enumeration. Distinctness of
  corners is expressed as `p₁ ≠ p₂`.
- **Two-corner theorem RHS**: `3 ∣ (rectangle n m \ (D₁ ∪ D₂)).ncard`
  ("number of cells divisible by 3"), matching the general statement.
  Alternative considered: `3 ∣ (n*m − |D₁| − |D₂|)`; rejected to keep the
  bridge trivial, and `Set.ncard` is standard. Approved by SL at
  Checkpoint 5.
- **Defect placement (Checkpoint 5)**: single-corner defects stated at the
  *bottom-left* corner (`(0,0)`, `{(0,0),(1,0)}`) per SL — pleasanter to
  read than `(n−1, m−1)`. General layer keeps top-right; bridged by 180°
  rotation.
- **All three defect theorems as iffs** of the form `tileable ↔ 3 ∣ area`
  (SL: symmetry of statements). This required adding the necessity
  direction for the corner-domino case, which the general layer had only as
  a sufficiency statement.
- **Two-file structure (Checkpoint 5)**: `Abstract.lean` = definitions +
  statements only (reader never meets proof machinery mid-file);
  `AbstractBridge.lean` = verbatim copies of the definitions + all proofs.
  Delegation `:= AbstractBridge.foo ...` type-checks by definitional
  equality — Lean itself guarantees the copies agree.

## Bridge notes

- `LTileable_iff_tileable` (elementary ↔ general tileability): ~80 lines
  total including the two placed-tile lemmas. The only real content is the
  4-case computation that a placed tile's cell set is one of the four
  explicit L-shapes and conversely (each case: `ext` + `simp only` + `omega`).
  Index-type conversion uses `Fintype.equivFin`. No surprises.
- The four headline bridges are each ≤ 8 lines: rewrite by the bridge
  theorem, `rfl`-convert `rectangle` to `rect`, translate `∣`/`% 3` with
  `omega`, and apply the general theorem. The layers had drifted very little
  because the general layer already uses concrete `Set (ℤ × ℤ)` regions.

## Stuck points

- None in Phase 5. (One mechanical hiccup: module docstring must follow
  `import` in Lean 4.)

## Times

- Phase 5 (abstract layer + bridges): ~1 session, 2026-07-04.
