# LOG.md — running project log

(Started 2026-07-04, when `AGENTS.md` was adopted; earlier history is in git.)

## Session log

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
