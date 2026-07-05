# LOG.md — running project log

(Started 2026-07-04, when `AGENTS.md` was adopted; earlier history is in git.)

## Session log

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
