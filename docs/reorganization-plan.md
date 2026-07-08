# Module reorganization plan

Status: EXECUTED 2026-07-08 (v4 as approved by SL; `assert_not_exists`
guards dropped per SL). Commits: e2c66c3 (stage 0), 4bd9dfe (stage 1),
80bf629 (stage 2), 0351cc0 (stages 3–4). Build green, both main theorems
verified with standard axioms. Deviation from the letter of the plan:
stages 3 and 4 were executed as one commit; 14 lemmas (not 2) lost
`private`; Cover.lean kept the embedded module docstring of the original
scratch file as its header.

Revision history (all after SL review):

- v2: boundary-successor + single-cycle theory → `Polyomino/`; `Aligned/`
  renamed `Decomposition/`.
- v3: top file `FatPolyomino.lean` (not `Main.lean`); fatness as a concept
  directory `Polyomino/Fat/` with light `Defs.lean`.
- v4 (**the separability principle**, SL): `Polyomino/` contains ONLY
  tiling-free polyomino theory, so it can one day spin off (e.g. toward
  `Mathlib.Combinatorics.Polyomino`) without dragging tiling along.
  Consequences: the corridor/offset machinery moves OUT of `Polyomino/`
  into a tiling-side `Corridor/` folder (every constant in it — the
  6-inflation, the 3×2 snap grid, side ≥ 6 — is an L-tromino number: it is
  proof scaffolding, not polyomino theory); `Fat.lean` reverts to a plain
  file in `Polyomino/` (the v3 concept-dir dissolves, and with it the
  Defs-sandwich); the vertical decomposition + spanning tree turn out to be
  tiling-free and move INTO `Polyomino/Decomposition/` (only
  `VPiece.toRectPiece`, 12 lines, is extracted to the tiling side); stage 0
  (`Grid.lean`) is promoted from optional to REQUIRED.

## 0. The governing rule

> **`Polyomino/` imports nothing but `Grid.lean` and Mathlib.**

(No `assert_not_exists` guards — SL 2026-07-08: they'd be noise to strip if
the folder is ever extracted. The import discipline itself is the rule.)

Scope: `FatPolyomino.lean`, `VerticalDecomposition.lean`, `EulerTour.lean`,
`AlignedPolyomino.lean`, `OffsetPolyomino.lean`, plus stage 0 which extracts
`Grid.lean` from three substrate files (`Tiling.lean`,
`TwoCornerDefects.lean`, `RectOmega.lean` — deletion of moved definitions
only). The substrate is otherwise untouched.

## 1. Diagnosis

The five files form a **linear import chain** that does not reflect the
mathematics:

```
TwoCornerDefects → FatPolyomino → VerticalDecomposition → EulerTour → OffsetPolyomino
                        ↘ AlignedPolyomino ————————————————————————————↗
```

Verified by grep (2026-07-08): **`OffsetPolyomino.lean` uses *nothing* from
`EulerTour.lean` or `VerticalDecomposition.lean`** (zero occurrences of
`VPiece`, `PieceTree`, `doorMid`, `exists_cornerChain`, `vDecomp`,
`IsCutLine`; the one hit on `LTileable_of_vertexAligned` is a docstring).
The `import TilingPolyomino.EulerTour` on line 2 is dead weight: the fat
theorem needs only the corner-chain interface + defect pushing (currently in
`FatPolyomino.lean`) and `LTileable_of_vertexOnGrid3x2`
(`AlignedPolyomino.lean`).

Individual problems:

- **`OffsetPolyomino.lean` (4961 lines)** is a monolith with ~9 separable
  topics, and its section numbering even restarts (§1–§8 at the top, a second
  §1–§7 from line 4122 — the file was grown by appending).
- **`FatPolyomino.lean` is misnamed**: it contains no fatness. It holds
  (a) basic polyomino vocabulary, (b) the corner-chain interface, (c) the
  defect-pushing tiling engine.
- **Boundary/Jordan material is split across two files** (walk lemmas in
  `VerticalDecomposition.lean` §1; `bndV`/`bndH`, ray parity, single-cycle
  theorem in `OffsetPolyomino.lean` §5–§7).
- **Tiling-free and tiling-specific content is interleaved everywhere**
  (the v4 principle exists because of this): vertical decomposition
  (tiling-free) sits between two tiling layers; the fatness definition
  (tiling-free) sits inside the corridor proof file; `Cell` is defined in
  the legacy finset-tiling file, `Corner` in the defect file.
- **No top-level file** tells the story of the main theorem the way
  `docs/offset-polyomino-argument.md` does.
- `Basic.lean` is `def hello` scaffold junk.

## 2. Target module tree

All folders live inside the library dir `TilingPolyomino/` (Lake maps
`TilingPolyomino/Corridor/Chain.lean` to module
`TilingPolyomino.Corridor.Chain`); nothing new at the project root.
Every file one topic, target ≤ ~800 lines (SL 2026-07-08 directive:
one-lemma-one-agent needs small, low-context modules).

```
TilingPolyomino.lean                     -- root: imports everything (regenerated)
TilingPolyomino/
  -- stage 0 (REQUIRED): shared vocabulary, below everything
  Grid.lean                   -- Cell, Corner, rect + mem_rect, rect_finite
                              --   (extracted from Tiling.lean /
                              --    TwoCornerDefects.lean / RectOmega.lean)

  -- tiling substrate (otherwise UNCHANGED, flat)
  Mod3.lean  Tiling.lean  RectOmega.lean  TilingSet.lean
  LTrominoBase.lean  LTromino.lean  LTrominoSetBridge.lean
  TwoCornerDefects.lean
  Abstract.lean  AbstractBridge.lean

  -- ============================================================
  -- PURE POLYOMINO THEORY — imports only Grid.lean + Mathlib.
  -- The future spin-off candidate (→ Mathlib.Combinatorics.Polyomino).
  -- ============================================================
  Polyomino/Basic.lean        -- CellAdj, CellConnected, IsVertex, VertexAligned,
                              --   exists_bound            [FatPolyomino §1 + VD private]
  Polyomino/Fat.lean          -- quadrant, box, Fat, Fat.mono, Fat.mem_iff,
                              --   Fat.not_diagonal, column/row no_dip/no_bump,
                              --   vertex_isolated       [OP §1 + local lemmas of §5]
  Polyomino/Boundary.lean     -- IsCutLine, discontinuity ⇒ vertex walk lemmas
                              --   [VD §1]; bndV, bndH, bnd_degree  [OP 1329–1367]
  Polyomino/RayParity.lean    -- abstract rayCross parity toolkit    [OP §6, 1369–1572]
  Polyomino/NextVtx.lean      -- H/V runs, walk_* lemmas, exists_nextVtx,
                              --   NextVtx.unique/pred_unique/far/perp,
                              --   vertexSet_finite, exists_prevVtx  [OP §5]
  Polyomino/BoundaryCycle.lean-- curveV/H, govern_*, band_*, curve_local,
                              --   curve_degree, curve_covers,
                              --   vertex_mem_of_closed  [OP §7, 1572–2735]
                              --   (optionally split band_* + curve_local out
                              --    if > 900 lines)
  Polyomino/Decomposition/Vertical.lean
                              -- VPiece, IsPieceOf, cover, alignment, doors,
                              --   vPiece_reachable, vDecomp [VD §2–§6,
                              --   MINUS VPiece.toRectPiece → EulerTour.lean]
  Polyomino/Decomposition/SpanningTree.lean
                              -- PieceTree, exists_spanning_pieceTree [VD §7]

  -- NOTE on NextVtx/BoundaryCycle: statements currently assume `Fat 16`,
  -- and *some* hypothesis is unavoidable (at a diagonal pinch vertex the
  -- boundary has degree 4, so "next vertex" is not a function). If later
  -- weakened (e.g. to "no diagonal vertex"), statements change in place,
  -- no file moves.

  -- ============================================================
  -- THE TILING MODULE — this project's actual subject.
  -- ============================================================
  CornerChain/Defs.lean       -- optSize, RectPiece + defect API, PushAdj,
                              --   ChainLink, chainCells, IsCornerChain [FatPolyomino §3]
  CornerChain/Tiling.lean     -- exists_pushTromino (4 core configs),
                              --   RectPiece.tileable_optDefects, chainCells_tileable,
                              --   IsCornerChain.tileable              [FatPolyomino §4]

  AlignedPolyomino.lean       -- VertexOnGrid, cornerOf, gridCell,
                              --   LTileable_of_vertexOnGrid3x2 (unchanged;
                              --   imports drop to Polyomino/Basic + LTromino)

  -- the corridor: the offset/snap construction. Proof-specific by design —
  -- every constant (6-inflation, 3×2 snap grid, sides ≥ 6) is an
  -- L-tromino number.
  Corridor/OffsetCore.lean    -- offBox, offsetCore, corridor, 6 ∣ area,
                              --   LTileable_offsetCore, corridor area/nonempty
                              --   [OP §2–§4, 128–293]
  Corridor/EdgePiece.lean     -- snapE/W/N/S + specs + criteria, eX0…eY1,
                              --   eEntry/eExit, edgePiece, eBounds,
                              --   edgePiece_pushAdj, edgePiece_subset_corridor
                              --   [OP 2752–3546]
  Corridor/Disjoint.lean      -- sep16, window*, clash_* (10), edgePiece_disjoint
                              --   [OP 3546–4122]
  Corridor/Cover.lean         -- pred/succ arm directions, quad_*, strip_*,
                              --   block_*, corridor_covered  [OP 4122–4771]
  Corridor/Chain.lean         -- exists_corridorChain (orbit argument)
                              --   [OP 4771–4947]

  EulerTour.lean              -- VPiece.toRectPiece (glue, from VD §6) +
                              --   door midpoints, tour construction,
                              --   exists_cornerChain, LTileable_of_vertexAligned
                              --   [EulerTour.lean, unchanged content]

  FatPolyomino.lean           -- the literate main file: LTileable_of_fat +
                              --   narrative docstring mirroring
                              --   docs/offset-polyomino-argument.md
                              --   (file morphs: misnamed original → stage-1
                              --    re-export shim → literate file; never deleted)
```

Resulting import DAG (pure theory above the line, tiling below; the two
proof routes each consume polyomino theory and add tiling on top):

```
Grid.lean
   ├── Polyomino/Basic ──┬── Polyomino/Fat ── Polyomino/NextVtx ── Polyomino/BoundaryCycle
   │                     ├── Polyomino/Boundary ──┬────────────────────┘        │
   │                     │                        └── Polyomino/Decomposition/Vertical
   │                     └── Polyomino/RayParity ────────────────┘              │
   │                                            Polyomino/Decomposition/SpanningTree
   │  ···················· tiling line ····················
   ├── TwoCornerDefects ── CornerChain/Defs ── CornerChain/Tiling
   │                                                 │           \
   └── (substrate) ── LTromino ── AlignedPolyomino   │       EulerTour.lean
                              \                      │      (+ Decomposition/*)
                            Corridor/OffsetCore ─────┤
                              Corridor/EdgePiece (+ NextVtx, BoundaryCycle)
                              Corridor/{Disjoint,Cover}
                                Corridor/Chain
                                     │
                              FatPolyomino.lean
```

Approximate sizes after the split: everything ≤ ~800 lines except
`Polyomino/BoundaryCycle` (~1150 — split option noted) and `EulerTour.lean`
(~1520, kept whole: off the main line; split later if it ever gets touched).

## 3. `FatPolyomino.lean` — the literate top-level file

A short file that *reads like* `docs/offset-polyomino-argument.md`, calling
the big theorems proved elsewhere:

```lean
import TilingPolyomino.Corridor.Chain

/-!
# Fat polyominoes are L-tileable

... (module docstring = condensed §1–§5 of the argument doc, with links:
`Fat`, `offsetCore`, `corridor`, `exists_corridorChain`,
`IsCornerChain.tileable`, `LTileable_of_vertexOnGrid3x2`) ...
-/

/-- **Fat polyominoes are L-tileable.** -/
theorem LTileable_of_fat (P : Set Cell) (hfin : P.Finite)
    (hconn : CellConnected P) (hsimp : CellConnected Pᶜ)
    (hfat : Fat 16 P) (harea : 3 ∣ P.ncard) : LTileable P := by
  ...  -- the existing 10-line assembly, moved verbatim
```

Only the docstring needs writing; the proof already has the narrative shape.
Blueprint-project pattern (PFR, FLT): the statement file is named after the
result. Also the natural home for the future `LTileable_of_fat_iff`
(converse) and the abstract-layer exposure.

## 4. What moves where — exact mapping

| Current location | New home |
|---|---|
| Tiling.lean `Cell`/`Region` abbrevs; TwoCornerDefects `Corner` inductive; RectOmega `rect`+`mem_rect`(+`rect_finite`) | Grid (stage 0) |
| FatPolyomino §1 (CellAdj … VertexAligned) | Polyomino/Basic |
| FatPolyomino §3 (optSize, RectPiece, PushAdj, ChainLink, IsCornerChain) | CornerChain/Defs |
| FatPolyomino §4 (pushTromino_*, tileable_*, chainCells_tileable, IsCornerChain.tileable) | CornerChain/Tiling |
| VerticalDecomposition §1 (IsCutLine, walk lemmas; exists_bound → Basic) | Polyomino/Boundary |
| VerticalDecomposition §2–§6 minus toRectPiece | Polyomino/Decomposition/Vertical |
| VerticalDecomposition §6 `VPiece.toRectPiece` + `toRectPiece_cells` | EulerTour (glue) |
| VerticalDecomposition §7 (PieceTree, spanning tree) | Polyomino/Decomposition/SpanningTree |
| EulerTour (all) | EulerTour (unchanged content, new imports) |
| AlignedPolyomino (all) | unchanged (imports shrink) |
| OffsetPolyomino §1 + Fat.* local lemmas (339–357, 1042–1194) | Polyomino/Fat |
| OffsetPolyomino §2–§4 (128–293) | Corridor/OffsetCore |
| OffsetPolyomino §5 runs/walks/NextVtx (293–1329) | Polyomino/NextVtx |
| OffsetPolyomino bndV/bndH/bnd_degree (1329–1367) | Polyomino/Boundary |
| OffsetPolyomino §6 rayCross (1369–1572) | Polyomino/RayParity |
| OffsetPolyomino §7 curve/single-cycle (1572–2735) | Polyomino/BoundaryCycle |
| OffsetPolyomino §8 snap/edgePiece/pushAdj/subset (2735–3546) | Corridor/EdgePiece |
| OffsetPolyomino clash/disjoint (3546–4122) | Corridor/Disjoint |
| OffsetPolyomino 2nd §1–§7 cover machinery (4122–4771) | Corridor/Cover |
| OffsetPolyomino exists_corridorChain (4771–4947) | Corridor/Chain |
| OffsetPolyomino LTileable_of_fat (4950–4961) | FatPolyomino (literate) |
| Basic.lean (`def hello`) | delete |

No identifier renames, no proof changes, no namespace changes — pure moves,
so `git log -S` archaeology still works and the blueprint keeps its names.

Caveat found while auditing: `private` declarations used across a new file
boundary must lose `private` (`exists_bound` in VerticalDecomposition;
`exists_prevVtx` since Cover and NextVtx separate). Simplest: drop `private`.

## 5. Mathlib best practices, for reference

### Where this would live (SL question, 2026-07-08)

Not with polygons: Mathlib has almost no polygon theory (triangles in
`Geometry/Euclidean/`, convex polytopes in `Analysis/Convex/`), and a
polyomino is a subset of ℤ² — a discrete object, which Mathlib sorts under
`Combinatorics/`. Realistic mapping:

- `Polyomino/*` → a new `Mathlib/Combinatorics/Polyomino/` subtree.
  Tiling-free by construction after this reorganization (the v4 rule); the
  discrete Jordan-type single-cycle theorem would be a standalone
  contribution (Mathlib has no discrete Jordan curve theorem), and the
  vertical decomposition / door graph / spanning tree is likewise general
  partition theory.
- The tiling substrate would NOT be ported wholesale: Joseph Myers's
  `Mathlib/Combinatorics/Tiling/` framework (prototiles in a space with a
  group action) already generalizes our `Prototile`/`TileSet`; ours would be
  re-expressed as its ℤ²-translation instance.
- L-tromino results, corner chains, the corridor construction,
  `LTileable_of_fat` → application files under `Combinatorics/Tiling/`.

The v4 rule makes the repo's `Polyomino/` boundary exactly the boundary a
future extraction would cut along.

### Conventions

- **Directory per concept; light defs low, minimal imports** so distant
  files import cheaply. → `Grid.lean`, `CornerChain/Defs.lean`.
- **Namespacing by concept** (`Polyomino.Fat`, dot notation `hfat.mono`).
  → deferred: flat-namespace preserved; a separate pass.
- **Import minimality, enforced** (`lake exe shake`, linters). → adopted:
  each new file imports only what it uses.
- **Small files** (monsters get split in review; 4961 lines would not fly).
- **No `Main.lean`** — the literate statement file named after the result is
  a blueprint-project pattern (PFR, FLT).
- **Module docstrings mandatory**, doc-strings on public declarations,
  100-column lines. The per-file `-- §n` banners stay as local flavor.
- **Moves ship with compatibility shims** — mirrored by the stage-1
  re-export shim below.

## 6. Migration order (each step compiles: `lake build` green, then commit)

0. **Extract Grid.lean** (Cell, Corner, rect + mem_rect, rect_finite) from
   Tiling.lean / TwoCornerDefects.lean / RectOmega.lean; those three import
   it. The only stage that edits substrate files, and only to delete the
   moved definitions.
1. **Split FatPolyomino** → Polyomino/Basic + CornerChain/{Defs,Tiling};
   FatPolyomino.lean temporarily becomes a 3-line re-export so nothing
   downstream changes.
2. **Split VerticalDecomposition** → Polyomino/Boundary +
   Polyomino/Decomposition/{Vertical,SpanningTree} + toRectPiece glue moved
   into EulerTour.lean; update the importers.
3. **Split OffsetPolyomino bottom-up**: Corridor/OffsetCore, then
   Polyomino/Fat + Polyomino/NextVtx, then
   Polyomino/{RayParity,BoundaryCycle}, then
   Corridor/{EdgePiece,Disjoint,Cover,Chain}. At each cut, the remainder of
   OffsetPolyomino.lean imports the new file — the build stays green
   throughout; the file shrinks to nothing and is deleted.
4. **Repurpose the shim**: FatPolyomino.lean becomes the literate main file
   (docstring + LTileable_of_fat); delete Basic.lean; point remaining
   imports at the real homes; regenerate root TilingPolyomino.lean.
5. **Docs**: update docs/offset-polyomino-argument.md §6, LOG.md, and the
   blueprint file list.
6. Validate: `lake build`, `lean_verify LTileable_of_fat` (axioms unchanged:
   propext, Classical.choice, Quot.sound), `lean_verify
   LTileable_of_vertexAligned`.

Stages 0–2 and the sub-steps of 3 are independent enough to parallelize with
one agent per new file (per SL's parallel-agent directive), with a serial
integrator doing the import surgery.

## 7. Open choices (defaults chosen, easy to override)

- **Polyomino/BoundaryCycle split**: keep one ~1150-line file (default) or
  carve out `Polyomino/CurveLocal.lean` (band_* + curve_local, ~650 lines).
- **EulerTour.lean**: kept as one ~1520-line file (default — off the main
  line, untouched content); split only if it gets active development again.
- **Section-numbering style**: keep `-- §n` banners per file (default),
  renumbered from §1 in each new module.
- **`VertexOnGrid` def** (tiling-free, currently in AlignedPolyomino.lean):
  could move to Polyomino/Basic for purity; default: leave, it's 3 lines and
  moves trivially later.

Settled by SL: the v4 separability rule (`Polyomino/` = tiling-free only,
imports Grid + Mathlib only); corridor machinery is tiling-side
(`Corridor/`); vertical decomposition + spanning tree are polyomino theory
(`Polyomino/Decomposition/`); `Polyomino/Fat.lean` a plain file; top
literate file `FatPolyomino.lean`; old route's tiling part stays in
`EulerTour.lean`.
