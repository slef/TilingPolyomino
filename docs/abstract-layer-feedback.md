# Feedback on building the `Abstract.lean` / `AbstractBridge.lean` pair

Practitioner notes from the first project to execute Phase 5 of the
methodology (TilingPolyomino, July 2026). Written by the coding agent for
incorporation into the methodology template.

## 1. The core structural problem, and the pattern that solves it

Lean is strictly sequential: a theorem's proof must appear with its
statement, after everything it uses. A single `Abstract.lean` therefore
forces the bridge machinery *between* the elementary definitions and the
headline statements — exactly where the reader's eyes are. The reader's file
should read like a paper abstract: definitions, then claims, nothing else.

**Pattern (defeq delegation).** Split into two files:

- `Abstract.lean` — the elementary definitions, then the headline theorems,
  each proved by a one-line delegation:

  ```lean
  theorem LTileable_rectangle_iff (n m : ℕ) :
      LTileable (rectangle n m) ↔ ... :=
    AbstractBridge.LTileable_rectangle_iff n m
  ```

- `AbstractBridge.lean` — restates the elementary definitions **verbatim**
  under its own namespace, and proves the full theorem statements against
  its copies, using anything it likes from the general layer.

The delegation type-checks because Lean unifies the two statements **up to
definitional equality**: both copies of each definition unfold to the same
term. This is not just a presentation trick — it is a machine-checked
consistency guarantee: if the two copies ever drift, `Abstract.lean` stops
compiling. The duplication maintains itself.

**The precondition that makes this work (important):** every abstract-layer
definition must be a plain `def` — a predicate or set expression built from
existentials, disjunctions, and equalities. Two separately declared
`structure`s or `inductive`s are *never* definitionally equal, so a single
new inductive type in the abstract layer kills the delegation trick. This
turns out to be a virtue, not a constraint: it pushes the abstract layer
toward flat, explicit formulations, which is what elementarity wanted anyway.

Concrete instance from this project: the general layer models corner defects
with `inductive Corner` and `inductive DefectType`. The abstract layer
instead uses one predicate `IsCornerDefect n m p D` — a flat 12-case
disjunction of explicit set equations, anchored at the corner *cell*
`p : ℤ × ℤ`. "Two distinct corners" becomes simply `p₁ ≠ p₂`. No new types
appear in the reader's contract, and the bridge direction is a 12-way `rfl`
enumeration.

## 2. Prove one central equivalence, not n bridges

Resist bridging each headline theorem separately from scratch. Prove **one**
equivalence between the elementary tiling notion and the general one,
quantified over all regions:

```lean
theorem tileable_iff (R : Set (ℤ × ℤ)) : LTileable R ↔ Tileable R LProtoset
```

Its two directions carry all the real content of Phase 5:

- general → elementary: each placed tile's cell set is one of the explicit
  shapes (one computation per rotation: `ext` + `simp only` + `omega`);
  convert the arbitrary `Fintype` index to `Fin k` via `Fintype.equivFin`.
- elementary → general: each explicit shape is realizable as a placement
  (`choose` + the same computations in reverse).

After this, every per-theorem bridge was ≤ 8 lines: rewrite by
`tileable_iff`, normalize the region, translate the arithmetic side
(`∣` vs `% k = 0` — `omega` does this), apply the general theorem.

**Make region equalities `rfl`.** Define the abstract `rectangle` so it is
*definitionally* the general layer's `rect 0 0 n m` (same set-builder, same
argument order). Then region conversion is `rfl`, not a lemma. Whenever an
abstract definition can be made rfl-equal to a general one, do it.

## 3. Statement design: expect a normalization round with the mathematician

All three revision requests we received at Checkpoint 5 were about *surface
form*, none about substance. They are predictable; the template could list
them as an explicit checklist for the Checkpoint 5 conversation:

1. **Uniform statement shape.** All defect theorems should read the same
   way (`tileable ↔ 3 ∣ area`), even when the general layer only proved a
   sufficiency direction. Budget for supplying the missing necessity in the
   bridge — it is usually cheap (here: the general area-divisibility lemma
   applied to a degenerate configuration, plus a 10-line `ncard`
   computation).
2. **Reader-pleasant normal forms differ from proof-convenient ones.** The
   proof placed defects at the top-right corner; the mathematician wanted
   them at `(0,0)` and `(1,0)`. The right bridge tool is symmetry transport
   (tileability is invariant under reflections/rotations). *Recommendation
   for Phase 4:* keep symmetry-transport lemmas (`tileable R → tileable
   (reflect R)` etc.) public in the general layer — Phase 5 will want them.
3. **Consistent hypothesis spelling** (`n ≥ 6` vs `6 ≤ n`) across theorems.
   Trivial, but it is exactly the kind of thing the mathematician notices.

## 4. Self-containedness is absolute

We initially exposed the layer-equivalence theorem itself in
`Abstract.lean` ("elementary tileable ↔ general tileable") as an honest
statement of the connection. The mathematician cut it: its statement names a
general-layer concept, so a reader parsing it must leave the file. Rule of
thumb the template can state: **every name appearing in the definitions and
theorem statements of `Abstract.lean` must be defined in `Abstract.lean` or
be core Mathlib vocabulary** (`Set`, `ℤ`, `Disjoint`, `Set.ncard`, `Odd`,
`∣`). The layer-equivalence lemma lives in the bridge file, doing its work
out of sight.

Related judgment call that was accepted: `Set.ncard` ("number of cells") is
fine in a statement; a working mathematician reads it instantly. The
alternative arithmetic form (`3 ∣ n·m − |D₁| − |D₂|`) was considered and
declined. Elementarity means *recognizable*, not *primitive*.

## 5. Build integration

The updated layout (abstract layer inside `[ProjectName]/`, not imported by
the root module) needs one lakefile line so the sorry-free contract is
enforced by every plain `lake build`, not just by remembering an explicit
target:

```toml
[[lean_lib]]
name = "TilingPolyomino"
roots = ["TilingPolyomino", "TilingPolyomino.Abstract"]
```

The extra root pulls in `Abstract` (and transitively `AbstractBridge`)
without the root module importing them, so nothing leaks into consumers'
namespace. Suggest putting this snippet directly in the template's
directory-layout note.

Also verify each headline theorem with `#print axioms` (or the lean-lsp
`verify` tool): expect exactly `propext`, `Classical.choice`, `Quot.sound`.
This catches a `sorry` anywhere in the transitive proof, which a green
build of a single file does not.

## 6. Small mechanical traps (worth a footnote each)

- A module docstring `/-! ... -/` must come **after** the `import` lines.
- Mathlib's `Set.ncard_diff` wants finiteness of the *subtracted* set.
- With the mathlib linter set on: unused `simp` arguments are warnings
  (each rotation case needs only its own `rotateCell_*` lemma), and `show`
  that changes the goal up to defeq should be `change`.
- `rw` is syntactic: pick one surface form of the general tileability
  predicate (`LTileable R` vs `Tileable R ps`) and state *all* bridge
  helpers in that form, or rewrites will mysteriously fail mid-chain.
  Definitional equality rescues `exact`, never `rw`.

## 7. Attribution (new policy) — division of labor

The attribution requirement is right, but the agent can only safely write
citations already recorded in the repo (README, docstrings). Precise theorem
numbers, page references, and priority questions ("is the rectangle
characterization older than this paper?") are facts the mathematician must
supply — an agent guessing them is exactly the failure mode principle 7
("you receive the mathematics") exists to prevent. Suggested template
addition: at Checkpoint 5 the mathematician hands over a short attribution
list (source, theorem number, page) per headline theorem, and the agent
formats it into the docstrings.

## 8. Cost datum

Phase 5 took roughly two short sessions: one to build the central
equivalence + four bridges + first draft of `Abstract.lean` (~250 lines of
bridge, all four headline proofs ≤ 8 lines), and one for the Checkpoint 5
revision round (normal forms, iff upgrade, file split, layout move). No
stop-and-ask triggers fired; the only genuinely new mathematics in the
bridge was the corner-domino necessity direction. The layers had drifted
very little — credited to the general layer already working with concrete
`Set (ℤ × ℤ)` regions rather than an abstract tile calculus.
