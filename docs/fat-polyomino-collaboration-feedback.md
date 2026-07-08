# Collaboration feedback — fat-polyomino formalization (2026-07-05/06)

Agent-side observations on the mathematician–agent interaction during the
fat-polyomino theorem (skeleton → tiling half → vertical decomposition →
spanning tree → Euler tour, ending sorry-free). Written to improve
`AGENTS.md` and the mathematician-side playbook. Not about the mathematics.

## What worked — worth encoding in AGENTS.md

1. **Checkpoints on statements, autonomy on proofs.** Every pause that
   mattered was about *definitions and lemma statements* (the corner-chain
   interface, the decomposition packaging). Proofs were then delegated
   wholesale ("get to work", "no need to stop if you are clear") and Lean
   played reviewer. `AGENTS.md` currently prescribes proof-level pacing
   ("one sorry at a time", "pause every N sorries") that we abandoned by
   mutual consent, profitably. Suggestion: make the two levels explicit —
   statement checkpoints are mandatory; proof-filling autonomy is a dial
   the mathematician sets per delegation ("continue until X / stop if Y").
   The explicit formulas used here ("if you're confident, continue",
   "stop if it seems too complicated") were effective and cheap; give them
   as recommended vocabulary.

2. **Interface-first decomposition.** The single best structural decision
   was formalizing `IsCornerChain` — the *contract* between the geometric
   half and the tiling half — before either half was proved. The easy half
   landed days before the hard half existed, and the hard half was
   developed against a frozen, reviewed target. Suggestion for Phase 3:
   when a proof has phases, define the inter-phase interface as a `Prop`
   (or structure) and checkpoint *it*, not just the top-level statement.

3. **Corrections to the informal construction are normal, not failures.**
   Twice the sketch needed repair (the vertical-split rule; the separator
   cuts turned out unnecessary). What made this cheap: the agent surfaced
   a concrete counterexample plus a minimal proposed fix, and the
   mathematician answered with an even simpler rule ("split all of them").
   The existing "never silently weaken" rule worked; add its positive
   counterpart: *propose the repair together with the obstruction*, and
   note that the mathematician may use the friction to simplify the
   construction — that simplification (uniform split, no separators)
   measurably shrank the formalization.

4. **Sanity-check `example`s for definitions.** `IsVertex` was validated
   by "the vertices of a rectangle are its four corners", demoted to an
   `example` on review. Good convention to standardize: each nontrivial
   definition ships with one or two validation facts, as `example` unless
   used downstream.

## Friction points — and proposed fixes

5. **The "Slab" misreading.** A correct per-component definition was read
   as "full strips" because the *name* suggested it and the headline
   packaging theorem (disjoint rectangles ⊆ P, union = P) had not been
   stated. Lesson: the mathematician reviews through names, docstrings and
   top-level statements — not through structure fields. Rule to add:
   every definitional cluster ends with one **packaging theorem** phrased
   in the mathematician's vocabulary, stated even when it is a trivial
   repackaging of the fields; and names are chosen against the informal
   text's usage (the sketch used "slab" for something else).

6. **"Proofs from THE BOOK" vs constructions.** The aesthetic guideline
   treats proof length as a smell. For *constructions* (the 16-case
   tromino pushing, the two column folds), length reflected genuinely
   distinct geometric configurations, not a missing idea; the honest move
   was enumerating them and saying so. Suggested refinement: distinguish
   "long because many genuinely distinct cases, each short" (acceptable —
   report the case inventory) from "long because one goal is being ground
   down" (stop-and-ask). The three-approaches trigger stays as is.

7. **Phase model vs multi-theorem repositories.** The project re-entered
   Phases 1–4 for a second theorem inside a finished repo; `AGENTS.md`
   implicitly assumes one pass. Minor fix: say phases restart per theorem,
   and that the new work must not disturb the finished abstract layer.

## For the mathematician-side playbook

8. **Decision style.** Short decisive answers ("yes this will be fine",
   "whatever works best, I'll let you figure out the details") unblocked
   work at near-zero cost. Splitting authority explicitly — mathematics
   decided by the mathematician, Lean engineering (library vs bespoke,
   induction shapes, file layout) delegated — avoided both micromanagement
   and silent drift. Recommend stating this split at project start.

9. **Answer questions with simplifications, not just verdicts.** The best
   replies reshaped the problem ("split all, fewer cases", "root at a
   leaf" later discarded when the agent found any root works). Treat agent
   friction reports as design probes.

10. **Sketch granularity was right.** Numbered steps naming the key
    objects (decomposition, dual tree, door midpoints, defect pushing),
    no formal detail. The agent asks batched, specific questions against
    that sketch; insist (as `AGENTS.md` does) that each question carries
    the agent's recommended answer.

11. **Session hygiene.** Ending sessions at phase boundaries with
    LOG.md/memory current made resumption trivial; the context-window
    limit was the real constraint, not the mathematics. Recommend: cut
    sessions at reviewed checkpoints, not mid-construction.
