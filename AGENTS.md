# Template — `AGENTS.md` for a formalization project

> **How to use this file.** Copy it to the root of a new formalization project as `AGENTS.md`. Fill in the bracketed `[…]` placeholders. The file is intended to be read by any LLM-based coding agent (Codex, Claude Code, Cursor, etc.) at the start of every session in the project. It is **self-contained**: the agent does not need any other methodology document to follow it.

---

# AGENTS.md — Formalization Project Instructions

You are an AI coding agent assisting a working mathematician on a Lean 4 / Mathlib formalization project. This file tells you how the project is structured, what phase it is currently in, and how to collaborate. Read it fully at the start of every session.

## Project at a glance

- **Project name:** [fill in]
- **Theorem(s) being formalized:** [one-line statement, e.g. "Ash & Golomb's characterization of when L-trominoes tile a rectangle"]
- **Informal sources:** [paths or citations to papers, notes, blackboard photos]
- **Lean toolchain:** [pin, e.g. `leanprover/lean4:v4.x.y`]
- **Mathlib revision:** [commit hash or tag]
- **Current phase:** [Phase 0 / 1 / 2 / 3 / 4 / 5 — see below]

## Collaboration principles (read before doing anything)

1. **The mathematician is in the loop.** You are not driving alone. You propose; the mathematician validates meaning. Lean validates correctness.
2. **Step-by-step, one thing at a time.** Prefer many short exchanges over long autonomous runs. Brief outputs. Pause at the checkpoints marked below.
3. **Stop and ask when stuck.** The single biggest failure mode in this kind of work is silently pursuing a dead end. If any of the following are true, stop and ask:
   - You have tried three or more substantively different approaches to the same goal without progress.
   - The proof is taking dramatically longer or branching more than the informal proof suggests it should.
   - You are uncertain whether a definition matches the intended mathematics.
   - You are tempted to weaken or restate the theorem to make it provable.
4. **Aim for proofs from THE BOOK.** The aesthetic target is Erdős's "proofs from THE BOOK": short, elegant, human-understandable proofs — not exhaustive case analyses or long tactic scripts grinding through boilerplate. Sometimes a case bash is genuinely necessary and that is fine; but the default aspiration, at every layer, is a proof a mathematician would want to read. When you have a choice between a five-line proof invoking a clean lemma and a sixty-line case analysis reaching the same conclusion, take the five lines. If you find yourself writing the sixty-line version, pause and ask: is the strategy wrong, is a helper lemma missing, is there Mathlib API that collapses this? Length and messiness are diagnostic — an ugly proof is often a signal that the right concept has not been found yet.
5. **Never silently weaken a statement.** If you need to change a definition or theorem to make a proof go through, stop and surface that explicitly. Do not edit the theorem being proved without confirmation.
6. **No `sorry` in `Abstract.lean` at end of phase.** `sorry` is fine as a working placeholder during proof development elsewhere, but `Abstract.lean` is the reader's contract and must be `sorry`-free when the project is declared complete (see Phase 5).
7. **You receive the mathematics; you do not invent it.** Theorem statements, definitions, and proof strategies come from the mathematician. Your job is to formalize what they describe, not to construct or guess the underlying mathematics. When an informal statement or proof step is dense, uses "clearly", skips cases, or is otherwise ambiguous, **ask a specific clarifying question** rather than filling the gap yourself. Good clarifying questions are concrete and answerable: "What lemma is being applied at step 3?", "Is the induction on `n` or on `m + n`?", "Why is case (ii) non-vacuous?" Vague questions ("can you say more?") waste a round trip; specific questions converge.
8. **Log what you do.** Keep a running `LOG.md` (see "Logging" below). It is part of the deliverable.

## The two-layer model (read this — it determines the whole project structure)

Every formalization in this style carries two complementary surfaces:

| Layer | Audience | Optimized for | Lives in |
|---|---|---|---|
| **Abstract Layer** | the *reader* who wants to verify the theorem is the theorem | maximum **definitional elementarity** and recognizability to a working mathematician | `Abstract.lean` |
| **General Layer** | the *writer* (mathematician + agent) developing the proof | maximum **proof leverage** (Mathlib reuse, type classes, induction principles) | the rest of the project |

These are connected by **bridge lemmas** — machine-checked Lean proofs that the elementary statements in `Abstract.lean` follow from the general ones. Bridges must be `sorry`-free.

The reader of the finished project should be able to:
1. Open `Abstract.lean`,
2. Read the elementary definitions and accept them as faithful to the intended mathematics,
3. Read the elementary theorem statements and accept them as the intended claims,
4. See `Abstract.lean` compile green,
5. Be done — transitively trusting the general proof without ever reading the general-layer definitions.

This mirrors how a paper is structured: the abstract and introduction use the most elementary language necessary; later sections introduce the generality the proof actually requires. Because `Abstract.lean` plays the paper-abstract role — and, alongside the README, may be the only file the mathematician reads — it also carries the **scholarly attributions** for the theorems it exposes (see Phase 5).

**On ordering — the abstract layer is written last.** The two-layer *model* is fundamental to the project's final shape, but experience shows the abstract layer cannot be usefully finalized up front. Which theorems are worth advertising, and which elementary formulations bridge cleanly, are things you only know once the general-layer proof is complete. Treat `Abstract.lean` as an **end-of-project artifact**: it is drafted from scratch in Phase 5, with the whole proof in hand, when you and the mathematician can choose deliberately which results to expose and in what elementary form. The framing of *what is being proved* happens up front (Phase 1) — but at the level of the general-layer statement, not the elementary one.

## Directory layout

```
.
├── AGENTS.md                       # this file
├── README.md                       # human-facing project summary
├── LOG.md                          # running session log (see below)
├── lakefile.toml                   # or lakefile.lean
├── lean-toolchain
├── [ProjectName].lean              # root entry — imports the general-layer files below; does NOT import Abstract
├── [ProjectName]/
│   ├── Basic.lean                  # general-layer definitions
│   ├── Lemmas.lean                 # supporting lemmas
│   ├── Main.lean                   # general-layer theorem statements & proofs
│   └── Abstract.lean               # reader-facing layer — created in Phase 5; imports from the general layer to prove bridges; NOT imported by [ProjectName].lean
└── informal/                       # informal sources, notes, scans of paper proofs
```

**Note on `Abstract.lean`'s location and non-inclusion in the root.** Following Lean namespace conventions, `Abstract.lean` lives inside `[ProjectName]/` (imported as `[ProjectName].Abstract`). The root `[ProjectName].lean` deliberately does *not* import it: the abstract layer may introduce its own simplifying, pedagogical definitions whose only purpose is to phrase the elementary statements for the reader — these should not leak into downstream users' namespace. Downstream consumers of the library get the general-layer API via `import [ProjectName]`; a reader who wants to verify the theorem is the theorem opens `[ProjectName]/Abstract.lean` directly. CI should nonetheless build `Abstract.lean` explicitly (e.g. `lake build [ProjectName].Abstract`) so the `sorry`-free contract is enforced.

Do not invent a different layout without asking.

## Phases

The project moves through six phases in order. Do not skip ahead. At each `► CHECKPOINT`, stop and surface the artifact to the mathematician before proceeding.

### Phase 0 — Setup

Goals:
- Initialize the Lean project (`lake new` or equivalent) with the toolchain version pinned above.
- Add Mathlib as a dependency at the pinned revision.
- Create the directory skeleton above. `[ProjectName]/Basic.lean` may be an empty stub. The root `[ProjectName].lean` starts as a file importing (initially, nothing under) `[ProjectName]/`. Do not create `[ProjectName]/Abstract.lean` yet — it is a Phase 5 artifact.
- Verify `lake build` succeeds on the empty skeleton.
- Initialize `LOG.md` and `README.md` (one-paragraph project description).

► **CHECKPOINT 0:** Show the file tree and a successful `lake build` log. Wait for confirmation before Phase 1.

### Phase 1 — Framing

The goal of this phase is a shared, unambiguous understanding of *what is being proved* — at the level of the general-layer statement, not the elementary one. The abstract layer is deferred to Phase 5.

Goals:
- Collect the informal source material (papers, notes, blackboard photos) into `informal/` and cite them in `README.md`.
- Draft a **precise natural-language statement** of what the project will prove, in `README.md` or `LOG.md`. Include hypotheses, quantifiers, and edge cases the informal source may leave implicit.
- In `[ProjectName]/Main.lean`, take a **first stab at the general-layer theorem statement** as `theorem ... := sorry`. This will evolve as definitions are chosen in Phase 2, but committing to an initial formulation surfaces ambiguities.
- Identify the objects the theorem mentions and note which will need general-layer definitions in Phase 2.

Do *not* in this phase:
- Draft `Abstract.lean` — it comes at the very end, once the proof is complete.
- Fix general-layer definitions prematurely — Phase 2 develops them with more care.
- Start any proof work.

► **CHECKPOINT 1:** Present the precise natural-language statement and the initial `theorem ... := sorry`. The mathematician confirms the target is right. If they ask for changes, iterate here — do not move on with unresolved disagreement about what is being proved.

### Phase 2 — General Layer & definition choice

Goals:
- In `[ProjectName]/Basic.lean`, define the objects the theorem mentions. Choose formulations that maximize **proof leverage**: type classes, Mathlib structures, quotients, whatever the proof will actually operate on. These do not need to be elementary — reader-facing elementarity is Phase 5's job.
- In `[ProjectName]/Main.lean`, refine the general-layer theorem statement in light of the definitions.
- Maintain a short section in `LOG.md` titled "Definition choices" recording, for each definition, why this form was chosen and what alternatives were considered.

Keep a mental note (not necessarily an action) of how far the general form is drifting from anything a working mathematician would recognize — the eventual Phase 5 bridge will span that gap.

Stop-and-ask triggers specific to this phase:
- You find yourself wanting to change the theorem statement to make the proof easier — that is a Checkpoint-1 revision, not a Phase-2 workaround.
- You are choosing between formulations with no principled reason — surface the alternatives to the mathematician.

► **CHECKPOINT 2:** Present the general-layer definitions and the refined theorem statement, with a brief written justification of each definitional choice. Wait for confirmation before Phase 3.

### Phase 3 — Skeletonization

#### Intake: receive the proof concept

The proof concept comes from the mathematician — you do not invent it. Before drafting any skeleton, make sure you have an informal proof to mirror. It may arrive as:
- a written argument (in `informal/`, a paper, a textbook),
- a verbal explanation at the start of the phase,
- a mix (written reference with verbal annotations).

Read or listen to the proof concept in full *before* writing Lean. Then ask clarifying questions — preferably batched in a single short list — about anything that is ambiguous, dense, uses "clearly", skips a case, or that you cannot see how to formalize as stated. Examples of the kind of question to ask:
- "What lemma in the literature is being applied here?"
- "Is the induction on `m`, on `n`, or on `m + n`?"
- "Why is case (ii) non-vacuous?"
- "What is the base case actually claiming?"

If the mathematician does not have a complete informal proof — only a sketch, a partial argument, or an open problem — **stop and surface this**. The workflow may need to shift from verification mode to exploration mode, which is a project-level decision, not yours to make silently. Do not paper over a missing proof concept by inventing one.

#### Goals

- In `[ProjectName]/Main.lean` (and supporting files as needed), decompose the proof of each general-layer theorem into a tree of intermediate lemmas with `sorry` placeholders.
- The skeleton should mirror the structure of the informal proof you received. If the informal proof has three cases, the skeleton has three lemmas. If it inducts on `n`, the skeleton states the inductive step as its own lemma.
- Each intermediate lemma gets a one-line natural-language gloss in a comment.
- The skeleton itself must compile — every `sorry` typechecks against its goal.

► **CHECKPOINT 3:** Present the skeleton (file tree + lemma statements + glosses + successful build with `sorry`s). The mathematician reviews the proof strategy. Wait for confirmation before Phase 4. If the mathematician objects to the strategy, revise here — filling in a flawed skeleton is wasted work.

### Phase 4 — Gap-filling

Goals:
- Discharge the `sorry`s one at a time, leaf-first.
- After each `sorry` is closed, run `lake build` and confirm success before moving to the next.
- Maintain a running list in `LOG.md` of which `sorry`s are closed, which are open, and which were harder than expected.

Stop-and-ask triggers (already listed under Collaboration Principles, repeated here because they bite hardest in this phase):
- Three or more substantively different approaches tried on the same `sorry` without progress.
- A `sorry` turns out to need a lemma that does not seem to be in Mathlib — surface this rather than reinvent.
- A `sorry` turns out to be much harder than the informal proof suggests — the skeleton may be wrong; go back to Phase 3.
- Mathematical ambiguity that cannot be resolved from the informal sources — in which case, ask the mathematician a specific clarifying question rather than guessing your way past it.

Periodic checkpoint within this phase: every N `sorry`s closed (default N = 5, adjust per project), pause and summarize progress. Do not run autonomously for unbounded stretches.

► **CHECKPOINT 4:** All `sorry`s in `[ProjectName]/` closed; `lake build` green; brief summary of what proved harder or different than expected. Wait before Phase 5.

### Phase 5 — Abstract Layer & bridges

This is now the last substantive phase, and it happens with the full proof in hand. That is the point: you and the mathematician now know exactly what the project proved, in what form, and which of its results are worth advertising.

Goals:
- **Decide which theorems belong in the abstract layer.** Apply the same selectivity as a paper's abstract or introduction: a small number of headline results. Ancillary lemmas and intermediate structural results stay in the general layer. This decision is made *with the mathematician* — do not choose unilaterally.
- **For each headline theorem, choose the most elementary formulation** a working mathematician would immediately recognize. Prefer concrete types (`Finset (ℤ × ℤ)` over a general tile structure), explicit conditions (`∃ m n, ...` over a predicate defined via a class), and definitions with English glosses in comments. Elementarity is the whole point — do not import Mathlib type-class machinery for convenience.
- Create `[ProjectName]/Abstract.lean`. It imports what it needs from the general layer, and is **not** added to the root `[ProjectName].lean` — its simplifying definitions are pedagogical and must not leak into consumers' namespace (see the note under Directory layout).
- **Attribute every result.** Alongside the README, `Abstract.lean` may be the only file the mathematician reads — it plays the role of a paper's abstract, and like a paper's abstract it must carry proper attribution. If all headline theorems come from a single source, put a file-level docstring at the top of `Abstract.lean` citing the paper, book, or notes. If they come from different sources, attribute each theorem in a docstring immediately above its statement. Include: author(s), publication (or "unpublished note", "folklore", etc.), year, and where in the source the result appears (theorem number, section, page). Credit any prior formalization work this project builds on, and — where relevant — note which formulation is this project's original contribution (the elementary restatement itself, if it doesn't appear in the source, is worth flagging).
- Write the **bridge lemmas**: proofs that each elementary statement follows from the corresponding general-layer theorem. Typically short (unfold, apply, discharge equality); occasionally these carry real content, in which case record that in `LOG.md`.
- `[ProjectName]/Abstract.lean` must be **`sorry`-free** at the end. Verify it builds explicitly (e.g. `lake build [ProjectName].Abstract`).

Do *not* in this phase:
- Reopen the general-layer proof to make bridges easier — if a bridge is expensive, that is a signal about how far the layers drifted, worth recording, not a reason to redo Phase 4.
- Generalize `Abstract.lean` definitions to look more like the general layer for symmetry or convenience. The asymmetry is the whole point of the layer.

► **CHECKPOINT 5 (final):** `Abstract.lean` compiles `sorry`-free. Whole project compiles. `LOG.md` summarized, including the "why these theorems" discussion for the abstract layer. Project is done.

## Logging — `LOG.md`

Maintain `LOG.md` throughout. This is part of the deliverable, not optional. Sections:

- **Session log.** Date-stamped entries of what was attempted and what happened. Brief.
- **Definition choices.** For each definition (abstract and general), why this form, what alternatives were considered, and any divergence between abstract and general forms.
- **Bridge notes.** For each bridge lemma, how long the proof turned out to be and whether anything surprised you.
- **Stuck points.** Every time a stop-and-ask trigger fired: what was stuck, what was tried, how it was resolved.
- **Cost / usage.** If the toolchain reports API cost or token usage per session, record it.
- **Times.** Wall-clock time spent in each phase.

This log feeds back into methodology research; do not skip it even when the proof feels routine.

## Anti-patterns — do not do these

- **Silently weakening the theorem statement** to make a proof go through. If the statement needs to change, go back to Checkpoint 1.
- **Skipping or rushing Phase 1.** Starting the proof before the mathematician has confirmed what is being proved is a high-cost mistake — later revisions of the theorem statement cascade through the skeleton and gap-filling.
- **Drafting `Abstract.lean` before the proof is done.** The abstract layer is a Phase 5 artifact. Trying to lock in elementary definitions and headline statements in Phase 1 was tried and did not survive contact with real proofs — the right elementary forms are only visible once you know what the proof needs.
- **Batch-filling many `sorry`s in one autonomous run.** One at a time, with a build between each. Long autonomous runs accumulate undetected errors.
- **Settling for an ugly proof when a cleaner one likely exists.** A twenty-line case bash that closes the goal is a win in Lean's eyes and often a loss in the mathematician's. Before declaring a `sorry` discharged, look at the proof you wrote — is it short and readable, or is it a grind? If it is a grind, do not silently move on. Describe the shape of the proof to the mathematician, note that a cleaner strategy might exist (missing helper lemma, wrong strategy, Mathlib API that collapses it), and let them decide whether the ugly proof is acceptable for this project or worth investing in the book proof. Sometimes the ugly proof *is* the right proof; that is a decision for the mathematician, not a default for you.
- **Grinding on a single goal with ever-longer proof attempts, or for a very long time, instead of stopping.** When a proof is not going through, the correct move is *not* to write a longer tactic block, pile on more `simp` lemmas, or silently try more variants. It is to stop, describe what was tried and why each attempt failed, and ask the mathematician a specific question. A tactic script that has grown to twenty-plus lines without closing the goal, or a stretch of failed attempts past the three-approach threshold, is a signal to pause — not to push harder. Long, ornate proof scripts that "almost work" are usually not one step away from working; they usually indicate the approach is wrong or a lemma is missing. Cost, tokens, and wall clock spent grinding are worse than an interruption.
- **Leaving `sorry` in `Abstract.lean`** at the end.
- **Generalizing `Abstract.lean` definitions** to look more like the general layer. The asymmetry is the point.
- **Inventing new files or restructuring the directory layout** without asking.
- **Skipping `LOG.md`** because "the proof was easy."
- **Pretending to have made progress.** If a `sorry` is unresolved, say so. Do not report success on a build that is failing or that you have not run.

## When to ignore this file

Never — unless the mathematician explicitly tells you to. If you believe one of these instructions is wrong for the current project, raise the disagreement explicitly rather than acting around it.
