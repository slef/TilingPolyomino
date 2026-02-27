# TilingPolyomino — Future Plans & Extensions

This file records Stefan's plans for extending the formalized results beyond
what Hache & Golomb originally proved. Each section has a theorem statement
(informal or partial), a proof sketch, and notes on formalization strategy.

---

## Extension 1: Rectangles with Two Corner Defects

### Informal Statement

An n×m rectangle with **two corner defects** (each defect removing 1 or 2 cells
from a corner) is L-tromino tileable if and only if its area (= n·m minus the
total defect size) is divisible by 3, provided n, m ≥ B for some bound B.

Stefan's current conjecture: B = 9 (to be tightened during formalization).

### Proof Sketch (from Stefan's handwritten notes, 2026-02-27)

**Structure**: Proof by induction on rectangle dimensions.

**Base cases**: Small explicit tilings (dimensions around 4–7) verified by
construction — analogous to the base cases in `LTromino.lean` for the
single-corner defect results.

**Inductive step**: Shown in the sketches as a strip-growing argument:
- Given a tileable defective rectangle of size k, grow to k+1 by appending
  a 2-wide strip on one side.
- The added strip can be tiled independently (2×m or n×2 sub-rectangles are
  tileable when 3 divides the area — using existing `LTileable_2xn_iff_set`).
- The bracket labeled "2" in the sketches indicates the strip width.

**Symmetry**: The four corner positions (TL, TR, BL, BR for each defect) are
handled by the `LTileable_swap_set` / `swapRegion` machinery, reducing to
2 canonical cases.

**Key cases in the proof** (6 diagrams from Stefan's sketches):
1. Top-left corner defect, small base case — explicit tiling
2. Top-right corner defect, small base case — explicit tiling (symmetric)
3. Middle left: defect position shifted — inductive hypothesis case
4. Middle right: wider rectangle, defect on right — symmetric case
5. Bottom left: elongated rectangle, defect bottom-left — inductive step
6. Bottom right: general case, strip of width 2 being added (labeled "2")

### Formalization Notes

- Define `rectMinus2Corners_set n m d1 d2` where d1, d2 ∈ {1, 2} are defect sizes
  and the two removed corners are at opposite corners (or adjacent corners — TBD).
- OR: define it for specific corner positions and use swap to generalize.
- Expected condition: `3 ∣ (n * m - d1 - d2)` and `n ≥ B` and `m ≥ B`.
- Proof approach: induction on `n + m`, stripping 2-wide borders using
  `horizontal_union` / `vertical_union`.
- Necessary condition: `SetTileable.ncard_dvd`.

### Status

- [ ] Exact theorem statement to be added when Stefan pastes the full proof
- [ ] Bound B to be determined (Stefan's guess: B = 9)
- [ ] Decide: arbitrary corner positions or fixed + swap?

---

## Notes on Proof Sketches (Images)

Stefan sent 3 scanned images on 2026-02-27 showing the handwritten proof structure.
Stored in OpenClaw media inbound:
- `393c9373-d66a-4995-9cd2-bec5c20d4bc4.png`
- `0de76374-13e3-4a5e-98d6-cc6d8bc6e9ca.png`
- `32caee78-31bf-478b-ba2b-ad8a4eed52fe.jpg`

The diagrams illustrate a 3×2 grid of cases: base cases (top row),
inductive hypothesis (middle row), and inductive step with 2-wide strip (bottom row).

---

## General Extension Philosophy

- All extensions should be proved in the **Set framework** (`LTrominoSet.lean`)
  without using the bridge to Finset.
- Follow the proof style: small helper lemmas → main theorem.
- Use `rect_omega` / `rexp_omega` for geometric set equalities wherever possible.
- The deficient rectangle regions should be defined as `Set Cell` expressions
  (plain set difference or union) so `omega`-based tactics apply directly.

---

*This file is updated as Stefan provides new proof ideas or extension targets.*
*Last updated: 2026-02-27*
