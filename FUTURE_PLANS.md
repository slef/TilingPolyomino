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

### Exact Statement (Stefan, 2026-02-27)

> **Lemma.** Every m×n rectangle with m ≥ 9, n ≥ 9, with at most two corners
> where 1 pixel or 2 adjacent pixels are missing, and area divisible by 3,
> can be tiled with L-trominoes.

References used in the proof:
- **Golomb Theorem 2**: any rectMinusCorner(n, m) with n, m ≥ 2 is L-tileable
  if area ≡ 0 (mod 3). (Works for size-1 defects always.)
- **Golomb Remark 2**: rectMinus2Cells(n, m) with size-2 corner defect needs
  every dimension to exceed 3. (n×2 with size-2 defect cannot be tiled.)
  Reference: https://condor.depaul.edu/mash/tilerec2a.pdf

### Proof Sketch (Stefan's text + handwritten diagrams, 2026-02-27)

WLOG say defects are on the left and right edges. Let m be the height.

**Case 1: m ≢ 0 (mod 3)**

Split with a vertical cut into two pieces, each containing one defect:
- Each piece has area ≡ 0 (mod 3) (since the total area ≡ 0 (mod 3) and
  m ≢ 0 (mod 3), we can choose the cut width so each piece's area works out).
- Each piece has every dimension ≥ 3 (leave 3 rows on each side, needing
  3 + 3 + 3 = 9 total, hence the bound m ≥ 9).
- Apply Golomb Theorem 2 (size-1 defect) or Remark 2 (size-2 defect) to each.

**Case 2: m ≡ 0 (mod 3)**

Observation: if m ≡ 0 (mod 3) and area ≡ 0 (mod 3), then
  n·m - d1 - d2 ≡ 0 - d1 - d2 ≡ 0 (mod 3)
so d1 + d2 ≡ 0 (mod 3). Since d1, d2 ∈ {0, 1, 2}:
- Either no defects (plain rectangle, Golomb handles it).
- Or exactly one defect of size 1 and one of size 2.

In the latter case, strip off a 2-row band that covers both defects:
1. **Start**: handle the size-2 defect in one of three ways (depending on
   its column position — 3 configurations shown in the left column of sketches).
2. **Middle**: fill the rest of the 2-row strip with 2×3 rectangles.
3. **End**: handle the size-1 defect in one of three ways (right column of sketches).

After removing this band: m decreases by 2. Since m ≡ 0 (mod 3), now
m - 2 ≡ 1 (mod 3) ≢ 0 (mod 3). Also the remaining rectangle still has
(at most) two corner defects and area ≡ 0 (mod 3).

→ Now m - 2 ≢ 0 (mod 3): apply Case 1 to finish.

**Diagrams** (6 sketches from Stefan's scan):
- Top row: 3 configurations for the size-2 defect start
- Bottom row: 3 configurations for the size-1 defect end (with "2" bracket
  indicating the 2-row strip being removed)

### Formalization Notes

**Region definition**: Define the region as:
```lean
def rectMinus2Corners_set (n m : ℤ) (d1 d2 : ℕ) : Set Cell :=
  rect 0 0 n m \ (corner_cells_left d1 ∪ corner_cells_right n m d2)
```
where `d1, d2 ∈ {1, 2}` are defect sizes (cells removed from the left/right
corner respectively). The "2 adjacent pixels" defect removes a 1×2 or 2×1
block from a corner.

**Key sub-lemmas needed**:
1. Tileable 2-row strip with size-2 start, 2×3 middle, size-1 end (3 × 3 cases)
   — the "band" lemma from Case 2 of the proof above.
2. The vertical-cut lemma from Case 1: splitting into two defective rectangles
   each with area ≡ 0 (mod 3).
3. The modular arithmetic showing d1 + d2 ≡ 0 (mod 3) when m ≡ 0 (mod 3).

**Proof structure in Lean**:
- Strong induction on m (or on n + m).
- Case split on `m % 3`:
  - `m % 3 ≠ 0`: vertical cut, apply Golomb (existing `LTileable_rectMinusCorner_iff_set`).
  - `m % 3 = 0`: strip a 2-row band (band lemma), recurse with m - 2.
- The 2-row band: use `SetTileable.horizontal_union` / `vertical_union` +
  `setTileable_translate` to assemble the strip from the 3-configuration base cases.

**Connections to existing proofs**:
- `LTileable_rectMinusCorner_iff_set` (Golomb Theorem 2 equivalent) — needed ✓ (in progress)
- `LTileable_2xn_iff_set` — already proved ✓
- `SetTileable.horizontal_union`, `vertical_union`, `scale_rect` — already proved ✓

### Status

- [x] Informal theorem statement and proof sketch recorded (2026-02-27)
- [ ] Formal Lean statement to be written (after deficient-rect work in LTrominoSet.lean)
- [ ] Bound B = 9 to be verified or tightened
- [ ] Band lemma (3 × 3 configurations) to be constructed
- [ ] Full proof: after `LTileable_rectMinusCorner_iff_set` is done (prerequisite)

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
