import TilingPolyomino.Corridor.Chain
import TilingPolyomino.CornerChain.Tiling

/-!
# Fat polyominoes are L-tileable

**Theorem** (`LTileable_of_fat`): every finite, connected, simply connected
(`Pᶜ` connected), 16-fat polyomino whose area is a multiple of 3 is
L-tileable.

*`l`-fat* (`Fat`) means: around every vertex of the boundary, throughout
the square of `L∞`-radius `l`, the polyomino looks like a quarter plane or
the complement of one — the formal rendering of "every vertex is at
distance ≥ `l` from every non-incident edge", a purely *local* condition
(unlike the global grid alignment of `LTileable_of_vertexAligned`).

## The argument (see `docs/offset-polyomino-argument.md`)

1. **Offset.**  Push every edge of `P` inwards by at least 6 and then
   further until it snaps onto the 3×2 grid: `offsetCore P` is the union
   of the complete 3×2 grid cells whose 6-neighbourhood lies inside `P`.
   The offset polyomino automatically has all its vertices on the 3×2
   grid — for *any* `P` — so it is L-tileable by
   `LTileable_of_vertexOnGrid3x2`, with no connectivity or area
   hypothesis (`LTileable_offsetCore`).
2. **Corridor.**  `corridor P = P \ offsetCore P` is the moat between the
   boundary of `P` and the offset polyomino, of thickness 6–8.  Its area
   is `≡ |P| (mod 3)` because the offset area is a multiple of 6
   (`dvd_ncard_corridor`).
3. **Corridor chain.**  The boundary of `P` is a *single* cycle
   (`vertex_mem_of_closed`, by the ray-crossing parity argument — this is
   where connectivity of `P` and of `Pᶜ` enter).  Walking it, each edge
   receives one corridor rectangle (`edgePiece`), cut forward at each
   vertex from the offset corner to the boundary (convex) or from the
   vertex to the offset boundary (reflex).  The rectangles have both
   sides ≥ 6, are pairwise disjoint, cover the corridor, and consecutive
   ones meet corner-to-corner — a corner chain (`exists_corridorChain`).
4. **Assembly.**  Defect pushing tiles the chain (`IsCornerChain.tileable`),
   the offset core is tiled by step 1, and the two glue along a disjoint
   union.

The constant: `Fat 16`.  16 = 2·8 keeps two offset edges from crossing
(touching is fine — `offsetCore` may degenerate or disconnect, which step 1
tolerates), and edges of length ≥ 16 lose at most 8 to a cut, leaving
rectangles of length ≥ 8 ≥ 6.
-/

open Set

/-- **Fat polyominoes are L-tileable.**  A finite, connected, simply
    connected (`Pᶜ` connected) 16-fat polyomino whose area is divisible
    by 3 is L-tileable. -/
theorem LTileable_of_fat (P : Set Cell) (hfin : P.Finite)
    (hconn : CellConnected P) (hsimp : CellConnected Pᶜ)
    (hfat : Fat 16 P) (harea : 3 ∣ P.ncard) : LTileable P := by
  rcases P.eq_empty_or_nonempty with rfl | hne
  · exact Tileable.empty _
  -- the corridor carries a corner chain …
  obtain ⟨l, hl⟩ := exists_corridorChain P hfin hconn hsimp hfat
    (corridor_nonempty hfin hne)
  -- … so defect pushing tiles it (its area is ≡ |P| ≡ 0 mod 3) …
  have hcorr : LTileable (corridor P) :=
    hl.tileable (dvd_ncard_corridor hfin harea)
  -- … and the offset core is tileable unconditionally; glue.
  rw [← offsetCore_union_corridor P]
  exact Tileable.union (LTileable_offsetCore hfin) hcorr
    (disjoint_offsetCore_corridor P)
