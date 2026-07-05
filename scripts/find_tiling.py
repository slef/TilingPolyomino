#!/usr/bin/env python3
"""Find an explicit L-tromino tiling of a region and print it in the repo's
PlacedTile (translation, rotation) convention.

Convention (from TilingPolyomino): placed tile (t, r) covers
  r=0: t, t+(0,1),  t+(1,0)
  r=1: t, t+(-1,0), t+(0,1)
  r=2: t, t+(0,-1), t+(-1,0)
  r=3: t, t+(1,0),  t+(0,-1)
"""

import sys

PATTERNS = {
    0: ((0, 0), (0, 1), (1, 0)),
    1: ((0, 0), (-1, 0), (0, 1)),
    2: ((0, 0), (0, -1), (-1, 0)),
    3: ((0, 0), (1, 0), (0, -1)),
}

# All ways an L can cover a given cell (pattern shifted so each cell is origin)
COVERING = []
for r, pat in PATTERNS.items():
    for anchor in pat:
        COVERING.append((r, tuple((c[0] - anchor[0], c[1] - anchor[1]) for c in pat)))


def solve(cells):
    cells = frozenset(cells)
    if len(cells) % 3 != 0:
        return None
    placed = []

    def go(remaining):
        if not remaining:
            return True
        p = min(remaining)
        for r, place in COVERING:
            tri = tuple((p[0] + dx, p[1] + dy) for (dx, dy) in place)
            if all(c in remaining for c in tri):
                placed.append((r, tri))
                if go(remaining - frozenset(tri)):
                    return True
                placed.pop()
        return False

    return placed if go(cells) else None


def to_placed(tri_list):
    """Convert (r, cells) to (translation, rotation)."""
    out = []
    for r, tri in tri_list:
        pat = PATTERNS[r]
        # translation = tri cell corresponding to pattern origin (first listed)
        # tri was built as p + shifted pattern; recover t: try each cell
        sett = frozenset(tri)
        found = False
        for t in tri:
            if frozenset((t[0] + dx, t[1] + dy) for (dx, dy) in pat) == sett:
                out.append((t, r))
                found = True
                break
        assert found, (r, tri)
    return out


def region_two_corners(n, m, defects):
    cells = {(x, y) for x in range(n) for y in range(m)}
    return cells - set(defects)


CASES = {
    "B1": (6, 2, [(0, 0), (5, 0), (5, 1)]),                  # single@BL, vert@BR
    "B2": (7, 4, [(0, 0), (0, 1), (6, 0), (6, 1)]),          # vert@BL, vert@BR
    "B3": (7, 7, [(0, 0), (0, 1), (6, 0), (6, 1)]),          # vert@BL, vert@BR
}


def main():
    for name, (n, m, defects) in CASES.items():
        cells = region_two_corners(n, m, defects)
        sol = solve(cells)
        if sol is None:
            print(f"{name}: NO TILING")
            continue
        placed = to_placed(sol)
        print(f"-- {name}: {n}x{m} minus {defects} ({len(placed)} tiles)")
        for (t, r) in placed:
            covered = sorted(
                (t[0] + dx, t[1] + dy) for (dx, dy) in PATTERNS[r]
            )
            print(f"  ⟨(), ({t[0]}, {t[1]}), {r}⟩,  -- covers {covered}")
        print()


if __name__ == "__main__":
    main()
