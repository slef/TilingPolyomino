#!/usr/bin/env python3
"""Brute-force L-tromino tileability of rectangles with two corner defects.

Region: [0,n) x [0,m) minus defect at corner c1 (type d1) and corner c2 (type d2).
Defect types: single (1 cell), horiz (2 cells along x), vert (2 cells along y).
Checks: tileable  vs  area % 3 == 0, to find the exact exceptional set.
"""

import sys
from functools import lru_cache

sys.setrecursionlimit(100000)

# The 4 rotations of the L-tromino {(0,0),(0,1),(1,0)} (as offset sets)
ROTS = [
    ((0, 0), (0, 1), (1, 0)),
    ((0, 0), (-1, 0), (0, 1)),
    ((0, 0), (0, -1), (-1, 0)),
    ((0, 0), (1, 0), (0, -1)),
]

# All placements of an L covering a given cell: for each rotation, each of the
# 3 cells can be the covering one.
COVERING = []
for rot in ROTS:
    for anchor in rot:
        COVERING.append(tuple((c[0] - anchor[0], c[1] - anchor[1]) for c in rot))
COVERING = list(set(COVERING))


def tileable(cells):
    """Backtracking: is the given frozenset of cells L-tromino tileable?"""
    if len(cells) % 3 != 0:
        return False

    def go(remaining):
        if not remaining:
            return True
        p = min(remaining)  # lexicographically smallest uncovered cell
        for place in COVERING:
            tri = [(p[0] + dx, p[1] + dy) for (dx, dy) in place]
            if all(c in remaining for c in tri):
                nxt = remaining - frozenset(tri)
                if go(nxt):
                    return True
        return False

    return go(frozenset(cells))


def defect_cells(corner, dtype, n, m):
    """Cells removed for a defect of given type at given corner of [0,n)x[0,m)."""
    if corner == "BL":
        base = (0, 0)
        sx, sy = 1, 1
    elif corner == "BR":
        base = (n - 1, 0)
        sx, sy = -1, 1
    elif corner == "TL":
        base = (0, m - 1)
        sx, sy = 1, -1
    else:  # TR
        base = (n - 1, m - 1)
        sx, sy = -1, -1
    if dtype == "single":
        return {base}
    if dtype == "horiz":
        return {base, (base[0] + sx, base[1])}
    return {base, (base[0], base[1] + sy)}  # vert


CORNERS = ["BL", "BR", "TL", "TR"]
DTYPES = ["single", "horiz", "vert"]
SIZE = {"single": 1, "horiz": 2, "vert": 2}

CORNER_PAIRS = [("BL", "BR"), ("BL", "TL"), ("BL", "TR"), ("BR", "TR"), ("TL", "TR"), ("BR", "TL")]


def main(nmax):
    surprises_untileable = []  # area % 3 == 0 but NOT tileable
    for n in range(2, nmax + 1):
        for m in range(2, nmax + 1):
            rect = {(x, y) for x in range(n) for y in range(m)}
            for (c1, c2) in CORNER_PAIRS:
                for d1 in DTYPES:
                    for d2 in DTYPES:
                        def1 = defect_cells(c1, d1, n, m)
                        def2 = defect_cells(c2, d2, n, m)
                        # skip degenerate: defects overlap or fall outside rect
                        if def1 & def2:
                            continue
                        if not (def1 <= rect and def2 <= rect):
                            continue
                        region = frozenset(rect - def1 - def2)
                        area_ok = len(region) % 3 == 0
                        if not area_ok:
                            continue  # necessity direction is trivial; only test sufficiency
                        t = tileable(region)
                        if not t:
                            surprises_untileable.append((n, m, c1, d1, c2, d2))
        print(f"done n={n}", file=sys.stderr)

    print("=== area%3==0 but NOT tileable ===")
    for s in surprises_untileable:
        print(s)
    print(f"total: {len(surprises_untileable)}")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 10)
