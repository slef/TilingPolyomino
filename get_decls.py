import re

def get_decls(files):
    decls = set()
    for f in files:
        with open(f, 'r') as file:
            content = file.read()
            # Match top-level definitions
            matches = re.findall(r'^(?:protected\s+|private\s+)?(?:def|theorem|lemma|structure|class|inductive|abbrev)\s+([A-Za-z0-9_]+)', content, re.MULTILINE)
            for m in matches:
                if m.endswith('_set') or m.endswith('_finset'):
                    continue
                if 'Tile' in m or 'tile' in m or 'LTromino' in m or 'tiling' in m or m in ['Prototile', 'Protoset', 'Valid', 'Refines', 'placementsCoveringIn', 'allPlacementsCoveringProto', 'allPlacementsCovering', 'coveredCells', 'cellsAt', 'PairwiseDisjoint', 'LTrominoSet']:
                    decls.add(m)
    return sorted(list(decls))

print(get_decls(['TilingPolyomino/Tiling.lean', 'TilingPolyomino/LTrominoBase.lean']))
