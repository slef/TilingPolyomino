import re
import glob

decls = [
    'LTileable', 'LTromino', 'LTrominoSet', 'PairwiseDisjoint', 'PlacedTile', 
    'Protoset', 'Prototile', 'Refines', 'TileSet', 'Tileable', 
    'Tileable_biUnion', 'Tileable_horizontal_union', 'Tileable_of_translate_eq', 
    'Tileable_refine', 'Tileable_translate', 'Tileable_translate_iff', 
    'Tileable_union', 'Tileable_vertical_union', 'Valid', 'allPlacementsCovering', 
    'allPlacementsCoveringProto', 'cellsAt', 'coveredCells', 'empty_tileable', 
    'mkPlacedTile', 'mkTileSet', 'placementsCoveringIn', 'tileable_2x2_minus', 
    'tileable_4x4_minus', 'tileable_5x2_minus', 'tileable_5x5_minus', 'tileable_5x9', 
    'tileable_7x7_minus', 'tileable_piece2_base', 'tiling_2x2_minus', 
    'tiling_2x2_minus_valid', 'tiling_4x4_minus', 'tiling_4x4_minus_valid', 
    'tiling_5x2_minus', 'tiling_5x2_minus_valid', 'tiling_5x5_minus', 
    'tiling_5x5_minus_valid', 'tiling_5x9', 'tiling_5x9_valid', 'tiling_7x7_minus', 
    'tiling_7x7_minus_valid', 'tiling_piece2_base', 'tiling_piece2_base_valid'
]

# Sort by length descending to replace longer names first
decls.sort(key=len, reverse=True)

files = glob.glob('TilingPolyomino/*.lean')

for file in files:
    with open(file, 'r') as f:
        content = f.read()

    new_content = []
    for line in content.split('\n'):
        if line.startswith('import '):
            new_content.append(line)
            continue
        
        for d in decls:
            # We want to match whole word.
            # But what if we already appended _finset or if it's followed by _set?
            # E.g. Tileable -> Tileable_finset. We use negative lookahead.
            pattern = r'\b' + d + r'\b(?!_set|_finset)'
            line = re.sub(pattern, d + '_finset', line)
            
        new_content.append(line)

    with open(file, 'w') as f:
        f.write('\n'.join(new_content))

print("Phase 1 complete!")
