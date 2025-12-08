from pathlib import Path
from math import dist, prod
from itertools import combinations

lines = Path(__file__).with_suffix(".txt").read_text().splitlines()
coords = [tuple(int(c) for c in line.split(",")) for line in lines]

pairs = list(combinations(coords, 2))
pairs.sort(key=lambda a: dist(a[0], a[1]))

sets = {coord: frozenset([coord]) for coord in coords}
i = 0
while True:
    a, b = pairs[i]
    merged_set = sets[a] | sets[b]
    for coord in merged_set:
        sets[coord] = merged_set
    i += 1
    if i == 1000:
        part1 = prod(
            sorted((len(s) for s in set(sets.values()) if len(s) > 1), reverse=True)[:3]
        )
        print(f"{part1=}")

    if len(merged_set) == len(coords):
        part2 = a[0] * b[0]
        print(f"{part2=}")
        break
