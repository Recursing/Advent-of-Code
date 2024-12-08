import itertools
from collections import defaultdict

lines = open(__file__.replace(".py", ".txt")).readlines()
lines = [line.strip() for line in lines]
width = max(len(lines[0]), len(lines))
grid = {
    x + y * 1j: value for y, line in enumerate(lines) for x, value in enumerate(line)
}

freq_coords = defaultdict(list)
for coord, freq in grid.items():
    if freq != ".":
        freq_coords[freq].append(coord)

part1 = set()
part2 = set()
for freq, coords in freq_coords.items():
    for c1, c2 in itertools.combinations(coords, 2):
        d = c2 - c1
        for i in range(-width - 1, width + 1):
            if i in (-1, 2):
                part1.add(c1 + i * d)
            part2.add(c1 + i * d)

print(len(part1 & set(grid)))
print(len(part2 & set(grid)))
