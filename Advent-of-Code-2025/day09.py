# /// script
# requires-python = ">=3.13"
# dependencies = [
#     "matplotlib>=3.10.7",
# ]
# ///
from pathlib import Path
from itertools import combinations, pairwise
# import matplotlib.pyplot as plt

Coord = tuple[int, int]

lines = Path(__file__).with_suffix(".txt").read_text().splitlines()
coords = [(int(a), int(b)) for a, b in (line.split(",") for line in lines)]
pairs = list(combinations(coords, 2))


def area(corners: tuple[Coord, Coord]) -> int:
    (c1x, c1y), (c2x, c2y) = corners
    return (abs(c1x - c2x) + 1) * (abs(c1y - c2y) + 1)


part1 = max(area(p) for p in pairs)
print(f"{part1=}")

# Part 2: find largest rectangle that doesn't cross the path
horizontal_segments: list[tuple[int, int, int]] = []  # y, min_x, max_x
vertical_segments: list[tuple[int, int, int]] = []  # x, min_y, max_y

for c1, c2 in pairwise(coords):
    (c1x, c1y), (c2x, c2y) = c1, c2
    if c1x == c2x:
        miny, maxy = sorted((c1y, c2y))
        vertical_segments.append((c1x, miny, maxy))
    elif c1y == c2y:
        minx, maxx = sorted((c1x, c2x))
        horizontal_segments.append((c1y, minx, maxx))
    else:
        raise ValueError("wat")

horizontal_segments.sort()
vertical_segments.sort()

max_min = max(min(c) for c in coords)
min_max = min(max(c) for c in coords)


def is_valid_rectangle(corners: tuple[Coord, Coord]) -> bool:
    (c1x, c1y), (c2x, c2y) = sorted(corners)
    ax, bx = sorted((c1x, c2x))
    ay, by = sorted((c1y, c2y))
    # If the rectangle crosses any line, it's not valid
    if any(
        ay < y < by and ((min_x < ax < max_x) or (min_x < bx < max_x))
        for (y, min_x, max_x) in horizontal_segments
    ):
        return False
    if any(
        ax < x < bx and ((min_y < ay < max_y) or (min_y < by < max_y))
        for (x, min_y, max_y) in vertical_segments
    ):
        return False

    # Heuristics, if one of the four corners is too far away, reject this,
    # not guaranteed to be correct (should check the two diagonals separately)
    # but good enough for my input
    if bx > max_min and by > max_min:
        return False
    if ax < min_max and ay < min_max:
        return False
    if bx > max_min and ay < min_max:
        return False
    if ax < min_max and by > max_min:
        return False
    return True


# plt.plot([c[0] for c in coords], [c[1] for c in coords])
part2 = max(area(p) for p in pairs if is_valid_rectangle(p))
print(f"{part2=}")

# top_pair = max((p for p in pairs if is_valid_rectangle(p)), key=area)
# (c1x, c1y), (c2x, c2y) = sorted(top_pair)
# ax, bx = sorted((c1x, c2x))
# ay, by = sorted((c1y, c2y))
# plt.plot([ax, ax, bx, bx], [ay, by, by, ay])
# plt.show()
