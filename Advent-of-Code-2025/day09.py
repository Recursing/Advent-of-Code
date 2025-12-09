# /// script
# requires-python = ">=3.13"
# dependencies = [
#     "matplotlib>=3.10.7",
# ]
# ///
from pathlib import Path
from itertools import combinations, pairwise
import matplotlib.pyplot as plt

Coord = tuple[int, int]

lines = Path(__file__).with_suffix(".txt").read_text().splitlines()
coords = [(int(a), int(b)) for a, b in (line.split(",") for line in lines)]
pairs = list(combinations(coords, 2))


def area(corners: tuple[Coord, Coord]) -> int:
    (c1x, c1y), (c2x, c2y) = corners
    return (abs(c1x - c2x) + 1) * (abs(c1y - c2y) + 1)


part1 = max(area(p) for p in pairs)
print(f"{part1=}")

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

max_sum = max(sum(c) for c in coords)
min_sum = min(sum(c) for c in coords)
max_diff = max(c[0] - c[1] for c in coords)
min_diff = min(c[0] - c[1] for c in coords)


def is_valid_rectangle(corners: tuple[Coord, Coord]) -> bool:
    (c1x, c1y), (c2x, c2y) = sorted(corners)
    ax, bx = sorted((c1x, c2x))
    ay, by = sorted((c1y, c2y))
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
    if bx + by > max_sum:
        return False
    if ax + ay < min_sum:
        return False
    if bx - ay > max_diff:
        return False
    if ax - by < min_diff:
        return False
    return True


part2 = max(area(p) for p in pairs if is_valid_rectangle(p))
print(f"{part2=}")

plt.plot([c[0] for c in coords], [c[1] for c in coords])
top_pair = max((p for p in pairs if is_valid_rectangle(p)), key=area)
(c1x, c1y), (c2x, c2y) = sorted(top_pair)
ax, bx = sorted((c1x, c2x))
ay, by = sorted((c1y, c2y))
plt.plot([ax, bx, bx, ax, ax], [ay, ay, by, by, ay], 'r-', label='part2')
# Bounds rectangle defined by the four diagonal constraints
# Corners: top (x+y=max_sum, x-y=0), right (x-y=max_diff, x+y=max_sum+max_diff?), etc.
# Actually: intersections of the four lines
# x+y=max_sum & x-y=max_diff -> x=(max_sum+max_diff)/2, y=(max_sum-max_diff)/2 (top-right)
# x+y=max_sum & x-y=min_diff -> x=(max_sum+min_diff)/2, y=(max_sum-min_diff)/2 (top-left)
# x+y=min_sum & x-y=max_diff -> x=(min_sum+max_diff)/2, y=(min_sum-max_diff)/2 (bottom-right)
# x+y=min_sum & x-y=min_diff -> x=(min_sum+min_diff)/2, y=(min_sum-min_diff)/2 (bottom-left)
tr = ((max_sum + max_diff) / 2, (max_sum - max_diff) / 2)
tl = ((max_sum + min_diff) / 2, (max_sum - min_diff) / 2)
br = ((min_sum + max_diff) / 2, (min_sum - max_diff) / 2)
bl = ((min_sum + min_diff) / 2, (min_sum - min_diff) / 2)
plt.plot([bl[0], br[0], tr[0], tl[0], bl[0]], [bl[1], br[1], tr[1], tl[1], bl[1]], 'g--', label='bounds')
plt.legend()
plt.show()
