from collections import Counter
from typing import cast

text_lines = open("day05.txt").read().splitlines(keepends=False)
lines = [tuple(map(int, line.replace(" -> ", ",").split(","))) for line in text_lines]
lines = cast(list[tuple[int, int, int, int]], lines)
straight_lines = [line for line in lines if line[0] == line[2] or line[1] == line[3]]


def steps(x1: int, y1: int, x2: int, y2: int) -> int:
    return max(abs(x2 - x1), abs(y2 - y1))


def direction(x1: int, y1: int, x2: int, y2: int) -> tuple[int, int]:
    dx = 0 if x1 == x2 else 1 if x2 > x1 else -1
    dy = 0 if y1 == y2 else 1 if y2 > y1 else -1
    return dx, dy


def solve(lines: list[tuple[int, int, int, int]]):
    overlaps = Counter(
        (x1 + t * dx, y1 + t * dy)
        for [x1, y1, x2, y2] in lines
        for dx, dy in [direction(x1, y1, x2, y2)]
        for t in range(steps(x1, y1, x2, y2) + 1)
    )
    print(sum(v >= 2 for v in overlaps.values()))


solve(straight_lines)
solve(lines)
