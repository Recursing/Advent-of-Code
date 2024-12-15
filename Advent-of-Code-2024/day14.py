from typing import NamedTuple
from collections import Counter, defaultdict
import math
import re

text = open(__file__.replace(".py", ".txt")).read().splitlines()

numbers = [list(map(int, re.findall(r"\-?\d+", l))) for l in text]

width = 101
height = 103

# width = 11
# height = 7


class Robot(NamedTuple):
    x: int
    y: int
    dx: int
    dy: int

    def pos_after(self, seconds: int):
        return (
            (self.x + self.dx * seconds) % width,
            (self.y + self.dy * seconds) % height,
        )


robots = [Robot(*nums) for nums in numbers]

final_positions = Counter(r.pos_after(100) for r in robots)


def quadrant(x: int, y: int):
    if x == width // 2 or y == height // 2:
        return -1
    return (x < width // 2) * 10 + (y < height // 2)


quadrants: defaultdict[int, int] = defaultdict(int)
for point, robs in final_positions.items():
    if quadrant(*point) < 0:
        continue
    quadrants[quadrant(*point)] += robs

print(math.prod(quadrants.values()))


def pprint(positions: Counter[tuple[int, int]]):
    s: list[str] = []
    for y in range(height):
        for x in range(width):
            if positions.get((y, x)):
                s.append("x")
            else:
                s.append(".")
        s.append("\n")
    return "".join(s)


with open("log.txt", "w") as of:
    for step in range(10000):
        s = pprint(Counter(r.pos_after(step) for r in robots))
        if "xxxxxxxx" in s:
            print(step, ":", file=of)
            print(s, file=of)
