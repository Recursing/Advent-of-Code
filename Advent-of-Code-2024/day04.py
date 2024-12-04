import re
from itertools import product

text = open(__file__.replace(".py", ".txt")).readlines()

grid = ["." + line.strip() + "." for line in text]
grid = ["." * len(grid[0])] + grid + ["." * len(grid[0])]

# part 1
directions = list(product((-1, 0, 1), (-1, 0, 1)))
occurrences = 0
for y, row in enumerate(grid):
    for x, char in enumerate(row):
        for dy, dx in directions:
            if dy == dx == 0:
                continue
            for i, c in enumerate("XMAS"):
                if grid[y + dy * i][x + dx * i] != c:
                    break
            else:
                occurrences += 1
print(occurrences)

# part 2
grid = ["." + line.strip() + "." for line in grid]
grid = ["." * len(grid[0])] + grid + ["." * len(grid[0])]

occurrences = 0
for y, row in enumerate(grid):
    for x, char in enumerate(row):
        if char == ".":
            continue
        # \ diagonal
        first_diagonal = "".join(grid[y + i][x + i] for i in range(3))
        # / diagonal
        second_diagonal = "".join(grid[y + i][2 + x - i] for i in range(3))
        if first_diagonal in ("MAS", "SAM") and second_diagonal in ("MAS", "SAM"):
            occurrences += 1
print(occurrences)
