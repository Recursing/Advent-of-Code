from pathlib import Path
from functools import cache

lines = Path(__file__).with_suffix(".txt").read_text().splitlines()

# Part 1
part1 = 0
beams = {i for i, c in enumerate(lines[0]) if c in "|S"}

for cur_line in lines[1:]:
    new_beams = set()
    for i in beams:
        if cur_line[i] == "^":
            part1 += 1
            new_beams.update([i - 1, i + 1])
        else:
            new_beams.add(i)
    beams = new_beams


# Part 2
@cache
def part2(row: int, col: int) -> int:
    if row == len(lines) - 1:
        return 1

    if lines[row + 1][col] == ".":
        return part2(row + 1, col)

    return part2(row + 1, col - 1) + part2(row + 1, col + 1)


start_col = next(i for i, c in enumerate(lines[0]) if c in "|S")

print(f"{part1=}")
print(f"part2={part2(0, start_col)}")