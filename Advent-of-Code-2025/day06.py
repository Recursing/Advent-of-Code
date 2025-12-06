from pathlib import Path
from math import prod

lines = Path(__file__).with_suffix(".txt").read_text().splitlines()
# Restore trailing spaces
WIDTH = max(len(line) for line in lines)
lines = [line.ljust(WIDTH, " ") for line in lines]

operations = lines.pop().split()
number_grid = [line.strip().split() for line in lines]
number_columns = list(zip(*number_grid))
accumulators = {"+": sum, "*": prod}
part1 = sum(
    accumulators[op](int(c) for c in number_columns[i])
    for i, op in enumerate(operations)
)

part2 = 0
flipped_lines = ["".join(col).strip() for col in zip(*lines)]

number_columns = [[]]
for col in flipped_lines:
    if col == "":
        number_columns.append([])
    else:
        number_columns[-1].append(int(col))

part2 = sum(
    accumulators[op](int(c) for c in number_columns[i])
    for i, op in enumerate(operations)
)
print(f"{part1=}")
print(f"{part2=}")
