from pathlib import Path

lines = Path(__file__).with_suffix(".txt").read_text().splitlines()
part1 = 0
part2 = 0

HEIGHT = len(lines)
WIDTH = len(lines[0].strip())
assert all(len(line.strip()) == WIDTH for line in lines)

initial_grid: dict[complex, str] = {
    row * 1j + col: lines[row][col] for row in range(HEIGHT) for col in range(WIDTH)
}


def neighbours(pos: complex):
    return (
        pos - 1j - 1,
        pos - 1j + 0,
        pos - 1j + 1,
        pos + 0j - 1,
        pos + 0j + 1,
        pos + 1j + 1,
        pos + 1j + 0,
        pos + 1j - 1,
    )


def is_removable(pos: complex, grid: dict[complex, str]) -> bool:
    return grid[pos] == "@" and sum(grid.get(n, "") == "@" for n in neighbours(pos)) < 4


part1 = sum(1 for pos in initial_grid if is_removable(pos, initial_grid))

print(f"{part1=}")


def step(oldgrid: dict[complex, str]) -> dict[complex, str]:
    return {pos: "." if is_removable(pos, oldgrid) else oldgrid[pos] for pos in oldgrid}


prev_grid = {}
current_grid = initial_grid
while current_grid != prev_grid:
    prev_grid = current_grid
    current_grid = step(current_grid)

part2 = sum(cell == "@" for cell in initial_grid.values()) - sum(
    cell == "@" for cell in current_grid.values()
)
print(f"{part2=}")
