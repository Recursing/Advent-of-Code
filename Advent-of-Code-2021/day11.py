import copy

energy_map = """5483143223
2745854711
5264556173
6141336146
6357385478
4167524645
2176841721
6882881134
4846848554
5283751526""".splitlines(
    keepends=False
)
energy_map = open("day11.txt").read().splitlines(keepends=False)
energy_map = [[int(c) for c in row] for row in energy_map]

HEIGHT = len(energy_map)
WIDTH = len(energy_map[0])


def neighbors(y: int, x: int) -> list[tuple[int, int]]:
    return [
        (y + dy, x + dx)
        for dy, dx in (
            (-1, -1),
            (-1, 0),
            (-1, 1),
            (0, -1),
            (0, 1),
            (1, -1),
            (1, 0),
            (1, 1),
        )
        if 0 <= y + dy < HEIGHT and 0 <= x + dx < WIDTH
    ]


def step(energy_map: list[list[int]]) -> int:
    flashers: set[tuple[int, int]] = set()
    for y, row in enumerate(energy_map):
        for x, _ in enumerate(row):
            energy_map[y][x] += 1
            if energy_map[y][x] > 9:
                flashers.add((y, x))

    flashed: set[tuple[int, int]] = set()
    while flashers:
        y, x = flashers.pop()
        for ny, nx in neighbors(y, x):
            energy_map[ny][nx] += 1
            if energy_map[ny][nx] > 9 and (ny, nx) not in (flashers | flashed):
                flashers.add((ny, nx))
        flashed.add((y, x))

    for y, x in flashed:
        energy_map[y][x] = 0
    return len(flashed)


part_1_map = copy.deepcopy(energy_map)
print(sum(step(part_1_map) for _ in range(100)))

for step_num in range(1, 100_000):
    if step(energy_map) == 100:
        print(step_num)
        break
