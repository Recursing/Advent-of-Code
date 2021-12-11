import math

heightmap = open("day09.txt").read().splitlines(keepends=False)
heightmap = [[int(c) for c in row] for row in heightmap]

HEIGHT = len(heightmap)
WIDTH = len(heightmap[0])


def neighbors(y: int, x: int) -> list[tuple[int, int]]:
    return [
        (y + dy, x + dx)
        for dy, dx in ((-1, 0), (1, 0), (0, -1), (0, 1))
        if 0 <= y + dy < HEIGHT and 0 <= x + dx < WIDTH
    ]


low_points = [
    (y, x)
    for y, row in enumerate(heightmap)
    for x, cell in enumerate(row)
    if all(heightmap[ny][nx] > cell for ny, nx in neighbors(y, x))
]


print(sum(heightmap[y][x] + 1 for y, x in low_points))


def basin_size(start_location: tuple[int, int]) -> int:
    explored = {start_location}
    frontier = [start_location]
    while frontier:
        y, x = frontier.pop()
        value = heightmap[y][x]
        for neighbor in neighbors(y, x):
            ny, nx = neighbor
            if heightmap[ny][nx] == 9 or heightmap[ny][nx] < value:
                continue
            if neighbor not in explored:
                frontier.append(neighbor)
                explored.add(neighbor)
    return len(explored)


basin_sizes = sorted(map(basin_size, low_points), reverse=True)
print(math.prod(basin_sizes[:3]))
