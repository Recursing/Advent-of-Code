import heapq

grid = [[int(c) for c in row.strip()] for row in open("day15.txt").readlines()]


def solve(grid: list[list[int]]) -> int:
    distances = [[2 ** 31 for _ in row] for row in grid]
    distances[0][0] = 0
    HEIGHT = len(grid)
    WIDTH = len(grid[0])

    def neighbors(y: int, x: int) -> list[tuple[int, int]]:
        return [
            (y + dy, x + dx)
            for dy, dx in ((-1, 0), (1, 0), (0, -1), (0, 1))
            if 0 <= y + dy < HEIGHT and 0 <= x + dx < WIDTH
        ]

    frontier = [(0, (0, 0))]
    while frontier:
        cost, (y, x) = heapq.heappop(frontier)
        for (ny, nx) in neighbors(y, x):
            if distances[ny][nx] > grid[ny][nx] + cost:
                new_cost = grid[ny][nx] + cost
                distances[ny][nx] = new_cost
                heapq.heappush(frontier, (new_cost, (ny, nx)))
    return distances[HEIGHT - 1][WIDTH - 1]


print(solve(grid))

big_grid = [
    [(c + i + j - 1) % 9 + 1 for j in range(5) for c in row]
    for i in range(5)
    for row in grid
]
print(solve(big_grid))
