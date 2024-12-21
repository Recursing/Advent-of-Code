from collections import deque


text = open(__file__.replace(".py", ".txt")).read()
pairs = [[int(a) for a in line.split(",")] for line in text.split("\n") if line]
max_x = 70
max_y = 70
type Grid = dict[complex, str]

grid: Grid = {x + 1j * y: "." for y in range(max_y + 1) for x in range(max_x + 1)}


def solve(grid: Grid) -> dict[complex, complex] | None:
    directions = (1, -1, 1j, -1j)
    frontier = deque([0 + 0j])
    predecessors: dict[complex, complex] = {}
    pos = 0
    while frontier:
        pos = frontier.popleft()
        if pos == max_x + max_y * 1j:
            return predecessors
        for direction in directions:
            new_pos = pos + direction
            if grid.get(new_pos, "#") == "." and new_pos not in predecessors:
                frontier.append(new_pos)
                predecessors[new_pos] = pos

    return None


for i, (x, y) in enumerate(pairs):
    grid[x + 1j * y] = "#"
    if i < 1023:
        continue
    predecessors = solve(grid)
    if predecessors is None:
        print("Part 2:", i, f"{x},{y}")
        break
    if i == 1023:
        pos = max_x + max_y * 1j
        path: list[complex] = []
        while pos != 0:
            path.append(pos)
            pos = predecessors[pos]

        print("Part 1:", len(path))
