from collections import deque

text = open(__file__.replace(".py", ".txt")).read()

type Grid = dict[complex, str]
type PosDir = tuple[complex, complex]

grid: Grid = {
    x + y * 1j: c for y, line in enumerate(text.split("\n")) for x, c in enumerate(line)
}

dirs = (1, -1, 1j, -1j)

min_costs: dict[PosDir, tuple[float, set[PosDir]]] = {
    (pos, direction): (float("inf"), set()) for pos in grid for direction in dirs
}


def find_char(grid: Grid, char: str) -> complex:
    return next(pos for pos, c in grid.items() if c == char)


start_pos = find_char(grid, "S")
for dir in dirs:
    min_costs[start_pos, dir] = 0, set()

east = 1 + 0j
frontier = deque([(start_pos, east)])
while frontier:
    current_pos, current_dir = frontier.popleft()
    current_cost, _ = min_costs[current_pos, current_dir]
    assert current_cost < float("inf")
    for next_dir, cost in (
        (current_dir, 1),
        (current_dir * 1j, 1001),
        (current_dir * -1j, 1001),
    ):
        next_pos = current_pos + next_dir
        if grid.get(next_pos, "#") not in "SE.":
            continue
        next_cost = current_cost + cost
        if min_costs[next_pos, next_dir][0] > next_cost:
            frontier.append((next_pos, next_dir))
            min_costs[next_pos, next_dir] = next_cost, {(current_pos, current_dir)}
        elif min_costs[next_pos, next_dir][0] == next_cost:
            min_costs[next_pos, next_dir][1].add((current_pos, current_dir))

end_pos = find_char(grid, "E")
end_dir = min(dirs, key=lambda dir: min_costs[end_pos, dir])
print(min_costs[end_pos, end_dir])

good_positions = {start_pos, end_pos}
frontier = deque([(end_pos, end_dir)])

while frontier:
    pos, dir = frontier.popleft()
    good_positions.add(pos)
    frontier.extend(min_costs[pos, dir][1])


print(len(good_positions))
