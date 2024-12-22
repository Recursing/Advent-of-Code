from collections import Counter, deque


text = open(__file__.replace(".py", ".txt")).read()

type Grid = dict[complex, str]

grid: Grid = {
    x + y * 1j: c for y, line in enumerate(text.split("\n")) for x, c in enumerate(line)
}


def find_char(grid: Grid, char: str) -> complex:
    return next(pos for pos, c in grid.items() if c == char)


def pprint(grid: Grid):
    min_x = int(min(p.real for p in grid))
    max_x = int(max(p.real for p in grid))
    min_y = int(min(p.imag for p in grid))
    max_y = int(max(p.imag for p in grid))
    print()
    for y in range(min_y, max_y + 1):
        print("".join(grid[x + y * 1j] for x in range(min_x, max_x + 1)))
    print()


start_pos = find_char(grid, "S")
end_pos = find_char(grid, "E")

frontier = deque([end_pos])
min_costs = {pos: float("inf") for pos in grid}
min_costs[end_pos] = 0
while frontier:
    pos = frontier.popleft()
    for dir in (1, -1, 1j, -1j):
        next_pos = pos + dir
        if grid.get(next_pos, "#") not in "SE.":
            continue
        if min_costs[next_pos] == float("inf"):
            min_costs[next_pos] = min_costs[pos] + 1
            frontier.append(next_pos)

print(min_costs[start_pos])

frontier = deque([start_pos])
visited = {start_pos}
shortcuts: set[tuple[complex, complex]] = set()
while frontier:
    pos = frontier.pop()
    for dir in (1, -1, 1j, -1j):
        next_pos = pos + dir
        if grid.get(next_pos, "#") in "E." and next_pos not in visited:
            frontier.append(next_pos)
            visited.add(next_pos)
        if grid.get(next_pos, "/") == "#":
            for dir2 in (1, -1, 1j, -1j):
                if grid.get(next_pos + dir2, "#") in "E.":
                    shortcuts.add((pos, next_pos + dir2))

saves = Counter(
    min_costs[a] - min_costs[b] - 2
    for a, b in shortcuts
    if min_costs[b] < min_costs[a] - 2
)

print(sum(v for k, v in saves.items() if k >= 100))


def man_dist(a: complex, b: complex) -> int:
    diff = a - b
    return int(abs(diff.real) + abs(diff.imag))


frontier = deque([start_pos])
visited = {start_pos}
shortcuts: set[tuple[complex, complex]] = set()
print()
i = 0
while frontier:
    i += 1
    if (i % 200) == 0:
        print(f"\033[F\033[K{i/min_costs[start_pos]:.0%}")
    pos = frontier.pop()
    for dir in (1, -1, 1j, -1j):
        next_pos = pos + dir
        if grid.get(next_pos, "#") in "E." and next_pos not in visited:
            frontier.append(next_pos)
            visited.add(next_pos)
    for dx in range(-21, 21):
        for dy in range(-21, 21):
            if dx == dy == 0:
                continue
            short_cut_end = pos + dx + dy * 1j
            if (
                man_dist(short_cut_end, pos) <= 20
                and grid.get(short_cut_end, "#") in "E."
            ):
                shortcuts.add((pos, short_cut_end))

saves = Counter(
    min_costs[a] - min_costs[b] - man_dist(a, b)
    for a, b in shortcuts
    if min_costs[b] < min_costs[a] - man_dist(a, b)
)
# 1046766 too high
# 1005864 too low
print(sum(v for k, v in saves.items() if k >= 100))
