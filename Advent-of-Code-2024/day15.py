text = open(__file__.replace(".py", ".txt")).read()
map_text, directions_text = text.split("\n\n")

type Grid = dict[complex, str]

original_grid: Grid = {
    x + y * 1j: c
    for y, line in enumerate(map_text.split("\n"))
    for x, c in enumerate(line)
}

directions: list[complex] = [
    {"<": -1, ">": 1, "^": -1j, "v": 1j}[d] for d in directions_text.replace("\n", "")
]


def find_robot(grid: Grid) -> complex:
    return next(pos for pos, c in grid.items() if c == "@")


def step(grid: Grid, direction: complex) -> Grid:
    pos = find_robot(grid)
    old_grid = grid
    new_grid = grid.copy()
    moving_obj = grid[pos]
    new_grid[pos] = "."
    assert moving_obj == "@"
    while True:
        new_pos = pos + direction
        moving_obj, new_grid[new_pos] = grid[new_pos], moving_obj

        if moving_obj == ".":
            return new_grid
        if moving_obj == "#":
            return old_grid
        pos = new_pos


def pprint(grid: Grid):
    min_x = int(min(p.real for p in grid))
    max_x = int(max(p.real for p in grid))
    min_y = int(min(p.imag for p in grid))
    max_y = int(max(p.imag for p in grid))
    print()
    for y in range(min_y, max_y + 1):
        print("".join(grid[x + y * 1j] for x in range(min_x, max_x + 1)))
    print()


grid = original_grid
for direction in directions:
    grid = step(grid, direction)
pprint(grid)

print(sum(100 * pos.imag + pos.real for pos, c in grid.items() if c == "O"))


def doubled_grid(grid: Grid) -> Grid:
    new_grid: Grid = {}
    for pos, c in grid.items():
        doubled = {
            "#": "##",
            "O": "[]",
            ".": "..",
            "@": "@.",
        }[c]
        new_grid[pos + pos.real], new_grid[pos + pos.real + 1] = doubled
    return new_grid


def step2(grid: Grid, direction: complex) -> Grid:
    if direction == 1 or direction == -1:
        return step(grid, direction)
    pos = find_robot(grid)
    frontier = [pos]
    old_grid = grid
    new_grid = grid.copy()
    new_grid[pos] = "."
    while frontier:
        pos = frontier.pop(0)
        new_pos = pos + direction
        next_block = new_grid[new_pos]
        if next_block == "#":
            return old_grid
        elif next_block == "[":
            if new_pos not in frontier:
                frontier.append(new_pos)
                assert grid[new_pos + 1] == "]"
                assert new_pos + 1 not in frontier
                frontier.append(new_pos + 1)
                if grid[pos + 1] != "]":
                    new_grid[new_pos + 1] = "."
        elif next_block == "]":
            if new_pos not in frontier:
                frontier.append(new_pos)
                assert grid[new_pos - 1] == "["
                assert new_pos - 1 not in frontier
                frontier.append(new_pos - 1)
                if grid[pos - 1] != "[":
                    new_grid[new_pos - 1] = "."
        else:
            assert next_block == "."
        new_grid[new_pos] = old_grid[pos]

    return new_grid


grid = doubled_grid(original_grid)
pprint(grid)

for i, direction in enumerate(directions):
    grid = step2(grid, direction)


pprint(grid)

print(sum(100 * pos.imag + pos.real for pos, c in grid.items() if c == "["))
