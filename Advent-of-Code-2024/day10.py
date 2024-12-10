grid = open(__file__.replace(".py", ".txt")).read().split("\n")
grid = {x + y * 1j: int(c) for y, row in enumerate(grid) for x, c in enumerate(row)}
directions = (1, -1, 1j, -1j)


def score(position, start=0):
    if grid.get(position) != start:
        return set()
    if start == 9:
        return {position}
    return set.union(*(score(position + direction, start + 1) for direction in directions))


print(sum(len(score(position)) for position in grid))


def score_2(position, start=0):
    if grid.get(position) != start:
        return 0
    if start == 9:
        return 1
    return sum((score_2(position + direction, start + 1) for direction in directions))

print(sum(score_2(position) for position in grid))