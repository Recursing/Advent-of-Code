from dataclasses import dataclass

data = open(__file__.replace(".py", ".txt")).read().split("\n")
grid = {x + y * 1j: c for y, row in enumerate(data) for x, c in enumerate(row)}

type Side = set[tuple[complex, complex]]


@dataclass
class Region:
    points: set[complex]
    fences: int
    sides: list[Side]

    def __hash__(self) -> int:
        return id(self)


directions = (1, -1, 1j, -1j)


def cost(region: Region):
    return len(region.points) * (region.fences)


def add_side(point: complex, dir: complex, region: Region):
    matching_sides: list[Side] = []
    for side in region.sides:
        for other_point, other_dir in side:
            if abs(other_point - point) == 1 and dir == other_dir:
                matching_sides.append(side)

    if len(matching_sides) == 1:
        matching_sides[0].add((point, dir))
        return

    if len(matching_sides) == 0:
        region.sides.append({(point, dir)})
        return

    assert len(matching_sides) == 2

    new_side: Side = matching_sides[0] | matching_sides[1] | {(point, dir)}

    region.sides = [s for s in region.sides if s not in matching_sides]
    region.sides.append(new_side)


seen: set[complex] = set()
regions: list[Region] = []


def explore(point: complex):
    region = Region(set(), 0, [])
    regions.append(region)
    frontier = [point]
    while frontier:
        point = frontier.pop()
        region.points.add(point)
        seen.add(point)
        for d in directions:
            n = point + d
            if grid.get(n) == grid[point]:
                if n not in seen and n not in frontier:
                    frontier.append(n)
            else:
                region.fences += 1
                add_side(point, d, region)


for point in grid:
    if point not in seen:
        explore(point)

print(sum(map(cost, regions)))


def cost2(region: Region):
    return len(region.points) * len(region.sides)


print(sum(map(cost2, regions)))
