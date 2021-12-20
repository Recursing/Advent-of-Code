from itertools import product


algorithm, lines = open("day20.txt").read().split("\n\n")
algorithm = [c == "#" for c in algorithm]
image = lines.splitlines(keepends=False)
Points = dict[tuple[int, int], bool]
points: Points = {
    (y, x): c == "#" for y, row in enumerate(image) for x, c in enumerate(row)
}


def iterate(points: Points, default: bool) -> Points:
    new_points: Points = {}
    min_y = min(p[0] for p in points) - 2
    max_y = max(p[0] for p in points) + 2
    min_x = min(p[1] for p in points) - 2
    max_x = max(p[1] for p in points) + 2
    for (y, x) in product(range(min_y, max_y), range(min_x, max_x)):
        index = 0
        for dy, dx in product([-1, 0, 1], repeat=2):
            index = index * 2 + points.get((y + dy, x + dx), default)
        new_points[(y, x)] = algorithm[index]

    return new_points


for i in range(2):
    points = iterate(points, i % 2 == 1)

print(sum(points.values()))
for i in range(2, 50):
    points = iterate(points, i % 2 == 1)

print(sum(points.values()))
