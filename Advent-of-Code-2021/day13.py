from functools import reduce

input = open("day13.txt").read()

Points = frozenset[tuple[int, ...]]
points_input, fold_input = input.split("\n\n")
points: Points = frozenset(
    tuple(int(c) for c in p.split(",")) for p in points_input.splitlines(keepends=False)
)
folds = tuple(
    tuple(f.removeprefix("fold along ").split("="))
    for f in fold_input.splitlines(keepends=False)
)


def apply_fold(points: Points, fold: tuple[str, ...]) -> Points:
    direction = fold[0]
    axis = int(fold[1])
    coord = "xy".index(direction)
    new_points: set[tuple[int, ...]] = set()
    for point in points:
        new_point = list(point)
        if point[coord] > axis:
            new_point[coord] = 2 * axis - point[coord]
        new_points.add(tuple(new_point))

    return frozenset(new_points)


print(len(apply_fold(points, folds[0])))
final_points = reduce(apply_fold, folds, points)

max_x = max(x for x, _ in final_points)
max_y = max(y for _, y in final_points)

for y in range(max_y + 1):
    for x in range(max_x + 1):
        print("#" if (x, y) in final_points else " ", end="")
    print()
