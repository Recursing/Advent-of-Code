from itertools import combinations, permutations, product


scanners_input = open("day19.txt").read().split("\n\n")
Vec3 = tuple[int, int, int]


def parse_point(string: str) -> Vec3:
    x, y, z = string.split(",")
    return (int(x), int(y), int(z))


scanners: list[list[tuple[int, int, int]]] = [
    [parse_point(line) for line in scanner.splitlines(keepends=False)[1:]]
    for scanner in scanners_input
]


def add(p1: Vec3, p2: Vec3) -> Vec3:
    x1, y1, z1 = p1
    x2, y2, z2 = p2
    return x1 + x2, y1 + y2, z1 + z2


def sub(p1: Vec3, p2: Vec3) -> Vec3:
    x1, y1, z1 = p1
    x2, y2, z2 = p2
    return x1 - x2, y1 - y2, z1 - z2


def rotated_positions(positions: list[Vec3]) -> list[list[Vec3]]:
    res: list[list[Vec3]] = []
    for ix, iy, iz in permutations([0, 1, 2]):
        for signx, signy, signz in product([1, -1], repeat=3):
            res.append(
                [
                    (point[ix] * signx, point[iy] * signy, point[iz] * signz)
                    for point in positions
                ]
            )
    return res


def internal_distances(positions: list[Vec3]):
    diffs: dict[Vec3, Vec3] = {}
    for a, b in combinations(positions, r=2):
        diffs[sub(a, b)] = a
        diffs[sub(b, a)] = b
    return diffs


scanner_rotated_positions = [rotated_positions(positions) for positions in scanners]

scanner_distances = [
    [internal_distances(positions) for positions in position_rotations]
    for position_rotations in scanner_rotated_positions
]

frontier = [0]
seen: set[int] = set()
scanner_locations: list[Vec3] = []
scanner_indexes = set(range(len(scanners)))
while frontier:
    i1 = frontier.pop()
    diffs1 = scanner_distances[i1][0]
    seen.add(i1)
    for i2 in scanner_indexes - seen:
        for diffs2 in scanner_distances[i2]:
            common_diffs = set(diffs1) & set(diffs2)
            if len(common_diffs) < 12 * 11:
                continue
            common_diff = common_diffs.pop()
            delta = sub(diffs2[common_diff], diffs1[common_diff])
            if not all(
                sub(diffs2[common_diff], diffs1[common_diff]) == delta
                for common_diff in common_diffs
            ):
                continue
            scanner_locations.append(delta)
            diffs2 = {d: sub(p, delta) for d, p in diffs2.items()}
            assert len(set(diffs2.values()) & set(diffs1.values())) >= 12
            frontier.append(i2)
            scanner_distances[i2] = [diffs2]
            break

print(len(set(p for rd in scanner_distances for p in rd[0].values())))


def length(v: Vec3) -> int:
    return sum(map(abs, v))


print(max(length(sub(v1, v2)) for v1, v2 in combinations(scanner_locations, r=2)))
