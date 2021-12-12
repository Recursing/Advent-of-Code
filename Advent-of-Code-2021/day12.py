from functools import cache
from collections import defaultdict

lines = open("day12.txt").read().splitlines(keepends=False)


graph: defaultdict[str, list[str]] = defaultdict(list)
for line in lines:
    a, b = line.split("-")
    assert a.islower() or b.islower()
    if a != "end" and b != "start":
        graph[a].append(b)
    if b != "end" and a != "start":
        graph[b].append(a)


@cache
def paths_from(
    node: str,
    visited: frozenset[str],
    has_visited_small_cave_twice: bool,
) -> int:
    paths = 0
    if node.islower():
        has_visited_small_cave_twice |= node in visited
        visited |= {node}
    for child in graph[node]:
        if child in visited and has_visited_small_cave_twice:
            continue
        if child == "end":
            paths += 1
            continue
        paths += paths_from(child, visited, has_visited_small_cave_twice)
    return paths


print(paths_from("start", frozenset(), True))
print(paths_from("start", frozenset(), False))
