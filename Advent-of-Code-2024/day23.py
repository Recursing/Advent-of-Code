from functools import cache

lines = open(__file__.replace(".py", ".txt")).read().strip().split("\n")

connections = [line.split("-") for line in lines]
hostnames = sorted(set(name for connection in connections for name in connection))
graph: dict[str, set[str]] = {hostname: set() for hostname in hostnames}
for a, b in connections:
    graph[a].add(b)
    graph[b].add(a)

three_sets: set[tuple[str, str, str]] = set()

for hostname in hostnames:
    for a in graph[hostname]:
        for b in graph[a]:
            if b in graph[hostname]:
                three_sets.add(tuple(sorted([hostname, a, b])))  # type: ignore

print(sum(any(h.startswith("t") for h in s) for s in three_sets))


@cache
def biggest_fully_connected_subgraph(
    required_nodes: frozenset[str],
) -> frozenset[str]:
    last_node = max(required_nodes)
    biggest = required_nodes
    for node in sorted(graph[last_node] - required_nodes):
        if graph[node] >= required_nodes:
            g = biggest_fully_connected_subgraph(required_nodes | {node})
            if len(g) > len(biggest):
                biggest = g
    return biggest


print(
    ",".join(
        sorted(
            max(
                (
                    biggest_fully_connected_subgraph(frozenset([hostname]))
                    for hostname in hostnames
                ),
                key=len,
            )
        )
    )
)
