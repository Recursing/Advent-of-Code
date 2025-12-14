from collections import defaultdict, deque
from functools import cache
from pathlib import Path


lines = Path(__file__).with_suffix(".txt").read_text().splitlines()


def parse_line(line: str) -> tuple[str, tuple[str, ...]]:
    source, *targets = line.split()
    assert source.endswith(":")
    return (source[:-1], tuple(targets))


connections = dict(parse_line(line) for line in lines)
parents = defaultdict(list)

for source, dests in connections.items():
    for dest in dests:
        parents[dest].append(source)


@cache
def solve(source: str, target: str) -> int:
    if source == target:
        return 1
    return sum(solve(source, parent) for parent in parents[target])


print(solve(source="you", target="out"))
assert solve(source="dac", target="fft") == 0
print(
    solve(source="svr", target="fft")
    * solve(source="fft", target="dac")
    * solve(source="dac", target="out")
)
