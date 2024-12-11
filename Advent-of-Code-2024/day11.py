from math import log10
from functools import cache

numbers = open(__file__.replace(".py", ".txt")).read().split()


def children(n: int) -> tuple[int] | tuple[int, int]:
    if n == 0:
        return (n + 1,)
    num_digits = int(log10(n) + 1)
    if num_digits % 2 == 0:
        a, b = divmod(n, 10 ** (num_digits // 2))
        return a, b
    return (n * 2024,)


@cache
def stone_descendents_length(n: int, steps: int) -> int:
    if steps == 0:
        return 1
    return sum(stone_descendents_length(child, steps - 1) for child in children(n))


print(sum(stone_descendents_length(int(stone), 25) for stone in numbers))
print(sum(stone_descendents_length(int(stone), 75) for stone in numbers))
