from collections import deque
from functools import cache

timers = list(map(int, open("day06.txt").read().split(",")))


@cache
def offspring_size(first_due: int, day: int) -> int:
    fishes = 1
    for birthday in range(first_due, day, 7):
        fishes += offspring_size(9, day - birthday)
    return fishes


print(sum(offspring_size(first_due, 80) for first_due in timers))
print(sum(offspring_size(first_due, 256) for first_due in timers))


def alternative_solution(nums: list[int], days: int = 256) -> int:
    fish_groups = deque(nums.count(i) for i in range(9))
    for _ in range(days):
        fish_groups[7] += fish_groups[0]
        fish_groups.rotate(-1)
    return sum(fish_groups)


assert alternative_solution(timers, 80) == 350149
assert alternative_solution(timers, 256) == 1590327954513
