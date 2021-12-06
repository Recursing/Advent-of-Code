from functools import cache

timers = map(int, open("day06.txt").read().split(","))


@cache
def offspring_size(first_due: int, day: int) -> int:
    fishes = 1
    for birthday in range(first_due, day, 7):
        fishes += offspring_size(9, day - birthday)
    return fishes


print(sum(offspring_size(first_due, 256) for first_due in timers))
