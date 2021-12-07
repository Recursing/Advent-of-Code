from statistics import mean, median

positions = list(map(int, open("day07.txt").read().split(",")))

median = int(median(positions))
print(sum(abs(p - median) for p in positions))


def sum_to_n(n: int) -> int:
    return (n * (n + 1)) // 2


mean1 = int(mean(positions))
mean2 = mean1 + 1
cost1 = sum(sum_to_n(abs(p - mean1)) for p in positions)
cost2 = sum(sum_to_n(abs(p - mean2)) for p in positions)
print(min(cost1, cost2))
