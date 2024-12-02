lists = open("day02.txt").read().splitlines()
rows = [list(map(int, row.split())) for row in lists]


# Part 1
def is_safe(row):
    diffs = [a - b for a, b in zip(row, row[1:])]
    return all(0 < d <= 3 for d in diffs) or all(0 > d >= -3 for d in diffs)


print(sum(map(is_safe, rows)))


# Part 2
def almost_all(predicate, row):
    return bool(any(predicate(row[:i] + row[i + 1 :]) for i in range(len(row))))


print(sum(almost_all(is_safe, row) for row in rows))
