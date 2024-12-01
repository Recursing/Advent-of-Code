lists = open("day01.txt").read().splitlines()
pairs = [list(map(int, row.split())) for row in lists]
columns = list(zip(*pairs))

# Part 1
sorted_columns = [sorted(column) for column in columns]
print(sum(abs(a - b) for a, b in zip(*sorted_columns)))

# Part 2
from collections import Counter

occurrences_in_second_column = Counter(columns[1])
print(sum(a * occurrences_in_second_column[a] for a in columns[0]))
