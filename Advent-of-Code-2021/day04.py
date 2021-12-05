import itertools
from collections import defaultdict

lines = open("day04.txt", "r").read().splitlines(keepends=False)
numbers = lines.pop(0).split(",")
lines.pop(0)
lines.append("")
tables: list[list[list[str]]] = []
current_table: list[list[str]] = []
for line in lines:
    if not line:
        tables.append(current_table)
        current_table = []
    else:
        current_table.append(line.split())

numbers_index: defaultdict[str, list[tuple[int, int, int]]] = defaultdict(list)
for table_i, table in enumerate(tables):
    for row, col in itertools.product(range(5), range(5)):
        numbers_index[table[row][col]].append((table_i, row, col))

winningNumber = None
losingNumber = None
uncalled_numbers_sum = None

won_tables: set[int] = set()
for number in numbers:
    for (table_i, row, col) in numbers_index[number]:
        if table_i in won_tables:
            continue
        table = tables[table_i]
        table[row][col] = ""
        if not (
            all(table[row][i] == "" for i in range(5))
            or all(table[i][col] == "" for i in range(5))
        ):
            continue
        won_tables.add(table_i)
        uncalled_numbers_sum = sum(int(n) for row in table for n in row if n)
        if winningNumber is None:
            winningNumber = int(number)
            print(winningNumber * uncalled_numbers_sum)
        losingNumber = int(number)

assert losingNumber is not None and uncalled_numbers_sum is not None
print(losingNumber * uncalled_numbers_sum)
