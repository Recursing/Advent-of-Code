import re
from itertools import product
from collections import defaultdict
from graphlib import TopologicalSorter


def to_ints(lines):
    return [[int(s) for s in line] for line in lines]


text = open(__file__.replace(".py", ".txt")).read()

first_part, second_part = text.split("\n\n")
page_numbers = to_ints(line.split("|") for line in first_part.splitlines())
requirements = defaultdict(set)
for requirement, page_number in page_numbers:
    requirements[page_number].add(requirement)


updates = to_ints(line.split(",") for line in second_part.splitlines())
part1 = 0
part2 = 0

for update in updates:
    pages = update.copy()
    while pages:
        last_page_number = pages.pop()
        remaining_pages = set(pages)
        if remaining_pages - requirements[last_page_number]:
            requirements_subset = {
                page_number: requirements[page_number] & set(update)
                for page_number in update
            }
            ordered = tuple(TopologicalSorter(requirements_subset).static_order())
            part2 += ordered[len(ordered) // 2]
            break
    else:
        part1 += update[len(update) // 2]
print(part1)
print(part2)
