from functools import cache
from collections import Counter

input = open("day14.txt").read()

start, rules_text = input.split("\n\n")
rules = dict(rule.split(" -> ") for rule in rules_text.splitlines(keepends=False))


@cache
def total_letters(pair: str, turns: int = 0) -> Counter[str]:
    counter: Counter[str] = Counter()
    if turns == 0:
        return counter
    middle_letter = rules.get(pair)
    if middle_letter is None:
        return counter
    counter[middle_letter] += 1
    return (
        counter
        + total_letters(pair[0] + middle_letter, turns - 1)
        + total_letters(middle_letter + pair[1], turns - 1)
    )


part_1 = sum(
    (total_letters(a + b, 10) for a, b in zip(start, start[1:])), Counter(start)
)
print(max(part_1.values()) - min(part_1.values()))
part_2 = sum(
    (total_letters(a + b, 40) for a, b in zip(start, start[1:])), Counter(start)
)
print(max(part_2.values()) - min(part_2.values()))
