import re

lines = [l.strip() for l in open(__file__.replace(".py", ".txt"))]


def parse_card(line: str) -> tuple[set[str], set[str]]:
    _game_id, cards = line.split(": ")
    winning_numbers, numbers_you_have = cards.split(" | ")
    return set(re.findall(r"\d+", winning_numbers)), set(
        re.findall(r"\d+", numbers_you_have)
    )


def number_of_winning_numbers(line: str) -> int:
    winning_numbers, numbers_you_have = parse_card(line)
    return len(winning_numbers & numbers_you_have)


print(sum(2 ** (n - 1) for l in lines if (n := number_of_winning_numbers(l))))

multipliers = {i: 1 for i in range(len(lines))}

for i, l in enumerate(lines):
    for di in range(1, number_of_winning_numbers(l) + 1):
        multipliers[i + di] += multipliers[i]

print(sum(multipliers.values()))
