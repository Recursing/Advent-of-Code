from pathlib import Path

lines = Path(__file__).with_suffix(".txt").read_text().splitlines()
part1 = 0
part2 = 0


def maxsub(line: str, digits: int) -> str:
    assert len(line) >= digits, f"{line=} {digits=}"

    if digits == 1:
        return max(line)

    remaining_digits = digits - 1
    first_digit = max(line[:-remaining_digits])
    first_index = line.index(first_digit)

    return first_digit + maxsub(line[first_index + 1 :], remaining_digits)


for line in lines:
    assert len(line) > 12
    part1 += int(maxsub(line, 2))
    part2 += int(maxsub(line, 12))

print(f"{part1=}")
print(f"{part2=}")
