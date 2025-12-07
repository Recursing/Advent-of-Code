from pathlib import Path
from functools import cache

lines = Path(__file__).with_suffix(".txt").read_text().splitlines()


def replace_at(s: str, i: int, c: str) -> str:
    return s[:i] + c + s[i + 1 :]


def step(prev_line: str, cur_line: str) -> tuple[str, int]:
    beams_indexes = {i for i, c in enumerate(prev_line) if c in "|S"}
    num_splits = sum(cur_line[i] == "^" for i in beams_indexes)

    new_line = "".join(
        "|"
        if c == "."
        and (
            i in beams_indexes
            or ((i + 1) in beams_indexes and cur_line[i + 1] == "^")
            or ((i - 1) in beams_indexes and cur_line[i - 1] == "^")
        )
        else c
        for i, c in enumerate(cur_line)
    )
    return new_line, num_splits


part1 = 0
prev_line = lines[0]
for cur_line in lines[1:]:
    prev_line, num_splits = step(prev_line, cur_line)
    part1 += num_splits


@cache
def part2(remaining_lines: tuple[str, ...]) -> int:
    if len(remaining_lines) == 1:
        return 1

    top_line, next_line, *rest = remaining_lines
    top_line = top_line.replace("S", "|")
    assert top_line.count("|") == 1
    beam_index = top_line.find("|")
    rest = tuple(rest)

    if next_line[beam_index] == ".":
        return part2((replace_at(next_line, beam_index, "|"),) + rest)

    return part2((replace_at(next_line, beam_index - 1, "|"),) + rest) + part2(
        (replace_at(next_line, beam_index + 1, "|"),) + rest
    )


print(f"{part1=}")
print(f"{part2(tuple(lines))=}")
