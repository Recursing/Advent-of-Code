from pathlib import Path

input_text = Path(__file__).with_suffix(".txt").read_text()
ranges_section, ids_section = input_text.split("\n\n")
ranges_str = [part.split("-") for part in ranges_section.split()]
ranges = [range(int(start), int(end) + 1) for start, end in ranges_str]
ids = [int(id_str) for id_str in ids_section.split()]


def is_fresh(value):
    return any(value in rng for rng in ranges)


part1 = sum(is_fresh(id_value) for id_value in ids)


ranges.sort(key=lambda r: r.start)


def compact(ranges: list[range]) -> list[range]:
    stack = [ranges[0]]
    for rng in ranges[1:]:
        top = stack[-1]
        if rng.start <= top.stop:
            stack[-1] = range(top.start, max(top.stop, rng.stop))
        else:
            stack.append(rng)
    return stack


ranges = compact(ranges)

part2 = sum(len(rng) for rng in ranges)

print(f"{part1=}")
print(f"{part2=}")
