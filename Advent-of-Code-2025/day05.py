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
    for idx, current in enumerate(ranges[:-1]):
        next_range = ranges[idx + 1]
        if current.stop in next_range or next_range.start in current:
            merged = range(current.start, max(current.stop, next_range.stop))
            return compact(ranges[:idx] + [merged] + ranges[idx + 2 :])
    return ranges


ranges = compact(ranges)

part2 = sum(len(rng) for rng in ranges)

print(f"{part1=}")
print(f"{part2=}")
