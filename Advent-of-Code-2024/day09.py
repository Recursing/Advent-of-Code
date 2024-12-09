row = open(__file__.replace(".py", ".txt")).read().strip()
numbers = list(map(int, row))
if len(numbers) % 2 == 1:
    numbers.append(0)

# part 1
disk = []
file_id = 0
for file_len, empty_space in zip(numbers[0::2], numbers[1::2]):
    disk.extend([file_id] * file_len)
    disk.extend(["."] * empty_space)
    file_id += 1

first_empty_space = disk.index(".")
while disk[-1] == ".":
    disk.pop()
last_filled_space = len(disk) - 1

while first_empty_space < last_filled_space:
    disk[first_empty_space], disk[last_filled_space] = (
        disk[last_filled_space],
        disk[first_empty_space],
    )
    while disk[first_empty_space] != ".":
        first_empty_space += 1
    while disk[last_filled_space] == ".":
        last_filled_space -= 1

print(sum(val * i for i, val in enumerate(disk) if val != "."))

# part 2
ranges = []
file_id = 0
for file_len, empty_space in zip(numbers[0::2], numbers[1::2]):
    if file_len > 0:
        ranges.append((file_id, file_len))
    if empty_space > 0:
        ranges.append((".", empty_space))
    file_id += 1

last_unmoved_file_i = len(ranges)
while last_unmoved_file_i > 0:
    last_unmoved_file_i -= 1
    sector_type, sector_len = ranges[last_unmoved_file_i]
    if sector_type == ".":
        continue

    i2 = next(
        (
            j
            for j in range(last_unmoved_file_i)
            if ranges[j][0] == "." and ranges[j][1] >= sector_len
        ),
        None,
    )
    if i2 is None:
        continue
    empty_len = ranges[i2][1]
    assert empty_len >= sector_len
    ranges[i2] = (sector_type, sector_len)
    ranges[last_unmoved_file_i] = (".", sector_len)
    if empty_len > sector_len:
        ranges.insert(i2 + 1, (".", empty_len - sector_len))
        last_unmoved_file_i += 1

extended_ranges = [
    e for (sector_type, sector_len) in ranges for e in [sector_type] * sector_len
]
print(sum(val * i for i, val in enumerate(extended_ranges) if val != "."))
