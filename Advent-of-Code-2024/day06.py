lines = open(__file__.replace(".py", ".txt")).readlines()


lines = [line.strip() for line in lines]
direction = 0 - 1j
grid = {}
for i, row in enumerate(lines):
    for j, char in enumerate(row):
        if char == "^":
            position = j + i * 1j
        grid[j + i * 1j] = char

initial_position = position
positions = {position}
part2 = set()
while grid.get(position + direction):
    while grid.get(position + direction) == "#":
        direction *= 1j
    position += direction

    # Part 2
    if (
        (position != initial_position)
        and grid.get(position)
        and (position) not in positions
    ):
        test_position = position - direction
        test_direction = direction
        grid[position] = "#"
        test_loop = set()
        while grid.get(test_position + test_direction):
            if (test_position, test_direction) in test_loop:
                part2.add(position)
                break
            test_loop.add((test_position, test_direction))
            while grid.get(test_position + test_direction) == "#":
                test_direction *= 1j
            test_position += test_direction
        grid[position] = "."

    positions.add(position)


print(len(positions))
print(len(part2))
