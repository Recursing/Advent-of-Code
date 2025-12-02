lines = open("day01.txt").read().splitlines()
position = 50
part1 = 0
part2 = 0
for line in lines:
    direction, *digits = line.strip()
    number = int("".join(digits))
    if direction == "R":
        position += number
    elif direction == "L":
        if position == 0:
            position = 100
        position -= number
    else:
        raise Exception("Invalid direction: " + direction)

    while position < 0:
        part2 += 1
        position += 100

    while position > 100:
        part2 += 1
        position -= 100

    position %= 100
    if position == 0:
        part1 += 1
        part2 += 1


print(f"{part1=}")
print(f"{part2=}")
