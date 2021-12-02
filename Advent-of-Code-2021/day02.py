pairs = list(map(str.split, open("day02.txt").readlines()))
horizontal, depth = 0, 0
for direction, amount in pairs:
    amount = int(amount)
    if direction == "forward":
        horizontal += amount
    elif direction == "up":
        depth -= amount
    elif direction == "down":
        depth += amount
print(horizontal * depth)

horizontal, depth, aim = 0, 0, 0
for direction, amount in pairs:
    amount = int(amount)
    if direction == "forward":
        horizontal += amount
        depth += aim * amount
    elif direction == "up":
        aim -= amount
    elif direction == "down":
        aim += amount
print(horizontal * depth)


# Cool part1 solution from reddit
pos = sum({"f": 1, "d": 1j, "u": -1j}[d[0][0]] * int(d[1]) for d in pairs)
print(pos.real * pos.imag)