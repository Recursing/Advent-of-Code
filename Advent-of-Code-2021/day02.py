lines = list(map(str.split, open("day02.txt").readlines()))
horizontal, depth = 0, 0
for direction, amount in lines:
    amount = int(amount)
    if direction == "forward":
        horizontal += amount
    elif direction == "up":
        depth -= amount
    elif direction == "down":
        depth += amount
print(horizontal * depth)

horizontal, depth, aim = 0, 0, 0
for direction, amount in lines:
    amount = int(amount)
    if direction == "forward":
        horizontal += amount
        depth += aim * amount
    elif direction == "up":
        aim -= amount
    elif direction == "down":
        aim += amount
print(horizontal * depth)