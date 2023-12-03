lines = open("day03.txt").readlines()
lines = ["." + line.strip() + "." for line in lines]
lines = ["." * len(lines[0])] + lines + ["." * len(lines[0])]


def issymbol(char):
    return not char.isdigit() and not char == "."


numbers = []
adj_symbols = set()
current_number = 0
for ri, line in enumerate(lines[1:-1], 1):
    for ci, char in enumerate(line[1:-1], 1):
        if char.isdigit():
            current_number = current_number * 10 + int(char)
            adj_symbols.update(
                (ri + dy, ci + dx)
                for dx, dy in (
                    (-1, -1),
                    (-1, 0),
                    (-1, 1),
                    (0, -1),
                    (0, 1),
                    (1, -1),
                    (1, 0),
                    (1, 1),
                )
                if issymbol(lines[ri + dy][ci + dx])
            )
        else:
            if current_number and adj_symbols:
                numbers.append((current_number, adj_symbols))
            current_number = 0
            adj_symbols = set()
print(numbers)
print(sum(n for n, _ in numbers))

numbers_close_to_star = {}
for number, adj_symbols in numbers:
    for ri, ci in adj_symbols:
        if lines[ri][ci] != "*":
            continue
        numbers_close_to_star[(ri, ci)] = numbers_close_to_star.get((ri, ci), []) + [
            number
        ]

print(sum(n[0] * n[1] for n in numbers_close_to_star.values() if len(n) == 2))
