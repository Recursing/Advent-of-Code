import z3

input_lines = open("day08.txt").read().splitlines(keepends=False)


def parse_line(line: str) -> tuple[list[str], list[str]]:
    input, output = line.split(" | ")
    return input.split(), output.split()


input_lines = list(map(parse_line, input_lines))

print(sum(len(digit) in {2, 3, 4, 7} for _, output in input_lines for digit in output))

positions_for_number: dict[int, tuple[int, ...]] = {
    0: (0, 1, 2, 4, 5, 6),
    1: (2, 5),
    2: (0, 2, 3, 4, 6),
    3: (0, 2, 3, 5, 6),
    4: (1, 2, 3, 5),
    5: (0, 1, 3, 5, 6),
    6: (0, 1, 3, 4, 5, 6),
    7: (0, 2, 5),
    8: (0, 1, 2, 3, 4, 5, 6),
    9: (0, 1, 2, 3, 5, 6),
}
number_from_positions = {frozenset(v): k for k, v in positions_for_number.items()}


numbers_by_size: dict[int, list[int]] = {}
for number, p in positions_for_number.items():
    numbers_by_size.setdefault(len(p), []).append(number)


def observation(letters: str, position_variables: dict[str, z3.ArithRef]) -> z3.BoolRef:
    possibilities: list[z3.BoolRef] = []
    for number in numbers_by_size[len(letters)]:
        possibilities.append(
            z3.And(
                *(
                    z3.Or(
                        *(
                            position_variables[l] == p
                            for p in positions_for_number[number]
                        )
                    )
                    for l in letters
                )
            )
        )

    return z3.Or(*possibilities)


def solve(solver: z3.Solver, input: list[str], output: list[str]) -> int:
    solver.push()
    constraints = [
        observation(letters, position_variables) for letters in input + output
    ]
    solver.add(*constraints)
    assert solver.check() == z3.sat, solver.check()
    model = solver.model()

    def get_position(letter: str) -> int:
        return model[position_variables[letter]].as_long()

    number = 0
    for letters in output:
        active_positions = frozenset(map(get_position, letters))
        number = number * 10 + number_from_positions[active_positions]
    solver.pop()
    return number


solver = z3.Solver()
position_variables = {letter: z3.Int(letter) for letter in "abcdefg"}
domain = z3.And(*[z3.And(0 <= p, p < 7) for p in position_variables.values()])
distinct = z3.Distinct(*position_variables.values())
solver.add(domain)
solver.add(distinct)
print(sum(solve(solver, input, output) for input, output in input_lines))
