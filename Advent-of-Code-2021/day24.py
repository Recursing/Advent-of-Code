import operator
from typing import Callable, Literal

import z3

Op = Literal["inp", "add", "mul", "div", "mod", "eql"]
VarName = Literal["x", "y", "z", "w"]
Instruction = tuple[Op, VarName] | tuple[Op, VarName, VarName | int]


def parse_instruction(input: str) -> Instruction:
    r = input.rstrip().split()
    if r[-1] not in "xyzw":
        r[-1] = int(r[-1])  # type: ignore
    return tuple(r)  # type: ignore


instructions = list(map(parse_instruction, open("day24.txt").readlines()))


def eval_z(instructions: list[Instruction], digits: list[int]) -> int:
    # I wanted to use this to auto-generate a z3 expression for z,
    # at least I get to use the match statement once

    getDigit = iter(digits).__next__
    variables: dict[str, int] = {l: 0 for l in "xyzw"}
    operators: dict[str, Callable[[int, int], int]] = {
        "add": operator.add,
        "mul": operator.mul,
        "div": operator.floordiv,
        "mod": operator.mod,
        "eql": operator.eq,
    }
    for op, *args in instructions:
        match op, args:
            case "inp", [target] if isinstance(target, str):
                variables[target] = getDigit()
            case op, [a, b] if op in operators and isinstance(a, str):
                if isinstance(b, str):
                    b = variables[b]
                variables[a] = operators[op](variables[a], b)
            case _:
                raise ValueError(f"Unknown instruction: {op=} {args=}")

    return variables["z"]


# Decompiled manually.
# Tried auto decompiling with the code above, but z3 was too slow
digits = tuple(z3.Int(f"d_{i}") for i in range(14))
domain: tuple[z3.BoolRef, ...] = tuple(z3.And(d > 0, d < 10) for d in digits)
getDigit = iter(digits).__next__

z = getDigit() + 14
w = getDigit()
z = z3.If((z % 26) + 14 != w, z * 26 + (w + 6), z)
w = getDigit()
z = z3.If((z % 26) + 15 != w, z * 26 + (w + 6), z)
w = getDigit()
z = z3.If((z % 26) + 13 != w, z * 26 + (w + 13), z)
w = getDigit()
old_z = z
z = z / 26
z = z3.If((old_z % 26) - 12 != w, z * 26 + (w + 8), z)
w = getDigit()
z = z3.If((z % 26) + 10 != w, z * 26 + (w + 8), z)
w = getDigit()
old_z = z
z = z / 26
z = z3.If(((old_z % 26) - 15) != w, z * 26 + (w + 7), z)
w = getDigit()
z = z3.If((z % 26) + 13 != w, z * 26 + (w + 10), z)
w = getDigit()
z = z3.If((z % 26) + 10 != w, z * 26 + (w + 8), z)
w = getDigit()
old_z = z
z = z / 26
z = z3.If((old_z % 26) - 13 != w, z * 26 + (w + 12), z)
w = getDigit()
old_z = z
z = z / 26
z = z3.If((old_z % 26) - 13 != w, z * 26 + (w + 10), z)
w = getDigit()
old_z = z
z = z / 26
z = z3.If((old_z % 26) - 14 != w, z * 26 + (w + 8), z)
w = getDigit()
old_z = z
z = z / 26
z = z3.If((old_z % 26) - 2 != w, z * 26 + (w + 8), z)
w = getDigit()
old_z = z
z = z / 26
z = z3.If((old_z % 26) - 9 != w, z * 26 + (w + 7), z)


def solve(part1: bool = True) -> list[int]:
    solver = z3.Solver()
    solver.add(*domain)
    solver.add(z == 0)
    code: list[int] = []
    digits_range = list(range(1, 10))
    if part1:
        digits_range = digits_range[::-1]
    for digit in digits:
        for value in digits_range:
            solver.push()
            solver.add(digit == value)
            if solver.check() == z3.sat:
                code.append(value)
                break
            else:
                solver.pop()

    return code


sol1 = solve(part1=True)
assert eval_z(instructions, sol1) == 0
sol2 = solve(part1=False)
assert eval_z(instructions, sol2) == 0
print("".join(map(str, sol1)))
print("".join(map(str, sol2)))
