from typing import cast
import z3
import re

text = open(__file__.replace(".py", ".txt")).read()

numbers = [int(n) for n in re.findall(r"\d+", text)]
reg_a, reg_b, reg_c, *program = numbers

ip = 0
while True:
    if ip + 1 >= len(program):
        break
    opcode, operand = program[ip], program[ip + 1]
    ip += 2
    is_combo = opcode not in (1, 3, 4)
    if is_combo:
        assert operand in range(7)
        if operand == 4:
            operand = reg_a
        elif operand == 5:
            operand = reg_b
        elif operand == 6:
            operand = reg_c
    if opcode == 0:
        res = reg_a // (2**operand)
        reg_a = res
    if opcode == 1:
        reg_b = operand ^ reg_b
    if opcode == 2:
        reg_b = operand % 8
    if opcode == 3:
        assert operand == 0
        if reg_a != 0:
            ip = operand
    if opcode == 4:
        reg_b = reg_b ^ reg_c
    if opcode == 5:
        print(operand % 8, end=",")
        pass
    if opcode == 6:
        res = reg_a // (2**operand)
        reg_b = res
    if opcode == 7:
        res = reg_a // (2**operand)
        reg_c = res


reg_a, reg_b, reg_c, *program = numbers
print()

print("??", program)

ip = 0

reg_a = z3.BitVec("reg_a", 64)
assert reg_a is not None
type Number = int | z3.BitVecRef


def generate_z3_problem(
    reg_a: Number, reg_b: Number, reg_c: Number, ip: int, target_outputs: list[int]
) -> list[z3.BoolRef | bool]:
    constraints: list[z3.BoolRef | bool] = []
    assert reg_a is not None
    while True:
        if ip + 1 >= len(program):
            if len(target_outputs) > 0:
                return [False]
            return constraints
        opcode, operand = program[ip], cast(Number, program[ip + 1])
        ip += 2
        is_combo = opcode not in (1, 3, 4)
        if is_combo:
            if operand not in range(7):
                return [False]
            if operand == 4:
                operand = reg_a
            elif operand == 5:
                operand = reg_b
            elif operand == 6:
                operand = reg_c
        if opcode == 0:
            res = reg_a >> operand
            reg_a = res
        if opcode == 1:
            reg_b = operand ^ reg_b
        if opcode == 2:
            reg_b = operand % 8
        if opcode == 3:
            assert operand == 0
            return constraints + [
                z3.If(
                    reg_a != 0,
                    z3.And(
                        *generate_z3_problem(
                            reg_a, reg_b, reg_c, 0, list(target_outputs)
                        )
                    ),
                    len(target_outputs) == 0,
                )
            ]
        if opcode == 4:
            reg_b = reg_b ^ reg_c
        if opcode == 5:
            if isinstance(operand, int) and operand % 8 != target_outputs[0]:
                return [False]
            if isinstance(operand, z3.BitVecRef):
                if len(target_outputs) == 0:
                    return [False]
                else:
                    constraints.append(operand % 8 == target_outputs[0])
            if len(target_outputs) == 0:
                print(operand)
            target_outputs.pop(0)
        if opcode == 6:
            res = reg_a >> operand
            reg_b = res
        if opcode == 7:
            res = reg_a >> operand
            reg_c = res


z3_problem = generate_z3_problem(
    reg_a, reg_b, reg_c, 0, [2, 4, 1, 2, 7, 5, 4, 5, 0, 3, 1, 7, 5, 5, 3, 0]
)

solver = z3.Solver()
solver.add(z3_problem)
while solver.check() == z3.sat:
    model = solver.model()
    print(model[reg_a])
    solver.add(reg_a < model[reg_a])
