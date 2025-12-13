# /// script
# requires-python = ">=3.13"
# dependencies = [
#     "z3-solver>=4.15.4.0",
# ]
# ///
from collections import deque
from pathlib import Path
from typing import NamedTuple

import z3

lines = Path(__file__).with_suffix(".txt").read_text().splitlines()

Button = tuple[int, ...]
State = tuple[bool, ...]


class Machine(NamedTuple):
    state: State
    goal: State
    buttons: tuple[Button, ...]
    joltage_goal: tuple[int, ...]


def parse_line(line: str) -> Machine:
    goal, *buttons, jolts = line.split()
    assert goal.startswith("[") and goal.endswith("]")
    target = tuple(c == "#" for c in goal[1:-1])

    for button in buttons:
        assert button.startswith("(") and button.endswith(")")
    parsed_buttons = tuple(
        tuple(int(i) for i in button[1:-1].split(",")) for button in buttons
    )

    assert jolts.startswith("{") and jolts.endswith("}")
    joltages = tuple(int(i) for i in jolts[1:-1].split(","))

    return Machine(
        state=(False,) * len(target),
        goal=target,
        buttons=parsed_buttons,
        joltage_goal=joltages,
    )


machines = [parse_line(line) for line in lines]


def solve_part_1(machine: Machine) -> int:
    descendants = deque([machine.state])
    depths = {machine.state: 0}

    while descendants:
        state = descendants.popleft()
        depth = depths[state]
        for button in machine.buttons:
            next_state = tuple(
                not cell if i in button else cell for i, cell in enumerate(state)
            )
            if next_state == machine.goal:
                return depth + 1
            if next_state not in depths:
                descendants.append(next_state)
                depths[next_state] = depth + 1

    raise Exception("No solution found")


def solve_part_2(machine: Machine) -> int:
    position_contributors: list[list[z3.ArithRef]] = [[] for _ in machine.joltage_goal]
    constraints = []
    button_presses = []

    for i, button in enumerate(machine.buttons):
        presses = z3.Int(f"button_{i}")
        for j in button:
            position_contributors[j].append(presses)
        constraints.append(presses >= 0)
        button_presses.append(presses)

    for target, contributors in zip(
        machine.joltage_goal, position_contributors, strict=True
    ):
        constraints.append(target == sum(contributors))

    solver = z3.Optimize()
    solver.add(constraints)
    minimum = solver.minimize(sum(button_presses))
    assert solver.check() == z3.sat

    return minimum.value().as_long()  # pyright: ignore[reportAttributeAccessIssue]


print(sum(solve_part_1(m) for m in machines))
print(sum(solve_part_2(m) for m in machines))
