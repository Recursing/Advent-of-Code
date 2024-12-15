from functools import cache
from typing import NamedTuple
import re
import z3

text = open(__file__.replace(".py", ".txt")).read()
machines_text = text.split("\n\n")


class Machine(NamedTuple):
    button_a: complex
    button_b: complex
    prize: complex

    @classmethod
    def from_text(cls, text: str):
        return Machine(
            *(complex(*map(int, re.findall(r"\d+", l))) for l in text.split("\n"))
        )

    @classmethod
    @cache
    def cost(cls, machine: "Machine") -> float:
        btn_a, btn_b, prize = machine
        if prize == 0:
            return 0
        if prize.imag < 0 or prize.real < 0:
            return float("inf")
        cost_a = Machine.cost(Machine(btn_a, btn_b, prize - btn_a)) + 3
        cost_b = Machine.cost(Machine(btn_a, btn_b, prize - btn_b)) + 1
        return min(cost_a, cost_b)

    @property
    def cost2(self) -> float:
        btn_a, btn_b, prize = self
        btn_a_x = btn_a.real
        btn_a_y = btn_a.imag
        btn_b_x = btn_b.real
        btn_b_y = btn_b.imag
        prize_x = prize.real + 10000000000000
        prize_y = prize.imag + 10000000000000
        a_presses = z3.Int("A")
        b_presses = z3.Int("B")
        solver = z3.Solver()
        solver.add(
            a_presses * btn_a_x + b_presses * btn_b_x == prize_x,
        )
        solver.add(
            a_presses * btn_a_y + b_presses * btn_b_y == prize_y,
        )

        if solver.check() == z3.unsat:
            return 0

        model = solver.model()
        solution = model[a_presses].as_long() * 3 + model[b_presses].as_long()

        # Check that there are no other solutions (i.e. aligned vectors)
        solver.add(z3.Or([variable() != model[variable] for variable in model]))
        assert solver.check() == z3.unsat

        return solution


machines = [Machine.from_text(m) for m in machines_text]
print(machines[0], Machine.cost(machines[0]))
print(sum(Machine.cost(m) for m in machines if Machine.cost(m) != float("inf")))
print(sum(m.cost2 for m in machines))
