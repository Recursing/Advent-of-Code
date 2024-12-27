import z3

initial_values_text, connections_text = open("day24.txt").read().split("\n\n")

x, y, z = z3.BitVecs("x y z", 46)


variables: dict[str, z3.BitVecRef] = {}


def get_variable(name: str) -> z3.BitVecRef:
    if name in variables:
        return variables[name]
    if name[0] in "xyz":
        number = int(name[1:])
    if name[0] == "x":
        var = z3.Extract(number, number, x)
    elif name[0] == "y":
        var = z3.Extract(number, number, y)
    elif name[0] == "z":
        var = z3.Extract(number, number, z)
    else:
        var = z3.BitVec(name, 1)
    variables[name] = var
    return var


input_constraints: list[z3.BoolRef] = []
for line in initial_values_text.split("\n"):
    key, val = line.split(": ")
    input_constraints.append(get_variable(key) == int(val))

target_constraints: dict[z3.BitVecRef, z3.BitVecRef] = {}
ancestors: dict[str, set[str]] = {}
for line in connections_text.split("\n"):
    input1_name, operator, input_2_name, arrow, target_var_name = line.split()
    a, b, target = map(get_variable, (input1_name, input_2_name, target_var_name))
    ancestors[target_var_name] = ancestors.get(target_var_name, set()) | {
        input1_name,
        input_2_name,
    }
    if operator == "AND":
        target_constraints[target] = a & b
    elif operator == "OR":
        target_constraints[target] = a | b
    elif operator == "XOR":
        target_constraints[target] = a ^ b
    else:
        raise Exception(f"Unknown operator {operator}")

solver = z3.Solver()
solver.add(input_constraints)
solver.add([k == v for k, v in target_constraints.items()])
assert solver.check() == z3.sat
model = solver.model()
print(model[z])


def get_all_ancestors(var_name: str) -> set[str]:
    return ancestors.get(var_name, set()).union(
        *(get_all_ancestors(a) for a in ancestors.get(var_name, set()))
    )


variables_swapped: list[str] = []
for bit_number in range(46):
    solver = z3.Solver()
    solver.add([k == v for k, v in target_constraints.items()])
    solver.add(z3.Extract(45, 45, x) == 0)
    solver.add(z3.Extract(45, 45, y) == 0)
    solver.add(
        z3.Extract(bit_number, bit_number, (x + y))
        != z3.Extract(bit_number, bit_number, z)
    )

    if solver.check() == z3.sat:
        assert bit_number > 0
        safe_variable_names = get_all_ancestors(f"z{bit_number-1:0>2}") | {
            f"z{i:0>2}" for i in range(bit_number)
        }
        print("fixing bit: ", bit_number)
        potential_variable_names = (
            get_all_ancestors(f"z{bit_number:0>2}") - safe_variable_names
        ) | {f"z{bit_number:0>2}"}

        potential_variables = set(map(get_variable, potential_variable_names))
        safe_variables = set(map(get_variable, safe_variable_names))

        potential_swaps: list[tuple[z3.BitVecRef, z3.BitVecRef]] = []
        for var1 in potential_variables & set(target_constraints):
            for var2 in set(target_constraints) - safe_variables - {var1}:
                t = target_constraints.copy()
                t[var1], t[var2] = t[var2], t[var1]
                solver = z3.Solver()
                solver.add([k == v for k, v in t.items()])
                solver.add(z3.Extract(45, 45, x) == 0)
                solver.add(z3.Extract(45, 45, y) == 0)
                solver.add(
                    z3.Extract(bit_number, bit_number, (x + y))
                    != z3.Extract(bit_number, bit_number, z)
                )
                if solver.check() == z3.unsat:
                    potential_swaps.append((var1, var2))

        assert len(potential_swaps) == 1
        a, b = potential_swaps[0]
        target_constraints[a], target_constraints[b] = (
            target_constraints[b],
            target_constraints[a],
        )
        variables_swapped += [k for k, v in variables.items() if v in (a, b)]
print(",".join(sorted(variables_swapped)))
