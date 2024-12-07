import re

lines = open(__file__.replace(".py", ".txt")).readlines()

parsed = [list(map(int, re.findall(r"\d+", line))) for line in lines]
equations = [[line[0], tuple(line[1:])] for line in parsed]

part = 1


def is_solvable(target: int, numbers: tuple[int, ...]):
    if len(numbers) == 1:
        return target == numbers[0]
    *other_numbers, last_number = numbers
    other_numbers = tuple(other_numbers)
    if (target % last_number == 0) and is_solvable(
        target // last_number, other_numbers
    ):
        return True
    elif part == 2 and target > last_number:
        target_str = str(target)
        last_number_str = str(last_number)
        if target_str.endswith(last_number_str) and is_solvable(
            int(target_str.removesuffix(last_number_str)), other_numbers
        ):
            return True

    return is_solvable(target - last_number, other_numbers)


print(sum(target for target, numbers in equations if is_solvable(target, numbers)))

part = 2
print(sum(target for target, numbers in equations if is_solvable(target, numbers)))
