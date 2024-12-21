from functools import cache


text = open(__file__.replace(".py", ".txt")).read()
blocks_text, targets_text = text.split("\n\n")
blocks = blocks_text.split(", ")
targets = targets_text.split("\n")


@cache
def is_solvable(target: str) -> bool:
    if target in blocks:
        return True
    return any(
        is_solvable(target[len(block) :])
        for block in blocks
        if target.startswith(block)
    )


print(sum(map(is_solvable, targets)))


@cache
def num_solutions(target: str) -> int:
    if target == "":
        return 1
    return sum(
        num_solutions(target[len(block) :])
        for block in blocks
        if target.startswith(block)
    )


print(sum(map(num_solutions, targets)))
