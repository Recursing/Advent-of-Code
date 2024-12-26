from functools import cache
from itertools import permutations

type Grid = dict[complex, str]
numpad_text = """789
456
123
.0A"""
numpad_grid: Grid = {
    x + y * 1j: c
    for y, line in enumerate(numpad_text.split("\n"))
    for x, c in enumerate(line)
}

keypad_text = """.^A
<v>"""
keypad_grid: Grid = {
    x + y * 1j: c
    for y, line in enumerate(keypad_text.split("\n"))
    for x, c in enumerate(line)
}


def _find_char(grid: Grid, char: str) -> complex:
    return next(pos for pos, c in grid.items() if c == char)


@cache
def find_numpad_char(char: str) -> complex:
    return _find_char(numpad_grid, char)


@cache
def find_keypad_char(char: str) -> complex:
    return _find_char(keypad_grid, char)


def vec_to_dirs(vec: complex) -> str:
    return (
        "^" * -int(vec.imag)
        + "v" * int(vec.imag)
        + "<" * -int(vec.real)
        + ">" * int(vec.real)
    )


def is_valid_path(pos: complex, path: tuple[str, ...], is_numpad: bool) -> bool:
    assert not (is_numpad and pos == find_numpad_char("."))
    assert not ((not is_numpad) and pos == find_keypad_char("."))
    for d in path:
        pos += {"^": -1j, "v": 1j, "<": -1 + 0j, ">": 1 + 0j}[d]
        if is_numpad and pos == find_numpad_char("."):
            return False
        if (not is_numpad) and pos == find_keypad_char("."):
            return False
        assert (is_numpad and pos in numpad_grid) or (
            (not is_numpad) and pos in keypad_grid
        )
    return True


@cache
def get_button_presses(
    position: complex,
    target_pos: complex,
    depth: int,
    is_numpad: bool = False,
) -> int:
    dirs = vec_to_dirs(target_pos - position)
    if depth == 0:
        return len(dirs) + 1
    assert depth > 0

    min_button_presses = None
    for path in set(permutations(dirs)):
        if not is_valid_path(position, path, is_numpad):
            continue
        buttons_presses = 0
        t_p = find_keypad_char("A")
        for d in path + ("A",):
            buttons_presses += get_button_presses(t_p, find_keypad_char(d), depth - 1)
            t_p = find_keypad_char(d)
        if min_button_presses is None or min_button_presses > buttons_presses:
            min_button_presses = buttons_presses
    assert min_button_presses is not None
    assert min_button_presses >= 1
    return min_button_presses


targets = """803A
528A
586A
341A
319A""".split("\n")
scores = 0
for target in targets:
    min_sequence_length = 0
    pos = find_numpad_char("A")
    for target_char in target:
        target_pos = find_numpad_char(target_char)
        min_sequence_length += get_button_presses(pos, target_pos, 25, is_numpad=True)
        pos = target_pos
        # print(positions)
    scores += min_sequence_length * int(target[:-1])

print(scores)
