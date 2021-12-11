lines = open("day10.txt").read().splitlines(keepends=False)
open_chars = "<{[("
reversed_char = {")": "(", "}": "{", "]": "[", ">": "<"}
scores = {")": 3, "]": 57, "}": 1197, ">": 25137}


def score(line: str) -> int:
    stack: list[str] = []
    for char in line:
        if char in open_chars:
            stack.append(char)
            continue
        if not stack:
            continue
        if reversed_char[char] != stack.pop():
            return scores[char]
    return 0


print(sum(map(score, lines)))

scores2 = {"(": 1, "[": 2, "{": 3, "<": 4}


def score2(line: str) -> int:
    stack: list[str] = []
    for char in line:
        if char in open_chars:
            stack.append(char)
            continue
        assert stack, "too many close parens"
        if reversed_char[char] != stack.pop():
            return 0
    total_score = 0
    while stack:
        char = stack.pop()
        total_score = total_score * 5 + scores2[char]

    return total_score


all_scores = [s for line in lines if (s := score2(line))]
assert len(all_scores) % 2 == 1
from statistics import median

print(median(all_scores))
