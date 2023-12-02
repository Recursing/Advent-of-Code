import math


lines = open("day02.txt").readlines()


# Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green -> (1, [{blue: 3, red: 4}, {red: 1, green: 2, blue: 6}, {green: 2}])
def parse_line(line: str):
    game, rest = line.split(":")
    game_id = int(game.split(" ")[1])
    extractions = [[h.strip().split() for h in e.split(",")] for e in rest.split(";")]
    return game_id, [{h[1]: int(h[0]) for h in e} for e in extractions]


lines = [parse_line(l) for l in lines]


def is_valid(extractions: list[dict[str, int]]):
    maximums = {"red": 12, "green": 13, "blue": 14}
    for extraction in extractions:
        for color, maxnum in maximums.items():
            if extraction.get(color, 0) > maxnum:
                return False
    return True


print(sum(id for id, extractions in lines if is_valid(extractions)))


def power(extractions: list[dict[str, int]]):
    return math.prod(
        max(e.get(color, 0) for e in extractions) for color in ["red", "green", "blue"]
    )


print(sum(power(extractions) for id, extractions in lines))
