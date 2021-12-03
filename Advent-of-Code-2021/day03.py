from statistics import mode

numbers = tuple([int(c) for c in s.rstrip()] for s in open("day03.txt").readlines())
BIT_LENGTH = len(numbers[0])
most_common_values = [
    mode(number[index] for number in numbers) for index in range(BIT_LENGTH)
]
least_common_values = [1 - v for v in most_common_values]


def bits_to_int(bits: list[int]) -> int:
    return int("".join(map(str, bits)), 2)


print(bits_to_int(most_common_values) * bits_to_int(least_common_values))


def find_rating(use_least_common: bool) -> list[int]:
    values = numbers
    for index in range(BIT_LENGTH):
        target = sum(v[index] for v in values)
        target = target >= len(values) // 2
        if use_least_common:
            target = 1 - target

        values = [v for v in values if v[index] == target]
        if len(values) == 1:
            return values[0]

    raise Exception()


print(bits_to_int(find_rating(False)) * bits_to_int(find_rating(True)))
