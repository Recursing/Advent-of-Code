from collections import Counter

lines = open(__file__.replace(".py", ".txt")).read().split("\n")


def mix(a: int, b: int) -> int:
    return a ^ b


assert mix(42, 15) == 37


def prune(a: int) -> int:
    return a % 16777216


assert prune(100000000) == 16113920


def next_number(secret: int) -> int:
    num1 = secret * 64
    secret = mix(num1, secret)
    secret = prune(secret)
    num2 = secret // 32
    secret = mix(num2, secret)
    secret = prune(secret)
    num3 = secret * 2048
    secret = mix(num3, secret)
    secret = prune(secret)
    return secret


result = 0
type FourInts = tuple[int, int, int, int]
max_price_dicts: list[Counter[FourInts]] = []
for secret in map(int, lines):
    max_price_dict: Counter[FourInts] = Counter()
    previous_four_deltas = None, None, None, None
    price = secret % 10
    for i in range(2000):
        secret = next_number(secret)
        diff = secret % 10 - price
        price = secret % 10
        previous_four_deltas = previous_four_deltas[1:] + (diff,)
        if (
            all(x is not None for x in previous_four_deltas)
            and previous_four_deltas not in max_price_dict
        ):
            max_price_dict[previous_four_deltas] = price  # type: ignore
    max_price_dicts.append(max_price_dict)
    result += secret

print(result)
print(sum(max_price_dicts, start=Counter[FourInts]()).most_common(1)[0][1])
