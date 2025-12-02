import re

lines = open(__file__.replace(".py", ".txt")).read().splitlines()
str_ranges = [r.split("-") for r in lines[0].split(",")]
ranges = [(int(a), int(b)) for a, b in str_ranges]
part1 = 0
part2 = 0
twice_re = re.compile(r"^(.+)\1$")
repeated_re = re.compile(r"^(.+)\1+$")
for a, b in ranges:
    for n in range(a, b + 1):
        nstr = str(n)
        if twice_re.match(nstr):
            part1 += n
        if repeated_re.match(nstr):
            part2 += n

print(f"{part1}")
print(f"{part2}")
