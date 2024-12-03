import re

text = open("day03.txt").read()
part1 = re.compile(r"mul\((\d+),(\d+)\)")
print(sum(int(a) * int(b) for a, b in part1.findall(text)))

part2 = re.compile(r"mul\((\d+),(\d+)\)|(do)\(\)|(don)\'t\(\)")
result = 0
is_active = True
for a, b, do, don in part2.findall(text):
    if do:
        is_active = True
    if don:
        is_active = False
    if is_active and a and b:
        result += int(a) * int(b)
print(result)
