lines = list(map(int, open("day01.txt").readlines()))
print(sum(cur > prev for cur, prev in zip(lines[1:], lines)))

windows = list(map(sum, zip(lines, lines[1:], lines[2:])))
print(sum(cur > prev for cur, prev in zip(windows[1:], windows)))
