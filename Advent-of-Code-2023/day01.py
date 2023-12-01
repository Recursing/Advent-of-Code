lines = open("day01.txt").readlines()
digits = [[int(c) for c in l if c.isdigit()] for l in lines]
print(sum(d[0] * 10 + d[-1] for d in digits))

numberWords = ["one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]


def replaceWords(l: str):
    for w in numberWords:
        l = l.replace(w, w + str(numberWords.index(w) + 1) + w)
    return l


assert replaceWords("abcone2threexyz") == "abcone1one2three3threexyz"
digits = [[int(c) for c in replaceWords(l) if c.isdigit()] for l in lines]
print(sum(d[0] * 10 + d[-1] for d in digits))
