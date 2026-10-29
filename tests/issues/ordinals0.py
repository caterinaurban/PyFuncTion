def main(n):
    bug = 0
    y = 0
    if n < 0:
        return 0
    x = n
    while x > 0:
        x = x - 1
        y = y + 1
    if n == y:
        bug = 1
    return 0
