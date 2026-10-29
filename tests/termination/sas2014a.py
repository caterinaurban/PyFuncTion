# expected: -domain polyhedra -precondition "x < y" -seed "x < y"
def main(x, y, r):
    while r > 0:
        r = r + x
        r = r - y
