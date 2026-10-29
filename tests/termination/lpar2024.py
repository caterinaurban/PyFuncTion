# expected: -domain polyhedra -precondition "x > 0" -seed "x > 0"
def main(x, y, z):
    while y > z:
        y = y - x
