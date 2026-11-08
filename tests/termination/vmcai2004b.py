# expected: -domain polyhedra -joinbwd 5 -precondition "x != 3"
def main(x):
    while x >= 0:
        x = -2 * x + 9
