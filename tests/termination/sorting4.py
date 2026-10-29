# expected: -domain polyhedra
def main(x1, x2, x3, x4):
    while x1 > x2 or x2 > x3 or x3 > x4:
        if x1 > x2:
            x1 = x2
            x2 = x1
        elif x2 > x3:
            x2 = x3
            x3 = x2
        elif x3 > x4:
            x4 = x3
            x3 = x4
    return 0
