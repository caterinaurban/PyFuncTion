# expected: -domain polyhedra -angelic x
# result: UNKNOWN
# Projection over the rationals vs over the integers: some rational x
# satisfies 3x <= y <= 3x + 1 for every y, but an integer x exists only if
# y mod 3 is 0 or 1: e.g. for y = 2 no choice of x terminates.
def main(y):
    x = input()
    while 3 * x > y or y > 3 * x + 1:
        pass
