# expected: -domain polyhedra -angelic x
# result: UNKNOWN
# 2x == y has no integer solution x for odd y: the projection of x over the
# rationals (true) must not be used
def main(y):
    x = input()
    if 2 * x == y:
        pass
    else:
        while True:
            pass
