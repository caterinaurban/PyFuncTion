# expected: -domain polyhedra
# result: UNKNOWN
# (the ranking function b + 1 depends on the bound b - 1 of a % b, which the
# affine functions domain of FuncTion loses in the backward assignment)
def main(a, b):
    assume(a >= 0 and b >= 0)
    while b != 0:
        a, b = b, a % b
    return a
