# expected: -domain polyhedra -precondition "x <= y" -ctl "AF{x == y}"

# RESET must under-approximate the atomic proposition (decision_tree.reset):
# with boxes, x == y is not representable; over-approximating it (top) would
# reset every leaf to 0 and "prove" AF{x == y} also for x > y, where x never
# reaches y; under-approximating it (bottom) gives UNKNOWN
# expected UNKNOWN: -domain boxes -precondition "x > y" -ctl "AF{x == y}"
def main(x, y):
    while x != y:
        x = x + 1
    while True:
        pass
