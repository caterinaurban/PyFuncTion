# expected: -domain boxes -angelic x -precondition "y + z >= 0"
# result: UNKNOWN
# A choice whose bounds are relational: some x in [0, y + z] satisfies x >= 5
# iff y + z >= 5, which boxes cannot represent. Over-approximating it (by
# top) would claim termination for every y + z >= 0, but for y = z = 0 the
# only choice is x = 0. The leaf must be dropped instead.
import random


def main(y, z):
    x = random.randint(0, y + z)
    if x < 5:
        while True:
            pass
