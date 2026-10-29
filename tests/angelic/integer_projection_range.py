# expected: -domain polyhedra -angelic x -precondition "0 <= y and y <= 20"
# result: UNKNOWN
# As integer_projection_band.py, with a bounded choice: x in [0, 10] and
# 2x == y has a rational solution for every y in [0, 20], an integer one
# only for even y (y = 1: none).
import random


def main(y):
    x = random.randint(0, 10)
    if 2 * x != y:
        while True:
            pass
