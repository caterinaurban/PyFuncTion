# expected: -domain octagons -angelic x -precondition "y + 2 * z >= 0"
# result: UNKNOWN
# As range_boxes.py with octagons: some x in [0, y + 2z] satisfies x >= 5
# iff y + 2z >= 5, which is not an octagonal constraint. For y = z = 0 the
# only choice is x = 0.
import random


def main(y, z):
    x = random.randint(0, y + 2 * z)
    if x < 5:
        while True:
            pass
