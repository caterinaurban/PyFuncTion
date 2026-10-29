# expected: -domain polyhedra -angelic x -precondition "y + 2 * z >= 5"
# as range_octagons.py, with polyhedra, which represent y + 2z >= 5 exactly:
# termination is proven under this precondition
import random


def main(y, z):
    x = random.randint(0, y + 2 * z)
    if x < 5:
        while True:
            pass
