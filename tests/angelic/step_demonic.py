# expected: -domain polyhedra -seed "s >= 1"
# result: UNKNOWN
# same as step.py, without -angelic: the step s may be <= 0
import random


def main(x):
    s = random.randint(-10, 10)
    while x > 0:
        x = x - s
