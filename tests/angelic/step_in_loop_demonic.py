# expected: -domain octagons
# result: UNKNOWN
# same as step_in_loop.py, without -angelic: d may always be <= 0
import random


def main(x):
    while x > 0:
        d = random.randint(-1, 1)
        x = x - d
