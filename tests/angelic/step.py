# expected: -domain polyhedra -seed "s >= 1" -angelic s
# the program picks the step s once: s >= 1 makes the loop terminate
import random


def main(x):
    s = random.randint(-10, 10)
    while x > 0:
        x = x - s
