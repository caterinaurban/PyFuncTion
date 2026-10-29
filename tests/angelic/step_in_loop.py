# expected: -domain octagons -angelic d
# the program picks a new step d at each iteration (boxes cannot express x - d)
import random


def main(x):
    while x > 0:
        d = random.randint(-1, 1)
        x = x - d
