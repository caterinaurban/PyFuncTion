# expected: -ordinals 2
import random


def main(x1, x2, x3):
    while x1 > 0 and x2 > 0 and x3 > 0:
        if random.randint(0, 1):
            x1 = x1 - 1
        elif random.randint(0, 1):
            x2 = x2 - 1
            x3 = int(input())
        else:
            x3 = x3 - 1
            x1 = int(input())
    return 0
