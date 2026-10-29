# expected: -ordinals 2
import random


def main(x1, x2):
    while x1 != 0 and x2 > 0:
        if x1 > 0:
            if random.randint(0, 1):
                x1 = x1 - 1
                x2 = int(input())
            else:
                x2 = x2 - 1
        else:
            if random.randint(0, 1):
                x1 = x1 + 1
            else:
                x2 = x2 - 1
                x1 = int(input())
    return 0
