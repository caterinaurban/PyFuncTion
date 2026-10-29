# expected: -ordinals 1
import random


def main(x, y):
    while x > 0 and y > 0:
        if random.randint(0, 1):
            x = x - 1
            y = int(input())
        else:
            y = y - 1
