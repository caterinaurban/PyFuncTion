# expected: -joinbwd 7
import random


def main():
    x = int(input())
    while x <= 100:
        if random.randint(0, 1):
            x = -2 * x + 2
        else:
            x = -3 * x - 2
    return 0
