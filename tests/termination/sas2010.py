import random


def main(x1, x2):
    while x1 >= 0 and x2 >= 0:
        if random.randint(0, 1):
            while x2 <= 10 and random.randint(0, 1):
                x2 = x2 + 1
            x1 = x1 - 1
        x2 = x2 - 1
    return 0
