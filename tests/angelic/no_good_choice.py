# expected: -domain octagons -angelic d
# result: UNKNOWN
# whatever the program picks, x never decreases
import random


def main(x):
    while x > 0:
        d = random.randint(-1, 0)
        x = x - d
