# expected UNKNOWN: -domain octagons -angelic d
# whatever the program picks, x never decreases
import random


def main(x):
    while x > 0:
        d = random.randint(-1, 0)
        x = x - d
