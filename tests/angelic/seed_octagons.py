# expected: -domain octagons -angelic y -seed "x - y <= 0"
# The program picks y once; the loop then runs x - y times. The tree after
# the choice is split on x - y (as the seed asks), and every path is
# reachable by picking y.
def main(x):
    y = input()
    while x - y > 0:
        x = x - 1
        y = y + 1
