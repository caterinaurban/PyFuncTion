# expected: -domain octagons -ordinals 1 -angelic d
# as step_in_loop.py with ordinal-valued ranking functions: the value of the
# angelic choice must be the best one for the program (the inf over d, as
# with affine functions), not the worst one (the sup, as in ASSIGN←_W), with
# which the ranking function does not decrease along the loop
import random


def main(x):
    while x > 0:
        d = random.randint(-1, 1)
        x = x - d
