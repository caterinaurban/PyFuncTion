# expected: -domain polyhedra -angelic a,c -precondition "x > 0" -seed "x > 0"
import random

def main(x):
    a = input()
    z = 10
    if a*a >= 0:
        while z >= 0:
            z = z - x
    else:
        while z >= x:
            c = random.randint(-2,1)
            z = z + c