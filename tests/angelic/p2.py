# expected: -domain polyhedra -angelic c -ordinals 1
import random

x = input()
z = 10
while z >= x:
    c = random.randint(-2, 1)
    z = z + c
