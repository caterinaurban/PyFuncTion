# expected: -domain polyhedra -ordinals 1
def main(x, y):
    while x >= 0:
        x = x + y
        if y >= 0:
            y = y - 1