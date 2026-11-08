# expected: -domain polyhedra -precondition "x > 6"
def main(x):
    while x <= 10:
        if x > 6:
            x = x + 2
