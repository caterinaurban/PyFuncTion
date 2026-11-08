# expected: -domain polyhedra -precondition "x >= 0 and y >= 0" -seed "y >= 0" -ctl "AG{x >= 0}"
def main(x, y):
    while True:
        if y > 5:
            x = x + 1
        else:
            x = x + y
