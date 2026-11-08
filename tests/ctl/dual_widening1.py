# expected: -domain polyhedra -ctl "AG{x != 0}" -precondition "x < 0"
def main(x):
    while True:
        x = x - 1