# expected: -domain polyhedra -ctl "AF{x == 3}" -precondition "x <= 3"
def main(x):
    while x >= 0:
        x = x + 1
    while True:
        if x <= 10:
            x = x + 1
        else:
            x = -x
