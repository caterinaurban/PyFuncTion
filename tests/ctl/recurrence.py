# expected: -domain polyhedra -ctl "AG{AF{x == 3}}" -precondition "x < 0"
def main(x):
    while x >= 0:
        x = x + 1
    while True:
        if x <= 10:
            x = x + 1
        else:
            x = -x
