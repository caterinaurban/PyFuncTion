# expected: -domain polyhedra -ctl "AF{z == 1}" -precondition "x < y"
# expected: -domain polyhedra -ctl "NOT{NOT{AF{z == 1}}}" -precondition "x < y"
# expected: -domain polyhedra -ctl "NOT{AF{z == 1}}" -precondition "z != 1 and x >= y"
# expected: -domain polyhedra -ctl "EG{z != 1}" -precondition "z != 1 and x >= y"
# expected UNKNOWN: -domain boxes -ctl "NOT{AF{z == 1}}" -precondition "z != 1 and x == 0 and y == 1"
def main(x, y, z):
    z = 0
    if x < y:
        z = 1
    while True:
        pass
