# expected: -domain polyhedra -angelic x -precondition "y + z >= 0"
# the program terminates iff it can pick x with -y <= x <= z, i.e. iff
# y + z >= 0: projecting the two conditions on x one by one (Algorithm 1 of
# the VMCAI 2026 paper) gives true for both, and termination for all y, z
def main(y, z):
    x = input()
    if x <= z and x + y >= 0:
        pass
    else:
        while True:
            pass
