# expected UNKNOWN: -domain polyhedra -angelic x
# as path_projection.py, without the precondition: no x exists if y + z < 0
def main(y, z):
    x = input()
    if x <= z and x + y >= 0:
        pass
    else:
        while True:
            pass
