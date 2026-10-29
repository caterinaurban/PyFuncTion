# expected: -domain octagons -precondition "r <= 0 or x < y"
# result: UNKNOWN
# (as FuncTion (OCaml): requires the smart widening of the SAS 2014 paper)
def main(x, y, r):
    while r > 0:
        r = r + x
        r = r - y
