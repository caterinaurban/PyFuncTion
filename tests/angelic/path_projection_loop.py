# expected: -domain octagons -angelic x
# result: UNKNOWN
# Projecting each decision node separately (Algorithm 1 of the VMCAI 2026
# paper) is unsound: the loop exits iff -y <= x <= z; projecting x out of
# x <= z and out of x + y >= 0 separately gives true for both, i.e. some x
# would always exist. But there is none when y + z < 0, e.g. y = 0, z = -1
# (0 <= x <= -1). The correct precondition is y + z >= 0 (see
# path_projection_loop_pre.py).
def main(y, z):
    x = input()
    while x > z or x + y < 0:
        pass
