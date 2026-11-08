# expected: -domain polyhedra -joinbwd 4
def main(n, m):
    y = n
    z = n + 1
    while m + y >= 0 and m <= n:
        m = 2 * m + y
        y = z
        z = z + 1
