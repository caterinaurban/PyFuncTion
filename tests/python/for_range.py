# expected: -domain polyhedra -ordinals 2
def main(n, m):
    s = 0
    for i in range(n):
        for j in range(i, m, 2):
            s += j
    return s
