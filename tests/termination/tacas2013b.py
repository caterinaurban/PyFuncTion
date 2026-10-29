# expected: -domain polyhedra
def main(x, K):
    while x != K:
        if x > K:
            x = x - 1
        else:
            x = x + 1
    return 0
