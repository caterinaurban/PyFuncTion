# expected: -domain octagons
def main(x, y):
    d = abs(x - y)
    while d > 0:
        d = d - max(1, min(d, 3))
