# expected: -domain octagons
def step(x):
    if x > 100:
        return 10
    if x > 10:
        return 2
    return 1


def main(x):
    while x > 0:
        x = x - step(x)
