# expected: -refine
def get_step(x):
    if x > 10:
        return 2
    return 1


def main(y):
    x = y
    while y < -2 or y > 2:
        if x > 0:
            y = y - get_step(x)
        else:
            y = y + get_step(-x)
    return 0
