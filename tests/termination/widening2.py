# expected: -ordinals 2
def main(x):
    while x != 0:
        if x > 0:
            x = x - 2
        else:
            x = x + 1
