def main(x):
    steps = 0
    while x > 0:
        x = x // 2
        steps += 1
    return steps
