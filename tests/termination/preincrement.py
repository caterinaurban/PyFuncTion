def main(x, y):
    while x <= 10:
        x += 1  # y += ++x
        y += x
    return 0
