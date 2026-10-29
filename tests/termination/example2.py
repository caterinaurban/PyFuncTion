def main(x, y):
    while y < -2 or y > 2:
        if y < 0 and x > 10:
            y = y + 2
        elif y < 0 and x <= 10:
            y = y + 1
        elif y >= 0 and x > 10:
            y = y - 2
        elif y >= 0 and x <= 10:
            y = y - 1
    return 0
