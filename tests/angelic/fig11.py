# expected: -domain polyhedra -angelic x -precondition "y > 0"
def main(y):
    x = input()
    if x < 0 and x + y >= 0:
        pass
    else:
        while True:
            pass