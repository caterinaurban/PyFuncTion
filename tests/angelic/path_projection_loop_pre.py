# expected: -domain octagons -angelic x -precondition "y + z >= 0"
# as path_projection_loop.py, under the precondition that makes it terminate
def main(y, z):
    x = input()
    while x > z or x + y < 0:
        pass
