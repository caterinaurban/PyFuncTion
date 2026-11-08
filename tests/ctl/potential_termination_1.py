# expected: -domain polyhedra -ctl "EF{exit: true}"
def main():
    y = 1
    i = int(input())
    x = int(input())
    if i > 10:
        x = 1
    while x == y:
        pass
    #LABEL: exit
