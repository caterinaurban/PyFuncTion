# expected: -domain polyhedra
# result: UNKNOWN
# FuncTion issue #21 (https://github.com/caterinaurban/function/issues/21):


def f2():
    while True:
        pass


def f1():
    f2()


def main():
    f1()
    return 0
