# expected: -refine
# result: UNKNOWN
# FuncTion (OCaml) proves the C version only because its inliner turns the
# returns inside get_step into program exits. With the correct semantics,
# proving termination requires the disjunctive invariant x > 0 => y > 0,
# which is not expressible in the convex partition domains.
def get_step(x):
    if x > 20:
        return 3
    elif x > 10:
        return 2
    return 1


def main(y):
    x = y
    while y < -3 or y > 3:
        if x > 0:
            y = y - get_step(x)
        else:
            y = y + get_step(-x)
    return 0
