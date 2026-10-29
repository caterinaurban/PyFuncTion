# expected: -angelic s
# result: UNKNOWN
# the value of an unknown call over-approximates what the program computes,
# it is not a choice: it stays demonic even if s is angelic
def main(x):
    s = compute_step(x)
    while x > 0:
        x = x - s
