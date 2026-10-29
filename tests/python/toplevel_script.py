import random

n = random.randint(0, 1000)
while n > 1:
    if n % 2 == 0:
        n = n // 2
    else:
        n = n - 1
