"""App code: plain Python that runs as-is. An AI may edit it; LAWS.laws says what must stay true."""
from minilaws import Nat


def add(n: Nat, m: Nat) -> Nat:
    # same definition as the Natural Number Game: n + 0 = n, n + succ m = succ (n + m)
    if m == 0:
        return n
    return add(n, m - 1) + 1
