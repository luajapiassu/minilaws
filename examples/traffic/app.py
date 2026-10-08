"""A traffic light where an avenue crosses a street. An AI may edit it; LAWS.laws says what must stay true."""
from minilaws import Nat

GREEN: Nat = 0
YELLOW: Nat = 1
RED: Nat = 2


def avenue(phase: Nat) -> Nat:
    if phase == 0:
        return GREEN
    return YELLOW if phase == 1 else RED


def street(phase: Nat) -> Nat:
    if phase == 2:
        return GREEN
    return YELLOW if phase == 3 else RED


def next_phase(phase: Nat) -> Nat:
    if phase == 3:
        return 0
    return phase + 1
