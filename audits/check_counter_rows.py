"""Finite and adversarial audits of the ternary counter-machine encoding.

The monitor sees only finite machine data, graph letters, and finite labels.
The source uses perfect-recall view coordinates. These tests are not an
end-to-end Lean undecidability proof; see COUNTER-MACHINE-REDUCTION.md.
"""

from argparse import ArgumentParser
from dataclasses import dataclass, replace
from itertools import product

from check_scaling_candidate import Plan, Views


@dataclass(frozen=True)
class Machine:
    # ("inc", counter, next), ("dec", counter, zero_next, positive_next), ("halt",)
    code: tuple
    initial: int = 0

    def branch(self, q, zero):
        instruction = self.code[q]
        if instruction[0] == "halt":
            return q, (3, 3)
        kind, counter, target, *positive = instruction
        factors = [3, 3]
        if kind == "inc":
            factors[counter] = 1
            return target, tuple(factors)
        if zero[counter]:
            return target, tuple(factors)
        factors[counter] = 9
        return positive[0], tuple(factors)

    def advance(self, config):
        q, counters = config
        target, factors = self.branch(q, tuple(c == 0 for c in counters))
        return target, tuple(c + 1 if m == 1 else c - 1 if m == 9 else c
                             for c, m in zip(counters, factors))


@dataclass(frozen=True)
class Label:
    control: int
    zero: tuple[bool, bool]
    carry: tuple[int, int]
    left: tuple[Plan, Plan]
    right: tuple[Plan, Plan]


@dataclass(frozen=True)
class State:
    one_left: bool = True
    left_boundary: bool = True
    right_boundary: bool = True
    previous: tuple | None = None  # control, zero flags, incident plans
    good: bool = True


def transition(machine, state, graph, one, two, *, anchor=True):
    """Finite monitor: no coordinate, depth, counter value, or row sum input."""
    digit = 1 if graph == "both" else (
        0 if (graph == "right") == state.one_left else 2)
    one_left = state.one_left != (graph == "both")
    lb = state.left_boundary and digit == 0
    rb = state.right_boundary and digit == 2
    left, right = (one, two) if one_left else (two, one)
    plans = left.right
    valid = all(
        0 <= label.control < len(machine.code)
        and all(type(z) is bool for z in label.zero)
        and all(0 <= c <= 8 for c in label.carry)
        and all(w in (0, 1) for p in (*label.left, *label.right)
                for w in (p.weight, *p.children))
        for label in (left, right))
    if not valid:
        return State(one_left, lb, rb, None, False)
    _, factors = machine.branch(left.control, left.zero)
    good = (state.good and machine.code[left.control][0] != "halt"
            and (left.control, left.zero) == (right.control, right.zero)
            and plans == right.left)
    for r, plan in enumerate(plans):
        good &= sum(plan.children) + left.carry[r] == (
            factors[r] * plan.weight + right.carry[r])
        good &= not left.zero[r] or plan.weight == 1
        good &= not lb or (left.carry[r] == 0 and (
            left.zero[r] or plan.weight == 0))
        good &= not rb or right.carry[r] == 0
    if state.previous is None:
        good &= left.control == machine.initial
        good &= not anchor or all(p.weight == 1 for p in plans)
    else:
        q, zero, old = state.previous
        good &= left.control == machine.branch(q, zero)[0]
        good &= all(p.weight == prev.children[digit] for p, prev in zip(plans, old))
    return State(one_left, lb, rb, (left.control, left.zero, plans), bool(good))


class Source:
    def __init__(self, machine, depth):
        self.machine = machine
        self.configs = [(machine.initial, (0, 0))]
        for _ in range(depth + 1):
            self.configs.append(machine.advance(self.configs[-1]))

    def weight(self, n, r, j):
        c = self.configs[n - 1][1][r]
        return (j + 1) // 3**c - j // 3**c

    def plan(self, n, r, j):
        return Plan(self.weight(n, r, j), tuple(
            self.weight(n + 1, r, 3*j + d) for d in range(3)))

    def label(self, n, j):
        q, counters = self.configs[n - 1]
        zero = tuple(c == 0 for c in counters)
        _, factors = self.machine.branch(q, zero)
        carries = tuple(m*j // 3**c - m*(j // 3**c)
                        for c, m in zip(counters, factors))
        default = (Plan(0, (0, 0, 0)),) * 2
        return Label(q, zero, carries,
                     tuple(self.plan(n, r, j-1) for r in range(2)) if j else default,
                     tuple(self.plan(n, r, j) for r in range(2)) if j < 3**n else default)


def audit_machine(name, machine, depth):
    views = Views()
    source = Source(machine, depth)
    layer = [(0, 1, State())]
    tested = 0
    for n in range(1, depth + 1):
        q, counters = source.configs[n - 1]
        if machine.code[q][0] == "halt":
            # Every graph rejects on the first halting row; no accepted prefix is hidden.
            for one, two, state in layer:
                for graph in ("left", "right", "both"):
                    u, v = views.advance(one, two, graph)
                    labels = [source.label(n, views.meta[x][2]) for x in (u, v)]
                    assert not transition(machine, state, graph, *labels).good
            print(f"{name}: every branch rejects at machine time {n-1}")
            return tested
        children = []
        for one, two, state in layer:
            graphs = ("right", "both", "left") if state.one_left else ("left", "both", "right")
            for graph in graphs:
                u, v = views.advance(one, two, graph)
                labels = [source.label(n, views.meta[x][2]) for x in (u, v)]
                new = transition(machine, state, graph, *labels)
                assert new.good, (name, n, graph, labels, state)
                children.append((u, v, new))
                tested += 1
        layer = children
        last = None
        masses = [0, 0]
        for j, (one, two, state) in enumerate(layer):
            left, right = (one, two) if state.one_left else (two, one)
            assert views.meta[left][2] == j and views.meta[right][2] == j + 1
            assert last is None or left == last
            assert state.left_boundary == (j == 0)
            assert state.right_boundary == (j == len(layer)-1)
            last = right
            for r, plan in enumerate(state.previous[2]):
                masses[r] += plan.weight
        assert all(masses[r] * 3**counters[r] == 3**n for r in range(2))
    print(f"{name}: {tested} literal transitions pass through depth {depth}; "
          f"last configuration {source.configs[depth-1]}")
    return tested


def guard(zero, row):
    return all(row) if zero else row[0] == 0


def adversarial_audit():
    checked = 0
    for row in product((0, 1), repeat=3):
        for z in (False, True):
            if not guard(z, row):
                continue
            assert z == (sum(row) == len(row))
            for children in product((0, 1), repeat=9):
                for m in (1, 3, 9):
                    carry = 0
                    valid = True
                    for j, w in enumerate(row):
                        carry += sum(children[3*j:3*j+3]) - m*w
                        valid &= 0 <= carry <= 8
                    if valid and carry == 0:
                        assert sum(children) == m * sum(row)
                    checked += 1

    # Dropping initialization permits an all-zero fake positive counter to
    # decrement forever although the actual zero-initialized machine halts.
    machine = Machine((("dec", 0, 1, 0), ("halt",)))
    plan = Plan(0, (0, 0, 0))
    fake = Label(0, (False, False), (0, 0), (plan, plan), (plan, plan))
    assert not transition(machine, State(), "right", fake, fake).good
    layer = [State()]
    for _ in range(6):
        layer = [transition(machine, state, graph, fake, fake, anchor=False)
                 for state in layer for graph in ("left", "right", "both")]
        assert all(state.good for state in layer)

    inc = Machine((("inc", 0, 0),))
    source = Source(inc, 3)
    a, b = source.label(1, 0), source.label(1, 1)
    assert transition(inc, State(), "right", a, b).good
    # Endpoint disagreement, carry leakage, and fake initial nonzero claims fail.
    assert not transition(inc, State(), "right", replace(a, zero=(False, True)), b).good
    assert not transition(inc, State(), "right", replace(a, carry=(1, 0)), b).good
    state = transition(inc, State(), "right", a, b)
    a2, b2 = source.label(2, 0), source.label(2, 1)
    bad_a = replace(a2, zero=(True, True))
    bad_b = replace(b2, zero=(True, True))
    assert not transition(inc, state, "right", bad_a, bad_b).good
    assert not transition(inc, replace(state, good=False), "right", a2, b2).good
    print(f"Adversarial audit: {checked} row-pair/multiplier cases; "
          "false flags and carry mutations rejected; missing-anchor cheat reproduced.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=8)
    args = parser.parse_args()
    if args.depth < 1:
        parser.error("depth must be positive")
    examples = {
        "unbounded_increment": Machine((("inc", 0, 0),)),
        "both_unbounded": Machine((("inc", 0, 1), ("inc", 1, 0))),
        "increment_decrement_zero_loop": Machine((
            ("inc", 0, 1), ("dec", 0, 2, 1), ("inc", 1, 3), ("dec", 1, 0, 3))),
        "halt_after_zero_test": Machine((("inc", 0, 1), ("dec", 0, 2, 1), ("halt",))),
        "halt_initially": Machine((("halt",),)),
    }
    total = sum(audit_machine(name, machine, args.depth) for name, machine in examples.items())
    adversarial_audit()
    print(f"Total {total} passing literal transitions. Finite tests, not an infinite proof.")
