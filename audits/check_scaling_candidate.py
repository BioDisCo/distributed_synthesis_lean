"""Finite-prefix audit of a candidate infinite-memory safety objective.

The checker uses the repository's no-acknowledgement view constructors. It
does not infer an infinite theorem from these tests; see SCALING-COUNTEREXAMPLE.md.
"""

from argparse import ArgumentParser
from dataclasses import dataclass


@dataclass(frozen=True)
class Plan:
    weight: int
    children: tuple[int, int, int]


@dataclass(frozen=True)
class Label:
    multiplier: int
    carry: int
    left: Plan
    right: Plan


@dataclass(frozen=True)
class State:
    one_left: bool = True
    left_boundary: bool = True
    right_boundary: bool = True
    previous: Plan | None = None
    good: bool = True


def transition(state, graph, one, two):
    """A genuinely finite monitor: no depth, index, view, or mass arguments."""
    digit = 1 if graph == "both" else (
        0 if (graph == "right") == state.one_left else 2
    )
    one_left = state.one_left != (graph == "both")
    left_boundary = state.left_boundary and digit == 0
    right_boundary = state.right_boundary and digit == 2
    left, right = (one, two) if one_left else (two, one)
    plan = left.right
    labels_valid = all(
        label.multiplier in (2, 4)
        and 0 <= label.carry <= 3
        and all(2 <= w <= 4 for p in (label.left, label.right)
                for w in (p.weight, *p.children))
        for label in (left, right)
    )
    good = (
        state.good and labels_valid
        and left.multiplier == right.multiplier
        and plan == right.left
        and sum(plan.children) + left.carry
        == left.multiplier * plan.weight + right.carry
        and (not left_boundary or left.carry == 0)
        and (not right_boundary or right.carry == 0)
        and (state.previous is None or
             plan.weight == state.previous.children[digit])
    )
    return State(one_left, left_boundary, right_boundary, plan, good)


def residue_update(x, y, graph):
    return ((3 * x if graph == "right" else x + 2 * y) % 3,
            (3 * y if graph == "left" else y + 2 * x) % 3)


def letter_plan(one, two, residues):
    x, y = residues
    assert (y - x) % 3 in (1, 2)
    return one.right if (y - x) % 3 == 1 else two.right


def local_pair_check(previous_labels, previous_residues, graph, labels, residues):
    """Only two letters are inspected: the LTL extension's local relation."""
    if residues != residue_update(*previous_residues, graph):
        return False
    one_left = (previous_residues[1] - previous_residues[0]) % 3 == 1
    digit = 1 if graph == "both" else (
        0 if (graph == "right") == one_left else 2)
    old = letter_plan(*previous_labels, previous_residues)
    new = letter_plan(*labels, residues)
    return old.children[digit] == new.weight


class Views:
    def __init__(self):
        self.ids = {("empty", 0): 0, ("empty", 1): 1}
        self.meta = [(0, 0, 0), (1, 0, 1)]  # process, depth, coordinate

    def intern(self, key, meta):
        if key not in self.ids:
            self.ids[key] = len(self.meta)
            self.meta.append(meta)
        result = self.ids[key]
        assert self.meta[result] == meta
        return result

    def blind(self, own):
        proc, depth, coord = self.meta[own]
        return self.intern(("blind", own), (proc, depth + 1, 3 * coord))

    def receive(self, own, other):
        proc, depth, coord = self.meta[own]
        other_proc, other_depth, other_coord = self.meta[other]
        assert other_proc != proc and other_depth == depth
        return self.intern(("receive", own, other),
                           (proc, depth + 1, coord + 2 * other_coord))

    def advance(self, one, two, graph):
        return (
            self.blind(one) if graph == "right" else self.receive(one, two),
            self.blind(two) if graph == "left" else self.receive(two, one),
        )


class Source:
    def __init__(self, depth):
        self.mass = [3]
        self.multiplier = []
        for n in range(depth + 1):
            m = 2 if self.mass[n] >= 3 * 3**n else 4
            self.multiplier.append(m)
            self.mass.append(m * self.mass[n])
        assert all(2 * 3**n <= w <= 4 * 3**n
                   for n, w in enumerate(self.mass))

    def prefix(self, n, j):
        return j * self.mass[n] // 3**n

    def weight(self, n, j):
        return self.prefix(n, j + 1) - self.prefix(n, j)

    def plan(self, n, j):
        return Plan(self.weight(n, j), tuple(
            self.weight(n + 1, 3 * j + d) for d in range(3)))

    def label(self, n, j):
        m = self.multiplier[n]
        carry = m * j * self.mass[n] // 3**n - m * self.prefix(n, j)
        default = Plan(2, (2, 2, 2))
        return Label(m, carry,
                     self.plan(n, j - 1) if j else default,
                     self.plan(n, j) if j < 3**n else default)


def audit(depth):
    views = Views()
    source = Source(depth)
    layer = [(0, 1, State())]
    transitions = 0
    for n in range(1, depth + 1):
        children = []
        for one, two, state in layer:
            graphs = ("right", "both", "left") if state.one_left else (
                "left", "both", "right")
            for graph in graphs:
                u, v = views.advance(one, two, graph)
                _, nu, ju = views.meta[u]
                _, nv, jv = views.meta[v]
                assert nu == nv == n
                labels = (source.label(n, ju), source.label(n, jv))
                new = transition(state, graph, *labels)
                assert new.good, (n, graph, ju, jv, state, new)
                _, _, old_j = views.meta[one]
                _, _, old_k = views.meta[two]
                residues = (ju % 3, jv % 3)
                assert residues == residue_update(old_j % 3, old_k % 3, graph)
                assert new.one_left == ((residues[1] - residues[0]) % 3 == 1)
                if n > 1:
                    assert local_pair_check(
                        (source.label(n - 1, old_j), source.label(n - 1, old_k)),
                        (old_j % 3, old_k % 3), graph, labels, residues)
                children.append((u, v, new))
                transitions += 1
        layer = children
        last_right = None
        mass = 0
        for j, (one, two, state) in enumerate(layer):
            left, right = (one, two) if state.one_left else (two, one)
            assert views.meta[left][2] == j and views.meta[right][2] == j + 1
            assert last_right is None or left == last_right
            assert state.left_boundary == (j == 0)
            assert state.right_boundary == (j == 3**n - 1)
            last_right = right
            mass += state.previous.weight
        assert mass == source.mass[n]
        assert len(layer) == 3**n
        print(f"depth {n}: {len(layer)} histories; view chain exact; "
              f"all safety checks pass; mass {mass}; multiplier {source.multiplier[n]}")

    # A monitor that accepted everything would not pass these negative checks.
    good = source.label(1, 0)
    other = source.label(1, 1)
    assert transition(State(), "right", good, other).good
    wrong_mode = Label(6 - good.multiplier, good.carry, good.left, good.right)
    assert not transition(State(), "right", wrong_mode, other).good
    wrong_carry = Label(good.multiplier, 1, good.left, good.right)
    assert not transition(State(), "right", wrong_carry, other).good
    assert not transition(State(good=False), "right", good, other).good
    print(f"Audited {transitions} transitions, {len(views.meta)} interned local views; "
          "negative checks pass. This is a finite-prefix test, not an infinite proof.")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=8)
    args = parser.parse_args()
    if args.depth < 1:
        parser.error("depth must be positive")
    audit(args.depth)
