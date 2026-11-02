# Nowhere denseness and LTL synthesis

[Repository README](../../README.md) · [Import index](IMPORTS.md)

## Public theorem

```lean
import DistributedSynthesis.Results.HolesCharacterization

open DistributedSynthesis
open DistributedSynthesis.GraphAdversaries

example (A : Set (Nat → Graph)) (regular : OmegaRegular A) :
    ComputablePred (Realizable A) ↔ IsNowhereDense (geometricMap '' A) :=
  realizable_computable_iff_nowhere_dense A regular
```

Fix an omega-regular adversary A over the two opposite one-way communication
graphs and the bidirectional graph. Let π be the reflected ternary coordinate
map of graph sequences used by the local-view path construction. Then LTL
synthesis over A is decidable if and only if π(A) is **nowhere dense** in
the relative topology on `[0,1]`:

```text
interior_[0,1] (closure_[0,1] (π(A))) = ∅.
```

Equivalently, every nonempty relatively open subset of `[0,1]` contains a
nonempty relatively open subset disjoint from π(A). The interval formulation
requires a hole of positive length inside every nondegenerate subinterval.
Deleting a single point need not satisfy this condition. The coordinate map
is not assumed injective at shared endpoints.

The public endpoint uses Mathlib's `IsNowhereDense` directly.
`GraphAdversaries.SingletonInputs.realizable_computable_iff_nowhere_dense`
gives the same iff in the original singleton-input encoding. The existing
`GeometricHoles` interval formulation and theorem names remain available;
`geometricHoles_iff_isNowhereDense` proves their equivalence to the standard
predicate. The explicit interior-of-closure endpoint is also retained.

## Model and computation

The operational model is the existing two-process full-view model. Processes
receive before producing their current output, retain perfect recall, and
can distinguish physical round numbers. Each instance specifies four finite
nonempty input/output alphabets, a finite atomic truth table, and an ordinary
postfix LTL formula. Specifications may inspect inputs, outputs, and the graph.
A graph adversary restricts only the graph sequence; both private input
streams remain unrestricted. The theorem includes `X` and does not establish
the negative direction for the next-free fragment.

`GraphAdversaries.Instance` is definitionally the existing
`EncodedNoDirect.Instance`, with its original `Primcodable` instance, graph
codes, and truth-table semantics. No new answer-dependent encoding is used.
For each fixed omega-regular A whose geometric image is nowhere dense,
`GraphAdversaries.nowhere_dense_primitive_recursive_solver` supplies

```text
∃ solve : Instance → Bool,
  Primrec solve ∧ ∀ i, solve i = true ↔ Realizable A i.
```

The adversary's finite presentation and graph bounds are fixed before the
instance varies. The theorem does not claim uniform extraction of these
constants from an arbitrary description of A, an efficient running-time
bound, or finite-memory sufficiency. Empty adversaries and nonclosed
omega-regular adversaries are included.

## Proof organization

| Location under `DistributedSynthesis` | Role |
| --- | --- |
| `Library.Topology.OpenHoles` | open holes characterize nowhere denseness |
| `Library.Automata.PrefixHoles`, `Library.Combinatorics.FiniteRows` | uniform finite-state hole depths and row bounds |
| `Library.Distributed.GraphAdversaries.*` | reflected graph geometry, live-prefix components, input model, solver application, and singleton-input compatibility |
| `Library.Distributed.GraphAdversaries.Undecidability.*` | prefix-dense safety reduction, residual adversaries, and guarded restart |
| `Library.Distributed.LeaderPhases.*` | agreed leaders, delayed boundaries, closing choices, and physical strategy composition |
| `Library.Distributed.LeaderGame.*` | numbered history families, complete compatible offers, and semantic game correspondence |
| `Library.Distributed.LeaderGame.Encoding.*` | finite numeric tables, primitive-recursive compilation, and correctness |
| `Library.Automata.EncodedMuller*`, `EncodedParityFamilies*`, `EncodedParityProduct*`, `EncodedParityConjunction*` | reusable numeric automata operations |
| `Formalizations.GraphAdversaries.HolesIff` | combines the two proved directions without additional hypotheses |
| `Results.HolesCharacterization` | public theorem names in `DistributedSynthesis.GraphAdversaries` |
| `Tests.GraphAdversaries*` | public clients, phase counterexamples, and the detailed axiom audit |

In the positive direction, nowhere denseness and omega-regularity bound graph-only
uncertainty. A leader communicates contingent output tables while arbitrarily
long one-way phases continue. Closing choices are checked against compatible
hidden histories. The game accounts for every physical priority, both over
infinitely many handovers and through a final endless phase. The resulting
numeric compiler invokes the existing parity-tree solver.

In the negative direction, failure of nowhere denseness yields a prefix-dense residual
adversary. The existing counter-machine safety reduction applies there;
a computable prefix guard and local restart transport it back to A.
The public endpoint is `GraphAdversaries.not_nowhere_dense_undecidable`;
it needs no omega-regularity assumption. A primitive-recursive
embedding gives both processes singleton input alphabets in the finite-input
model. Its graph-code translation and input renaming preserve the formula
and each execution at the same physical round, transferring undecidability.

## Library organization and import boundaries

All proof implementations and regression tests live under
`DistributedSynthesis/`. Use `DistributedSynthesis.Results.HolesCharacterization`
for the public API. Internal declarations in the `Characterisation` namespace
are defined in the maintained library; no separate import directory is needed.
The public aliases are definitionally equal to the existing model.

The positive construction is independent of the negative reduction. The no-direct-reversal
specialization lives in `GraphAdversaries.NoDirectReversal`; its realizability
predicate still agrees with the original library predicate by `Iff.rfl`.
The existing no-direct solver, counter-machine source, and formula compiler
implementations are unchanged.

The import checker guards the model against leader-game and negative-proof
dependencies, the positive proof against counter-machine dependencies, and
the generic numeric automata against graph geometry and leader constructions.
The numeric operations retain existing automata adapters; this
integration is not a complete extraction of those older adapters.

The root umbrellas also include the existing private-input/no-communication
result and its tests. These modules were already present but omitted from the
aggregate build; their theorem statements and proofs are unchanged.

## Validation commands

From the repository root:

```sh
lake build
python3 scripts/check_library.py --axioms
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_library.py --axioms DistributedSynthesis/Tests/GraphAdversaries/Audit.lean
```

The public tests check the exact iff types, primitive-recursive solver
statement, input encoding, and the no-direct-reversal definitional equality.
The axiom checks accept only `propext`, `Classical.choice`, and `Quot.sound`.
The detailed graph-hole audit checks the intermediate characterization
endpoints using the same axiom policy as the main checker.

An additional [Docker Comparator/Nanoda workflow](../../verification/README.md)
checks the public mathematical API exposed by `DistributedSynthesis.Results`,
including the graph-hole theorems and solver, against a separately saved
reference. Its coverage is discovered from the compiled declarations.
