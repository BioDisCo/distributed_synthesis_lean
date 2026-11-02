# From the paper to Lean

Start with the result you want to review. **Statement and proof** opens the
same Lean file as its PDF badge. Each file presents the paper statement,
explains the relevant notation, and gives the full Lean statement and proof.
**Proof locations** links directly to the underlying declarations used there.

[Model and view complexes](Model.lean) · [Synthesis problem](ProblemStatement.lean) ·
[Definitions](#definitions) · [Notation](#reading-the-lean-statements) ·
[Verification](#verification)

The names below describe the results without requiring the paper's TeX source.
They are grouped by subject, independently of theorem numbering. Source labels
in the Lean comments identify the corresponding manuscript statements.

## Main results

| Result | Statement and proof | Proof locations |
| --- | --- | --- |
| Undecidability of lossy-link synthesis | [Undecidability](Undecidability.lean) | [Underlying proofs](PROOFS.md#undecidability-of-lossy-link-synthesis) |
| Nowhere denseness characterizes decidability | [Characterization](Characterization.lean) | [Underlying proofs](PROOFS.md#nowhere-denseness-characterizes-decidability) |
| Deciding realizability and constructing an algorithm | [Decidability](Decidability.lean) | [Underlying proofs](PROOFS.md#deciding-realizability-and-constructing-an-algorithm) |

## Views and their geometry

| Result | Statement and proof | Proof locations |
| --- | --- | --- |
| Indistinguishability and preceding views | [Indistinguishability](Indistinguishability.lean) | [Underlying proofs](PROOFS.md#indistinguishability-and-preceding-views) |
| One round subdivides an edge into three | [SingleSubdivision](SingleSubdivision.lean) | [Underlying proofs](PROOFS.md#one-round-subdivides-an-edge-into-three) |
| The inputless view complex is a path | [ViewPath](ViewPath.lean) | [Underlying proofs](PROOFS.md#the-inputless-view-complex-is-a-path) |
| The extreme vertices | [ExtremeVertices](ExtremeVertices.lean) | [Underlying proofs](PROOFS.md#the-extreme-vertices) |
| The index of an edge | [PathIndex](PathIndex.lean) | [Underlying proofs](PROOFS.md#the-index-of-an-edge) |
| Computing the position of a view | [FindIndex](FindIndex.lean) | [Underlying proofs](PROOFS.md#computing-the-position-of-a-view) |
| Prefixes and inclusion of intervals | [CellInclusion](CellInclusion.lean) | [Underlying proofs](PROOFS.md#prefixes-and-inclusion-of-intervals) |
| Continuity and surjectivity of the geometric map | [GeometricMap](GeometricMap.lean) | [Underlying proofs](PROOFS.md#continuity-and-surjectivity-of-the-geometric-map) |
| The geometric map preserves closure | [Closure](Closure.lean) | [Underlying proofs](PROOFS.md#the-geometric-map-preserves-closure) |
| Removing a prefix from an edge index | [ConcatenationIndex](ConcatenationIndex.lean) | [Underlying proofs](PROOFS.md#removing-a-prefix-from-an-edge-index) |
| Removing a prefix from an interval | [ConcatenationCell](ConcatenationCell.lean) | [Underlying proofs](PROOFS.md#removing-a-prefix-from-an-interval) |
| Removing a prefix from the geometric image | [ConcatenationMap](ConcatenationMap.lean) | [Underlying proofs](PROOFS.md#removing-a-prefix-from-the-geometric-image) |
| The preimage of an interval interior | [CellInterior](CellInterior.lean) | [Underlying proofs](PROOFS.md#the-preimage-of-an-interval-interior) |
| Prefix cylinders are clopen | [ClopenCones](ClopenCones.lean) | [Underlying proofs](PROOFS.md#prefix-cylinders-are-clopen) |

## Consensus and adversaries

| Result | Statement and proof | Proof locations |
| --- | --- | --- |
| Consensus and the geometric image | [Consensus](Consensus.lean) | [Underlying proofs](PROOFS.md#consensus-and-the-geometric-image) |
| Consensus in bounded time | [BoundedConsensus](BoundedConsensus.lean) | [Underlying proofs](PROOFS.md#consensus-in-bounded-time) |
| Repeated consensus and nowhere denseness | [RepeatedConsensus](RepeatedConsensus.lean) | [Underlying proofs](PROOFS.md#repeated-consensus-and-nowhere-denseness) |
| Empty interior implies repeated consensus | [EmptyInterior](EmptyInterior.lean) | [Underlying proofs](PROOFS.md#empty-interior-implies-repeated-consensus) |
| Agreeing on a broadcaster | [Broadcaster](Broadcaster.lean) | [Underlying proofs](PROOFS.md#agreeing-on-a-broadcaster) |
| Computing a uniform consensus bound | [ConsensusBound](ConsensusBound.lean) | [Underlying proofs](PROOFS.md#computing-a-uniform-consensus-bound) |
| Nowhere denseness and missing extensions | [MissingExtension](MissingExtension.lean) | [Underlying proofs](PROOFS.md#nowhere-denseness-and-missing-extensions) |
| A dense residual adversary | [DenseResidual](DenseResidual.lean) | [Underlying proofs](PROOFS.md#a-dense-residual-adversary) |

## The counter encoding

| Result | Statement and proof | Proof locations |
| --- | --- | --- |
| Agreement along a view path | [PathAgreement](PathAgreement.lean) | [Underlying proofs](PROOFS.md#agreement-along-a-view-path) |
| Position residues and orientation | [PositionOrder](PositionOrder.lean) | [Underlying proofs](PROOFS.md#position-residues-and-orientation) |
| Agreement on the control state | [ControlAgreement](ControlAgreement.lean) | [Underlying proofs](PROOFS.md#agreement-on-the-control-state) |
| The local weight identity | [LocalSum](LocalSum.lean) | [Underlying proofs](PROOFS.md#the-local-weight-identity) |
| Checking whether the counter is zero | [ZeroCheck](ZeroCheck.lean) | [Underlying proofs](PROOFS.md#checking-whether-the-counter-is-zero) |
| Checking the initial configuration | [InitialCheck](InitialCheck.lean) | [Underlying proofs](PROOFS.md#checking-the-initial-configuration) |
| Checking a machine transition | [ProperTransition](ProperTransition.lean) | [Underlying proofs](PROOFS.md#checking-a-machine-transition) |
| The formula and the row conditions | [RowConditions](RowConditions.lean) | [Underlying proofs](PROOFS.md#the-formula-and-the-row-conditions) |
| Soundness of the counter encoding | [CounterSoundness](CounterSoundness.lean) | [Underlying proofs](PROOFS.md#soundness-of-the-counter-encoding) |
| Completeness of the counter encoding | [CounterCompleteness](CounterCompleteness.lean) | [Underlying proofs](PROOFS.md#completeness-of-the-counter-encoding) |
| Nonhalting is equivalent to realizability | [CounterEquivalence](CounterEquivalence.lean) | [Underlying proofs](PROOFS.md#nonhalting-is-equivalent-to-realizability) |
| Safety and closure of the adversary | [SafetyClosure](SafetyClosure.lean) | [Underlying proofs](PROOFS.md#safety-and-closure-of-the-adversary) |
| Reduction to an adversary with a dense residual | [GuardedReduction](GuardedReduction.lean) | [Underlying proofs](PROOFS.md#reduction-to-an-adversary-with-a-dense-residual) |

## Component trees and the decision procedure

| Result | Statement and proof | Proof locations |
| --- | --- | --- |
| The specification automaton | [SpecificationAutomaton](SpecificationAutomaton.lean) | [Underlying proofs](PROOFS.md#the-specification-automaton) |
| The block automaton and live states | [BlockAutomaton](BlockAutomaton.lean) | [Underlying proofs](PROOFS.md#the-block-automaton-and-live-states) |
| Algorithms and uncompressed component trees | [UncompressedTrees](UncompressedTrees.lean) | [Underlying proofs](PROOFS.md#algorithms-and-uncompressed-component-trees) |
| Extending maps of view complexes | [ViewExtension](ViewExtension.lean) | [Underlying proofs](PROOFS.md#extending-maps-of-view-complexes) |
| A common preceding view in a component | [CommonView](CommonView.lean) | [Underlying proofs](PROOFS.md#a-common-preceding-view-in-a-component) |
| Compressing a component | [Compression](Compression.lean) | [Underlying proofs](PROOFS.md#compressing-a-component) |
| Uncompressed and compressed trees | [BoundedRepresentation](BoundedRepresentation.lean) | [Underlying proofs](PROOFS.md#uncompressed-and-compressed-trees) |
| Compressed and symbolic trees | [SymbolicTrees](SymbolicTrees.lean) | [Underlying proofs](PROOFS.md#compressed-and-symbolic-trees) |
| MSO defines the accepting symbolic trees | [MSO](MSO.lean) | [Underlying proofs](PROOFS.md#mso-defines-the-accepting-symbolic-trees) |

## Definitions

These links open the definition or its explicit unfolding. For the compressed
tree, the linked block includes validity, compatible runs, and acceptance.

| Paper definition | Lean declaration |
| --- | --- |
| Lossy-link synthesis | [`full_synthesis_iff`](ProblemStatement.lean#L57) |
| Lossy-link synthesis under an adversary | [`adversary_synthesis_iff`](ProblemStatement.lean#L47) |
| View complex with output | [`ViewComplexOutput`](Model.lean#L95) |
| Uncompressed component tree | [`UncompressedTree`](../ComponentTrees/Trees.lean#L62) |
| Live graph history | [`LivePrefix`](../../Library/Distributed/GraphAdversaries/Cells.lean#L101) |
| Compressed component tree and acceptance | [`CompressedTree`](../ComponentTrees/Trees.lean#L78) |
| Symbolic component tree labels | [`Description`](../ComponentTrees/GeneratingAlphabet.lean#L27) |

## Reading the Lean statements

| In the paper | In the formalization |
| --- | --- |
| Two processes | `Proc.one` and `Proc.two`; `p.other` is the other process. |
| Left, right, and bidirectional communication | `Graph.left`, `Graph.right`, and `Graph.both`. |
| A distributed algorithm | `StrategyPair`: two functions of their respective local views. |
| Finite nonempty input and output alphabets | `Fin (k + 1)` in the encoded synthesis instance; private inputs remain arbitrary. |
| An inputless construction | Both input types are `Unit`, the singleton type. |
| Round r, starting at 1 | Execution index `r - 1`; a history of length r still has length r. |
| The geometric image in [0,1] | `geometricMap '' A`; topological predicates use the relative topology of the interval. |
| Decidability | `ComputablePred` or a concrete solver with a correctness theorem. |
| A finite collection and decidable equality | `[Fintype α]` and `[DecidableEq α]`. These describe the represented data. |

The scalar counter statements use the paper's five output components. The
implementation reuses a two-counter development through an embedding whose
correctness is proved. `OnlyFirst` describes one-counter instruction syntax;
`ofCode_onlyFirst` establishes it for every scalar program. The final scalar
soundness, completeness, and equivalence statements do not ask the reader to
supply this premise. Position residues use modulo three.

In the component-tree construction, finite orders select representatives and
indices for finite alphabets. The bound on `capacity` ensures that the chosen
finite representation fits. `liveCorrect` states that the live-state test
recognizes extendible prefixes; the constructed block automaton supplies it.
The [decision theorem](Decidability.lean) assembles these constructions from
the adversary automaton and formula under the nowhere-denseness hypothesis.

The explicit theorem types retain every hypothesis, including implicit type
parameters and instance arguments in square brackets. A short proof invoking
a library theorem is checked at exactly the displayed type. Follow its
**Proof locations** link to inspect the actual argument and any intervening
construction. In particular, the characterization entry proves the iff using
the existing characterization library; the separate decision entry follows
the component-tree construction.

## Verification

From the repository root:

```sh
python3 verification/verify.py fast
```

This builds the library and tests, checks the paper guide's source links, and
runs the axiom audits, including every theorem in these entry files. The
allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

For a focused review, the following checks just the paper endpoints after
building their imports:

```sh
lake build DistributedSynthesis.Tests.Paper
python3 scripts/check_library.py --axioms DistributedSynthesis/Tests/Paper/Audit.lean
```

Lean checks the formal statements and proofs. Comparing their hypotheses and
conclusions with the paper remains part of reviewing the correspondence.
The [verification guide](../../../verification/README.md) describes the
optional Docker/Comparator checks.
