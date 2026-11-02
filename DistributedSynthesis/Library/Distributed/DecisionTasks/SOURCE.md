# Decision-task proof provenance and status

This directory is restricted to finite decision-task solvability: the
two-process decision theorem and the three-process wait-free IIS argument.

`Source/` contains selected dependencies of `ConsensusLTL.decidableSolvesTaskAdv`
and the IIS graph characterization. Selection used the checked proof terms
and source references, followed by rebuilding the excerpts. Small excerpts
were consolidated into `Model`, `Views`, `NodeTransport`, and `TaskColouring`.
`source-manifest.json` records the original commit, file hashes, selected
source declarations, and destinations. These are adapted excerpts, not
byte-identical copies. The extracted parity-game solver and tree-automaton
record have been removed in favor of the existing library implementations.
The source parity development credits GPT-6-Astra assistance; that provenance
also applies to its retained notation lemmas.

Declarations live under `DistributedSynthesis.DecisionTasks.Source`, including
the `FiniteParity` namespace. The port uses this repository's
pinned Lean/Mathlib 4.30. Adaptations include explicit beta reduction in two
proofs and unfolding reception bits in a simplification. The full-information
state machine was separated from the source's leader decision rule, and the
unused consensus-output field was removed from `Source.Algorithm`.
That name is now a transparent abbreviation of the canonical task protocol.

`Model` is the single universe-polymorphic task model. It accepts arbitrary
process types and directed graphs with self-loops. Inputs arrive initially;
each transition sees only the old local state and incoming sender/state pairs.
It defines process-specific alphabets, termination, irrevocability, and validity.
`Source.Model` retains only compatibility aliases and lookup helpers;
`TypedTasks` contains the proved alphabet-packing equivalence.

`ProcessTransport` proves generic process renaming preserves runs and solvability.
`TwoProcessModel` connects the public `Proc` identifiers and `Option Graph` to
the internal Boolean encoding. `none` is silent; `some g` preserves each existing
graph's directions. The existing three-graph reactive model is unchanged:
it intentionally supplies fresh private inputs every round, whereas a task has
one initial input. The definitions are therefore connected at their graph and
observation interfaces rather than incorrectly identified.

`TwoProcessViews.history_eq_iff_view_eq` proves the compact source histories and
the canonical finite-depth task views induce precisely the same observations
on executions. The former is an internal encoding for the labelling proof,
not a second solvability model.
`FiniteViews.solvable_of_solves` factors a solver with states in any universe
through the canonical full-view protocol, justifying the existential endpoint's
fixed state universe. It preserves termination, irrevocability, and validity
without imposing a uniform decision time.

`TwoProcess.solveGraphTask_correct` is the public decision theorem, including
the existing verified `LTLComputable` compiler. It uses separate alphabets
indexed by `Proc`, and formulas over `Option Graph`.
`solveGraphParityTask_correct` accepts arbitrary finite parity automata directly.
The Boolean-process endpoints remain as backend compatibility interfaces.
Candidate protocols can have arbitrary state spaces.

The direct task automaton is the library's `RunParityTreeAutomaton`.
The generic `Automata/RunTreeNonemptiness` adapter packs successor choices into
labels and calls `TreeNonemptiness`, backed by `FiniteOrbitParity`. It preserves
the whole-successor-vector quantifier order and rejects illegal transitions.
The existing regular-tree basis theorem also supplies the task's regular run.
There is no second parity-game solver or run-tree semantics in `Source`.
`Automata/PriorityPairMonitor` sends the observed bounded priorities through
the existing `EncodedParityFamilies` compiler. `Source.Union` now contains
only compatibility aliases and acceptance-notation lemmas; the extracted IAR
algorithm was removed. The task monitor's proved branch condition is unchanged.
The shared encoded compiler is expensive; this development claims decidability,
not a practical complexity bound.

This proves an executable finite-data decision function, not a numerical
`ComputablePred` theorem. The formalization does not implement the alternative
general MSO presentation or an effective extraction of solving protocols from
regular labels.

`IISGraphs` proves the six-bit event encoding, the exact thirteen-graph
enumeration, and the fixed LTL formula's semantics. `CompactTermination`
proves a uniform round bound for finite oblivious alphabets; `IISGraphs`
specializes it to IIS.

The following additional modules are proved locally:

- `BoundedProtocol` implements a fixed-depth local decision rule by stopping
  the simulated state at that depth. `IISBoundedProtocol` proves the IIS
  equivalence between unrestricted-state solvability and a bounded protocol.
- `IISParticipation` implements both state-machine simulations for the
  inactive-input encoding. `filterInactive_run` proves that filtering incoming
  states simulates the active subexecution. `run_complete_eq` proves that a
  final block of inactive processes preserves every active process's state.
  `Task.solvable_iff_bounded` equates padded graph solvability with one bounded
  IIS protocol valid on all legal participating subsets. `paddedTable` computes
  the output table, including unrestricted validity on illegal inputs.
- `FiniteViews` proves that every protocol factors through the recursive
  sender-indexed local views, and that these views are implemented by a
  full-information protocol. Each fixed level has a constructive finite
  enumeration. `IISFiniteViews` specializes it to full and partial-participation
  IIS protocols. The generic model, bounded-protocol and finite-view modules
  have no dependency on IIS or on the source backend.
- `IISFiniteSearch.check_correct` proves that some finite-depth exhaustive
  check succeeds exactly when a three-process graph task is solvable.
  The check itself has no classical decision oracle. There is no claim of a
  computable upper bound on the depth to search.
- `ChromaticTasks` represents input and output complexes by partial
  assignments and includes downward closure and monotone task carriers.
  Its padding retains every input face, enforces the all-inactive case, and
  preserves validity for every partial set of decisions.

The three-process hardness result is not proved here. It requires the
Gafni–Koutsoupias task-hardness construction (including its undecidable
loop-contractibility/group-word source) and the equivalence of the concrete
finite IIS local-view criterion with wait-free read/write solvability. The
operational finite-view criteria above do not prove the topological
identification with iterated standard chromatic subdivision or the read/write
simulation theorem. The padding equivalence is now proved at the bounded
IIS protocol interface; composing it with the missing classical theorems
is still necessary for the requested undecidability endpoint. The source's conditional
`not_computablePred_solvable` has deliberately not been imported: assuming
these facts would not meet the requested complete formalization.

The eventual `ComputablePred` endpoint also requires uniform instance
encodings and a `Computable` proof of the reduction. The executable
`paddedTable` transformation does not by itself supply that encoded theorem.

To check this development independently, run from the repository root:

```sh
lake --wfail build DistributedSynthesis.Results.TaskDecidability DistributedSynthesis.Library.Distributed.DecisionTasks
python3 scripts/check_library.py --axioms DistributedSynthesis/Tests/DecisionTasksAxioms.lean
```

The audit permits only the project's standard logical axioms (`propext`,
`Classical.choice`, and `Quot.sound`). No `sorry`, added axiom, or native
decision shortcut is used in this development.
