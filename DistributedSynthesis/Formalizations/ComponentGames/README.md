# Component games and constructive synthesis

Import the public result with:

```lean
import DistributedSynthesis.Results.ComponentGames
```

The declarations are in `Characterisation.ComponentGames`. `solve` takes an
encoded adversary and finite-input LTL instance together with the paper's
nowhere-dense-image promise. `solve_correct` identifies its Boolean result
with the existing `WithInputs.Realizable` predicate. `synthesize` returns
`Option (WithInputs.Strategies d.2)`; `synthesize_complete` characterizes when
it returns a strategy, and `synthesize_sound` proves that **the returned
strategy** satisfies the original formula on every admitted execution.
The promise is a proof argument erased at runtime. The three-row alphabet
condition identifies the automaton's letters with the existing three graphs.
Input and output alphabets are finite and nonempty, as in the manuscript.

```lean
open DistributedSynthesis Characterisation

example (d : EncodedGuardedObjective.Data)
    (alphabet : (EncodedParityTables.rows d.1).length = 3)
    (promise : IsNowhereDense
      (geometricMap '' {w | (ComponentGames.graphInput d.1).Accepts w})) :
    ComponentGames.solve d promise = true ↔
      WithInputs.Realizable {w | (ComponentGames.graphInput d.1).Accepts w} d.2 :=
  ComponentGames.solve_correct d alphabet promise
```

The API examples are compiled in `DistributedSynthesis.Tests.ComponentGames`.
The exhaustive implementation establishes effective construction, not a
practical running-time bound. No new numeric `Primrec` theorem is claimed.

## Shared definitions and dependencies

There is one finite-set type: Mathlib's `Finset`. Finite domains use `Fintype`.
The proof reuses the library's `View`, `StrategyPair`, executions, LTL,
`ClosingLayer`, `ClosingPolicy`, `BlockWord`, `BlockPrefix`, `BlockType`, ranks,
automata compilers, and parity-game results. It does not copy these definitions.

`HistoryGame.Position` stores actual sets of histories and their objective
states. `Representation.Data` stores their finite view relations and state
labels. These are the two different objects in the manuscript; the isomorphism
and strategy-transfer theorems connect them explicitly.

General utilities live in the shared library:

- `Library.Automata.FiniteController`: executable winning-policy extraction
  from the existing deterministic block monitor and finite-orbit solver.
- `Library.Computability.FiniteOrders`: opt-in computable orders used to select
  a finite table. Mathlib's general Pi lexicographic order is noncomputable;
  the finite case uses standard sorted lists and `LinearOrder.lift'`.
- `Library.Distributed.DecidableViews`: opt-in derived equality for the
  existing view type, using Mathlib's `Equiv.psumEquivSum` for input tags.

Importing these modules does not activate their scoped instances. Implementation
files opt in with `open scoped DistributedSynthesis.FiniteOrders` and
`open scoped DistributedSynthesis.DecidableViews`. The representation-specific
orders are scoped separately. In particular, the normal pointwise order on
products and functions is preserved for clients of the public result.
`numberSubset` is only an abbreviation for Mathlib's `Finset.orderIsoOfFin`.
Closing-policy ordering uses `Equiv.piCurry`; it has no second policy encoding.

The existing `PeriodicBlocks` formalization remains available independently.
This construction reuses its common lemmas and data, while proving the
manuscript's actual replacement-before-extension game equivalences.

## Proof organization

| Part | Modules |
| --- | --- |
| Literal games and exact local moves | `HistoryGames`, `MoveLegality`, `BasicLemmas` |
| Component game and local prescriptions | `ComponentReadback`, `ComponentExecutions`, `ComponentCoverage`, `ComponentSoundness`, `ComponentEquivalence` |
| Replacement simulation | `SimulationLocal`, `SimulationStrategy`, `SimulationRuns` |
| Exact bound and representatives | `CommonView`, `ComponentRoots`, `Representatives`, `BoundedReplay`, `BoundedChoice`, `BoundedStrategy`, `BoundedWinning`, `BoundedEquivalence` |
| Computable consensus bound | `ConsensusFinite`, `ConsensusHoles`, `ConsensusFiniteTest`, `ConsensusSearchTermination`, `ConsensusExecution`, `ConsensusProposals`, `ConsensusExistence`, `ConsensusBound`, `ConsensusConsequences` |
| Finite representations and monitor | `RepresentationTransport`, `RepresentationComponents`, `RepresentationHistories`, `FiniteRepresentations`, `FiniteArena`, `FiniteTransitions`, `MonitorCompiler` |
| Complete strategy transfers | `SupportedInterpreter`, `RepresentationSteps`, `RepresentationLift`, `FiniteToHistory`, `FiniteToHistoryRuns`, `HistoryToFinite`, `HistoryToFiniteRuns`, `FiniteProduct`, `FiniteEquivalence` |
| Decision and executable synthesis | `Decision`, `ArenaController`, `ExecutableHistories`, `ExecutableIsomorphisms`, `ExecutableComponents`, `ExecutableFiniteToHistory`, `ExecutableSimulation`, `ExecutableReadback`, `ExecutableReadbackWinning`, `ExecutableSynthesis`, `BoundedSynthesis`, `Synthesis` |

## Paper correspondence

These game results are reusable independently of the paper's component-tree
proof. For the paper's current statements and proofs, use the
[paper guide](../Paper/README.md). Intermediate conditions such as exact-depth
missing extensions are derived before they are used in the decision and
synthesis theorems.

## Verification

Run the repository's normal checks from the repository root:

```sh
python3 verification/verify.py fast
```

For the complete component-game declaration audit:

```sh
lake build DistributedSynthesis.Tests.ComponentGames.Audit
python3 scripts/check_library.py --axioms DistributedSynthesis/Tests/ComponentGames/Audit.lean
```

The audit accepts only `propext`, `Classical.choice`, and `Quot.sound`.
Classical choices occur in semantic proofs, including the completeness rank
argument. The synthesis function itself computes finite choices and local
outputs; it does not use a classical realizing strategy as input data.
The existing `verification/README.md` describes optional Comparator replay
against a reviewed reference; the fast checks do not replace that comparison.
