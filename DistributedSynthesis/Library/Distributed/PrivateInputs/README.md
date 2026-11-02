# Private inputs and no communication

This separate model and reduction explain the refining path structure shared
by the communication result and the classical Pnueli–Rosner architecture.
Existing graph types, model definitions, and result modules are unchanged.

`Model.lean` defines two independent private input streams, local strategies
on their complete input histories, and executions using the existing generic
`RoundRecord`. The graph alphabet is a singleton denoting the empty graph.
Each process reads its current input before producing its output. Legality
assumptions and encodings are not built into the model.

The proof is split into the following modules:

- `Paths.lean`: ternary displacement encoding, local position reconstruction,
  and exact preservation of the existing full-view equality relations.
- `Simulation.lean`: legal input streams and strategy transfer in both directions.
- `Ternary.lean`: an ordinary LTL assumption selecting those streams, a
  primitive-recursive postfix compiler, and realizability equivalence.
- `BinaryBlocks.lean`: local two-round input coding and execution correspondence.
- `Binary.lean`: an output clock, the ordinary LTL block translation, a
  primitive-recursive compiler, and realizability equivalence with binary inputs.

Import `DistributedSynthesis.Results.PrivateInputUndecidability` for the closed
endpoint:

```lean
PrivateInputUndecidability.binary_input_ltl_synthesis_undecidable :
  ¬ ComputablePred PrivateInputs.Binary.Realizable
```

The target has one private Boolean input per process, four output symbols at
process 1 (data and clock), and two at process 2. The formula uses ordinary
finite current-letter tests; its interpretation does not run a source machine.
Strategies have unrestricted perfect recall, with no finite-state requirement.
The proof invokes the existing communication undecidability theorem, not the
historical Pnueli–Rosner theorem.

From `lean/`, build and audit the new endpoint without changing the existing
aggregate imports:

```sh
lake build DistributedSynthesis.Tests.PrivateInputUndecidability
lake env lean DistributedSynthesis/Tests/PrivateInputUndecidability.lean
```

The test module checks the public theorem types and prints the axioms of the
correspondence, compiler, and final theorem. Their dependencies are limited to
Lean's `propext`, `Classical.choice`, and `Quot.sound`.
