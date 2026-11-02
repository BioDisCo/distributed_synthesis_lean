/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks

/-! Finite two-process decision tasks under LTL graph assumptions.

The executable endpoint is `DistributedSynthesis.DecisionTasks.TwoProcess.solveGraphTask`;
its correctness theorem is `solveGraphTask_correct`. It uses the existing `Proc`
identifiers and `Option Graph`, where `none` is silent. Input/output alphabets
may differ between processes. Protocol state spaces are unrestricted.
`solveGraphParityTask_correct` accepts a finite parity adversary directly.
The imported proof shares the canonical task model, existing LTL compiler,
and tree-nonemptiness backend; no external correctness theorem is a hypothesis.
`TwoProcess.history_eq_iff_view_eq` connects the internal two-process encoding
to the shared finite-depth views. Encoded numerical computability and effective
extraction of solving protocols are separate from this finite-data decider.

`IISParticipation.Task.solvable_iff_bounded` proves the participation transfer
to bounded IIS protocols; `IISFiniteSearch.check_correct` proves finite-depth
search complete for three-process graph solvability. Neither asserts the
Gafni–Koutsoupias hardness theorem, which is not proved here.
-/
