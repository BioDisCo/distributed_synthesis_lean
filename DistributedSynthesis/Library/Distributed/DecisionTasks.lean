/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.TwoProcess
import DistributedSynthesis.Library.Distributed.DecisionTasks.TwoProcessViews
import DistributedSynthesis.Library.Distributed.DecisionTasks.IISGraphs
import DistributedSynthesis.Library.Distributed.DecisionTasks.IISFiniteSearch
import DistributedSynthesis.Library.Distributed.DecisionTasks.ChromaticTasks

/-! Initial-input decision tasks under graph-language assumptions.

`TwoProcess.solveGraphTask_correct` proves the two-process LTL decision theorem
on the existing `Proc` and `Graph` types, extending the graphs by `none` for
silence. `solveGraphParityTask_correct` accepts a parity automaton directly.
The task model, LTL compiler, and tree-nonemptiness backend are shared.
The IIS modules prove the fixed graph language, the finite local-view criterion,
and the padding equivalence for bounded protocols on all input faces.
`IISFiniteSearch.check_correct` supplies executable search at each finite depth.
The Gafni–Koutsoupias hardness theorem and the link to wait-free read/write
solvability are not proved here; see DecisionTasks/SOURCE.md.
-/
