/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmCounterMachineBinaryUndecidability

/-! # Undecidability with one Boolean output per process

Assuming the stated undecidability of zero-initialized two-counter-machine
halting, no algorithm decides LTL realizability when each process has a Boolean
output and a singleton input alphabet. Communication may follow any infinite
sequence of the three graphs, and each strategy may use its full local history.
The source assumption is discharged in `Results.UnconditionalUndecidability`.

`CounterMachine.BinaryCompiler.binary_ltl_synthesis_undecidable` takes only
the explicit MM2 source interface. The composed instance compiler is primitive
recursive and its realizability equivalence is proved. The model retains
singleton inputs, full-view messages, perfect recall, and all three graphs;
LTL uses the fixed graph/output atoms. The finite-output theorem is unchanged.
-/
