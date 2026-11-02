/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.TwoCounterMachines
import DistributedSynthesis.Formalizations.Theorem.ThmCounterMachineEncodedUndecidability
import DistributedSynthesis.Formalizations.Undecidability.CounterArithmetic
import DistributedSynthesis.Formalizations.Undecidability.FormulaCorrespondence
import DistributedSynthesis.Formalizations.Undecidability.SoundnessCorrespondence
import DistributedSynthesis.Formalizations.Undecidability.Adversaries
import DistributedSynthesis.Formalizations.Undecidability.GuardedFormulaCorrespondence

/-! # Perfect-recall LTL synthesis: counter-machine reduction
Every encoded two-counter machine is translated by a primitive-recursive
compiler to an LTL specification that is realizable exactly when the machine
does not halt from its zero-initialized configuration. The target has
singleton inputs, finite output alphabets depending on the machine, and
unrestricted sequences of the three communication graphs. Specifications may
inspect graph letters, and strategies have full-view perfect recall.

The output tuple is the current manuscript's right-plan-only encoding.
`CounterMachine.Paper.checks_realizable_iff_nonhalting` identifies the exact
formula clauses with nonhalting. `Paper.source_checks` verifies the explicit
realizing algorithm, and `Paper.checks_safety` proves its safety objective.
The arithmetic and adversary modules expose the logarithmic counter identity,
closure transfer, and guarded safety reduction. `Paper.formula_logarithmic_run`
derives positive edge masses and the exact machine counters from any realizing
strategy. `Characterisation.guardFormula_realizable_iff` connects the exact
compiled guard to the closure-based reduction, and `guardedCompile_safety`
proves safety on its actual finite alphabet. The fixed-prefix guarded compiler
is primitive recursive (`guardedCompile_primrec`). Manuscript discrepancies
are documented in `Formalizations/Undecidability/README.md`.

The undecidability theorem in this module takes `SourceUndecidability` as an
explicit hypothesis. The proved source theorem discharges that hypothesis in
`Results.UnconditionalUndecidability`. -/
