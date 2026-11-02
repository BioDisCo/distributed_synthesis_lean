/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines.MMA2ToMM2
import DistributedSynthesis.Library.Computability.CounterMachines.MathlibBridge.BinaryUniversalStackMachine
import DistributedSynthesis.Library.Computability.CounterMachines.BSMMacros
import DistributedSynthesis.Library.Computability.CounterMachines.BSMSource
import DistributedSynthesis.Library.Computability.CounterMachines.MMSource
import DistributedSynthesis.Library.Computability.CounterMachines.FRACTRANSource
import DistributedSynthesis.Library.Computability.CounterMachines.Source

/-! # Modular Rocq-to-Lean counter-machine port

The port currently proves MMA2-to-MM2 and arbitrary-input-to-zero-initialized
MM2 reductions, including primitive recursiveness and exact halting equivalence.
The independent Mathlib bridge proves unconditional halting undecidability for
one fixed finite-control four-stack machine, now with a verified binary-stack
compiler and primitive-recursive binary inputs. The Rocq BSM semantics and local
jump/peek blocks are proved separately. `TM2ToBSM.compile_correct` now proves
whole-program control compilation, and `BSMSource.halting_not_computable` proves
unconditional halting undecidability for the Rocq four-stack BSM model.
`BSMToMM.compile_correct` now ports the register simulation, and
`MMSource.halting_not_computable` supplies an unconditional six-register MM
source with an explicit primitive-recursive input reduction. The two-phase
`MMToFRACTRAN` compiler now proves halting equivalence without a self-jump
restriction. `FRACTRANSource.regularHalting_not_computable` supplies unconditional
regular FRACTRAN halting undecidability, again with a primitive-recursive reduction.
`FRACTRANToMMA.compile_correct` now proves the final two-register simulation.
`SourcePort.source` discharges `CounterMachine.MM2.SourceUndecidability` through
an explicit primitive-recursive Mathlib-code reduction. No source premise,
new axiom, or distributed-synthesis dependency remains in this library.
See `CounterMachines/README.md` for credits, licensing, and exact status.
-/
