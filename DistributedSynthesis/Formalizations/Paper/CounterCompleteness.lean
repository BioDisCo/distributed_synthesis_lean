/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.OneCounterSoundness

/-!
# Completeness of the counter encoding

Manuscript source label: `lem:completeness`.

## Paper statement

If $M_\single$ does not halt, then $f$ given by Algorithm~\ref{algo:completeness} realizes $\phi(M_\single)$.

## Correspondence

sourceStrategy is the paper's right-plan construction, projected to the scalar output
tuple. OnlyFirst expresses one-counter syntax and is discharged by ofCode_onlyFirst.

## Reading the proof

`source_realizes` checks the right-plan strategy after projecting its outputs
to the scalar tuple. `completeness` instantiates this construction for an
arbitrary scalar program, using `ofCode_onlyFirst` to discharge the encoding
condition. It does not assume an invariant about the machine's run.

See the [proof locations](PROOFS.md#completeness-of-the-counter-encoding) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation
open DistributedSynthesis.CounterMachine.OneCounter

namespace DistributedSynthesis.Paper.CounterCompleteness

universe u_1

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.source_realizes`. -/
theorem source_realizes :
    ∀ {Q : Type u_1} [DecidableEq Q] [inst : Fintype Q]
      (M : CounterMachine.Machine Q),
      OnlyFirst M →
        Nonhalting M →
          ∀ (env : EnvironmentSequence Unit Unit),
            LTL.Satisfies FiniteLetterLTL.interp (execution (sourceStrategy M) env)
              (formula M) :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.source_realizes


/-- The constructed strategy works for every nonhalting scalar program. -/
theorem completeness {Q : Type*} [DecidableEq Q] [Fintype Q]
    (initial : Q) (code : Q → Option (Q ⊕ (Q × Q)))
    (nonhalting : Nonhalting (ofCode initial code)) (env : EnvironmentSequence Unit Unit) :
    LTL.Satisfies FiniteLetterLTL.interp
      (execution (sourceStrategy (ofCode initial code)) env) (formula (ofCode initial code)) :=
  source_realizes (ofCode initial code) (ofCode_onlyFirst initial code) nonhalting env

end DistributedSynthesis.Paper.CounterCompleteness
