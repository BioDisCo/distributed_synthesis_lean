/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Undecidability.OneCounterTransport

/-!
# Nonhalting is equivalent to realizability

Manuscript source label: `thm:nonhalt<=>realizability`.

## Paper statement

Machine $M_\single$ does not halt if and only if $\phi(M_\single)$ is realizable.

## Correspondence

The code argument ranges over all scalar programs: none halts, inl increments, and inr
gives the zero and positive decrement branches. No OnlyFirst premise remains at this
endpoint.

## Reading the proof

See the [proof locations](PROOFS.md#nonhalting-is-equivalent-to-realizability) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation
open DistributedSynthesis.CounterMachine.OneCounter

namespace DistributedSynthesis.Paper.CounterEquivalence

universe u_1

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.ofCode_realizable_iff`. -/
theorem ofCode_realizable_iff :
    ∀ {Q : Type u_1} [DecidableEq Q] [inst : Fintype Q] (initial : Q)
      (code : Q → Option (Q ⊕ Q × Q)),
      (∃ (σ : StrategyPair Unit Unit (Output Q) (Output Q)),
          ∀ (env : EnvironmentSequence Unit Unit),
            LTL.Satisfies FiniteLetterLTL.interp (execution σ env)
              (formula (ofCode initial code))) ↔
        Nonhalting (ofCode initial code) :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.ofCode_realizable_iff

end DistributedSynthesis.Paper.CounterEquivalence
