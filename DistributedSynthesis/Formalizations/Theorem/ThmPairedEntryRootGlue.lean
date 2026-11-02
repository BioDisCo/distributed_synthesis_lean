/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryBranchFlatten

/-!
# First-entry rational runs

This file constructs the two possible entries after round zero and packages
the rational runs supplied by a winning strategy for each first input pair.
These entries do not cover an arbitrarily long initial homogeneous block:
after an initial `left`, the paired process-one state describes the next
opposite/right block rather than another `left` continuation.

The stored root minimum is `A.initial`. Its single finite occurrence does
not affect parity; successor minima are computed by the paired transition.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)

/-- The `left`/`both` paired node created by the first input pair. -/
def firstProcOneMemory
    (inputOne : In₁) (inputTwo : In₂) :
    PairedStrategyMemory A strategy :=
  .processOne
    (procOneFreshPair strategy
      ([] : History In₁ In₂ Graph Out₁ Out₂)
      StrategyGeneratedPrefix.empty inputOne inputTwo)
    A.initial

/-- The `right`/`both` paired node created by the first input pair. -/
def firstProcTwoMemory
    (inputOne : In₁) (inputTwo : In₂) :
    PairedStrategyMemory A strategy :=
  .processTwo
    (procTwoFreshPair strategy
      ([] : History In₁ In₂ Graph Out₁ Out₂)
      StrategyGeneratedPrefix.empty inputOne inputTwo)
    A.initial

/-- Rational paired runs at all possible round-zero entries.  These runs are
the witnesses used to prove root-close feasibility; they are not alone a
finite implementation of an arbitrarily long initial one-sided block. -/
structure FirstEntryRationalRuns where
  processOne : ∀ inputOne inputTwo,
    (pairedEntryRunAutomaton A
      (firstProcOneMemory A strategy inputOne inputTwo).toTreeState).HasRationalRun
  processTwo : ∀ inputOne inputTwo,
    (pairedEntryRunAutomaton A
      (firstProcTwoMemory A strategy inputOne inputTwo).toTreeState).HasRationalRun

/-- A winning distributed strategy yields rational runs from every possible
first paired entry.  The only external input is the classical rational-run
basis, instantiated at each finite initial automaton state. -/
theorem firstEntryRationalRuns_of_winning
    [Inhabited In₁] [Inhabited In₂]
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ initialState : PairedEntryTreeState A,
      (pairedEntryRunAutomaton A initialState).RationalRunBasis) :
    FirstEntryRationalRuns A strategy := by
  constructor
  · intro inputOne inputTwo
    exact PairedStrategyMemory.hasRationalRun_of_winning_flattened
      (A := A) hwin (firstProcOneMemory A strategy inputOne inputTwo)
      (basis _)
  · intro inputOne inputTwo
    exact PairedStrategyMemory.hasRationalRun_of_winning_flattened
      (A := A) hwin (firstProcTwoMemory A strategy inputOne inputTwo)
      (basis _)

end DetParityAutomaton

end DistributedSynthesis
