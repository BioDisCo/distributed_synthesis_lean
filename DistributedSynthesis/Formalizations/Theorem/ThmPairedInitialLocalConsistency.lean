/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialBlockFromWinning
import DistributedSynthesis.Formalizations.Lemma.LemLocallyConsistentSenderNarrowing

/-!
# Local consistency at the first reversal

At the close of an initial left block, process one does not receive in a
`right` round.  Its reversal output may depend on its current input but not
on process two's hidden current input.  The mirror law holds for process two
when an initial right block closes by `left`.

These laws mention only equality between entries of one contingent table.
They do not reveal which process is the strict leader and require no leader
signal or hierarchy transducer.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- The no-receive process-one output is independent of current input two. -/
def InitialLeftTableLocallyConsistent
    (table : In₁ × In₂ ->
      InitialLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ inputOne inputTwo inputTwo',
    (table (inputOne, inputTwo)).reversingOne =
      (table (inputOne, inputTwo')).reversingOne

/-- The mirrored no-receive process-two output is independent of input one. -/
def InitialRightTableLocallyConsistent
    (table : In₂ × In₁ ->
      InitialRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ inputTwo inputOne inputOne',
    (table (inputTwo, inputOne)).reversingTwo =
      (table (inputTwo, inputOne')).reversingTwo

/-- The initial-left restriction of an actual distributed strategy obeys
the table law at every full-information prefix. -/
theorem initialLeftTableLocallyConsistent_lambdaOfStrategy
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₁ × In₂)) :
    InitialLeftTableLocallyConsistent
      (initialLeftReceiverStrategy (initialLeftLambdaOfStrategy strategy) past) := by
  intro inputOne inputTwo inputTwo'
  simp [InitialLeftTableLocallyConsistent, initialLeftReceiverStrategy,
    initialLeftLambdaOfStrategy, rightEnvironment, nextView,
    advanceViewsWithEnvironment]

/-- Mirror of `initialLeftTableLocallyConsistent_lambdaOfStrategy`. -/
theorem initialRightTableLocallyConsistent_lambdaOfStrategy
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (past : List (In₂ × In₁)) :
    InitialRightTableLocallyConsistent
      (initialRightReceiverStrategy (initialRightLambdaOfStrategy strategy) past) := by
  intro inputTwo inputOne inputOne'
  simp [InitialRightTableLocallyConsistent, initialRightReceiverStrategy,
    initialRightLambdaOfStrategy, leftEnvironment, nextView,
    advanceViewsWithEnvironment]

end DetParityAutomaton

end DistributedSynthesis
