/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDPACombinators
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRationalTree
import DistributedSynthesis.Formalizations.Lemma.LemIndexedLineageRootDeduplication

/-!
# Fail-fast test for the raw joint-family public code

This file uses genuine strategy-generated delay-one histories.  It checks
whether the finite payload currently proposed for one raw right-family slot
(the paired DPA code, epoch state, and first informed boundary profile)
determines the process-one block lambda.

It does not.  For the accept-all one-state DPA, two reachable paired entries
have identical finite payloads while their blind sender lambdas already
disagree on the empty block history.  A singleton within-lane equality pattern
cannot distinguish the entries either.  Thus a public state containing only
the profiled slots and within-lane patterns cannot *recover the original
semantic lambda/shared origin* as a function of that state.

This is deliberately not overstated as an incompatible-legality result.
`ProfiledRawJointLambdaFamilyMove.Valid code move` is indexed only by `code`;
therefore equal codes definitionally have the same set of syntactically legal
moves.  In this accept-all instance an alternative common winning lambda
certainly exists.  The remaining substantive test is semantic: a move selected
at the common finite state must have children represented at every co-occurring
exact source (or the construction must prove that replacing the original move
still yields one globally local strategy).  The collision below shows why
that source/child realization cannot be obtained by simply recovering the raw
strategy label from the four finite fields.
-/

namespace DistributedSynthesis

namespace DetParityAutomaton

/-- Process one distinguishes precisely the extra old `noRecv` nested below
the current receive and the following blind `right` step. -/
def rawJointCodeCollisionStrategy :
    StrategyPair Unit Unit Bool Bool where
  one := fun view =>
    match view with
    | .noRecv (.recv (.noRecv _ _) _ _ _) _ => true
    | _ => false
  two := fun _ => false

/-- The older base is empty. -/
def rawJointCodeCollisionBaseZero :
    History Unit Unit Graph Bool Bool :=
  []

/-- The second base is a genuine one-round `right` execution prefix. -/
def rawJointCodeCollisionBaseOne :
    History Unit Unit Graph Bool Bool :=
  History.append []
    (nextRound rawJointCodeCollisionStrategy [] ⟨(), (), Graph.right⟩)

theorem rawJointCodeCollisionBaseOne_generated :
    StrategyGeneratedPrefix rawJointCodeCollisionStrategy
      rawJointCodeCollisionBaseOne := by
  exact StrategyGeneratedPrefix.append StrategyGeneratedPrefix.empty _

/-- Reachable process-one pending pair at the initial base. -/
def rawJointCodeCollisionEntryZero :
    ProcOnePairedEntryRep rawJointCodeCollisionStrategy :=
  procOneFreshPair rawJointCodeCollisionStrategy rawJointCodeCollisionBaseZero
    StrategyGeneratedPrefix.empty () ()

/-- Reachable process-one pending pair one round later. -/
def rawJointCodeCollisionEntryOne :
    ProcOnePairedEntryRep rawJointCodeCollisionStrategy :=
  procOneFreshPair rawJointCodeCollisionStrategy rawJointCodeCollisionBaseOne
    rawJointCodeCollisionBaseOne_generated () ()

/-- The concrete accept-all objective used by the collision. -/
abbrev rawJointCodeCollisionDPA :=
  (top : DetParityAutomaton (RoundRecord Unit Unit Graph Bool Bool))

/-- The collision strategy is a genuine realizer of the objective. -/
theorem rawJointCodeCollisionStrategy_wins :
    ∀ env : EnvironmentSequence Unit Unit,
      rawJointCodeCollisionDPA.Accepts
        (execution rawJointCodeCollisionStrategy env) := by
  intro env
  exact top_accepts _

/-- The exact finite payload stored by one right slot of the proposed public
code, before the outer optional/indexed family wrapper is added. -/
def rawJointCodeCollisionSlot
    (entry : ProcOnePairedEntryRep rawJointCodeCollisionStrategy) :
    (((rawJointCodeCollisionDPA.State × rawJointCodeCollisionDPA.State) ×
        rawJointCodeCollisionDPA.State) ×
      RightInitialActionProfile (In₁ := Unit) (In₂ := Unit) (Out₂ := Bool)) :=
  ((entry.code (A := rawJointCodeCollisionDPA), ()),
    rightInitialFirstProfile entry.lambdaOfStrategy)

/-- A four-field public family code for the finite-code collision example. -/
structure RawJointFiniteCodeMirror where
  right : Unit → Option
    ((((rawJointCodeCollisionDPA.State ×
          rawJointCodeCollisionDPA.State) ×
        rawJointCodeCollisionDPA.State) ×
      RightInitialActionProfile
        (In₁ := Unit) (In₂ := Unit) (Out₂ := Bool)))
  left : Unit → Option
    ((((rawJointCodeCollisionDPA.State ×
          rawJointCodeCollisionDPA.State) ×
        rawJointCodeCollisionDPA.State) ×
      LeftInitialActionProfile
        (In₁ := Unit) (In₂ := Unit) (Out₁ := Bool)))
  rightPattern : IndexedLineageEqualityPattern Unit
  leftPattern : IndexedLineageEqualityPattern Unit

/-- Singleton-right family obtained from one reachable entry. -/
def rawJointCodeCollisionFamilyCode
    (entry : ProcOnePairedEntryRep rawJointCodeCollisionStrategy) :
    RawJointFiniteCodeMirror where
  right := fun _ => some (rawJointCodeCollisionSlot entry)
  left := fun _ => none
  rightPattern := fun _ _ => true
  leftPattern := fun _ _ => false

/-- Both entries are genuine generated pending pairs. -/
theorem rawJointCodeCollision_entries_generated :
    StrategyGeneratedPrefix rawJointCodeCollisionStrategy
        rawJointCodeCollisionEntryZero.leftHistory ∧
      StrategyGeneratedPrefix rawJointCodeCollisionStrategy
        rawJointCodeCollisionEntryZero.bothHistory ∧
      StrategyGeneratedPrefix rawJointCodeCollisionStrategy
        rawJointCodeCollisionEntryOne.leftHistory ∧
      StrategyGeneratedPrefix rawJointCodeCollisionStrategy
        rawJointCodeCollisionEntryOne.bothHistory := by
  exact ⟨rawJointCodeCollisionEntryZero.leftGenerated,
    rawJointCodeCollisionEntryZero.bothGenerated,
    rawJointCodeCollisionEntryOne.leftGenerated,
    rawJointCodeCollisionEntryOne.bothGenerated⟩

/-- The complete finite right-slot payload collides. -/
theorem rawJointCodeCollision_sameSlot :
    rawJointCodeCollisionSlot rawJointCodeCollisionEntryZero =
      rawJointCodeCollisionSlot rawJointCodeCollisionEntryOne := by
  rfl

/-- Optional slots and both within-lane patterns still collide. -/
theorem rawJointCodeCollision_sameWholeFamilyCode :
    rawJointCodeCollisionFamilyCode rawJointCodeCollisionEntryZero =
      rawJointCodeCollisionFamilyCode rawJointCodeCollisionEntryOne := by
  rfl

/-- Nevertheless the process-local raw lambdas disagree at the very first
blind output of the following right block. -/
theorem rawJointCodeCollision_blind_outputs :
    rawJointCodeCollisionEntryZero.lambdaOfStrategy.blind [] () = false ∧
      rawJointCodeCollisionEntryOne.lambdaOfStrategy.blind [] () = true := by
  constructor <;> rfl

theorem rawJointCodeCollision_incompatibleBlindLambdas :
    rawJointCodeCollisionEntryZero.lambdaOfStrategy.blind ≠
      rawJointCodeCollisionEntryOne.lambdaOfStrategy.blind := by
  intro heq
  have hpoint := congrFun (congrFun heq []) ()
  have hvalues := rawJointCodeCollision_blind_outputs
  simp [hvalues.1, hvalues.2] at hpoint

/-- No one blind lambda can literally recover both strategy projections.  This
is a recovery/semantic-origin obstruction, not a claim that the common finite
code has no other syntactically legal winning lambda. -/
theorem rawJointCodeCollision_noCommonLiteralBlindProjection :
    ¬ ∃ blind : SenderBlockStrategy Unit Bool,
      blind = rawJointCodeCollisionEntryZero.lambdaOfStrategy.blind ∧
        blind = rawJointCodeCollisionEntryOne.lambdaOfStrategy.blind := by
  rintro ⟨blind, hzero, hone⟩
  exact rawJointCodeCollision_incompatibleBlindLambdas (hzero.symm.trans hone)

/-- The smallest one-round enrichment separating this particular collision is
the blind initial action profile, missing from `RightInitialActionProfile`.
This statement does not claim that a bounded action prefix determines the
whole raw lambda. -/
theorem rawJointCodeCollision_blindInitialProfiles_ne :
    (fun input =>
        rawJointCodeCollisionEntryZero.lambdaOfStrategy.blind [] input) ≠
      (fun input =>
        rawJointCodeCollisionEntryOne.lambdaOfStrategy.blind [] input) := by
  intro heq
  have hpoint := congrFun heq ()
  have hvalues := rawJointCodeCollision_blind_outputs
  simp [hvalues.1, hvalues.2] at hpoint

/-- Kernel-checked verdict at the exact granularity of the proposed code:
reachable finite slot equality does not determine the raw sender projection.
For a singleton family, both within-lane patterns are definitionally the same,
so adding those patterns does not remove this collision. -/
theorem profiledRawJointFiniteCode_doesNotDetermineBlindLambda :
    ∃ (left right : ProcOnePairedEntryRep rawJointCodeCollisionStrategy),
      StrategyGeneratedPrefix rawJointCodeCollisionStrategy left.leftHistory ∧
      StrategyGeneratedPrefix rawJointCodeCollisionStrategy left.bothHistory ∧
      StrategyGeneratedPrefix rawJointCodeCollisionStrategy right.leftHistory ∧
      StrategyGeneratedPrefix rawJointCodeCollisionStrategy right.bothHistory ∧
      rawJointCodeCollisionSlot left = rawJointCodeCollisionSlot right ∧
      left.lambdaOfStrategy.blind ≠ right.lambdaOfStrategy.blind := by
  exact ⟨rawJointCodeCollisionEntryZero, rawJointCodeCollisionEntryOne,
    rawJointCodeCollision_entries_generated.1,
    rawJointCodeCollision_entries_generated.2.1,
    rawJointCodeCollision_entries_generated.2.2.1,
    rawJointCodeCollision_entries_generated.2.2.2,
    rawJointCodeCollision_sameSlot,
    rawJointCodeCollision_incompatibleBlindLambdas⟩

/-- The same verdict packaged with the whole four-field code and the fact that
the raw strategy wins the actual accept-all DPA objective. -/
theorem profiledRawJointWholeFiniteCode_same_but_blindLambda_incompatible :
    (∀ env : EnvironmentSequence Unit Unit,
        rawJointCodeCollisionDPA.Accepts
          (execution rawJointCodeCollisionStrategy env)) ∧
      rawJointCodeCollisionFamilyCode rawJointCodeCollisionEntryZero =
        rawJointCodeCollisionFamilyCode rawJointCodeCollisionEntryOne ∧
      rawJointCodeCollisionEntryZero.lambdaOfStrategy.blind ≠
        rawJointCodeCollisionEntryOne.lambdaOfStrategy.blind := by
  exact ⟨rawJointCodeCollisionStrategy_wins,
    rawJointCodeCollision_sameWholeFamilyCode,
    rawJointCodeCollision_incompatibleBlindLambdas⟩

end DetParityAutomaton

end DistributedSynthesis
