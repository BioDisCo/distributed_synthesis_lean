/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntrySelectionStrictPrefixFeasibility

/-!
# The literal post-resolve strict/common overlap

The entry bootstrap closes a one-sided physical block at the resolving input.
The resulting semantic child is itself a fresh paired entry: for a left block
its two histories use `left` and `both` at the resolving input after the same
preceding left block; for a right block they use `right` and `both` after the
same preceding right block.  These are exactly the two pending-overlap facts
needed before the strict and common obligations are narrowed jointly.

The live-member equations below are essential.  They identify the explicit
fresh pairs with the members of the actual one-sided semantic children, not
merely with unrelated pairs having the same finite incidence code.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

/-! ## Explicit live members of the two actual children -/

/-- The literal process-one pair produced by the left block consisting of
`entry`, closed at `input` from the simultaneous row of the current common
occurrence. -/
def profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProcOnePairedEntryRep strategy × A.State :=
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy initial
  profiledRawLeftSemanticChildPair A (installed.world.procTwoMember A) .both
    [entry] input

/-- The process-two mirror, with the physical right-block inputs swapped into
receiver/sender order. -/
def profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProcTwoPairedEntryRep strategy × A.State :=
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy initial
  profiledRawRightSemanticChildPair A (installed.world.procOneMember A) .both
    [(entry.2, entry.1)] (input.2, input.1)

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- The explicit left-block pair is the live member of the actual semantic
child reconstructed in the feasibility audit. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt_live
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt
      A strategy initial entry input).family.right () =
      some
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
          A strategy initial entry input) := by
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy initial
  let source := installed.world.oneSidedState A .left
  let actual := profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) .both [entry] input
  have hslot :
      profiledRawJointOneSidedCurrentSlots A .left (source.code A) () =
        some (.inr (installed.world.procTwoSlot A)) := by
    rfl
  have hreflexiveCode := source.leftPattern_self_of_currentSlot A
    (.inr (installed.world.procTwoSlot A)) hslot .both
  have hreflexive :
      source.family.leftPattern A ((), .both) ((), .both) = true := by
    simpa [ProfiledRawJointOneSidedSemanticState.code,
      ProfiledRawJointSemanticFamily.incidenceCode] using hreflexiveCode
  have hselected := source.family.leftSelectedChild_eq_some_of_pattern A
    actual.direction () (installed.world.procTwoMember A) rfl .both
      hreflexive
  simpa [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt,
    installed, source, actual,
    ProfiledRawJointOneSidedSemanticState.step] using hselected

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Right-block live-member mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt_live
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt
      A strategy initial entry input).family.left () =
      some
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
          A strategy initial entry input) := by
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy initial
  let source := installed.world.oneSidedState A .right
  let actual := profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) .both
      [(entry.2, entry.1)] (input.2, input.1)
  have hslot :
      profiledRawJointOneSidedCurrentSlots A .right (source.code A) () =
        some (.inl (installed.world.procOneSlot A)) := by
    rfl
  have hreflexiveCode := source.rightPattern_self_of_currentSlot A
    (.inl (installed.world.procOneSlot A)) hslot .both
  have hreflexive :
      source.family.rightPattern A ((), .both) ((), .both) = true := by
    simpa [ProfiledRawJointOneSidedSemanticState.code,
      ProfiledRawJointSemanticFamily.incidenceCode] using hreflexiveCode
  have hselected := source.family.rightSelectedChild_eq_some_of_pattern A
    actual.direction () (installed.world.procOneMember A) rfl .both
      hreflexive
  simpa [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt,
    installed, source, actual,
    ProfiledRawJointOneSidedSemanticState.step] using hselected

/-! ## Exact post-resolve pending overlaps -/

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Process one's strict-left and simultaneous histories at the resolving
input form the required literal pending overlap. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPostResolvePendingOverlap
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    let pair :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
        A strategy initial entry input
    ProcOnePendingOverlap pair.1.leftHistory pair.1.bothHistory := by
  dsimp only
  exact
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
      A strategy initial entry input).1.pending

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Process-two mirror. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPostResolvePendingOverlap
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    let pair :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
        A strategy initial entry input
    ProcTwoPendingOverlap pair.1.rightHistory pair.1.bothHistory := by
  dsimp only
  exact
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
      A strategy initial entry input).1.pending

/-! ## Exact sender installed by the root-pinned child policy -/

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At the strict-left child, the root-pinned policy installs the literal
process-one lambda of the live post-resolve pair. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt_rightLambda
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    let pair :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
        A strategy initial entry input
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt
      A strategy hwin initial entry input).rootMove.rightLambda () =
      some pair.1.lambdaOfStrategy := by
  dsimp only
  rw [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt_rootMove
      A strategy hwin initial entry input]
  simp only [ProfiledRawJointOneSidedSemanticState.move,
    ProfiledRawJointSemanticFamily.move,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftLiteralChildAt_live
      A strategy initial entry input, Option.map_some]

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The installed strict-left sender is simultaneously the original strategy
sender on the strict and common histories of the pending pair. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt_sender
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    let pair :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
        A strategy initial entry input
    ∃ lambda : ProcOnePairedRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt
        A strategy hwin initial entry input).rootMove.rightLambda () =
          some lambda ∧
      pairedRightSenderStrategy lambda =
        blockSenderOne strategy pair.1.leftHistory ∧
      pairedRightSenderStrategy lambda =
        blockSenderOne strategy pair.1.bothHistory := by
  dsimp only
  let pair :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftPairAt
      A strategy initial entry input
  refine ⟨pair.1.lambdaOfStrategy, ?_, rfl, ?_⟩
  · exact
      profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictLeftChildPolicyAt_rightLambda
        A strategy hwin initial entry input
  · simpa [pairedRightSenderStrategy] using
      pair.1.lambdaOfStrategy_blind_eq_both

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At the strict-right child, the mirror root-pinned policy installs the
literal process-two lambda. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt_leftLambda
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    let pair :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
        A strategy initial entry input
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt
      A strategy hwin initial entry input).rootMove.leftLambda () =
      some pair.1.lambdaOfStrategy := by
  dsimp only
  rw [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt_rootMove
      A strategy hwin initial entry input]
  simp only [ProfiledRawJointOneSidedSemanticState.move,
    ProfiledRawJointSemanticFamily.move,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightLiteralChildAt_live
      A strategy initial entry input, Option.map_some]

omit [DecidableEq In₁] [DecidableEq In₂] in
omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Strict-right sender mirror, simultaneously identified on the `right` and
`both` histories. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt_sender
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    let pair :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
        A strategy initial entry input
    ∃ lambda : ProcTwoPairedLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt
        A strategy hwin initial entry input).rootMove.leftLambda () =
          some lambda ∧
      pairedLeftSenderStrategy lambda =
        blockSenderTwo strategy pair.1.rightHistory ∧
      pairedLeftSenderStrategy lambda =
        blockSenderTwo strategy pair.1.bothHistory := by
  dsimp only
  let pair :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightPairAt
      A strategy initial entry input
  refine ⟨pair.1.lambdaOfStrategy, ?_, rfl, ?_⟩
  · exact
      profiledRawJointGuardedCommonLiteralCrossRootPinnedStrictRightChildPolicyAt_leftLambda
        A strategy hwin initial entry input
  · simpa [pairedLeftSenderStrategy] using
      pair.1.lambdaOfStrategy_blind_eq_both

end

end DetParityAutomaton

end DistributedSynthesis
