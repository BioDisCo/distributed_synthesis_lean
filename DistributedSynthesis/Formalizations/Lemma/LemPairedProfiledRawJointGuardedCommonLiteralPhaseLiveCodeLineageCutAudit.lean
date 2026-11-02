/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseLiveFreshnessLineage
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralBranchStagePhysicalPriority

/-!
# Code-lineage audit at a fresh literal-table cut

The phase-live table exposes a literal target at every physical cut.  Before
using the accepted common-code lineage, one must check that a newly installed
table really starts in the corresponding literal child rather than in an
unrelated equal-code representative.

This file closes that check at the first table record.  For either orientation
and either stored table member, the live lane of the selected `.both` target at
depth zero is exactly the same lane of the next literal common-child code.  In
particular, the result also holds for the code-erased `false` member: its
first record remains root pinned even though later records are only constrained
by its finite table monitor.

The depth-zero qualification is essential.  The theorem does not identify a
positive-depth target with the next occurrence selected by the outer
decorated policy.  That later identification additionally needs preservation
of the guarded child pair through the policy transition (the parent-linked
rationalization supplies precisely such data).  No executable endpoint here
receives a graph, orientation, hierarchy side, leader bit, history, or view.
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
variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))

/-! ## Literal first-block equations -/

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The right lane of the root-pinned left first-block target is the right
lane of the exact next common-child code. -/
theorem profiledRawJointGuardedFirstLeftTarget_both_rightSlot_eq_stepCode
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (input : In₁ × In₂) :
    let installed := profiledRawJointGuardedCommonPointInstalled A strategy
      point
    ((profiledRawJointGuardedFirstLeftTarget A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)
      (profiledRawJointHybridExactLeftPolicy A hwin installed) .both []
        input).1).family.right () =
      ((point.step A strategy input).code A strategy).family.right () := by
  dsimp only
  let installed := profiledRawJointGuardedCommonPointInstalled A strategy point
  let initial := installed.world.oneSidedState A .left
  let predicate := profiledRawJointHybridExactLeftRootPredicate A installed
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  let selected := profiledRawJointRootPinnedSelectedSource A strategy initial
    predicate package
  have hcode : selected.code A = initial.code A :=
    profiledRawJointRootPinnedSelectedSource_code A strategy initial predicate
      package
  have hmove : selected.move A = initial.move A := by
    rw [profiledRawJointRootPinnedSelectedSource_move A strategy initial
      predicate package]
    exact profiledRawJointHybridExactLeft_rootMove A installed package
  change
    (profiledRawJointOneSidedNext A (selected.code A) (selected.move A)
      (profiledRawJointUnitLeftActualDirection
        (In₁ := In₁) (In₂ := In₂) .both [] input)).family.right () = _
  rw [hcode, hmove]
  have hmerge := profiledRawJointBothTargetMerge_eq_commonWorldAfterBoth A
    (point.world A strategy) input
  have hfield := congrArg (fun code ↦ code.family.right ()) hmerge
  simpa [installed, initial,
    ProfiledRawJointGuardedCommonSemanticPoint.step,
    ProfiledRawJointGuardedCommonSemanticPoint.code,
    profiledRawJointGuardedCommonPointInstalled,
    profiledRawJointBothTargetMerge] using hfield

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Mirror: the left lane of the root-pinned right first-block target is the
left lane of the exact next common-child code. -/
theorem profiledRawJointGuardedFirstRightTarget_both_leftSlot_eq_stepCode
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (input : In₁ × In₂) :
    let installed := profiledRawJointGuardedCommonPointInstalled A strategy
      point
    ((profiledRawJointGuardedFirstRightTarget A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)
      (profiledRawJointHybridExactRightPolicy A hwin installed) .both []
        (input.2, input.1)).1).family.left () =
      ((point.step A strategy input).code A strategy).family.left () := by
  dsimp only
  let installed := profiledRawJointGuardedCommonPointInstalled A strategy point
  let initial := installed.world.oneSidedState A .right
  let predicate := profiledRawJointHybridExactRightRootPredicate A installed
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  let selected := profiledRawJointRootPinnedSelectedSource A strategy initial
    predicate package
  have hcode : selected.code A = initial.code A :=
    profiledRawJointRootPinnedSelectedSource_code A strategy initial predicate
      package
  have hmove : selected.move A = initial.move A := by
    rw [profiledRawJointRootPinnedSelectedSource_move A strategy initial
      predicate package]
    exact profiledRawJointHybridExactRight_rootMove A installed package
  change
    (profiledRawJointOneSidedNext A (selected.code A) (selected.move A)
      (profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂) .both []
          (input.2, input.1))).family.left () = _
  rw [hcode, hmove]
  have hmerge := profiledRawJointBothTargetMerge_eq_commonWorldAfterBoth A
    (point.world A strategy) input
  have hfield := congrArg (fun code ↦ code.family.left ()) hmerge
  simpa [installed, initial,
    ProfiledRawJointGuardedCommonSemanticPoint.step,
    ProfiledRawJointGuardedCommonSemanticPoint.code,
    profiledRawJointGuardedCommonPointInstalled,
    profiledRawJointBothTargetMerge] using hfield

private theorem literalRightFalsePlay_zero_rightSlot_eq_stepCode
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (input : In₁ × In₂) :
    let installed := profiledRawJointGuardedCommonPointInstalled A strategy
      point
    ((profiledRawJointLiteralRightBothExactReceiverRecv A strategy hwin
      installed
      (profiledRawJointLiteralRightBothExactReceiverInitial A strategy hwin
        installed false)
      input.1 input.2).1.1.target .both).family.right () =
      ((point.step A strategy input).code A strategy).family.right () := by
  dsimp only
  rw [profiledRawJointLiteralRightBothExactReceiverFirst_false_target_code]
  exact profiledRawJointGuardedFirstLeftTarget_both_rightSlot_eq_stepCode A
    strategy hwin point input

private theorem literalLeftFalsePlay_zero_leftSlot_eq_stepCode
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (input : In₁ × In₂) :
    let installed := profiledRawJointGuardedCommonPointInstalled A strategy
      point
    ((profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
      installed
      (profiledRawJointLiteralLeftBothExactReceiverInitial A strategy hwin
        installed false)
      input.2 input.1).1.1.target .both).family.left () =
      ((point.step A strategy input).code A strategy).family.left () := by
  dsimp only
  let installed := profiledRawJointGuardedCommonPointInstalled A strategy point
  have htarget :=
    profiledRawJointLiteralLeftBothExactReceiverFirst_false_target_code A
      strategy hwin installed .both (input.2, input.1)
  rw [show
    (profiledRawJointLiteralLeftBothExactReceiverRecv A strategy hwin
      installed
      (profiledRawJointLiteralLeftBothExactReceiverInitial A strategy hwin
        installed false)
      input.2 input.1).1.1.target .both =
      (profiledRawJointGuardedFirstRightTarget A strategy
        (installed.world.oneSidedState A .right)
        (profiledRawJointHybridExactRightRootPredicate A installed)
        (profiledRawJointHybridExactRightPolicy A hwin installed) .both []
          (input.2, input.1)).1 from htarget]
  exact profiledRawJointGuardedFirstRightTarget_both_leftSlot_eq_stepCode A
    strategy hwin point input

/-! ## The internally selected table member -/

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin)

/-- At depth zero, either member selected by a right-seam table carries the
right lane of the exact next child of the occurrence stored in its key. -/
theorem literalRightSeamSelectedTableTargetCode_zero_rightSlot_eq_childStepCode
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (anchor : Bool) (env : Nat → In₁ × In₂) :
    let installed := package.literalRightSeamInstalled A strategy hwin key
    (literalRightSeamSelectedTableTargetCode A strategy hwin installed anchor
      env 0 .both).family.right () =
      (((package.literalRightSeamChildPoint A strategy hwin key).step A
        strategy (env 0)).code A strategy).family.right () := by
  cases anchor
  · dsimp only
    simpa [literalRightSeamSelectedTableTargetCode,
      profiledRawJointLiteralRightBothExactFalsePlay,
      literalRightSeamInstalled] using
        (literalRightFalsePlay_zero_rightSlot_eq_stepCode A strategy hwin
          (package.literalRightSeamChildPoint A strategy hwin key) (env 0))
  · dsimp only
    have htarget :=
      package.literalRightSeamExactTruePlay_zero_target A strategy hwin key env
        .both
    rw [literalRightSeamSelectedTableTargetCode, if_pos rfl, htarget]
    exact profiledRawJointGuardedFirstLeftTarget_both_rightSlot_eq_stepCode A
      strategy hwin (package.literalRightSeamChildPoint A strategy hwin key)
        (env 0)

/-- Mirror depth-zero equality for the selected left-seam member. -/
theorem literalLeftSeamSelectedTableTargetCode_zero_leftSlot_eq_childStepCode
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (anchor : Bool) (env : Nat → In₂ × In₁) :
    let installed := package.literalLeftSeamInstalled A strategy hwin key
    (literalLeftSeamSelectedTableTargetCode A strategy hwin installed anchor
      env 0 .both).family.left () =
      (((package.literalRightSeamChildPoint A strategy hwin key).step A
        strategy ((env 0).2, (env 0).1)).code A strategy).family.left () := by
  cases anchor
  · dsimp only
    simpa [literalLeftSeamSelectedTableTargetCode,
      profiledRawJointLiteralLeftBothExactFalsePlay,
      literalLeftSeamInstalled] using
        (literalLeftFalsePlay_zero_leftSlot_eq_stepCode A strategy hwin
          (package.literalRightSeamChildPoint A strategy hwin key)
            ((env 0).2, (env 0).1))
  · dsimp only
    have htarget :=
      package.literalLeftSeamExactTruePlay_zero_target A strategy hwin key env
        .both
    rw [literalLeftSeamSelectedTableTargetCode, if_pos rfl, htarget]
    exact profiledRawJointGuardedFirstRightTarget_both_leftSlot_eq_stepCode A
      strategy hwin (package.literalRightSeamChildPoint A strategy hwin key)
        ((env 0).2, (env 0).1)

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
