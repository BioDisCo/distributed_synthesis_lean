/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedPhysicalSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonFiniteSiblingMove

/-!
# Cross-side coherence of the guarded common sibling moves

The right and left guarded tables are extracted separately, but their pinned
first records come from the two projections of one literal common semantic
world.  This file records the resulting cross-side equations.  They are the
fail-fast anti-mosaic test at a repeated simultaneous round: the `.both`
closing output stored for either process in one receiver table is exactly the
`.both` informed output stored for that process in the other receiver table.

The equalities use no graph, orientation, leader bit, or semantic-history
test at runtime.  The graph is used only in the proof that the two pinned
records are projections of the same literal semantic round.
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

private abbrev CommonControl :=
  ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin

/-! ## The two finite guarded moves at one common world -/

/-- Right/common--strict-left guarded table at an arbitrary recurrent common
control. -/
noncomputable def profiledRawJointHybridCommonGuardedRightSiblingMove
    (control : CommonControl A strategy hwin) (current : In₁ × In₂) :
    ProfiledRawJointGuardedRightPhysicalSiblingMove A :=
  profiledRawJointGuardedRightPhysicalSiblingMoveOf A hwin
    (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
    (profiledRawJointBothRestartDirection current)
    ((profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
      ).procOneMember A)
    (profiledRawJointHybridCommonSibling_right A strategy hwin control current)

/-- Left/common--strict-right mirror. -/
noncomputable def profiledRawJointHybridCommonGuardedLeftSiblingMove
    (control : CommonControl A strategy hwin) (current : In₁ × In₂) :
    ProfiledRawJointGuardedLeftPhysicalSiblingMove A :=
  profiledRawJointGuardedLeftPhysicalSiblingMoveOf A hwin
    (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
    (profiledRawJointBothRestartDirection current)
    ((profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
      ).procTwoMember A)
    (profiledRawJointHybridCommonSibling_left A strategy hwin control current)

/-! ## Literal anti-mosaic equations -/

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Process one's `.both` closing output in the right receiver record is the
process-one `.both` informed output in the left receiver record. -/
theorem profiledRawJointHybridCommonSiblingLiteralRoots_outputOne
    (control : CommonControl A strategy hwin) (current input : In₁ × In₂) :
    let family :=
      profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
    let direction := profiledRawJointBothRestartDirection current
    let world :=
      profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
    let rightRecord :=
      profiledRawJointRightSiblingLiteralRootRecord A hwin family direction
        (world.procOneMember A)
        (profiledRawJointHybridCommonSibling_right A strategy hwin control
          current)
        (input.2, input.1)
    let leftRecord :=
      profiledRawJointLeftSiblingLiteralRootRecord A hwin family direction
        (world.procTwoMember A)
        (profiledRawJointHybridCommonSibling_left A strategy hwin control
          current)
        input
    rightRecord.2.1.physical.closingBoth =
      pairedLeftInformedForRow .both leftRecord.2.1.physical := by
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Process-two mirror. -/
theorem profiledRawJointHybridCommonSiblingLiteralRoots_outputTwo
    (control : CommonControl A strategy hwin) (current input : In₁ × In₂) :
    let family :=
      profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
    let direction := profiledRawJointBothRestartDirection current
    let world :=
      profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
    let rightRecord :=
      profiledRawJointRightSiblingLiteralRootRecord A hwin family direction
        (world.procOneMember A)
        (profiledRawJointHybridCommonSibling_right A strategy hwin control
          current)
        (input.2, input.1)
    let leftRecord :=
      profiledRawJointLeftSiblingLiteralRootRecord A hwin family direction
        (world.procTwoMember A)
        (profiledRawJointHybridCommonSibling_left A strategy hwin control
          current)
        input
    leftRecord.2.1.physical.closingBoth =
      pairedRightInformedForRow .both rightRecord.2.1.physical := by
  rfl

/-! ## The extracted finite controllers inherit the equations -/

/-- The first labels emitted by the two independently narrowed finite tables
still agree on process one's actual simultaneous output. -/
theorem profiledRawJointHybridCommonGuardedRoots_outputOne
    (control : CommonControl A strategy hwin) (current input : In₁ × In₂)
    (rightMember leftMember : Bool) :
    let rightMove :=
      profiledRawJointHybridCommonGuardedRightSiblingMove A strategy hwin
        control current
    let leftMove :=
      profiledRawJointHybridCommonGuardedLeftSiblingMove A strategy hwin
        control current
    let rightRecord := narrowedRecord
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A rightMove.1
        rightMember)
      ((rightMove.memberController A rightMember).labeledTree [])
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A rightMove.1
        rightMember).initial (input.2, input.1)
    let leftRecord := narrowedRecord
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A leftMove.1
        leftMember)
      ((leftMove.memberController A leftMember).labeledTree [])
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A leftMove.1
        leftMember).initial input
    rightRecord.2.1.physical.closingBoth =
      pairedLeftInformedForRow .both leftRecord.2.1.physical := by
  classical
  let family :=
    profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
  let direction := profiledRawJointBothRestartDirection current
  let world :=
    profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
  have hright :=
    profiledRawJointGuardedRightPhysicalSiblingMoveOf_root_record A hwin
      family direction (world.procOneMember A)
      (profiledRawJointHybridCommonSibling_right A strategy hwin control
        current)
      rightMember (input.2, input.1)
  have hleft :=
    profiledRawJointGuardedLeftPhysicalSiblingMoveOf_root_record A hwin
      family direction (world.procTwoMember A)
      (profiledRawJointHybridCommonSibling_left A strategy hwin control
        current)
      leftMember input
  dsimp only
  simp only [profiledRawJointHybridCommonGuardedRightSiblingMove,
    profiledRawJointHybridCommonGuardedLeftSiblingMove]
  rw [hright, hleft]
  exact profiledRawJointHybridCommonSiblingLiteralRoots_outputOne A strategy
    hwin control current input

/-- Process-two mirror. -/
theorem profiledRawJointHybridCommonGuardedRoots_outputTwo
    (control : CommonControl A strategy hwin) (current input : In₁ × In₂)
    (rightMember leftMember : Bool) :
    let rightMove :=
      profiledRawJointHybridCommonGuardedRightSiblingMove A strategy hwin
        control current
    let leftMove :=
      profiledRawJointHybridCommonGuardedLeftSiblingMove A strategy hwin
        control current
    let rightRecord := narrowedRecord
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A rightMove.1
        rightMember)
      ((rightMove.memberController A rightMember).labeledTree [])
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A rightMove.1
        rightMember).initial (input.2, input.1)
    let leftRecord := narrowedRecord
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A leftMove.1
        leftMember)
      ((leftMove.memberController A leftMember).labeledTree [])
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A leftMove.1
        leftMember).initial input
    leftRecord.2.1.physical.closingBoth =
      pairedRightInformedForRow .both rightRecord.2.1.physical := by
  classical
  let family :=
    profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
  let direction := profiledRawJointBothRestartDirection current
  let world :=
    profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
  have hright :=
    profiledRawJointGuardedRightPhysicalSiblingMoveOf_root_record A hwin
      family direction (world.procOneMember A)
      (profiledRawJointHybridCommonSibling_right A strategy hwin control
        current)
      rightMember (input.2, input.1)
  have hleft :=
    profiledRawJointGuardedLeftPhysicalSiblingMoveOf_root_record A hwin
      family direction (world.procTwoMember A)
      (profiledRawJointHybridCommonSibling_left A strategy hwin control
        current)
      leftMember input
  dsimp only
  simp only [profiledRawJointHybridCommonGuardedRightSiblingMove,
    profiledRawJointHybridCommonGuardedLeftSiblingMove]
  rw [hright, hleft]
  exact profiledRawJointHybridCommonSiblingLiteralRoots_outputTwo A strategy
    hwin control current input

end

end DetParityAutomaton

end DistributedSynthesis
