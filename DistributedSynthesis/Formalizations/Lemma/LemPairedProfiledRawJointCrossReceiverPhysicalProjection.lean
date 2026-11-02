/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedPhysicalSiblingCoherence

/-!
# Physical projection of a hidden-member cross receiver

A narrowed right receiver returns all four physical predictions stored in a
`PairedRightReceiverOutput`; its actual local strict/common-seam output is the
`informedBoth` coordinate.  The left receiver uses the mirror coordinate.
These projections do not inspect the hidden table member: that member has
already selected the finite receiver label inside the receiver's own state.

The existing anti-mosaic equations show why these are the correct physical
coordinates.  For arbitrary choices of the hidden right and left members,
the left receiver's `informedBoth` is the right table's `closingBoth`, and the
right receiver's `informedBoth` is the left table's `closingBoth`.  Thus both
local receives form one coherent simultaneous output without any runtime
graph, orientation, leader, or semantic-history argument.
-/

namespace DistributedSynthesis

universe u v x y s t z

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-! ## The two genuinely local physical projections -/

/-- Physical output emitted by process two from a right-block receiver
result.  The latent `first` coordinate is monitor data, not a runtime branch. -/
def pairedRightReceiverBothPhysicalOutput
    (output : PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) :
    Out₂ :=
  pairedRightInformedForRow .both output

/-- Process-one mirror for a left-block receiver result. -/
def pairedLeftReceiverBothPhysicalOutput
    (output : PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) :
    Out₁ :=
  pairedLeftInformedForRow .both output

@[simp] theorem pairedRightReceiverBothPhysicalOutput_eq
    (output : PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) :
    pairedRightReceiverBothPhysicalOutput output = output.informedBoth :=
  rfl

@[simp] theorem pairedLeftReceiverBothPhysicalOutput_eq
    (output : PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂)) :
    pairedLeftReceiverBothPhysicalOutput output = output.informedBoth :=
  rfl

/-- Strip a target certificate and read the physical right receiver output. -/
def profiledRawJointTargetRightReceiverBothPhysicalOutput
    {Target : Type t}
    (output : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target) : Out₂ :=
  pairedRightReceiverBothPhysicalOutput output.physical

/-- Target-parametric left mirror. -/
def profiledRawJointTargetLeftReceiverBothPhysicalOutput
    {Target : Type t}
    (output : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) Target) : Out₁ :=
  pairedLeftReceiverBothPhysicalOutput output.physical

/-- Compose the physical projection with any finite local right-receiver
transition result.  The next-state coordinate is irrelevant to the output. -/
def profiledRawJointTargetRightReceiverResultPhysicalOutput
    {Target : Type t} {Next : Type z}
    (result :
      ProfiledRawJointTargetRightReceiverOutput
          (Out₁ := Out₁) (Out₂ := Out₂) Target × Next) : Out₂ :=
  profiledRawJointTargetRightReceiverBothPhysicalOutput result.1

/-- Compose the mirror projection with a local left-receiver result. -/
def profiledRawJointTargetLeftReceiverResultPhysicalOutput
    {Target : Type t} {Next : Type z}
    (result :
      ProfiledRawJointTargetLeftReceiverOutput
          (Out₁ := Out₁) (Out₂ := Out₂) Target × Next) : Out₁ :=
  profiledRawJointTargetLeftReceiverBothPhysicalOutput result.1

/-! ## Abstract cross-side coherence -/

/-- The two `informedBoth` projections form exactly the pair of opposite
`closingBoth` predictions whenever the anti-mosaic equations hold. -/
theorem pairedReceiverBothPhysicalOutputs_eq_closingBoth
    (right :
      PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    (left :
      PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    (hone : right.closingBoth = pairedLeftInformedForRow .both left)
    (htwo : left.closingBoth = pairedRightInformedForRow .both right) :
    (pairedLeftReceiverBothPhysicalOutput left,
      pairedRightReceiverBothPhysicalOutput right) =
      (right.closingBoth, left.closingBoth) := by
  exact Prod.ext hone.symm htwo.symm

/-- Target certificates do not alter the same cross-side equation. -/
theorem profiledRawJointTargetReceiverBothPhysicalOutputs_eq_closingBoth
    {RightTarget : Type t} {LeftTarget : Type z}
    (right : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) RightTarget)
    (left : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) LeftTarget)
    (hone : right.physical.closingBoth =
      pairedLeftInformedForRow .both left.physical)
    (htwo : left.physical.closingBoth =
      pairedRightInformedForRow .both right.physical) :
    (profiledRawJointTargetLeftReceiverBothPhysicalOutput left,
      profiledRawJointTargetRightReceiverBothPhysicalOutput right) =
      (right.physical.closingBoth, left.physical.closingBoth) :=
  pairedReceiverBothPhysicalOutputs_eq_closingBoth right.physical left.physical
    hone htwo

/-! ## The guarded common tables satisfy the equation for every member -/

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

/-- At a guarded common root, projecting `informedBoth` from both narrowed
receiver records gives the coherent simultaneous output for arbitrary hidden
right/left table members.  No member test is needed by the projection. -/
theorem profiledRawJointHybridCommonGuardedRoots_receiverBothPhysicalOutputs
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
    (profiledRawJointTargetLeftReceiverBothPhysicalOutput leftRecord.2.1,
      profiledRawJointTargetRightReceiverBothPhysicalOutput rightRecord.2.1) =
      (rightRecord.2.1.physical.closingBoth,
        leftRecord.2.1.physical.closingBoth) := by
  dsimp only
  apply profiledRawJointTargetReceiverBothPhysicalOutputs_eq_closingBoth
  · exact profiledRawJointHybridCommonGuardedRoots_outputOne A strategy hwin
      control current input rightMember leftMember
  · exact profiledRawJointHybridCommonGuardedRoots_outputTwo A strategy hwin
      control current input rightMember leftMember

end


end DetParityAutomaton

end DistributedSynthesis
