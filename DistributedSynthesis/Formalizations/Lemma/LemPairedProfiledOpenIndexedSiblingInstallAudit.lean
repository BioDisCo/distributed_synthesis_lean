/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedCodePolicyUniformityGate
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndJointSafetyGame

/-!
# Sibling installation audit for the indexed code policy

There are two different assertions at the last locality seam, and they must
not be conflated.

* Operationally, a graph-blind receive table can choose one joint family move
  before Nature resolves `left`, `right`, or `both`.  In the existing joint
  family controller the receiver-side summaries on the hidden strict/both
  pairs are definitionally equal.  Thus the current receive does not require
  two child policy states to coordinate independent choices.
* The move labeling an indexed outer-tree node is source-typed by that node's
  active root carrier.  After one indexed successor the carriers are the
  cross-swapped child carriers.  Consequently the parent's indexed move is
  not automatically a legal move at either child.  If the same active move is
  valid at two codes, their corresponding root carriers must be equal.

The second point is the exact reason why the operational sibling fact alone
does not yet close the code-policy proof: one still needs a pre-graph choice
of the *next* source-typed family table (or an equivalent one-step retiming)
that preserves the parity run.  No orientation, graph, selected lineage, or
strict-leader bit is exposed below.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## What one rational-policy parent actually supplies -/

/-- Two finite policy states are siblings when they are successors of one
reachable parent state.  The directions remain proof-side environment data;
the definition does not make either direction observable to a process. -/
def ProfiledOpenIndexedCodePolicySiblings
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedCodeRationalPolicy A initialCode)
    (leftState rightState : ProfiledOpenIndexedCodePolicyState A initialCode) :
    Prop :=
  ∃ parentState : ProfiledOpenIndexedCodePolicyState A initialCode,
    ∃ leftDirection rightDirection :
        ProfiledOpenIndexedBiBeliefDirection
          (I := I) (In₁ := In₁) (In₂ := In₂),
      SourceFreeBeliefCodeParityRationalPolicy.Reachable
          (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
          initialCode (ProfiledOpenIndexedBiBeliefValid A)
          (profiledOpenIndexedBiBeliefNext A) policy parentState ∧
        policy.successor parentState leftDirection = leftState ∧
        policy.successor parentState rightDirection = rightState

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Siblinghood exposes one move at the common parent.  It deliberately does
not claim that this move realizes either child state. -/
theorem profiledOpenIndexedCodePolicySiblings_parentMove
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedCodeRationalPolicy A initialCode)
    (leftState rightState : ProfiledOpenIndexedCodePolicyState A initialCode)
    (hsiblings : ProfiledOpenIndexedCodePolicySiblings A initialCode policy
      leftState rightState) :
    ∃ parentState : ProfiledOpenIndexedCodePolicyState A initialCode,
      ∃ parentMove : ProfiledOpenIndexedBiBeliefMove A,
        ProfiledOpenIndexedCodePolicyMoveRealizesAt A initialCode policy
            parentState parentMove ∧
          ∃ leftDirection rightDirection :
              ProfiledOpenIndexedBiBeliefDirection
                (I := I) (In₁ := In₁) (In₂ := In₂),
            policy.successor parentState leftDirection = leftState ∧
              policy.successor parentState rightDirection = rightState := by
  rcases hsiblings with
    ⟨parentState, leftDirection, rightDirection, hreachable, hleft, hright⟩
  obtain ⟨parentMove, hmove⟩ :=
    SourceFreeBeliefCodeParityRationalPolicy.exists_sourceFreeMove
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode (ProfiledOpenIndexedBiBeliefValid A)
      (profiledOpenIndexedBiBeliefNext A) policy parentState hreachable
  exact ⟨parentState, parentMove, hmove, leftDirection, rightDirection,
    hleft, hright⟩

/-! ## The current hidden-graph output pair is already closed -/

/-- The exact current-round sibling law supplied by one parent move.  It asks
only for the two graph pairs which a process cannot distinguish: process two
on `right`/`both`, and process one on `left`/`both`. -/
def ProfiledOpenIndexedCurrentHiddenPairOutputCoherent
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A) : Prop :=
  (∀ rightLineage leftLineage rightRow leftRow inputOne inputTwo,
      (profiledOpenIndexedStrictRightInitialOutput A code move rightLineage
          rightRow inputOne inputTwo).2 =
        (profiledOpenIndexedBothInitialOutput A code move rightLineage
          leftLineage rightRow leftRow inputOne inputTwo).2) ∧
    (∀ rightLineage leftLineage rightRow leftRow inputOne inputTwo,
      (profiledOpenIndexedStrictLeftInitialOutput A code move leftLineage
          leftRow inputOne inputTwo).1 =
        (profiledOpenIndexedBothInitialOutput A code move rightLineage
          leftLineage rightRow leftRow inputOne inputTwo).1)

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] in
/-- Every fixed parent move passes the current hidden-graph pair test by
definition.  No policy-child move and no leader/orientation observation is
involved. -/
theorem profiledOpenIndexedCurrentHiddenPairOutputCoherent
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A) :
    ProfiledOpenIndexedCurrentHiddenPairOutputCoherent A code move := by
  constructor
  · intro rightLineage leftLineage rightRow leftRow inputOne inputTwo
    exact profiledOpenIndexed_right_both_initial_outputTwo A code move
      rightLineage leftLineage rightRow leftRow inputOne inputTwo
  · intro rightLineage leftLineage rightRow leftRow inputOne inputTwo
    exact profiledOpenIndexed_left_both_initial_outputOne A code move
      rightLineage leftLineage rightRow leftRow inputOne inputTwo

/-! ## The weaker, side-specific next-table staging gate -/

/-- The two table projections stored by process one: its blind right sender
and its left receiver.  This is the part that must agree on a process-one
local-belief fibre; process-two projections are irrelevant on that fibre. -/
def ProfiledOpenIndexedProcessOneInitialOutputCoherent
    (leftCode rightCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (leftMove rightMove : ProfiledOpenIndexedBiBeliefMove A) : Prop :=
  (∀ inputOne,
      profiledOpenIndexedRightBlindInitialOutput A leftMove inputOne =
        profiledOpenIndexedRightBlindInitialOutput A rightMove inputOne) ∧
    (∀ lineage row inputOne inputTwo,
      profiledOpenIndexedLeftReceiveInitialOutput A leftCode leftMove lineage
          row inputOne inputTwo =
        profiledOpenIndexedLeftReceiveInitialOutput A rightCode rightMove
          lineage row inputOne inputTwo)

/-- Process-two's locally stored projections. -/
def ProfiledOpenIndexedProcessTwoInitialOutputCoherent
    (leftCode rightCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (leftMove rightMove : ProfiledOpenIndexedBiBeliefMove A) : Prop :=
  (∀ inputTwo,
      profiledOpenIndexedLeftBlindInitialOutput A leftMove inputTwo =
        profiledOpenIndexedLeftBlindInitialOutput A rightMove inputTwo) ∧
    (∀ lineage row inputOne inputTwo,
      profiledOpenIndexedRightReceiveInitialOutput A leftCode leftMove lineage
          row inputOne inputTwo =
        profiledOpenIndexedRightReceiveInitialOutput A rightCode rightMove
          lineage row inputOne inputTwo)

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] in
/-- The former four-projection test is exactly the conjunction of the two
process-local tests when applied to one fixed pair of moves. -/
theorem profiledOpenIndexedInitialOutputPairCoherent_iff_processes
    (leftCode rightCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (leftMove rightMove : ProfiledOpenIndexedBiBeliefMove A) :
    ProfiledOpenIndexedInitialOutputPairCoherent A leftCode rightCode leftMove
        rightMove ↔
      ProfiledOpenIndexedProcessOneInitialOutputCoherent A leftCode rightCode
          leftMove rightMove ∧
        ProfiledOpenIndexedProcessTwoInitialOutputCoherent A leftCode rightCode
          leftMove rightMove := by
  constructor
  · rintro ⟨hrightBlind, hleftBlind, hrightReceive, hleftReceive⟩
    exact ⟨⟨hrightBlind, hleftReceive⟩, ⟨hleftBlind, hrightReceive⟩⟩
  · rintro ⟨⟨hrightBlind, hleftReceive⟩,
      ⟨hleftBlind, hrightReceive⟩⟩
    exact ⟨hrightBlind, hleftBlind, hrightReceive, hleftReceive⟩

/-- Exact policy staging gate for process one.  Only states which coexist in
one process-one local belief are compared, and only process one's two stored
table projections must agree. -/
def ProfiledOpenIndexedCodePolicyProcessOneStagingCoherentOn
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedCodeRationalPolicy A initialCode)
    (CanCooccurOne : ProfiledOpenIndexedCodePolicyState A initialCode →
      ProfiledOpenIndexedCodePolicyState A initialCode → Prop) : Prop :=
  ∀ leftState rightState,
    CanCooccurOne leftState rightState →
      ∃ leftMove rightMove,
        ProfiledOpenIndexedCodePolicyMoveRealizesAt A initialCode policy
            leftState leftMove ∧
          ProfiledOpenIndexedCodePolicyMoveRealizesAt A initialCode policy
            rightState rightMove ∧
          ProfiledOpenIndexedProcessOneInitialOutputCoherent A leftState.1
            rightState.1 leftMove rightMove

/-- Process-two staging mirror. -/
def ProfiledOpenIndexedCodePolicyProcessTwoStagingCoherentOn
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedCodeRationalPolicy A initialCode)
    (CanCooccurTwo : ProfiledOpenIndexedCodePolicyState A initialCode →
      ProfiledOpenIndexedCodePolicyState A initialCode → Prop) : Prop :=
  ∀ leftState rightState,
    CanCooccurTwo leftState rightState →
      ∃ leftMove rightMove,
        ProfiledOpenIndexedCodePolicyMoveRealizesAt A initialCode policy
            leftState leftMove ∧
          ProfiledOpenIndexedCodePolicyMoveRealizesAt A initialCode policy
            rightState rightMove ∧
          ProfiledOpenIndexedProcessTwoInitialOutputCoherent A leftState.1
            rightState.1 leftMove rightMove

omit [Inhabited In₁] [Inhabited In₂] in
/-- The old joint gate implies each side-specific staging gate on the same
cooccurrence relation.  The converse would require one pair of moves to serve
both processes and is deliberately not claimed. -/
theorem profiledOpenIndexedCodePolicyProcessStagingCoherentOn_of_pair
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedCodeRationalPolicy A initialCode)
    (CanCooccur : ProfiledOpenIndexedCodePolicyState A initialCode →
      ProfiledOpenIndexedCodePolicyState A initialCode → Prop)
    (hpair : ProfiledOpenIndexedCodePolicyPairOutputCoherentOn A initialCode
      policy CanCooccur) :
    ProfiledOpenIndexedCodePolicyProcessOneStagingCoherentOn A initialCode
        policy CanCooccur ∧
      ProfiledOpenIndexedCodePolicyProcessTwoStagingCoherentOn A initialCode
        policy CanCooccur := by
  constructor
  · intro leftState rightState hcooccur
    rcases hpair leftState rightState hcooccur with
      ⟨leftMove, rightMove, hleft, hright, hcoherent⟩
    exact ⟨leftMove, rightMove, hleft, hright,
      (profiledOpenIndexedInitialOutputPairCoherent_iff_processes A
        leftState.1 rightState.1 leftMove rightMove).mp hcoherent |>.1⟩
  · intro leftState rightState hcooccur
    rcases hpair leftState rightState hcooccur with
      ⟨leftMove, rightMove, hleft, hright, hcoherent⟩
    exact ⟨leftMove, rightMove, hleft, hright,
      (profiledOpenIndexedInitialOutputPairCoherent_iff_processes A
        leftState.1 rightState.1 leftMove rightMove).mp hcoherent |>.2⟩

/-! ## Why the parent indexed move is not automatically a child move -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- One fixed active right move can be valid at two codes only if their
right root carriers agree.  This is the source-typing obstruction to simply
running the parent's indexed move at a child code. -/
theorem profiledOpenIndexed_sameRightMove_valid_carrier_eq
    (leftCode rightCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (leftMove : ProfiledOpenClassifiedMove A)
    (hleft : ProfiledOpenIndexedBiBeliefValid A leftCode
      (.right source table, leftMove))
    (hright : ProfiledOpenIndexedBiBeliefValid A rightCode
      (.right source table, leftMove)) :
    profiledOpenIndexedSlotRoots A leftCode.rightSlots =
      profiledOpenIndexedSlotRoots A rightCode.rightSlots := by
  exact hleft.1.2.symm.trans hright.1.2

/-- Left-lane mirror. -/
theorem profiledOpenIndexed_sameLeftMove_valid_carrier_eq
    (leftCode rightCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (rightMove : ProfiledOpenClassifiedMove A)
    (hleft : ProfiledOpenIndexedBiBeliefValid A leftCode
      (rightMove, .left source table))
    (hright : ProfiledOpenIndexedBiBeliefValid A rightCode
      (rightMove, .left source table)) :
    profiledOpenIndexedSlotRoots A leftCode.leftSlots =
      profiledOpenIndexedSlotRoots A rightCode.leftSlots := by
  exact hleft.2.1.2.symm.trans hright.2.1.2

/-- In particular, reusing an active parent right move after one indexed
successor forces the parent's right carrier to equal the cross-swapped child
carrier.  No such fixed-point equation is part of policy siblinghood. -/
theorem profiledOpenIndexed_parentRightMove_valid_at_child_carrier_eq
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (leftMove : ProfiledOpenClassifiedMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hparent : ProfiledOpenIndexedBiBeliefValid A code
      (.right source table, leftMove))
    (hchild : ProfiledOpenIndexedBiBeliefValid A
      (profiledOpenIndexedBiBeliefNext A code
        (.right source table, leftMove) direction)
      (.right source table, leftMove)) :
    profiledOpenIndexedSlotRoots A code.rightSlots =
      profiledOpenIndexedSlotRoots A
        (profiledOpenIndexedLeftChildCode A code
          (.right source table, leftMove) direction).rootSlots := by
  simpa only [profiledOpenIndexedBiBeliefNext_rightSlots] using
    profiledOpenIndexed_sameRightMove_valid_carrier_eq A code
      (profiledOpenIndexedBiBeliefNext A code
        (.right source table, leftMove) direction)
      source table leftMove hparent hchild

/-- Left-lane mirror of the cross-swapped carrier condition. -/
theorem profiledOpenIndexed_parentLeftMove_valid_at_child_carrier_eq
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (rightMove : ProfiledOpenClassifiedMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hparent : ProfiledOpenIndexedBiBeliefValid A code
      (rightMove, .left source table))
    (hchild : ProfiledOpenIndexedBiBeliefValid A
      (profiledOpenIndexedBiBeliefNext A code
        (rightMove, .left source table) direction)
      (rightMove, .left source table)) :
    profiledOpenIndexedSlotRoots A code.leftSlots =
      profiledOpenIndexedSlotRoots A
        (profiledOpenIndexedRightChildCode A code
          (rightMove, .left source table) direction).rootSlots := by
  simpa only [profiledOpenIndexedBiBeliefNext_leftSlots] using
    profiledOpenIndexed_sameLeftMove_valid_carrier_eq A code
      (profiledOpenIndexedBiBeliefNext A code
        (rightMove, .left source table) direction)
      source table rightMove hparent hchild

end

/-! ## The existing graph-blind operational pair really does pass -/

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- Process two receives on both `right` and `both`.  Because the joint move
is selected before the graph branch, its complete post-receive local summary
is definitionally identical in the two cases. -/
@[simp] theorem endToEndFamilyJointSafetySummaryNext_right_both_two
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    (endToEndFamilyJointSafetySummaryNext A package state move .right).2 =
      (endToEndFamilyJointSafetySummaryNext A package state move .both).2 :=
  rfl

/-- Process-one mirror for the hidden `left`/`both` pair. -/
@[simp] theorem endToEndFamilyJointSafetySummaryNext_left_both_one
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package) :
    (endToEndFamilyJointSafetySummaryNext A package state move .left).1 =
      (endToEndFamilyJointSafetySummaryNext A package state move .both).1 :=
  rfl

/-- Therefore the complete next local observation, including the next input,
stays equal for process two on `right`/`both` when Nature supplies the same
next local input. -/
@[simp] theorem endToEndFamilyJointSafetyNext_right_both_two
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    (endToEndFamilyJointSafetyNext A package state move
      (.right, nextInputOne, nextInputTwo)).two =
      (endToEndFamilyJointSafetyNext A package state move
        (.both, nextInputOne, nextInputTwo)).two :=
  rfl

/-- Process-one mirror. -/
@[simp] theorem endToEndFamilyJointSafetyNext_left_both_one
    (state : EndToEndFamilyReceiveObservation A package)
    (move : EndToEndFamilyJointMove A package)
    (nextInputOne : In₁) (nextInputTwo : In₂) :
    (endToEndFamilyJointSafetyNext A package state move
      (.left, nextInputOne, nextInputTwo)).one =
      (endToEndFamilyJointSafetyNext A package state move
        (.both, nextInputOne, nextInputTwo)).one :=
  rfl

end

end

end DetParityAutomaton

end DistributedSynthesis
