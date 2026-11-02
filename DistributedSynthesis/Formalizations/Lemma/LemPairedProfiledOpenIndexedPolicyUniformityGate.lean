/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefNodePolicy
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedBeliefThreadSystem

/-!
# The first local-uniformity gate after indexed rationalization

At one fixed indexed public move, the locally hidden graph pairs are sound:
process one reads the same left-receiver output on `left` and `both`, and
process two reads the same right-receiver output on `right` and `both`.
These equalities are definitional and require no orientation or leader bit.

The rational policy creates a separate issue.  Its finite state also contains
the universal-thread DPA control.  Two states that can occur in one local
belief may therefore select different classified tables.  The existing
`ProfiledOpenIndexedBiBeliefT1` compares hidden members inside one fixed
table; it has no premise or conclusion comparing two selected tables.

`ProfiledOpenIndexedPolicyPairOutputCoherentOn` is the exact two-state gate
needed before the generic finite-global-belief construction can prove output
uniformity.  The accompanying collision record is a fail-fast interface: a
single reachable co-occurring pair separated for every legal move witness
refutes that gate, even though every witness separately satisfies T1.
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

/-! ## The four initial local output projections of one fixed move -/

/-- Blind process-one output of the right table at its shared initial
control.  Ill-shaped moves are totalized by the default output. -/
noncomputable def profiledOpenIndexedRightBlindInitialOutput
    (move : ProfiledOpenIndexedBiBeliefMove A) (inputOne : In₁) : Out₁ :=
  match move.1 with
  | .right source table =>
      (table.toTransitionRationalTree.labelOf
        table.toTransitionRationalTree.initial).1 inputOne
  | _ => default

/-- Blind process-two output of the left table. -/
noncomputable def profiledOpenIndexedLeftBlindInitialOutput
    (move : ProfiledOpenIndexedBiBeliefMove A) (inputTwo : In₂) : Out₂ :=
  match move.2 with
  | .left source table =>
      (table.toTransitionRationalTree.labelOf
        table.toTransitionRationalTree.initial).1 inputTwo
  | _ => default

/-- Process-two's informed output from the right table at the initial shared
node.  The lineage and row are proof-side coordinates only. -/
noncomputable def profiledOpenIndexedRightReceiveInitialOutput
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (lineage : I) (row : PairedEntryRow)
    (inputOne : In₁) (inputTwo : In₂) : Out₂ :=
  match move.1 with
  | .right source table =>
      let member := profiledOpenIndexedRightSourceMember A code source lineage
      let output := profiledOpenRightClassifiedSharedNodeOutput A source table
        [] member (inputTwo, inputOne)
      pairedRightInformedForRow row output.1.physical
  | _ => default

/-- Process-one's informed output from the left table. -/
noncomputable def profiledOpenIndexedLeftReceiveInitialOutput
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (lineage : I) (row : PairedEntryRow)
    (inputOne : In₁) (inputTwo : In₂) : Out₁ :=
  match move.2 with
  | .left source table =>
      let member := profiledOpenIndexedLeftSourceMember A code source lineage
      let output := profiledOpenLeftClassifiedSharedNodeOutput A source table
        [] member (inputOne, inputTwo)
      pairedLeftInformedForRow row output.1.physical
  | _ => default

/-- Output pair on one strict right round at the initial table control. -/
noncomputable def profiledOpenIndexedStrictRightInitialOutput
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (rightLineage : I) (rightRow : PairedEntryRow)
    (inputOne : In₁) (inputTwo : In₂) : Out₁ × Out₂ :=
  (profiledOpenIndexedRightBlindInitialOutput A move inputOne,
    profiledOpenIndexedRightReceiveInitialOutput A code move rightLineage
      rightRow inputOne inputTwo)

/-- Output pair on one strict left round. -/
noncomputable def profiledOpenIndexedStrictLeftInitialOutput
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (leftLineage : I) (leftRow : PairedEntryRow)
    (inputOne : In₁) (inputTwo : In₂) : Out₁ × Out₂ :=
  (profiledOpenIndexedLeftReceiveInitialOutput A code move leftLineage leftRow
      inputOne inputTwo,
    profiledOpenIndexedLeftBlindInitialOutput A move inputTwo)

/-- The locally sound hybrid on a `both` round: process one's component is
read from the left receiver table and process two's from the right receiver
table. -/
noncomputable def profiledOpenIndexedBothInitialOutput
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (rightLineage leftLineage : I)
    (rightRow leftRow : PairedEntryRow)
    (inputOne : In₁) (inputTwo : In₂) : Out₁ × Out₂ :=
  (profiledOpenIndexedLeftReceiveInitialOutput A code move leftLineage leftRow
      inputOne inputTwo,
    profiledOpenIndexedRightReceiveInitialOutput A code move rightLineage
      rightRow inputOne inputTwo)

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] in
/-- The hidden `right`/`both` graph choice is invisible to process two, and
its output component agrees for one fixed table state. -/
@[simp] theorem profiledOpenIndexed_right_both_initial_outputTwo
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (rightLineage leftLineage : I)
    (rightRow leftRow : PairedEntryRow)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledOpenIndexedStrictRightInitialOutput A code move rightLineage
        rightRow inputOne inputTwo).2 =
      (profiledOpenIndexedBothInitialOutput A code move rightLineage
        leftLineage rightRow leftRow inputOne inputTwo).2 :=
  rfl

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] in
/-- The hidden `left`/`both` graph choice is invisible to process one. -/
@[simp] theorem profiledOpenIndexed_left_both_initial_outputOne
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (rightLineage leftLineage : I)
    (rightRow leftRow : PairedEntryRow)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledOpenIndexedStrictLeftInitialOutput A code move leftLineage
        leftRow inputOne inputTwo).1 =
      (profiledOpenIndexedBothInitialOutput A code move rightLineage
        leftLineage rightRow leftRow inputOne inputTwo).1 :=
  rfl

/-! ## The cross-policy-state gate -/

abbrev ProfiledOpenIndexedRationalPolicy
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  SourceFreeBeliefRationalPolicy
    (profiledOpenIndexedBiBeliefThreadSystem A initialCode)
    initialCode (ProfiledOpenIndexedBiBeliefValid A)
    (profiledOpenIndexedBiBeliefNext A)

abbrev ProfiledOpenIndexedPolicyState
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  (sourceFreeBeliefNodeRunAutomaton
    (profiledOpenIndexedBiBeliefThreadSystem A initialCode)
    initialCode (ProfiledOpenIndexedBiBeliefValid A)
    (profiledOpenIndexedBiBeliefNext A)).State

/-- One concrete indexed move realizes the rational policy transition at a
finite policy state. -/
def ProfiledOpenIndexedPolicyMoveRealizesAt
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedRationalPolicy A initialCode)
    (state : ProfiledOpenIndexedPolicyState A initialCode)
    (move : ProfiledOpenIndexedBiBeliefMove A) : Prop :=
  SourceFreeBeliefRationalPolicy.MoveRealizesAt
    (profiledOpenIndexedBiBeliefThreadSystem A initialCode)
    initialCode (ProfiledOpenIndexedBiBeliefValid A)
    (profiledOpenIndexedBiBeliefNext A) policy state move

/-- Two selected moves give identical local output projections at the
initial controls.  This is deliberately cross-table; T1 is only intra-table.
-/
def ProfiledOpenIndexedInitialOutputPairCoherent
    (leftCode rightCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (leftMove rightMove : ProfiledOpenIndexedBiBeliefMove A) : Prop :=
  (∀ inputOne,
      profiledOpenIndexedRightBlindInitialOutput A leftMove inputOne =
        profiledOpenIndexedRightBlindInitialOutput A rightMove inputOne) ∧
    (∀ inputTwo,
      profiledOpenIndexedLeftBlindInitialOutput A leftMove inputTwo =
        profiledOpenIndexedLeftBlindInitialOutput A rightMove inputTwo) ∧
    (∀ lineage row inputOne inputTwo,
      profiledOpenIndexedRightReceiveInitialOutput A leftCode leftMove lineage row
          inputOne inputTwo =
        profiledOpenIndexedRightReceiveInitialOutput A rightCode rightMove lineage
          row inputOne inputTwo) ∧
    (∀ lineage row inputOne inputTwo,
      profiledOpenIndexedLeftReceiveInitialOutput A leftCode leftMove lineage row
          inputOne inputTwo =
        profiledOpenIndexedLeftReceiveInitialOutput A rightCode rightMove lineage
          row inputOne inputTwo)

/-- Exact two-state output gate, relative to the model-specific relation
`CanCooccur` saying that two finite policy states occur in one reachable local
belief. -/
def ProfiledOpenIndexedPolicyPairOutputCoherentOn
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedRationalPolicy A initialCode)
    (CanCooccur : ProfiledOpenIndexedPolicyState A initialCode →
      ProfiledOpenIndexedPolicyState A initialCode → Prop) : Prop :=
  ∀ leftState rightState,
    CanCooccur leftState rightState →
      ∃ leftMove rightMove,
        ProfiledOpenIndexedPolicyMoveRealizesAt A initialCode policy leftState
            leftMove ∧
          ProfiledOpenIndexedPolicyMoveRealizesAt A initialCode policy
            rightState rightMove ∧
          ProfiledOpenIndexedInitialOutputPairCoherent A leftState.1
            rightState.1 leftMove rightMove

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- T1 is available for each realizing move separately. -/
theorem profiledOpenIndexedPolicyMove_t1
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedRationalPolicy A initialCode)
    (state : ProfiledOpenIndexedPolicyState A initialCode)
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (hmove : ProfiledOpenIndexedPolicyMoveRealizesAt A initialCode policy state
      move) :
    ProfiledOpenIndexedBiBeliefT1 A state.1 move :=
  profiledOpenIndexedBiBeliefT1_of_valid A state.1 move hmove.1

/-- A kernel-checkable failure certificate for the first output-uniformity
pair test.  Separation quantifies over every legal witness, so changing the
representative chosen from `policy.legal_at` cannot repair it. -/
structure ProfiledOpenIndexedPolicyPairOutputCollision
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedRationalPolicy A initialCode)
    (CanCooccur : ProfiledOpenIndexedPolicyState A initialCode →
      ProfiledOpenIndexedPolicyState A initialCode → Prop) where
  leftState : ProfiledOpenIndexedPolicyState A initialCode
  rightState : ProfiledOpenIndexedPolicyState A initialCode
  cooccurs : CanCooccur leftState rightState
  separated :
    ∀ leftMove rightMove,
      ProfiledOpenIndexedPolicyMoveRealizesAt A initialCode policy leftState
          leftMove →
        ProfiledOpenIndexedPolicyMoveRealizesAt A initialCode policy rightState
          rightMove →
        ¬ ProfiledOpenIndexedInitialOutputPairCoherent A leftState.1
          rightState.1 leftMove rightMove

omit [Inhabited In₁] [Inhabited In₂] in
/-- One collision refutes the pair-output gate. -/
theorem not_profiledOpenIndexedPolicyPairOutputCoherentOn_of_collision
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedRationalPolicy A initialCode)
    (CanCooccur : ProfiledOpenIndexedPolicyState A initialCode →
      ProfiledOpenIndexedPolicyState A initialCode → Prop)
    (collision : ProfiledOpenIndexedPolicyPairOutputCollision A initialCode
      policy CanCooccur) :
    ¬ ProfiledOpenIndexedPolicyPairOutputCoherentOn A initialCode policy
      CanCooccur := by
  intro hcoherent
  rcases hcoherent collision.leftState collision.rightState
      collision.cooccurs with ⟨leftMove, rightMove, hleft, hright, hagree⟩
  exact collision.separated leftMove rightMove hleft hright hagree

end

end DetParityAutomaton

end DistributedSynthesis
