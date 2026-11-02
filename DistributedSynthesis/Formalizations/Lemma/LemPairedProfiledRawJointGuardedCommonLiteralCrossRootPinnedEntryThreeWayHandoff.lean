/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonControl
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBootstrapStrictHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPhysical

/-!
# Selection-based handoff from the literal entry bootstrap

The entry boundary has three semantic continuations.  A simultaneous
continuation uses the guarded pair stored in the exact parent-linked child
state.  A strict-right or strict-left continuation uses the corresponding
dependent one-sided child exposed by the retained literal-cross table; those
two handoffs are supplied by
`LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBootstrapStrictHandoff`.

This file proves the common arm and its compatibility with the retained
literal tables.  It deliberately does not equate a common child with either
strict child.  Once a delivered control resolves the old ambiguity, those
histories are distinguishable and the local transition must select the
matching arm.  Before selection, no-receive coherence is provided by the
entry bootstrap's blind relation.

All runtime data below are finite.  Semantic occurrences occur only in proof
arguments and in the construction of the finite policy table.
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

/-! ## Exact common data at the entry child -/

/-- The two literal-cross receiver roots stored in the parent-linked entry
state are the complete receiver roots of the guarded pair stored in that same
state.  No equal-code representative is selected in this statement. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntry_rootPhysical_eq_pair
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (rightAnchor leftAnchor : Bool) :
    let state :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState
        A strategy hwin initial entry
    let pair := state.2.1.2.1
    let extra := state.2.1.2.2
    let rightReceiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
        rightAnchor
    let leftReceiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
        leftAnchor
    ((profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
        rightReceiver input.2 input.1).1.physical,
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
        leftReceiver input.1 input.2).1.physical) =
      ((pair.rightRootRecord A strategy hwin input).2.1.physical,
        (pair.leftRootRecord A strategy hwin input).2.1.physical) := by
  dsimp only
  rw [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_pair,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_extra]
  apply Prod.ext
  · exact
      profiledRawJointGuardedCommonRightLiteralCrossOfPoint_rootPhysical_eq_pair
        A strategy hwin (initial.step A strategy entry) rightAnchor input
  · exact
      profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_rootPhysical_eq_pair
        A strategy hwin (initial.step A strategy entry) leftAnchor input

/-- The complete move chosen by the parent-linked policy at the entry child
selects an allowed common successor of the exact pair stored at that child. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntry_childPair_allowed
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    let point := initial.step A strategy entry
    let move :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryMoveAt
        A strategy hwin initial entry
    ProfiledRawJointGuardedCommonSuccessorAllowed A strategy hwin
      (point.move A strategy hwin) input (move.2 input).1 := by
  dsimp only
  let move :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryMoveAt
      A strategy hwin initial entry
  have hrealizes :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryMoveAt_realizes
      A strategy hwin initial entry
  rcases hrealizes.2.2 with
    ⟨witness, _hcode, _hannotation, hwitnessMove, hchildren⟩
  have hcurrent : witness.move A strategy hwin =
      (initial.step A strategy entry).move A strategy hwin :=
    hwitnessMove.trans hrealizes.1
  have hchild :
      (witness.step A strategy input).move A strategy hwin =
        (move.2 input).1 := by
    have := congrArg Prod.fst (hchildren input)
    simpa [move,
      profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf] using this
  rw [← hcurrent, ← hchild]
  refine ⟨witness.world A strategy, input, rfl, rfl, ?_⟩
  exact ProfiledRawJointGuardedCommonSemanticPoint.step_code A strategy hwin
    witness input

/-- Finite allowed-child package used by the existing common shadow
constructor. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonSuccessor
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonSuccessor A strategy hwin
      ((initial.step A strategy entry).move A strategy hwin) input :=
  ⟨(profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryMoveAt
      A strategy hwin initial entry).2 input |>.1,
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntry_childPair_allowed
      A strategy hwin initial entry input⟩

/-! ## Common-arm installation -/

/-- Process-one common shadow selected at the exact entry child. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartOne
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    Out₁ × ProfiledRawJointGuardedCommonOneShadow A strategy hwin :=
  profiledRawJointGuardedCommonStartOneShadowOfSuccessor A strategy hwin
    ((initial.step A strategy entry).move A strategy hwin) input
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonSuccessor
      A strategy hwin initial entry input)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartTwo
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    Out₂ × ProfiledRawJointGuardedCommonTwoShadow A strategy hwin :=
  profiledRawJointGuardedCommonStartTwoShadowOfSuccessor A strategy hwin
    ((initial.step A strategy entry).move A strategy hwin) input
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonSuccessor
      A strategy hwin initial entry input)

/-- Both local common states retain the exact entry-child pair as their
strict source. -/
@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartOne_source
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartOne
      A strategy hwin initial entry input).2.source =
      (initial.step A strategy entry).move A strategy hwin :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartTwo_source
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartTwo
      A strategy hwin initial entry input).2.source =
      (initial.step A strategy entry).move A strategy hwin :=
  rfl

/-- The two common shadows install one and the same complete child pair. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStart_agree
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartOne
      A strategy hwin initial entry input).2.common =
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartTwo
        A strategy hwin initial entry input).2.common :=
  rfl

/-- The selected common arm emits the coherent simultaneous cut of the exact
entry-child pair. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStart_outputs
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartOne
        A strategy hwin initial entry input).1,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartTwo
        A strategy hwin initial entry input).1) =
      let pair := (initial.step A strategy entry).move A strategy hwin
      ((pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth,
        (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth) :=
  profiledRawJointGuardedCommonStartSuccessorShadows_outputs A strategy hwin
    ((initial.step A strategy entry).move A strategy hwin) input
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonSuccessor
      A strategy hwin initial entry input)

/-- The selected common-arm output is the literal strategy output at the
exact simultaneous child occurrence. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStart_outputs_literal
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartOne
        A strategy hwin initial entry input).1,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartTwo
        A strategy hwin initial entry input).1) =
      ((profiledRawJointGuardedCommonPointInstalled A strategy
          (initial.step A strategy entry)).bothOutputOne A input,
        (profiledRawJointGuardedCommonPointInstalled A strategy
          (initial.step A strategy entry)).bothOutputTwo A input) := by
  calc
    _ = (pairedLeftInformedForRow .both
          (((initial.step A strategy entry).move A strategy hwin
            ).leftRootRecord A strategy hwin input).2.1.physical,
        pairedRightInformedForRow .both
          (((initial.step A strategy entry).move A strategy hwin
            ).rightRootRecord A strategy hwin input).2.1.physical) :=
      profiledRawJointGuardedCommonStartShadows_both_pair A strategy hwin
        ((initial.step A strategy entry).move A strategy hwin)
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonSuccessor
          A strategy hwin initial entry input).1 input
    _ = _ :=
      profiledRawJointGuardedCommonPoint_move_bothReceiverOutputs A strategy
        hwin (initial.step A strategy entry) input

/-- At a simultaneous selection, reading the exact retained literal tables
and starting the exact common shadow are observationally identical.  This is
the required common-arm coherence; it makes no cross-history equality claim
for a later resolving strict receive. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntry_tables_eq_commonStart
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (rightAnchor leftAnchor : Bool) :
    let state :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState
        A strategy hwin initial entry
    let extra := state.2.1.2.2
    let rightReceiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
        rightAnchor
    let leftReceiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
        leftAnchor
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
        leftReceiver input.1 input.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
        rightReceiver input.2 input.1).1) =
      ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartOne
          A strategy hwin initial entry input).1,
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStartTwo
          A strategy hwin initial entry input).1) := by
  dsimp only
  rw [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_extra]
  calc
    _ = ((((initial.step A strategy entry).move A strategy hwin
              ).rightRootRecord A strategy hwin input).2.1.physical.closingBoth,
          (((initial.step A strategy entry).move A strategy hwin
              ).leftRootRecord A strategy hwin input).2.1.physical.closingBoth) :=
      profiledRawJointGuardedCommonLiteralCrossOfPoint_bothPhysicalOutputs_eq_cut
        A strategy hwin (initial.step A strategy entry) rightAnchor leftAnchor
          input
    _ = _ :=
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonStart_outputs
        A strategy hwin initial entry input).symm

/-! ## Handoff into the recurrent parent-linked common control -/

/-- Operational common start whose result retains both the common shadow and
the reachable successor key of the same accepting parent-linked policy. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartOne
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStartOne
    A strategy hwin initial
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey A
        strategy hwin initial entry) input

noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartTwo
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStartTwo
    A strategy hwin initial
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey A
        strategy hwin initial entry) input

/-- Both recurrent common controls carry the same successor key. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStart_states_agree
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStatesAgree
      A strategy hwin
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartOne
        A strategy hwin initial entry input).2
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartTwo
        A strategy hwin initial entry input).2 :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStart_states_agree
    A strategy hwin initial
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey A
        strategy hwin initial entry) input

/-- The recurrent common-control start still emits the literal simultaneous
output of the exact entry child. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStart_outputs_literal
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartOne
        A strategy hwin initial entry input).1,
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartTwo
        A strategy hwin initial entry input).1) =
      ((profiledRawJointGuardedCommonPointInstalled A strategy
          (initial.step A strategy entry)).bothOutputOne A input,
        (profiledRawJointGuardedCommonPointInstalled A strategy
          (initial.step A strategy entry)).bothOutputTwo A input) := by
  calc
    _ = (pairedLeftInformedForRow .both
          (((initial.step A strategy entry).move A strategy hwin
            ).leftRootRecord A strategy hwin input).2.1.physical,
        pairedRightInformedForRow .both
          (((initial.step A strategy entry).move A strategy hwin
            ).rightRootRecord A strategy hwin input).2.1.physical) := by
      have houtputs :=
        profiledRawJointGuardedCommonStartShadows_both_pair A strategy hwin
          ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey
            A strategy hwin initial entry).pair A strategy hwin)
          (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedKey_successorChild
            A strategy hwin initial
              (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey
                A strategy hwin initial entry) input).1 input
      simpa only [
        profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartOne,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartTwo,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStartOne,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedCommonStartTwo,
        profiledRawJointGuardedCommonStartOneShadowOfSuccessor,
        profiledRawJointGuardedCommonStartTwoShadowOfSuccessor,
        profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryKey_pair]
        using houtputs
    _ = _ :=
      profiledRawJointGuardedCommonPoint_move_bothReceiverOutputs A strategy
        hwin (initial.step A strategy entry) input

/-- The retained literal tables agree with the operational recurrent common
start.  The successor controls on the right retain the accepting policy key,
so this equality is a genuine handoff rather than a one-round readback. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntry_tables_eq_commonControlStart
    (initial : CommonPoint A strategy) (entry input : In₁ × In₂)
    (rightAnchor leftAnchor : Bool) :
    let state :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState
        A strategy hwin initial entry
    let extra := state.2.1.2.2
    let rightReceiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A extra.1
        rightAnchor
    let leftReceiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A extra.2
        leftAnchor
    ((profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecvPhysical A
        leftReceiver input.1 input.2).1,
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecvPhysical A
        rightReceiver input.2 input.1).1) =
      ((profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartOne
          A strategy hwin initial entry input).1,
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStartTwo
          A strategy hwin initial entry input).1) := by
  dsimp only
  rw [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_extra]
  calc
    _ = ((profiledRawJointGuardedCommonPointInstalled A strategy
            (initial.step A strategy entry)).bothOutputOne A input,
          (profiledRawJointGuardedCommonPointInstalled A strategy
            (initial.step A strategy entry)).bothOutputTwo A input) :=
      profiledRawJointGuardedCommonLiteralCrossOfPoint_bothPhysicalOutputs A
        strategy hwin (initial.step A strategy entry) rightAnchor leftAnchor
          input
    _ = _ :=
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryCommonControlStart_outputs_literal
        A strategy hwin initial entry input).symm

end

end DetParityAutomaton

end DistributedSynthesis
