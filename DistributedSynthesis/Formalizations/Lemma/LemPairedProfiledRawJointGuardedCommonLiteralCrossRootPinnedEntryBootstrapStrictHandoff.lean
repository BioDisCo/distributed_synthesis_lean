/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBootstrapResolve
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstPolicyRootHandoff

/-!
# Strict recurrent handoff after the root-pinned entry bootstrap

The entry bootstrap retains both ends of one literal-cross table through the
entry input.  Its next receiver output is consequently the second exact
record of that table.  On a strict resolving round, the target in this record
must not be compared with a freshly restarted table or with an independently
chosen equal-code common successor.  It is already the value of a dependent
literal child of the root-pinned one-sided policy from which the table was
constructed.

This file keeps that dependent child until the handoff has selected the
ordinary recurrent child-policy bank.  The resulting recurrent macro starts
at `run []`, and its public code is exactly the target emitted by the retained
receiver.  The final two theorems state this directly for the endpoint-local
bootstrap controls and for either hidden member.

The simultaneous resolving case is intentionally not claimed here.  It must
jointly synchronize the two independently visible marginal targets; a pair
of one-sided strict handoffs does not prove that common-close law.
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

/-! ## The retained target is an actual dependent child -/

/-- Every row of the second right-oriented literal-cross record is the value
of the corresponding dependent child of the exact root-pinned policy. -/
theorem
    profiledRawJointGuardedCommonRightLiteralCrossOfPoint_secondTarget_eq_exactChild
    (point : CommonPoint A strategy) (anchor : Bool)
    (first second : In₂ × In₁) (row : PairedEntryRow) :
    let move :=
      profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint A strategy
        hwin point
    let receiverRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
        receiverRoot first.1 first.2).2
    (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
        receiverAfterFirst second.1 second.2).1.target row =
      let installed :=
        profiledRawJointGuardedCommonPointInstalled A strategy point
      let initial := installed.world.oneSidedState A .right
      let predicate :=
        profiledRawJointHybridExactRightRootPredicate A installed
      let package :=
        profiledRawJointHybridExactRightPolicy A hwin installed
      (profiledRawJointGuardedFirstRightTarget A strategy initial predicate
        package row [first] second).1 := by
  have hrecord :=
    profiledRawJointGuardedCommonRightLiteralCrossOfPoint_secondRecord A
      strategy hwin point anchor first second
  have htarget := congrArg (fun record ↦ record.2.1.target row) hrecord
  simpa [profiledRawJointHybridExactRightUniformActivation] using htarget

/-- Left-oriented mirror of the dependent-child target equation. -/
theorem
    profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_secondTarget_eq_exactChild
    (point : CommonPoint A strategy) (anchor : Bool)
    (first second : In₁ × In₂) (row : PairedEntryRow) :
    let move :=
      profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint A strategy
        hwin point
    let receiverRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move
        anchor
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
        receiverRoot first.1 first.2).2
    (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
        receiverAfterFirst second.1 second.2).1.target row =
      let installed :=
        profiledRawJointGuardedCommonPointInstalled A strategy point
      let initial := installed.world.oneSidedState A .left
      let predicate :=
        profiledRawJointHybridExactLeftRootPredicate A installed
      let package :=
        profiledRawJointHybridExactLeftPolicy A hwin installed
      (profiledRawJointGuardedFirstLeftTarget A strategy initial predicate
        package row [first] second).1 := by
  have hrecord :=
    profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_secondRecord A
      strategy hwin point anchor first second
  have htarget := congrArg (fun record ↦ record.2.1.target row) hrecord
  simpa [profiledRawJointHybridExactLeftUniformActivation] using htarget

/-! ## Installation in the ordinary one-sided recurrent banks -/

/-- The retained right-oriented target starts the ordinary left-policy macro
at the exact dependent child and at the root state of its selected policy. -/
theorem
    exists_profiledRawJointGuardedCommonRightLiteralCrossOfPoint_secondPolicyRoot
    (point : CommonPoint A strategy) (anchor : Bool)
    (first second : In₂ × In₁) (row : PairedEntryRow) :
    let move :=
      profiledRawJointGuardedCommonRightLiteralCrossMoveOfPoint A strategy
        hwin point
    let receiverRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
        receiverRoot first.1 first.2).2
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy point
    let initial := installed.world.oneSidedState A .right
    let predicate :=
      profiledRawJointHybridExactRightRootPredicate A installed
    let package :=
      profiledRawJointHybridExactRightPolicy A hwin installed
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial predicate package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hwin initial predicate package
    ∃ (child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected)
        (target : ProfiledRawJointUnitLeftPolicyMacro A strategy child.1
          (bank child)),
      child.1 =
        (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
          receiverAfterFirst second.1 second.2).1.target row ∧
      target.state = (bank child).run [] := by
  dsimp only
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy point
  let initial := installed.world.oneSidedState A .right
  let predicate := profiledRawJointHybridExactRightRootPredicate A installed
  let package := profiledRawJointHybridExactRightPolicy A hwin installed
  let activation :=
    profiledRawJointHybridExactRightActivation A hwin installed
  let selected := profiledRawJointRootPinnedSelectedSource A strategy
    initial predicate package
  let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
    initial predicate package
  let child := profiledRawJointGuardedFirstRightTarget A strategy initial
    predicate package row [first] second
  let slot := profiledRawRightChildSlot A installed.world.procOneSlot
    activation.lambda row [first] second
  have hslot : child.1.family.left () = some slot := by
    exact activation.target_active_slot row [first] second
  let target := profiledRawJointLiteralChildLeftPolicyRoot A strategy selected
    bank child slot hslot
  refine ⟨child, target, ?_, rfl⟩
  exact
    (profiledRawJointGuardedCommonRightLiteralCrossOfPoint_secondTarget_eq_exactChild
      A strategy hwin point anchor first second row).symm

/-- The retained left-oriented target starts the ordinary right-policy macro
at the exact dependent child and at `run []`. -/
theorem
    exists_profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_secondPolicyRoot
    (point : CommonPoint A strategy) (anchor : Bool)
    (first second : In₁ × In₂) (row : PairedEntryRow) :
    let move :=
      profiledRawJointGuardedCommonLeftLiteralCrossMoveOfPoint A strategy
        hwin point
    let receiverRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move
        anchor
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
        receiverRoot first.1 first.2).2
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy point
    let initial := installed.world.oneSidedState A .left
    let predicate :=
      profiledRawJointHybridExactLeftRootPredicate A installed
    let package :=
      profiledRawJointHybridExactLeftPolicy A hwin installed
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial predicate package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hwin initial predicate package
    ∃ (child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected)
        (target : ProfiledRawJointUnitRightPolicyMacro A strategy child.1
          (bank child)),
      child.1 =
        (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
          receiverAfterFirst second.1 second.2).1.target row ∧
      target.state = (bank child).run [] := by
  dsimp only
  let installed :=
    profiledRawJointGuardedCommonPointInstalled A strategy point
  let initial := installed.world.oneSidedState A .left
  let predicate := profiledRawJointHybridExactLeftRootPredicate A installed
  let package := profiledRawJointHybridExactLeftPolicy A hwin installed
  let activation := profiledRawJointHybridExactLeftActivation A hwin installed
  let selected := profiledRawJointRootPinnedSelectedSource A strategy initial
    predicate package
  let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
    initial predicate package
  let child := profiledRawJointGuardedFirstLeftTarget A strategy initial
    predicate package row [first] second
  let slot := profiledRawLeftChildSlot A installed.world.procTwoSlot
    activation.lambda row [first] second
  have hslot : child.1.family.right () = some slot := by
    exact activation.target_active_slot row [first] second
  let target := profiledRawJointLiteralChildRightPolicyRoot A strategy selected
    bank child slot hslot
  refine ⟨child, target, ?_, rfl⟩
  exact
    (profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_secondTarget_eq_exactChild
      A strategy hwin point anchor first second row).symm

/-! ## Endpoint-facing strict resolving handoffs -/

/-- Starting from either hidden bootstrap member, a strict-right resolving
receive exposes one exact child key and initializes its ordinary left-policy
macro.  The hidden member does not occur in the selected public target. -/
theorem
    exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictRight_policyRoot
    (point : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) :
    let two :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
        strategy hwin point entry member
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy point
    let initial := installed.world.oneSidedState A .right
    let predicate := profiledRawJointHybridExactRightRootPredicate A installed
    let package := profiledRawJointHybridExactRightPolicy A hwin installed
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial predicate package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hwin initial predicate package
    ∃ (child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected)
        (target : ProfiledRawJointUnitLeftPolicyMacro A strategy child.1
          (bank child)),
      child.1 =
        (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
          (two.2.2.candidate two.1) input.2 input.1).1.target row ∧
      target.state = (bank child).run [] := by
  have hroot :=
    exists_profiledRawJointGuardedCommonRightLiteralCrossOfPoint_secondPolicyRoot
      A strategy hwin point member (entry.2, entry.1)
        (input.2, input.1) row
  cases member <;>
    simpa [
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoSharedInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra] using hroot

/-- Strict-left mirror of the endpoint-facing recurrent handoff. -/
theorem
    exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_strictLeft_policyRoot
    (point : CommonPoint A strategy) (entry input : In₁ × In₂)
    (member : Bool) (row : PairedEntryRow) :
    let one :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
        strategy hwin point entry member
    let installed :=
      profiledRawJointGuardedCommonPointInstalled A strategy point
    let initial := installed.world.oneSidedState A .left
    let predicate := profiledRawJointHybridExactLeftRootPredicate A installed
    let package := profiledRawJointHybridExactLeftPolicy A hwin installed
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial predicate package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hwin initial predicate package
    ∃ (child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected)
        (target : ProfiledRawJointUnitRightPolicyMacro A strategy child.1
          (bank child)),
      child.1 =
        (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
          (one.2.2.candidate one.1) input.1 input.2).1.target row ∧
      target.state = (bank child).run [] := by
  have hroot :=
    exists_profiledRawJointGuardedCommonLeftLiteralCrossOfPoint_secondPolicyRoot
      A strategy hwin point member entry input row
  cases member <;>
    simpa [
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneSharedInitial,
      profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra] using hroot

end

end DetParityAutomaton

end DistributedSynthesis
