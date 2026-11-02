/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedPhysicalSiblingCoherence
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingLocalInstallation

/-!
# Guarded local installation for the root-pinned common sibling front

The unguarded finite sibling table is sufficient after a strict orientation
has been resolved, but not at a locally ambiguous repeated simultaneous
round: two independently narrowed tables could otherwise choose incompatible
root outputs.  The first-record guards already prove that the right and left
tables retain the two projections of one literal common round.

This file packages those guarded tables in one finite installation alphabet.
The first summand is the special sibling below the initial simultaneous root;
the second summand is the recurrent root-pinned common case.  Every active
installation exposes one exact root-pinned common successor, so another
simultaneous round can prepare the next installation without reselecting the
guarded policy.
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

/-! ## The guarded initial sibling pair -/

/-- First-record-guarded right/common--strict-left table immediately below
the two input pairs at the initial simultaneous root. -/
noncomputable def profiledRawJointHybridInitialGuardedRightSiblingMove
    (first current : In₁ × In₂) :
    ProfiledRawJointGuardedRightPhysicalSiblingMove A :=
  profiledRawJointGuardedRightPhysicalSiblingMoveOf A hwin
    (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
    (profiledRawJointHybridInitialSiblingDirection current)
    ((profiledRawJointHybridInitialSiblingWorld A strategy first current
      ).procOneMember A)
    (profiledRawJointHybridInitialCommonSemanticSibling_right A strategy
      first current)

/-- Process-two/left mirror. -/
noncomputable def profiledRawJointHybridInitialGuardedLeftSiblingMove
    (first current : In₁ × In₂) :
    ProfiledRawJointGuardedLeftPhysicalSiblingMove A :=
  profiledRawJointGuardedLeftPhysicalSiblingMoveOf A hwin
    (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
    (profiledRawJointHybridInitialSiblingDirection current)
    ((profiledRawJointHybridInitialSiblingWorld A strategy first current
      ).procTwoMember A)
    (profiledRawJointHybridInitialCommonSemanticSibling_left A strategy
      first current)

/-! ### Initial anti-mosaic equations -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The two literal initial sibling roots are projections of the same common
semantic round at process one. -/
theorem profiledRawJointHybridInitialSiblingLiteralRoots_outputOne
    (first current input : In₁ × In₂) :
    let family :=
      profiledRawJointHybridInitialSiblingParentFamily A strategy first
    let direction := profiledRawJointHybridInitialSiblingDirection current
    let world :=
      profiledRawJointHybridInitialSiblingWorld A strategy first current
    let rightRecord :=
      profiledRawJointRightSiblingLiteralRootRecord A hwin family direction
        (world.procOneMember A)
        (profiledRawJointHybridInitialCommonSemanticSibling_right A strategy
          first current)
        (input.2, input.1)
    let leftRecord :=
      profiledRawJointLeftSiblingLiteralRootRecord A hwin family direction
        (world.procTwoMember A)
        (profiledRawJointHybridInitialCommonSemanticSibling_left A strategy
          first current)
        input
    rightRecord.2.1.physical.closingBoth =
      pairedLeftInformedForRow .both leftRecord.2.1.physical := by
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Process-two mirror. -/
theorem profiledRawJointHybridInitialSiblingLiteralRoots_outputTwo
    (first current input : In₁ × In₂) :
    let family :=
      profiledRawJointHybridInitialSiblingParentFamily A strategy first
    let direction := profiledRawJointHybridInitialSiblingDirection current
    let world :=
      profiledRawJointHybridInitialSiblingWorld A strategy first current
    let rightRecord :=
      profiledRawJointRightSiblingLiteralRootRecord A hwin family direction
        (world.procOneMember A)
        (profiledRawJointHybridInitialCommonSemanticSibling_right A strategy
          first current)
        (input.2, input.1)
    let leftRecord :=
      profiledRawJointLeftSiblingLiteralRootRecord A hwin family direction
        (world.procTwoMember A)
        (profiledRawJointHybridInitialCommonSemanticSibling_left A strategy
          first current)
        input
    leftRecord.2.1.physical.closingBoth =
      pairedRightInformedForRow .both rightRecord.2.1.physical := by
  rfl

/-- The independently finite guarded initial tables inherit the literal
process-one root equation. -/
theorem profiledRawJointHybridInitialGuardedRoots_outputOne
    (first current input : In₁ × In₂)
    (rightMember leftMember : Bool) :
    let rightMove :=
      profiledRawJointHybridInitialGuardedRightSiblingMove A strategy hwin
        first current
    let leftMove :=
      profiledRawJointHybridInitialGuardedLeftSiblingMove A strategy hwin
        first current
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
    profiledRawJointHybridInitialSiblingParentFamily A strategy first
  let direction := profiledRawJointHybridInitialSiblingDirection current
  let world :=
    profiledRawJointHybridInitialSiblingWorld A strategy first current
  have hright :=
    profiledRawJointGuardedRightPhysicalSiblingMoveOf_root_record A hwin
      family direction (world.procOneMember A)
      (profiledRawJointHybridInitialCommonSemanticSibling_right A strategy
        first current)
      rightMember (input.2, input.1)
  have hleft :=
    profiledRawJointGuardedLeftPhysicalSiblingMoveOf_root_record A hwin
      family direction (world.procTwoMember A)
      (profiledRawJointHybridInitialCommonSemanticSibling_left A strategy
        first current)
      leftMember input
  dsimp only
  simp only [profiledRawJointHybridInitialGuardedRightSiblingMove,
    profiledRawJointHybridInitialGuardedLeftSiblingMove]
  rw [hright, hleft]
  exact profiledRawJointHybridInitialSiblingLiteralRoots_outputOne A strategy
    hwin first current input

/-- Extracted process-two root equation. -/
theorem profiledRawJointHybridInitialGuardedRoots_outputTwo
    (first current input : In₁ × In₂)
    (rightMember leftMember : Bool) :
    let rightMove :=
      profiledRawJointHybridInitialGuardedRightSiblingMove A strategy hwin
        first current
    let leftMove :=
      profiledRawJointHybridInitialGuardedLeftSiblingMove A strategy hwin
        first current
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
    profiledRawJointHybridInitialSiblingParentFamily A strategy first
  let direction := profiledRawJointHybridInitialSiblingDirection current
  let world :=
    profiledRawJointHybridInitialSiblingWorld A strategy first current
  have hright :=
    profiledRawJointGuardedRightPhysicalSiblingMoveOf_root_record A hwin
      family direction (world.procOneMember A)
      (profiledRawJointHybridInitialCommonSemanticSibling_right A strategy
        first current)
      rightMember (input.2, input.1)
  have hleft :=
    profiledRawJointGuardedLeftPhysicalSiblingMoveOf_root_record A hwin
      family direction (world.procTwoMember A)
      (profiledRawJointHybridInitialCommonSemanticSibling_left A strategy
        first current)
      leftMember input
  dsimp only
  simp only [profiledRawJointHybridInitialGuardedRightSiblingMove,
    profiledRawJointHybridInitialGuardedLeftSiblingMove]
  rw [hright, hleft]
  exact profiledRawJointHybridInitialSiblingLiteralRoots_outputTwo A strategy
    hwin first current input

/-! ## One finite initial/recurrent installation alphabet -/

/-- Either the special table below the initial simultaneous root or a table
below an arbitrary root-pinned common control. -/
abbrev ProfiledRawJointHybridGuardedSiblingInstallation :=
  ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂) ⊕
    (CommonControl A strategy hwin × (In₁ × In₂))

noncomputable instance
    profiledRawJointHybridGuardedSiblingInstallationFintype :
    Fintype
      (ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin) := by
  classical
  infer_instance

/-- The exact right guarded table selected by an installation. -/
noncomputable def profiledRawJointHybridGuardedRightMoveAt
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin) :
    ProfiledRawJointGuardedRightPhysicalSiblingMove A :=
  match installation with
  | .inl initial =>
      profiledRawJointHybridInitialGuardedRightSiblingMove A strategy hwin
        initial.first initial.current
  | .inr recurrent =>
      profiledRawJointHybridCommonGuardedRightSiblingMove A strategy hwin
        recurrent.1 recurrent.2

/-- Left mirror. -/
noncomputable def profiledRawJointHybridGuardedLeftMoveAt
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin) :
    ProfiledRawJointGuardedLeftPhysicalSiblingMove A :=
  match installation with
  | .inl initial =>
      profiledRawJointHybridInitialGuardedLeftSiblingMove A strategy hwin
        initial.first initial.current
  | .inr recurrent =>
      profiledRawJointHybridCommonGuardedLeftSiblingMove A strategy hwin
        recurrent.1 recurrent.2

/-- Root-pinned common control represented by the common member of the active
installation. -/
noncomputable def profiledRawJointHybridGuardedInstallationCommon
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin) :
    CommonControl A strategy hwin :=
  match installation with
  | .inl initial =>
      profiledRawJointHybridRootPinnedInitialCommonControl A strategy hwin
        initial.first initial.current
  | .inr recurrent =>
      profiledRawJointHybridRootPinnedCommonNext A strategy hwin recurrent.1
        recurrent.2

/-- A simultaneous round prepares the guarded sibling pair below the exact
same-policy common successor. -/
noncomputable def profiledRawJointHybridGuardedNextInstallation
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin :=
  .inr (profiledRawJointHybridGuardedInstallationCommon A strategy hwin
    installation, input)

/-! ## Finite owner and receiver controls -/

abbrev ProfiledRawJointHybridGuardedRightOwnerAt
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin) :=
  ((profiledRawJointHybridGuardedRightMoveAt A strategy hwin installation
    ).memberController A false).Control

abbrev ProfiledRawJointHybridGuardedLeftOwnerAt
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin) :=
  ((profiledRawJointHybridGuardedLeftMoveAt A strategy hwin installation
    ).memberController A false).Control

abbrev ProfiledRawJointHybridGuardedRightInstalledOwner :=
  Sigma (ProfiledRawJointHybridGuardedRightOwnerAt A strategy hwin)

abbrev ProfiledRawJointHybridGuardedLeftInstalledOwner :=
  Sigma (ProfiledRawJointHybridGuardedLeftOwnerAt A strategy hwin)

noncomputable instance :
    Fintype (ProfiledRawJointHybridGuardedRightInstalledOwner A strategy
      hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointHybridGuardedLeftInstalledOwner A strategy
      hwin) := by
  classical
  infer_instance

abbrev ProfiledRawJointHybridGuardedRightReceiverAt
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin) :=
  PairedEntryRow ×
    (profiledRawJointGuardedRightPhysicalSiblingMonitor A
      (profiledRawJointHybridGuardedRightMoveAt A strategy hwin
        installation).1 false).State ×
    Option (ProfiledRawJointUnitTarget A)

abbrev ProfiledRawJointHybridGuardedLeftReceiverAt
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin) :=
  PairedEntryRow ×
    (profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      (profiledRawJointHybridGuardedLeftMoveAt A strategy hwin
        installation).1 false).State ×
    Option (ProfiledRawJointUnitTarget A)

abbrev ProfiledRawJointHybridGuardedRightInstalledReceiver :=
  Sigma (ProfiledRawJointHybridGuardedRightReceiverAt A strategy hwin)

abbrev ProfiledRawJointHybridGuardedLeftInstalledReceiver :=
  Sigma (ProfiledRawJointHybridGuardedLeftReceiverAt A strategy hwin)

noncomputable instance :
    Fintype (ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy
      hwin) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy
      hwin) := by
  classical
  infer_instance

noncomputable def initialProfiledRawJointHybridGuardedRightReceiver
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridGuardedRightInstalledReceiver A strategy hwin :=
  let move := profiledRawJointHybridGuardedRightMoveAt A strategy hwin
    installation
  ⟨installation, row,
    (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1 false
      ).initial,
    none⟩

noncomputable def initialProfiledRawJointHybridGuardedLeftReceiver
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridGuardedLeftInstalledReceiver A strategy hwin :=
  let move := profiledRawJointHybridGuardedLeftMoveAt A strategy hwin
    installation
  ⟨installation, row,
    (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 false
      ).initial,
    none⟩

/-- Advance a guarded right receiver with the honestly delivered right owner.
The emitted target and monitor state come from the same guarded table. -/
noncomputable def stepProfiledRawJointHybridGuardedRightReceiverAt
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (owner : ProfiledRawJointHybridGuardedRightOwnerAt A strategy hwin
      installation)
    (state : ProfiledRawJointHybridGuardedRightReceiverAt A strategy hwin
      installation)
    (input : In₂ × In₁) :
    Out₂ × ProfiledRawJointHybridGuardedRightReceiverAt A strategy hwin
      installation :=
  let move := profiledRawJointHybridGuardedRightMoveAt A strategy hwin
    installation
  let monitor :=
    profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let label := controller.labelOf owner
  let output := label.2 state.2.1 input
  let nextState := monitor.step state.2.1
    (input, output, label.1 input.2)
  (pairedRightInformedForRow state.1 output.physical,
    (state.1, nextState, some (output.target state.1)))

/-- Guarded left receiver mirror. -/
noncomputable def stepProfiledRawJointHybridGuardedLeftReceiverAt
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (owner : ProfiledRawJointHybridGuardedLeftOwnerAt A strategy hwin
      installation)
    (state : ProfiledRawJointHybridGuardedLeftReceiverAt A strategy hwin
      installation)
    (input : In₁ × In₂) :
    Out₁ × ProfiledRawJointHybridGuardedLeftReceiverAt A strategy hwin
      installation :=
  let move := profiledRawJointHybridGuardedLeftMoveAt A strategy hwin
    installation
  let monitor :=
    profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let label := controller.labelOf owner
  let output := label.2 state.2.1 input
  let nextState := monitor.step state.2.1
    (input, output, label.1 input.2)
  (pairedLeftInformedForRow state.1 output.physical,
    (state.1, nextState, some (output.target state.1)))

@[simp] theorem stepProfiledRawJointHybridGuardedRightReceiverAt_target
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (owner : ProfiledRawJointHybridGuardedRightOwnerAt A strategy hwin
      installation)
    (state : ProfiledRawJointHybridGuardedRightReceiverAt A strategy hwin
      installation)
    (input : In₂ × In₁) :
    (stepProfiledRawJointHybridGuardedRightReceiverAt A strategy hwin
      installation owner state input).2.2.2 =
      some (((((profiledRawJointHybridGuardedRightMoveAt A strategy hwin
        installation).memberController A false).labelOf owner).2 state.2.1
          input).target state.1) :=
  rfl

@[simp] theorem stepProfiledRawJointHybridGuardedLeftReceiverAt_target
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (owner : ProfiledRawJointHybridGuardedLeftOwnerAt A strategy hwin
      installation)
    (state : ProfiledRawJointHybridGuardedLeftReceiverAt A strategy hwin
      installation)
    (input : In₁ × In₂) :
    (stepProfiledRawJointHybridGuardedLeftReceiverAt A strategy hwin
      installation owner state input).2.2.2 =
      some (((((profiledRawJointHybridGuardedLeftMoveAt A strategy hwin
        installation).memberController A false).labelOf owner).2 state.2.1
          input).target state.1) :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
