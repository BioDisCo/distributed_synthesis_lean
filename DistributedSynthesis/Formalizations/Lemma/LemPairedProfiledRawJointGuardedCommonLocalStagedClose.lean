/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLocalStrictReachability
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTargetFamily

/-!
# Finite staged closes below a guarded common strict block

A strict receiver computes its prospective recurrent child from only the
represented common pair, its finite controller/monitor state, the current
input, and the entry row.  A staged close retains that finite handoff and a
proof-side recurrent root package.  Thus a later local communication switch
can install the child key without retaining or reconstructing the prefix.

The constructors below are total.  They use the receiver's prospective close
when its finite state satisfies the checked close invariant, and use a fixed
valid close below the same represented pair otherwise.  The latter branch is
unreachable on every real controller prefix.
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

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

/-! ## Finite local close states and dependent recurrent packages -/

/-- Finite controller and guarded-monitor state carried on a strict-right
receiver branch. -/
abbrev ProfiledRawJointGuardedCommonRightCloseState
    (pair : CommonPair A strategy hwin) :=
  ((pair.1.1).memberController A false).Control ×
    (profiledRawJointGuardedRightPhysicalSiblingMonitor A pair.1.1.1 false
      ).State

/-- Strict-left mirror. -/
abbrev ProfiledRawJointGuardedCommonLeftCloseState
    (pair : CommonPair A strategy hwin) :=
  ((pair.1.2).memberController A false).Control ×
    (profiledRawJointGuardedLeftPhysicalSiblingMonitor A pair.1.2.1 false
      ).State

/-- Recurrent package indexed by a finite guarded-right handoff. -/
abbrev ProfiledRawJointGuardedCommonRightHandoffRootPackage
    (handoff : ProfiledRawJointGuardedCommonRightHandoff A strategy hwin) :=
  ProfiledRawJointRightSiblingTargetChildRootPackage A strategy hwin
    (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
    (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
    handoff.2

/-- Left recurrent package. -/
abbrev ProfiledRawJointGuardedCommonLeftHandoffRootPackage
    (handoff : ProfiledRawJointGuardedCommonLeftHandoff A strategy hwin) :=
  ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy hwin
    (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
    (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
    handoff.2

/-- Everything a later local switch needs in order to install the recurrent
child selected at a strict-right receiver step.  The package is proof-side;
the executable key is the finite `handoff` and `row`. -/
structure ProfiledRawJointGuardedCommonRightStagedClose where
  handoff : ProfiledRawJointGuardedCommonRightHandoff A strategy hwin
  row : PairedEntryRow
  root : Nonempty
    (ProfiledRawJointGuardedCommonRightHandoffRootPackage A strategy hwin
      handoff)

/-- Strict-left mirror. -/
structure ProfiledRawJointGuardedCommonLeftStagedClose where
  handoff : ProfiledRawJointGuardedCommonLeftHandoff A strategy hwin
  row : PairedEntryRow
  root : Nonempty
    (ProfiledRawJointGuardedCommonLeftHandoffRootPackage A strategy hwin
      handoff)

noncomputable instance profiledRawJointGuardedCommonRightStagedCloseFintype :
    Fintype
      (ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin) := by
  classical
  apply Fintype.ofInjective
    (fun close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin
      ↦ (close.handoff, close.row))
  intro left right heq
  cases left
  cases right
  cases heq
  rfl

noncomputable instance profiledRawJointGuardedCommonLeftStagedCloseFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin) := by
  classical
  apply Fintype.ofInjective
    (fun close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin
      ↦ (close.handoff, close.row))
  intro left right heq
  cases left
  cases right
  cases heq
  rfl

/-! ## Total local constructors -/

/-- Checked close predicate computed from one finite strict-right receiver
state. -/
def ProfiledRawJointGuardedCommonRightCloseSafe
    (pair : CommonPair A strategy hwin)
    (state : ProfiledRawJointGuardedCommonRightCloseState A strategy hwin pair)
    (input : In₂ × In₁) (row : PairedEntryRow) : Prop :=
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  erasePairedProfiledState A
      (profiledRawJointUnitRightTargetProjection A
        (record.2.1.target row)) =
      pairedRightCloseTarget A (state.2.base.2.1) row
        (profiledRawJointTargetRightPhysicalLetter A record) ∧
    profiledRawJointRightPhysicalSiblingAllowed A pair.1.1.1.base
      (record.2.1.target row)

/-- Strict-left checked close predicate. -/
def ProfiledRawJointGuardedCommonLeftCloseSafe
    (pair : CommonPair A strategy hwin)
    (state : ProfiledRawJointGuardedCommonLeftCloseState A strategy hwin pair)
    (input : In₁ × In₂) (row : PairedEntryRow) : Prop :=
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  erasePairedProfiledState A
      (profiledRawJointUnitLeftTargetProjection A
        (record.2.1.target row)) =
      pairedLeftCloseTarget A (state.2.base.2.1) row
        (profiledRawJointTargetLeftPhysicalLetter A record) ∧
    profiledRawJointLeftPhysicalSiblingAllowed A pair.1.2.1.base
      (record.2.1.target row)

set_option maxHeartbeats 800000 in
/-- A real right controller prefix supplies the oriented left-root package
that the recurrent target family consumes. -/
theorem
    nonempty_profiledRawJointGuardedCommonRightPrefixOrientedRootPackage
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) (row : PairedEntryRow) :
    Nonempty
      (ProfiledRawJointGuardedCommonRightHandoffRootPackage A strategy hwin
        (profiledRawJointGuardedCommonRightPrefixHandoff A strategy hwin pair
          past input row)) := by
  let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair past
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  let handoff := profiledRawJointGuardedCommonRightPrefixHandoff A strategy
    hwin pair past input row
  apply
    nonempty_profiledRawJointGuardedCommonRightOrientedRootPackage_of_close A
      strategy hwin handoff state.2.base.2.1 row
      (profiledRawJointTargetRightPhysicalLetter A record)
  have hsafe := profiledRawJointGuardedCommonRightPrefixTargetSafe A strategy
    hwin pair past input row
  simpa [handoff, record, state,
    profiledRawJointGuardedCommonRightPrefixHandoff,
    profiledRawJointGuardedCommonRightPrefixOutput] using hsafe.1

set_option maxHeartbeats 800000 in
/-- Left-prefix oriented package. -/
theorem
    nonempty_profiledRawJointGuardedCommonLeftPrefixOrientedRootPackage
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    Nonempty
      (ProfiledRawJointGuardedCommonLeftHandoffRootPackage A strategy hwin
        (profiledRawJointGuardedCommonLeftPrefixHandoff A strategy hwin pair
          past input row)) := by
  let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair past
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  let handoff := profiledRawJointGuardedCommonLeftPrefixHandoff A strategy hwin
    pair past input row
  apply
    nonempty_profiledRawJointGuardedCommonLeftOrientedRootPackage_of_close A
      strategy hwin handoff state.2.base.2.1 row
      (profiledRawJointTargetLeftPhysicalLetter A record)
  have hsafe := profiledRawJointGuardedCommonLeftPrefixTargetSafe A strategy
    hwin pair past input row
  simpa [handoff, record, state,
    profiledRawJointGuardedCommonLeftPrefixHandoff,
    profiledRawJointGuardedCommonLeftPrefixOutput] using hsafe.1

/-- Fixed valid fallback below the same guarded pair. -/
private noncomputable def profiledRawJointGuardedCommonRightFallbackClose
    (pair : CommonPair A strategy hwin) :
    ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin :=
  let input : In₂ × In₁ := default
  let row : PairedEntryRow := .both
  let handoff := profiledRawJointGuardedCommonRightPrefixHandoff A strategy hwin
    pair [] input row
  ⟨handoff, row,
    nonempty_profiledRawJointGuardedCommonRightPrefixOrientedRootPackage A
      strategy hwin pair [] input row⟩

/-- Left fallback. -/
private noncomputable def profiledRawJointGuardedCommonLeftFallbackClose
    (pair : CommonPair A strategy hwin) :
    ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin :=
  let input : In₁ × In₂ := default
  let row : PairedEntryRow := .both
  let handoff := profiledRawJointGuardedCommonLeftPrefixHandoff A strategy hwin
    pair [] input row
  ⟨handoff, row,
    nonempty_profiledRawJointGuardedCommonLeftPrefixOrientedRootPackage A
      strategy hwin pair [] input row⟩

/-- Total strict-right local constructor.  Its fallback is taken exactly
when the finite state fails the checked close invariant. -/
noncomputable def profiledRawJointGuardedCommonRightStageClose
    (pair : CommonPair A strategy hwin)
    (state : ProfiledRawJointGuardedCommonRightCloseState A strategy hwin pair)
    (input : In₂ × In₁) (row : PairedEntryRow) :
    ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin := by
  classical
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  if hsafe : ProfiledRawJointGuardedCommonRightCloseSafe A strategy hwin pair
      state input row then
    let handoff := profiledRawJointGuardedCommonRightHandoffOfSafe A strategy
      hwin pair (record.2.1.target row) hsafe.2
    exact ⟨handoff, row,
      nonempty_profiledRawJointGuardedCommonRightOrientedRootPackage_of_close A
        strategy hwin handoff state.2.base.2.1 row
        (profiledRawJointTargetRightPhysicalLetter A record) hsafe.1⟩
  else
    exact profiledRawJointGuardedCommonRightFallbackClose A strategy hwin pair

/-- Total strict-left local constructor. -/
noncomputable def profiledRawJointGuardedCommonLeftStageClose
    (pair : CommonPair A strategy hwin)
    (state : ProfiledRawJointGuardedCommonLeftCloseState A strategy hwin pair)
    (input : In₁ × In₂) (row : PairedEntryRow) :
    ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin := by
  classical
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  let record := narrowedRecord monitor (controller.labelOf state.1) state.2
    input
  if hsafe : ProfiledRawJointGuardedCommonLeftCloseSafe A strategy hwin pair
      state input row then
    let handoff := profiledRawJointGuardedCommonLeftHandoffOfSafe A strategy
      hwin pair (record.2.1.target row) hsafe.2
    exact ⟨handoff, row,
      nonempty_profiledRawJointGuardedCommonLeftOrientedRootPackage_of_close A
        strategy hwin handoff state.2.base.2.1 row
        (profiledRawJointTargetLeftPhysicalLetter A record) hsafe.1⟩
  else
    exact profiledRawJointGuardedCommonLeftFallbackClose A strategy hwin pair

/-! ## Real prefixes never take the fallback -/

theorem profiledRawJointGuardedCommonRightCloseSafe_of_prefix
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) (row : PairedEntryRow) :
    ProfiledRawJointGuardedCommonRightCloseSafe A strategy hwin pair
      (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin pair
        past) input row :=
  profiledRawJointGuardedCommonRightPrefixTargetSafe A strategy hwin pair past
    input row

theorem profiledRawJointGuardedCommonLeftCloseSafe_of_prefix
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    ProfiledRawJointGuardedCommonLeftCloseSafe A strategy hwin pair
      (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin pair
        past) input row :=
  profiledRawJointGuardedCommonLeftPrefixTargetSafe A strategy hwin pair past
    input row

set_option maxHeartbeats 800000 in
theorem profiledRawJointGuardedCommonRightStageClose_of_prefix_handoff
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) (row : PairedEntryRow) :
    (profiledRawJointGuardedCommonRightStageClose A strategy hwin pair
      (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin pair
        past) input row).handoff =
      profiledRawJointGuardedCommonRightPrefixHandoff A strategy hwin pair past
        input row := by
  classical
  have hsafe := profiledRawJointGuardedCommonRightCloseSafe_of_prefix A
    strategy hwin pair past input row
  simp only [profiledRawJointGuardedCommonRightStageClose, hsafe, dite_true]
  rfl

set_option maxHeartbeats 800000 in
theorem profiledRawJointGuardedCommonLeftStageClose_of_prefix_handoff
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    (profiledRawJointGuardedCommonLeftStageClose A strategy hwin pair
      (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin pair
        past) input row).handoff =
      profiledRawJointGuardedCommonLeftPrefixHandoff A strategy hwin pair past
        input row := by
  classical
  have hsafe := profiledRawJointGuardedCommonLeftCloseSafe_of_prefix A strategy
    hwin pair past input row
  simp only [profiledRawJointGuardedCommonLeftStageClose, hsafe, dite_true]
  rfl

theorem profiledRawJointGuardedCommonRightStageClose_of_prefix_row
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) (row : PairedEntryRow) :
    (profiledRawJointGuardedCommonRightStageClose A strategy hwin pair
      (profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin pair
        past) input row).row = row := by
  classical
  have hsafe := profiledRawJointGuardedCommonRightCloseSafe_of_prefix A
    strategy hwin pair past input row
  simp [profiledRawJointGuardedCommonRightStageClose, hsafe]

theorem profiledRawJointGuardedCommonLeftStageClose_of_prefix_row
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) (row : PairedEntryRow) :
    (profiledRawJointGuardedCommonLeftStageClose A strategy hwin pair
      (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin pair
        past) input row).row = row := by
  classical
  have hsafe := profiledRawJointGuardedCommonLeftCloseSafe_of_prefix A strategy
    hwin pair past input row
  simp [profiledRawJointGuardedCommonLeftStageClose, hsafe]

/-- Both branches of the total right constructor remain below the represented
common pair supplied by the local state. -/
@[simp] theorem profiledRawJointGuardedCommonRightStageClose_pair
    (pair : CommonPair A strategy hwin)
    (state : ProfiledRawJointGuardedCommonRightCloseState A strategy hwin pair)
    (input : In₂ × In₁) (row : PairedEntryRow) :
    (profiledRawJointGuardedCommonRightStageClose A strategy hwin pair state
      input row).handoff.1 = pair := by
  classical
  by_cases hsafe : ProfiledRawJointGuardedCommonRightCloseSafe A strategy hwin
    pair state input row
  · simp [profiledRawJointGuardedCommonRightStageClose, hsafe,
      profiledRawJointGuardedCommonRightHandoffOfSafe]
  · simp [profiledRawJointGuardedCommonRightStageClose, hsafe,
      profiledRawJointGuardedCommonRightFallbackClose]

/-- Left mirror. -/
@[simp] theorem profiledRawJointGuardedCommonLeftStageClose_pair
    (pair : CommonPair A strategy hwin)
    (state : ProfiledRawJointGuardedCommonLeftCloseState A strategy hwin pair)
    (input : In₁ × In₂) (row : PairedEntryRow) :
    (profiledRawJointGuardedCommonLeftStageClose A strategy hwin pair state
      input row).handoff.1 = pair := by
  classical
  by_cases hsafe : ProfiledRawJointGuardedCommonLeftCloseSafe A strategy hwin
    pair state input row
  · simp [profiledRawJointGuardedCommonLeftStageClose, hsafe,
      profiledRawJointGuardedCommonLeftHandoffOfSafe]
  · simp [profiledRawJointGuardedCommonLeftStageClose, hsafe,
      profiledRawJointGuardedCommonLeftFallbackClose]

/-- The staged right payload always carries a valid recurrent root package;
on a real prefix its handoff is the exact checked prefix handoff by the theorem
above. -/
theorem ProfiledRawJointGuardedCommonRightStagedClose.hasRoot
    (close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin) :
    Nonempty
      (ProfiledRawJointGuardedCommonRightHandoffRootPackage A strategy hwin
        close.handoff) :=
  close.root

/-- Left mirror. -/
theorem ProfiledRawJointGuardedCommonLeftStagedClose.hasRoot
    (close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin) :
    Nonempty
      (ProfiledRawJointGuardedCommonLeftHandoffRootPackage A strategy hwin
        close.handoff) :=
  close.root

end

end DetParityAutomaton

end DistributedSynthesis
