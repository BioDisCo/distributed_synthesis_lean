/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridGuardedSiblingCoupledFront
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreStrictAcceptance

/-!
# Exact finite-prefix trajectory of the guarded sibling front

The guarded hybrid front transports the generic finite common-sibling table
through either an initial or recurrent installation tag.  This file records
that the transport commutes with appending one strict input and therefore
identifies the executable owner/receiver pair after every finite strict block.
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

private abbrev Installation :=
  ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin

/-! ## Transported append laws -/

theorem profiledRawJointHybridGuardedRightFiniteStateAfter_append_one
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    profiledRawJointHybridGuardedRightFiniteStateAfter A strategy hwin
        installation (past ++ [input]) =
      let state :=
        profiledRawJointHybridGuardedRightFiniteStateAfter A strategy hwin
          installation past
      let move := profiledRawJointHybridGuardedRightMoveAt A strategy hwin
        installation
      let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
        move.1 false
      let controller := move.memberController A false
      (controller.step state.1 input.2,
        monitor.step state.2
          (narrowedRecord monitor (controller.labelOf state.1) state.2
            input)) := by
  cases installation with
  | inl initial =>
      exact
        profiledRawJointGuardedCommonRightFiniteStateAfter_append_one A
          strategy hwin
            (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
              (.inl initial)) past input
  | inr recurrent =>
      exact
        profiledRawJointGuardedCommonRightFiniteStateAfter_append_one A
          strategy hwin
            (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
              (.inr recurrent)) past input

theorem profiledRawJointHybridGuardedLeftFiniteStateAfter_append_one
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    profiledRawJointHybridGuardedLeftFiniteStateAfter A strategy hwin
        installation (past ++ [input]) =
      let state :=
        profiledRawJointHybridGuardedLeftFiniteStateAfter A strategy hwin
          installation past
      let move := profiledRawJointHybridGuardedLeftMoveAt A strategy hwin
        installation
      let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
        move.1 false
      let controller := move.memberController A false
      (controller.step state.1 input.2,
        monitor.step state.2
          (narrowedRecord monitor (controller.labelOf state.1) state.2
            input)) := by
  cases installation with
  | inl initial =>
      exact
        profiledRawJointGuardedCommonLeftFiniteStateAfter_append_one A
          strategy hwin
            (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
              (.inl initial)) past input
  | inr recurrent =>
      exact
        profiledRawJointGuardedCommonLeftFiniteStateAfter_append_one A
          strategy hwin
            (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
              (.inr recurrent)) past input

/-! ## Exact owner progression -/

theorem profiledRawJointHybridGuardedRightPrefixOwner_step
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    (stepProfiledRawJointHybridGuardedRightOwner A strategy hwin
      (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
        installation past) input.2).2 =
      profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
        installation (past ++ [input]) := by
  unfold profiledRawJointHybridGuardedRightPrefixOwner
  unfold stepProfiledRawJointHybridGuardedRightOwner
  rw [profiledRawJointHybridGuardedRightFiniteStateAfter_append_one A
    strategy hwin]

theorem profiledRawJointHybridGuardedLeftPrefixOwner_step
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    (stepProfiledRawJointHybridGuardedLeftOwner A strategy hwin
      (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
        installation past) input.2).2 =
      profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
        installation (past ++ [input]) := by
  unfold profiledRawJointHybridGuardedLeftPrefixOwner
  unfold stepProfiledRawJointHybridGuardedLeftOwner
  rw [profiledRawJointHybridGuardedLeftFiniteStateAfter_append_one A strategy
    hwin]

/-! ## Exact receiver progression -/

theorem profiledRawJointHybridGuardedRightPrefixReceiverAfter_eq
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
        installation past input =
      let finite :=
        profiledRawJointHybridGuardedRightFiniteStateAfter A strategy hwin
          installation (past ++ [input])
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let target :=
        (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin pair
          past input).target .both
      ⟨installation, .both, finite.2, some target⟩ := by
  classical
  unfold profiledRawJointHybridGuardedRightPrefixReceiverAfter
  unfold profiledRawJointHybridGuardedRightPrefixReceiverBefore
  unfold profiledRawJointHybridGuardedRightPrefixOwner
  rw [stepProfiledRawJointHybridGuardedRightReceiver_same]
  rw [profiledRawJointHybridGuardedRightFiniteStateAfter_append_one A
    strategy hwin]
  cases installation <;> rfl

theorem profiledRawJointHybridGuardedLeftPrefixReceiverAfter_eq
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
        installation past input =
      let finite :=
        profiledRawJointHybridGuardedLeftFiniteStateAfter A strategy hwin
          installation (past ++ [input])
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let target :=
        (profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin pair
          past input).target .both
      ⟨installation, .both, finite.2, some target⟩ := by
  classical
  unfold profiledRawJointHybridGuardedLeftPrefixReceiverAfter
  unfold profiledRawJointHybridGuardedLeftPrefixReceiverBefore
  unfold profiledRawJointHybridGuardedLeftPrefixOwner
  rw [stepProfiledRawJointHybridGuardedLeftReceiver_same]
  rw [profiledRawJointHybridGuardedLeftFiniteStateAfter_append_one A strategy
    hwin]
  cases installation <;> rfl

theorem stepProfiledRawJointHybridGuardedRightReceiver_target_irrel
    (installation : Installation A strategy hwin)
    (row : PairedEntryRow)
    (monitor : (profiledRawJointGuardedRightPhysicalSiblingMonitor A
      (profiledRawJointHybridGuardedRightMoveAt A strategy hwin
        installation).1 false).State)
    (targetOne targetTwo : Option (ProfiledRawJointUnitTarget A))
    (owner : ProfiledRawJointHybridGuardedRightOwnerAt A strategy hwin
      installation)
    (ownInput : In₂) (deliveredInput : In₁) :
    stepProfiledRawJointHybridGuardedRightReceiver A strategy hwin
        ⟨installation, row, monitor, targetOne⟩ ⟨installation, owner⟩
          ownInput deliveredInput =
      stepProfiledRawJointHybridGuardedRightReceiver A strategy hwin
        ⟨installation, row, monitor, targetTwo⟩ ⟨installation, owner⟩
          ownInput deliveredInput := by
  rw [stepProfiledRawJointHybridGuardedRightReceiver_same,
    stepProfiledRawJointHybridGuardedRightReceiver_same]
  rfl

theorem stepProfiledRawJointHybridGuardedLeftReceiver_target_irrel
    (installation : Installation A strategy hwin)
    (row : PairedEntryRow)
    (monitor : (profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      (profiledRawJointHybridGuardedLeftMoveAt A strategy hwin
        installation).1 false).State)
    (targetOne targetTwo : Option (ProfiledRawJointUnitTarget A))
    (owner : ProfiledRawJointHybridGuardedLeftOwnerAt A strategy hwin
      installation)
    (ownInput : In₁) (deliveredInput : In₂) :
    stepProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
        ⟨installation, row, monitor, targetOne⟩ ⟨installation, owner⟩
          ownInput deliveredInput =
      stepProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
        ⟨installation, row, monitor, targetTwo⟩ ⟨installation, owner⟩
          ownInput deliveredInput := by
  rw [stepProfiledRawJointHybridGuardedLeftReceiver_same,
    stepProfiledRawJointHybridGuardedLeftReceiver_same]
  rfl

theorem profiledRawJointHybridGuardedRightPrefixReceiverAfter_step
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input nextInput : In₂ × In₁) :
    (stepProfiledRawJointHybridGuardedRightReceiver A strategy hwin
      (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
        installation past input)
      (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
        installation (past ++ [input])) nextInput.1 nextInput.2).2 =
      profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
        installation (past ++ [input]) nextInput := by
  classical
  rw [profiledRawJointHybridGuardedRightPrefixReceiverAfter_eq A strategy hwin]
  unfold profiledRawJointHybridGuardedRightPrefixReceiverAfter
  unfold profiledRawJointHybridGuardedRightPrefixReceiverBefore
  unfold profiledRawJointHybridGuardedRightPrefixOwner
  rw [stepProfiledRawJointHybridGuardedRightReceiver_target_irrel A strategy
    hwin installation]

theorem profiledRawJointHybridGuardedLeftPrefixReceiverAfter_step
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input nextInput : In₁ × In₂) :
    (stepProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
      (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
        installation past input)
      (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
        installation (past ++ [input])) nextInput.1 nextInput.2).2 =
      profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
        installation (past ++ [input]) nextInput := by
  classical
  rw [profiledRawJointHybridGuardedLeftPrefixReceiverAfter_eq A strategy hwin]
  unfold profiledRawJointHybridGuardedLeftPrefixReceiverAfter
  unfold profiledRawJointHybridGuardedLeftPrefixReceiverBefore
  unfold profiledRawJointHybridGuardedLeftPrefixOwner
  rw [stepProfiledRawJointHybridGuardedLeftReceiver_target_irrel A strategy
    hwin installation]

/-! ## Exact physical outputs along a certified prefix -/

/-- The continuing guarded-right owner emits the sender component of the
same literal finite-monitor record used by the receiver. -/
theorem profiledRawJointHybridGuardedRightPrefixOwner_step_output
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    (stepProfiledRawJointHybridGuardedRightOwner A strategy hwin
      (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
        installation past) input.2).1 =
      (profiledRawJointTargetRightPhysicalLetter A record).2.2 := by
  cases installation <;> rfl

/-- The continuing guarded-right receiver emits the `.both` informed
component of that same record; the stored target from the preceding round is
irrelevant to the output computation. -/
theorem profiledRawJointHybridGuardedRightPrefixReceiverAfter_step_output
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input nextInput : In₂ × In₁) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair (past ++ [input])
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      nextInput
    (stepProfiledRawJointHybridGuardedRightReceiver A strategy hwin
      (profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
        installation past input)
      (profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
        installation (past ++ [input])) nextInput.1 nextInput.2).1 =
      pairedRightInformedForRow .both
        (profiledRawJointTargetRightPhysicalLetter A record).2.1 := by
  classical
  rw [profiledRawJointHybridGuardedRightPrefixReceiverAfter_eq A strategy hwin]
  unfold profiledRawJointHybridGuardedRightPrefixOwner
  rw [stepProfiledRawJointHybridGuardedRightReceiver_same]
  cases installation <;> rfl

/-- Guarded-left owner output mirror. -/
theorem profiledRawJointHybridGuardedLeftPrefixOwner_step_output
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    (stepProfiledRawJointHybridGuardedLeftOwner A strategy hwin
      (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
        installation past) input.2).1 =
      (profiledRawJointTargetLeftPhysicalLetter A record).2.2 := by
  cases installation <;> rfl

/-- Guarded-left receiver output mirror. -/
theorem profiledRawJointHybridGuardedLeftPrefixReceiverAfter_step_output
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input nextInput : In₁ × In₂) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair (past ++ [input])
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      nextInput
    (stepProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
      (profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
        installation past input)
      (profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
        installation (past ++ [input])) nextInput.1 nextInput.2).1 =
      pairedLeftInformedForRow .both
        (profiledRawJointTargetLeftPhysicalLetter A record).2.1 := by
  classical
  rw [profiledRawJointHybridGuardedLeftPrefixReceiverAfter_eq A strategy hwin]
  unfold profiledRawJointHybridGuardedLeftPrefixOwner
  rw [stepProfiledRawJointHybridGuardedLeftReceiver_same]
  cases installation <;> rfl

/-! ## First strict round from a coupled installation -/

theorem profiledRawJointHybridGuardedRightFiniteStateAfter_nil
    (installation : Installation A strategy hwin) :
    profiledRawJointHybridGuardedRightFiniteStateAfter A strategy hwin
        installation [] =
      let move := profiledRawJointHybridGuardedRightMoveAt A strategy hwin
        installation
      ((move.memberController A false).initial,
        (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1 false
          ).initial) := by
  cases installation <;> rfl

theorem profiledRawJointHybridGuardedLeftFiniteStateAfter_nil
    (installation : Installation A strategy hwin) :
    profiledRawJointHybridGuardedLeftFiniteStateAfter A strategy hwin
        installation [] =
      let move := profiledRawJointHybridGuardedLeftMoveAt A strategy hwin
        installation
      ((move.memberController A false).initial,
        (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 false
          ).initial) := by
  cases installation <;> rfl

theorem initialProfiledRawJointHybridGuardedCoupledOne_eq_prefixOwner_nil
    (installation : Installation A strategy hwin) :
    initialProfiledRawJointHybridGuardedCoupledOne A strategy hwin
        installation =
      profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
        installation [] := by
  unfold initialProfiledRawJointHybridGuardedCoupledOne
  unfold profiledRawJointHybridGuardedRightPrefixOwner
  cases installation <;> rfl

theorem initialProfiledRawJointHybridGuardedCoupledTwo_eq_prefixOwner_nil
    (installation : Installation A strategy hwin) :
    initialProfiledRawJointHybridGuardedCoupledTwo A strategy hwin
        installation =
      profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
        installation [] := by
  unfold initialProfiledRawJointHybridGuardedCoupledTwo
  unfold profiledRawJointHybridGuardedLeftPrefixOwner
  cases installation <;> rfl

theorem profiledRawJointHybridGuardedRight_startOwner_eq_prefix
    (installation : Installation A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (startProfiledRawJointHybridGuardedRightOwner A strategy hwin
      (initialProfiledRawJointHybridGuardedCoupledOne A strategy hwin
        installation) inputOne).2 =
      profiledRawJointHybridGuardedRightPrefixOwner A strategy hwin
        installation [(inputTwo, inputOne)] := by
  unfold startProfiledRawJointHybridGuardedRightOwner
  unfold initialProfiledRawJointHybridGuardedCoupledOne
  unfold profiledRawJointHybridGuardedRightPrefixOwner
  rw [show [(inputTwo, inputOne)] = [] ++ [(inputTwo, inputOne)] by rfl]
  rw [profiledRawJointHybridGuardedRightFiniteStateAfter_append_one A
    strategy hwin]
  cases installation <;> rfl

theorem profiledRawJointHybridGuardedRight_startReceiver_eq_prefix
    (installation : Installation A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (startProfiledRawJointHybridGuardedRightReceiver A strategy hwin
      (initialProfiledRawJointHybridGuardedCoupledOne A strategy hwin
        installation) inputTwo inputOne).2 =
      profiledRawJointHybridGuardedRightPrefixReceiverAfter A strategy hwin
        installation [] (inputTwo, inputOne) := by
  rw [initialProfiledRawJointHybridGuardedCoupledOne_eq_prefixOwner_nil A
    strategy hwin]
  unfold startProfiledRawJointHybridGuardedRightReceiver
  unfold profiledRawJointHybridGuardedRightPrefixReceiverAfter
  unfold profiledRawJointHybridGuardedRightPrefixReceiverBefore
  unfold profiledRawJointHybridGuardedRightPrefixOwner
  unfold initialProfiledRawJointHybridGuardedRightReceiver
  rw [stepProfiledRawJointHybridGuardedRightReceiver_same]
  rw [profiledRawJointHybridGuardedRightFiniteStateAfter_nil A strategy hwin]

theorem profiledRawJointHybridGuardedLeft_startOwner_eq_prefix
    (installation : Installation A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (startProfiledRawJointHybridGuardedLeftOwner A strategy hwin
      (initialProfiledRawJointHybridGuardedCoupledTwo A strategy hwin
        installation) inputTwo).2 =
      profiledRawJointHybridGuardedLeftPrefixOwner A strategy hwin
        installation [(inputOne, inputTwo)] := by
  unfold startProfiledRawJointHybridGuardedLeftOwner
  unfold initialProfiledRawJointHybridGuardedCoupledTwo
  unfold profiledRawJointHybridGuardedLeftPrefixOwner
  rw [show [(inputOne, inputTwo)] = [] ++ [(inputOne, inputTwo)] by rfl]
  rw [profiledRawJointHybridGuardedLeftFiniteStateAfter_append_one A strategy
    hwin]
  cases installation <;> rfl

theorem profiledRawJointHybridGuardedLeft_startReceiver_eq_prefix
    (installation : Installation A strategy hwin)
    (inputOne : In₁) (inputTwo : In₂) :
    (startProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
      (initialProfiledRawJointHybridGuardedCoupledTwo A strategy hwin
        installation) inputOne inputTwo).2 =
      profiledRawJointHybridGuardedLeftPrefixReceiverAfter A strategy hwin
        installation [] (inputOne, inputTwo) := by
  rw [initialProfiledRawJointHybridGuardedCoupledTwo_eq_prefixOwner_nil A
    strategy hwin]
  unfold startProfiledRawJointHybridGuardedLeftReceiver
  unfold profiledRawJointHybridGuardedLeftPrefixReceiverAfter
  unfold profiledRawJointHybridGuardedLeftPrefixReceiverBefore
  unfold profiledRawJointHybridGuardedLeftPrefixOwner
  unfold initialProfiledRawJointHybridGuardedLeftReceiver
  rw [stepProfiledRawJointHybridGuardedLeftReceiver_same]
  rw [profiledRawJointHybridGuardedLeftFiniteStateAfter_nil A strategy hwin]

end

end DetParityAutomaton

end DistributedSynthesis
