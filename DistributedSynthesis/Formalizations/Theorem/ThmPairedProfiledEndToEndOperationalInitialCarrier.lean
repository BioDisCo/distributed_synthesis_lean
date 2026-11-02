/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalControllerPackage

/-!
# Finite initial carrier for the end-to-end operational package

The two root-pinned streaming controllers are exposed as local finite-state
operations.  A receiving initial state carries the controller control, the
finite monitor state, and the optional checked boundary key produced by its
last table lookup.  The blind side carries only the controller control.

At a receive, both locally possible shadows are retained.  The subsequent
strict round selects the appropriate first-block projection.  No transition
uses the current graph, an orientation flag, or a strict-leader detector.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (bundle : EndToEndOperationalControllerPackage A)

/-! ## Initial streaming states -/

abbrev EndToEndOperationalInitialLeft :=
  (bundle.leftController.Control ×
      (endToEndInitialLeftPinnedMonitor A bundle.rational).State) ×
    Option (EndToEndInitialLeftBoundaryKey A bundle.rational)

abbrev EndToEndOperationalInitialRight :=
  (bundle.rightController.Control ×
      (endToEndInitialRightPinnedMonitor A bundle.rational).State) ×
    Option (EndToEndInitialRightBoundaryKey A bundle.rational)

noncomputable instance : Fintype
    (EndToEndOperationalInitialLeft A bundle) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (EndToEndOperationalInitialRight A bundle) := by
  classical
  infer_instance

def initialEndToEndOperationalInitialLeft :
    EndToEndOperationalInitialLeft A bundle :=
  ((bundle.leftController.initial,
      (endToEndInitialLeftPinnedMonitor A bundle.rational).initial), none)

def initialEndToEndOperationalInitialRight :
    EndToEndOperationalInitialRight A bundle :=
  ((bundle.rightController.initial,
      (endToEndInitialRightPinnedMonitor A bundle.rational).initial), none)

/-! ## Checked boundary keys -/

noncomputable def endToEndOperationalInitialLeftKey
    (monitorState : (endToEndInitialLeftPinnedMonitor A bundle.rational).State)
    (move : In₁ × In₂) (answer : EndToEndInitialLeftReceiverOutput A)
    (senderOutput : Out₂) :
    Option (EndToEndInitialLeftBoundaryKey A bundle.rational) := by
  classical
  let physical := endToEndInitialLeftPhysicalLetter A
    (move, answer, senderOutput)
  exact if hsource : endToEndInitialLeftSourceOK A bundle.rational
      monitorState.base.1.1 physical answer.2 then
    some ⟨(monitorState.base.1.1, physical, answer.2), hsource⟩
  else none

noncomputable def endToEndOperationalInitialRightKey
    (monitorState : (endToEndInitialRightPinnedMonitor A bundle.rational).State)
    (move : In₂ × In₁) (answer : EndToEndInitialRightReceiverOutput A)
    (senderOutput : Out₁) :
    Option (EndToEndInitialRightBoundaryKey A bundle.rational) := by
  classical
  let physical := endToEndInitialRightPhysicalLetter A
    (move, answer, senderOutput)
  exact if hsource : endToEndInitialRightSourceOK A bundle.rational
      monitorState.base.1.1 physical answer.2 then
    some ⟨(monitorState.base.1.1, physical, answer.2), hsource⟩
  else none

/-! ## Local initial steps -/

noncomputable def endToEndOperationalInitialLeftRecv
    (state : EndToEndOperationalInitialLeft A bundle)
    (move : In₁ × In₂) :
    Out₁ × EndToEndOperationalInitialLeft A bundle :=
  let label := bundle.leftController.labelOf state.1.1
  let answer := label.2 state.1.2 move
  let senderOutput := label.1 move.2
  let record : RealizedBlockRound In₁ In₂
      (EndToEndInitialLeftReceiverOutput A) Out₂ :=
    (move, answer, senderOutput)
  (answer.1.informedOne,
    ((bundle.leftController.step state.1.1 move.2,
      (endToEndInitialLeftPinnedMonitor A bundle.rational).step state.1.2
        record),
      endToEndOperationalInitialLeftKey A bundle state.1.2 move answer
        senderOutput))

noncomputable def endToEndOperationalInitialLeftBlind
    (control : bundle.leftController.Control) (input : In₂) :
    Out₂ × bundle.leftController.Control :=
  ((bundle.leftController.labelOf control).1 input,
    bundle.leftController.step control input)

noncomputable def endToEndOperationalInitialRightRecv
    (state : EndToEndOperationalInitialRight A bundle)
    (move : In₂ × In₁) :
    Out₂ × EndToEndOperationalInitialRight A bundle :=
  let label := bundle.rightController.labelOf state.1.1
  let answer := label.2 state.1.2 move
  let senderOutput := label.1 move.2
  let record : RealizedBlockRound In₂ In₁
      (EndToEndInitialRightReceiverOutput A) Out₁ :=
    (move, answer, senderOutput)
  (answer.1.informedTwo,
    ((bundle.rightController.step state.1.1 move.2,
      (endToEndInitialRightPinnedMonitor A bundle.rational).step state.1.2
        record),
      endToEndOperationalInitialRightKey A bundle state.1.2 move answer
        senderOutput))

noncomputable def endToEndOperationalInitialRightBlind
    (control : bundle.rightController.Control) (input : In₁) :
    Out₁ × bundle.rightController.Control :=
  ((bundle.rightController.labelOf control).1 input,
    bundle.rightController.step control input)

/-! ## The locally indistinguishable root pair -/

abbrev EndToEndOperationalRootHybridOne :=
  EndToEndOperationalInitialLeft A bundle × bundle.rightController.Control

abbrev EndToEndOperationalRootHybridTwo :=
  bundle.leftController.Control × EndToEndOperationalInitialRight A bundle

noncomputable def endToEndOperationalRootRecvOne
    (move : In₁ × In₂) :
    Out₁ × EndToEndOperationalRootHybridOne A bundle :=
  let left := endToEndOperationalInitialLeftRecv A bundle
    (initialEndToEndOperationalInitialLeft A bundle) move
  let right := endToEndOperationalInitialRightBlind A bundle
    bundle.rightController.initial move.1
  (left.1, (left.2, right.2))

noncomputable def endToEndOperationalRootRecvTwo
    (move : In₁ × In₂) :
    Out₂ × EndToEndOperationalRootHybridTwo A bundle :=
  let left := endToEndOperationalInitialLeftBlind A bundle
    bundle.leftController.initial move.2
  let right := endToEndOperationalInitialRightRecv A bundle
    (initialEndToEndOperationalInitialRight A bundle) (move.2, move.1)
  (right.1, (left.2, right.2))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The hybrid root outputs are exactly the left-initial physical pair. -/
theorem endToEndOperationalRoot_output_eq_left (move : In₁ × In₂) :
    ((endToEndOperationalRootRecvOne A bundle move).1,
      (endToEndOperationalRootRecvTwo A bundle move).1) =
    (((bundle.leftController.labelOf bundle.leftController.initial).2
        (endToEndInitialLeftPinnedMonitor A bundle.rational).initial move).1.informedOne,
      ((bundle.leftController.labelOf bundle.leftController.initial).2
        (endToEndInitialLeftPinnedMonitor A bundle.rational).initial move).1.reversingTwo) := by
  apply Prod.ext
  · rfl
  · exact (bundle.root_outputTwo A move).symm

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The same pair is exactly the right-initial physical pair. -/
theorem endToEndOperationalRoot_output_eq_right (move : In₁ × In₂) :
    ((endToEndOperationalRootRecvOne A bundle move).1,
      (endToEndOperationalRootRecvTwo A bundle move).1) =
    (((bundle.rightController.labelOf bundle.rightController.initial).2
        (endToEndInitialRightPinnedMonitor A bundle.rational).initial
          (move.2, move.1)).1.reversingOne,
      ((bundle.rightController.labelOf bundle.rightController.initial).2
        (endToEndInitialRightPinnedMonitor A bundle.rational).initial
          (move.2, move.1)).1.informedTwo) := by
  apply Prod.ext
  · exact bundle.root_outputOne A move
  · rfl

/-! ## Fresh first-block pairs -/

noncomputable def endToEndOperationalFreshFirstRight
    (staged : Option (EndToEndInitialLeftBoundaryKey A bundle.rational))
    (receiverPreviouslyReceived : Bool) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndGuardedFirstRightOwnerControl A bundle.rational ×
        EndToEndGuardedFirstRightReceiverControl A bundle.rational) :=
  match staged with
  | none => ((default, default), none)
  | some key =>
      let owner := initialEndToEndGuardedFirstRightOwner A bundle.rational key
      let receiver := initialEndToEndGuardedFirstRightReceiver A bundle.rational
        key (guardedEntryRowOfReceived receiverPreviouslyReceived)
      let nextOne := stepEndToEndGuardedFirstRightOwner A bundle.rational owner
        move.1
      let nextTwo := continueEndToEndGuardedFirstRightReceiver A bundle.rational
        receiver owner (move.2, move.1)
      ((nextOne.1, nextTwo.1), some (nextOne.2, nextTwo.2))

noncomputable def endToEndOperationalFreshFirstLeft
    (staged : Option (EndToEndInitialRightBoundaryKey A bundle.rational))
    (receiverPreviouslyReceived : Bool) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndGuardedFirstLeftOwnerControl A bundle.rational ×
        EndToEndGuardedFirstLeftReceiverControl A bundle.rational) :=
  match staged with
  | none => ((default, default), none)
  | some key =>
      let owner := initialEndToEndGuardedFirstLeftOwner A bundle.rational key
      let receiver := initialEndToEndGuardedFirstLeftReceiver A bundle.rational
        key (guardedEntryRowOfReceived receiverPreviouslyReceived)
      let nextOne := continueEndToEndGuardedFirstLeftReceiver A bundle.rational
        receiver owner (move.1, move.2)
      let nextTwo := stepEndToEndGuardedFirstLeftOwner A bundle.rational owner
        move.2
      ((nextOne.1, nextTwo.1), some (nextTwo.2, nextOne.2))

/-! ## Initial seam states and refresh -/

abbrev EndToEndOperationalInitialLeftSeamOne :=
  EndToEndOperationalInitialLeft A bundle ×
    (EndToEndGuardedFirstRightOwnerControl A bundle.rational ×
      EndToEndGuardedFirstRightReceiverControl A bundle.rational)

abbrev EndToEndOperationalInitialLeftSeamTwo :=
  bundle.leftController.Control ×
    (EndToEndGuardedFirstRightOwnerControl A bundle.rational ×
      EndToEndGuardedFirstRightReceiverControl A bundle.rational)

abbrev EndToEndOperationalInitialRightSeamOne :=
  bundle.rightController.Control ×
    (EndToEndGuardedFirstLeftOwnerControl A bundle.rational ×
      EndToEndGuardedFirstLeftReceiverControl A bundle.rational)

abbrev EndToEndOperationalInitialRightSeamTwo :=
  EndToEndOperationalInitialRight A bundle ×
    (EndToEndGuardedFirstLeftOwnerControl A bundle.rational ×
      EndToEndGuardedFirstLeftReceiverControl A bundle.rational)

noncomputable def endToEndOperationalInitialLeftSeamRecv
    (one : EndToEndOperationalInitialLeft A bundle)
    (two : bundle.leftController.Control)
    (receiverPreviouslyReceived : Bool) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndOperationalInitialLeftSeamOne A bundle ×
        EndToEndOperationalInitialLeftSeamTwo A bundle) :=
  let anchorOne := endToEndOperationalInitialLeftRecv A bundle one move
  let anchorTwo := endToEndOperationalInitialLeftBlind A bundle two move.2
  let fresh := endToEndOperationalFreshFirstRight A bundle one.2
    receiverPreviouslyReceived move
  ((anchorOne.1, fresh.1.2), fresh.2.map fun pair =>
    ((anchorOne.2, pair), (anchorTwo.2, pair)))

noncomputable def endToEndOperationalInitialRightSeamRecv
    (one : bundle.rightController.Control)
    (two : EndToEndOperationalInitialRight A bundle)
    (receiverPreviouslyReceived : Bool) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndOperationalInitialRightSeamOne A bundle ×
        EndToEndOperationalInitialRightSeamTwo A bundle) :=
  let anchorOne := endToEndOperationalInitialRightBlind A bundle one move.1
  let anchorTwo := endToEndOperationalInitialRightRecv A bundle two
    (move.2, move.1)
  let fresh := endToEndOperationalFreshFirstLeft A bundle two.2
    receiverPreviouslyReceived move
  ((fresh.1.1, anchorTwo.1), fresh.2.map fun pair =>
    ((anchorOne.2, pair), (anchorTwo.2, pair)))

/-! ## Strict selection of a staged first pair -/

noncomputable def endToEndOperationalInitialLeftSeamResolveRight
    (pair : EndToEndGuardedFirstRightOwnerControl A bundle.rational ×
      EndToEndGuardedFirstRightReceiverControl A bundle.rational)
    (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndOperationalPostOne A bundle.rational ×
        EndToEndOperationalPostTwo A bundle.rational) :=
  match endToEndMatchedRightOfControls A bundle.rational
      (.inl pair.1) (.inl pair.2) with
  | none => ((default, default), none)
  | some phase =>
      let next := phase.continue A bundle.rational move
      (next.1, some (.inl next.2.oneControl, .inl next.2.twoControl))

noncomputable def endToEndOperationalInitialRightSeamResolveLeft
    (pair : EndToEndGuardedFirstLeftOwnerControl A bundle.rational ×
      EndToEndGuardedFirstLeftReceiverControl A bundle.rational)
    (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (EndToEndOperationalPostOne A bundle.rational ×
        EndToEndOperationalPostTwo A bundle.rational) :=
  match endToEndMatchedLeftOfControls A bundle.rational
      (.inr (.inl pair.2)) (.inr (.inl pair.1)) with
  | none => ((default, default), none)
  | some phase =>
      let next := phase.continue A bundle.rational move
      (next.1, some (.inl next.2.oneControl, .inl next.2.twoControl))

end

end DetParityAutomaton

end DistributedSynthesis
