/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOperationalPostStep

/-!
# Finite operational steps at the initial seam

At the first possible reversal, a receiving process cannot distinguish a
strict receive from `both`.  It therefore retains the old initial anchor and
the complete freshly activated exceptional pair.  Retaining both projections
is the finite delay-one table: if the other process did not receive on that
round, the next delivered summary supplies the projection it could not have
computed locally.  No current-orientation or strict-leader flag is stored.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (rightBasis : ∀ target profile,
    (rightProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (leftBasis : ∀ target profile,
    (leftProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (controllers : LocallyConsistentProfiledGuardedInitialControllers
    A strategy hwin rightBasis leftBasis)
  (firstBank : FiniteProfiledGuardedFirstControllerBank A)

/-! ## Initial anchor updates -/

/-- Advance the receiving initial-left anchor and stage its next exceptional
key. -/
noncomputable def profiledInitialLeftAnchorRecv
    (state : ProfiledOperationalInitialLeft A strategy hwin rightBasis
      leftBasis controllers) (move : In₁ × In₂) :
    Out₁ × ProfiledOperationalInitialLeft A strategy hwin rightBasis leftBasis
      controllers :=
  let answer := (controllers.leftController.labelOf state.1.1).2 state.1.2 move
  (answer.1.informedOne,
    (stepProfiledGuardedInitialLeftFiniteReadback A strategy hwin rightBasis
      leftBasis controllers state.1 move,
    profiledGuardedInitialLeftLocalFirstMacro A strategy hwin rightBasis
      leftBasis controllers state.1 move))

/-- Advance the blind initial-left anchor at process two. -/
noncomputable def profiledInitialLeftAnchorBlind
    (state : controllers.leftController.Control) (input : In₂) :
    Out₂ × controllers.leftController.Control :=
  ((controllers.leftController.labelOf state).1 input,
    controllers.leftController.step state input)

/-- Initial-right receiving anchor. -/
noncomputable def profiledInitialRightAnchorRecv
    (state : ProfiledOperationalInitialRight A strategy hwin rightBasis
      leftBasis controllers) (move : In₂ × In₁) :
    Out₂ × ProfiledOperationalInitialRight A strategy hwin rightBasis leftBasis
      controllers :=
  let answer := (controllers.rightController.labelOf state.1.1).2 state.1.2 move
  (answer.1.informedTwo,
    (stepProfiledGuardedInitialRightFiniteReadback A strategy hwin rightBasis
      leftBasis controllers state.1 move,
    profiledGuardedInitialRightLocalFirstMacro A strategy hwin rightBasis
      leftBasis controllers state.1 move))

/-- Blind initial-right anchor at process one. -/
noncomputable def profiledInitialRightAnchorBlind
    (state : controllers.rightController.Control) (input : In₁) :
    Out₁ × controllers.rightController.Control :=
  ((controllers.rightController.labelOf state).1 input,
    controllers.rightController.step state input)

/-! ## Fresh exceptional pairs -/

/-- Step a fresh first-right pair using the key staged on the preceding
initial-left receive. -/
noncomputable def profiledFreshFirstRight
    (staged : Option (ProfiledGuardedFirstRightMacro A))
    (receiverPreviouslyReceived : Bool) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledGuardedFirstRightOwnerControl A firstBank ×
        ProfiledGuardedFirstRightActiveReceiverControl A) :=
  match staged with
  | none => ((default, default), none)
  | some key =>
      let owner := initialProfiledGuardedFirstRightOwner A firstBank key
      let receiver := initialProfiledGuardedFirstRightActiveReceiver A key
        (guardedEntryRowOfReceived receiverPreviouslyReceived)
      let nextOne := stepProfiledGuardedFirstRightOwner A firstBank owner move.1
      let nextTwo := continueProfiledGuardedFirstRightReceiver A firstBank
        receiver owner (move.2, move.1)
      ((nextOne.1, nextTwo.1), some (nextOne.2, nextTwo.2))

/-- Fresh first-left mirror. -/
noncomputable def profiledFreshFirstLeft
    (staged : Option (ProfiledGuardedFirstLeftMacro A))
    (receiverPreviouslyReceived : Bool) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledGuardedFirstLeftOwnerControl A firstBank ×
        ProfiledGuardedFirstLeftActiveReceiverControl A) :=
  match staged with
  | none => ((default, default), none)
  | some key =>
      let owner := initialProfiledGuardedFirstLeftOwner A firstBank key
      let receiver := initialProfiledGuardedFirstLeftActiveReceiver A key
        (guardedEntryRowOfReceived receiverPreviouslyReceived)
      let nextOne := continueProfiledGuardedFirstLeftReceiver A firstBank
        receiver owner move
      let nextTwo := stepProfiledGuardedFirstLeftOwner A firstBank owner move.2
      ((nextOne.1, nextTwo.1), some (nextTwo.2, nextOne.2))

/-! ## Receive refreshes -/

/-- Refresh the first-right shadow while continuing the initial-left anchor.
The process-one output comes from the anchor, and the process-two output from
the exceptional shadow, exactly as forced by the two receive branches. -/
noncomputable def profiledInitialLeftSeamRecv
    (one : ProfiledOperationalInitialLeft A strategy hwin rightBasis
      leftBasis controllers)
    (two : controllers.leftController.Control)
    (receiverPreviouslyReceived : Bool) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledOperationalInitialLeftSeamOne A strategy hwin rightBasis
          leftBasis controllers firstBank ×
        ProfiledOperationalInitialLeftSeamTwo A strategy hwin rightBasis
          leftBasis controllers firstBank) :=
  let anchorOne := profiledInitialLeftAnchorRecv A strategy hwin rightBasis
    leftBasis controllers one move
  let anchorTwo := profiledInitialLeftAnchorBlind A strategy hwin rightBasis
    leftBasis controllers two move.2
  let fresh := profiledFreshFirstRight A firstBank one.2
    receiverPreviouslyReceived move
  ((anchorOne.1, fresh.1.2), fresh.2.map fun pair =>
    ((anchorOne.2, pair), (anchorTwo.2, pair)))

/-- Initial-right mirror. -/
noncomputable def profiledInitialRightSeamRecv
    (one : controllers.rightController.Control)
    (two : ProfiledOperationalInitialRight A strategy hwin rightBasis
      leftBasis controllers)
    (receiverPreviouslyReceived : Bool) (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledOperationalInitialRightSeamOne A strategy hwin rightBasis
          leftBasis controllers firstBank ×
        ProfiledOperationalInitialRightSeamTwo A strategy hwin rightBasis
          leftBasis controllers firstBank) :=
  let anchorOne := profiledInitialRightAnchorBlind A strategy hwin rightBasis
    leftBasis controllers one move.1
  let anchorTwo := profiledInitialRightAnchorRecv A strategy hwin rightBasis
    leftBasis controllers two (move.2, move.1)
  let fresh := profiledFreshFirstLeft A firstBank two.2
    receiverPreviouslyReceived move
  ((fresh.1.1, anchorTwo.1), fresh.2.map fun pair =>
    ((anchorOne.2, pair), (anchorTwo.2, pair)))

/-! ## Strict resolution of a staged seam -/

/-- A strict-right round selects and advances the stored first-right pair. -/
noncomputable def profiledInitialLeftSeamResolveRight
    (pair : ProfiledGuardedFirstRightOwnerControl A firstBank ×
      ProfiledGuardedFirstRightActiveReceiverControl A)
    (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledOperationalPostOne A firstBank ×
        ProfiledOperationalPostTwo A firstBank) :=
  match profiledMatchedRightOfControls A firstBank (.inl pair.1) (.inl pair.2) with
  | none => ((default, default), none)
  | some phase =>
      let next := phase.continue A firstBank move
      (next.1, some (.inl next.2.oneControl, .inl next.2.twoControl))

/-- Strict-left mirror. -/
noncomputable def profiledInitialRightSeamResolveLeft
    (pair : ProfiledGuardedFirstLeftOwnerControl A firstBank ×
      ProfiledGuardedFirstLeftActiveReceiverControl A)
    (move : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledOperationalPostOne A firstBank ×
        ProfiledOperationalPostTwo A firstBank) :=
  match profiledMatchedLeftOfControls A firstBank
      (.inr (.inl pair.2)) (.inr (.inl pair.1)) with
  | none => ((default, default), none)
  | some phase =>
      let next := phase.continue A firstBank move
      (next.1, some (.inl next.2.oneControl, .inl next.2.twoControl))

end

end

end DetParityAutomaton

end DistributedSynthesis
