/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRecurrentPhaseStep

/-!
# The matched profiled phase invariant

This module packages the reachable same-key configurations of the two local
phase carriers.  It proves closure under every ordinary interior round and
under every strict reversal, including the exceptional-to-recurrent switch.

The invariant is a relation between two local controls, not a shared run-time
phase.  Its constructors and equality proofs exist only in the correctness
argument.  The ambiguous `both` transition, where the local modes can differ,
is deliberately kept for the subsequent overlap/pasting layer.
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
variable (firstBank : FiniteProfiledGuardedFirstControllerBank A)

/-- Proof-level packaging of the four synchronized post-initial modes. -/
inductive ProfiledMatchedPhase where
  | firstRight
      (owner : ProfiledGuardedFirstRightOwnerControl A firstBank)
      (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
      (sameKey : owner.1 = receiver.1)
  | firstLeft
      (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
      (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
      (sameKey : receiver.1 = owner.1)
  | bankRight
      (owner : ProfiledBankRightOwnerControl A)
      (receiver : ProfiledBankRightReceiverControl A)
      (sameKey : owner.1 = receiver.1)
  | bankLeft
      (receiver : ProfiledBankLeftReceiverControl A)
      (owner : ProfiledBankLeftOwnerControl A)
      (sameKey : receiver.1 = owner.1)

/-- Forget the proof invariant to process one's actual local carrier. -/
def ProfiledMatchedPhase.oneControl :
    ProfiledMatchedPhase A firstBank → ProfiledPhaseOneControl A firstBank
  | .firstRight owner _ _ => .inl owner
  | .firstLeft receiver _ _ => .inr (.inl receiver)
  | .bankRight owner _ _ => .inr (.inr (.inl owner))
  | .bankLeft receiver _ _ => .inr (.inr (.inr receiver))

/-- Forget to process two's local carrier. -/
def ProfiledMatchedPhase.twoControl :
    ProfiledMatchedPhase A firstBank → ProfiledPhaseTwoControl A firstBank
  | .firstRight _ receiver _ => .inl receiver
  | .firstLeft _ owner _ => .inr (.inl owner)
  | .bankRight _ receiver _ => .inr (.inr (.inl receiver))
  | .bankLeft _ owner _ => .inr (.inr (.inr owner))

/-! ## Entry from the profiled initial handoff -/

variable
  (leftReceiver : ReceiverBlockStrategy In₁ In₂
    (ProfiledGuardedInitialLeftReceiverOutput A))
  (leftSender : SenderBlockStrategy In₂ Out₂)

noncomputable def profiledInitialLeftMatchedPhaseAt
    (hmonitor : ∀ env : Nat → In₁ × In₂,
      (profiledGuardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay leftReceiver leftSender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) : ProfiledMatchedPhase A firstBank :=
  let key := profiledGuardedInitialLeftFirstMacroAt A leftReceiver leftSender
    hmonitor past move
  .firstRight
    (initialProfiledGuardedFirstRightOwner A firstBank key)
    (initialProfiledGuardedFirstRightActiveReceiver A key row) rfl

@[simp] theorem profiledInitialLeftMatchedPhaseAt_controls
    (hmonitor : ∀ env : Nat → In₁ × In₂,
      (profiledGuardedInitialLeftBlockMonitor A).WinsPlay
        (pairPlay leftReceiver leftSender env))
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    let key := profiledGuardedInitialLeftFirstMacroAt A leftReceiver leftSender
      hmonitor past move
    (profiledInitialLeftMatchedPhaseAt A firstBank leftReceiver leftSender
        hmonitor past move row).oneControl =
        (.inl (initialProfiledGuardedFirstRightOwner A firstBank key)) ∧
      (profiledInitialLeftMatchedPhaseAt A firstBank leftReceiver leftSender
        hmonitor past move row).twoControl =
        (.inl (initialProfiledGuardedFirstRightActiveReceiver A key row)) := by
  exact ⟨rfl, rfl⟩

variable
  (rightReceiver : ReceiverBlockStrategy In₂ In₁
    (ProfiledGuardedInitialRightReceiverOutput A))
  (rightSender : SenderBlockStrategy In₁ Out₁)

noncomputable def profiledInitialRightMatchedPhaseAt
    (hmonitor : ∀ env : Nat → In₂ × In₁,
      (profiledGuardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay rightReceiver rightSender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) : ProfiledMatchedPhase A firstBank :=
  let key := profiledGuardedInitialRightFirstMacroAt A rightReceiver rightSender
    hmonitor past move
  .firstLeft
    (initialProfiledGuardedFirstLeftActiveReceiver A key row)
    (initialProfiledGuardedFirstLeftOwner A firstBank key) rfl

@[simp] theorem profiledInitialRightMatchedPhaseAt_controls
    (hmonitor : ∀ env : Nat → In₂ × In₁,
      (profiledGuardedInitialRightBlockMonitor A).WinsPlay
        (pairPlay rightReceiver rightSender env))
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    let key := profiledGuardedInitialRightFirstMacroAt A rightReceiver
      rightSender hmonitor past move
    (profiledInitialRightMatchedPhaseAt A firstBank rightReceiver rightSender
        hmonitor past move row).oneControl =
        (.inr (.inl
          (initialProfiledGuardedFirstLeftActiveReceiver A key row))) ∧
      (profiledInitialRightMatchedPhaseAt A firstBank rightReceiver rightSender
        hmonitor past move row).twoControl =
        (.inr (.inl
          (initialProfiledGuardedFirstLeftOwner A firstBank key))) := by
  exact ⟨rfl, rfl⟩

/-! ## Closure under an interior round -/

/-- Advance whichever matched block is active.  The result remains in the
same proof-level phase because both local steps preserve their common key. -/
noncomputable def ProfiledMatchedPhase.continue
    (phase : ProfiledMatchedPhase A firstBank) (move : In₁ × In₂) :
    (Out₁ × Out₂) × ProfiledMatchedPhase A firstBank :=
  match phase with
  | .firstRight owner receiver sameKey =>
      let one := stepProfiledGuardedFirstRightOwner A firstBank owner move.1
      let two := continueProfiledGuardedFirstRightReceiver A firstBank receiver
        owner (move.2, move.1)
      ((one.1, two.1), .firstRight one.2 two.2 (by
        rw [stepProfiledGuardedFirstRightOwner_key,
          continueProfiledGuardedFirstRightReceiver_key]
        exact sameKey))
  | .firstLeft receiver owner sameKey =>
      let one := continueProfiledGuardedFirstLeftReceiver A firstBank receiver
        owner move
      let two := stepProfiledGuardedFirstLeftOwner A firstBank owner move.2
      ((one.1, two.1), .firstLeft one.2 two.2 (by
        rw [continueProfiledGuardedFirstLeftReceiver_key,
          stepProfiledGuardedFirstLeftOwner_key]
        exact sameKey))
  | .bankRight owner receiver sameKey =>
      let one := stepProfiledBankRightOwner A owner move.1
      let two := continueProfiledBankRightReceiver A receiver owner
        (move.2, move.1)
      ((one.1, two.1), .bankRight one.2 two.2 (by
        rw [stepProfiledBankRightOwner_source,
          continueProfiledBankRightReceiver_source]
        exact sameKey))
  | .bankLeft receiver owner sameKey =>
      let one := continueProfiledBankLeftReceiver A receiver owner move
      let two := stepProfiledBankLeftOwner A owner move.2
      ((one.1, two.1), .bankLeft one.2 two.2 (by
        rw [continueProfiledBankLeftReceiver_source,
          stepProfiledBankLeftOwner_source]
        exact sameKey))

/-! ## Closure under strict reversals -/

/-- Reverse a right-oriented matched phase into the recurrent left bank.
`none` occurs only when the old receiver has no staged key or when the phase
has the wrong orientation. -/
noncomputable def ProfiledMatchedPhase.reverseRightToLeft
    (phase : ProfiledMatchedPhase A firstBank) (move : In₁ × In₂)
    (previouslyReceived : Bool) :
    (Out₁ × Out₂) × Option (ProfiledMatchedPhase A firstBank) :=
  match phase with
  | .firstRight owner receiver _ =>
      let one := switchProfiledFirstRightOwnerToBankLeftReceiver A firstBank
        owner receiver move previouslyReceived
      let two := switchProfiledFirstRightReceiverToBankLeftOwner A receiver
        move.2
      let next :=
        match hOne : one.2, hTwo : two.2 with
        | some nextReceiver, some nextOwner =>
            some (.bankLeft nextReceiver nextOwner
              (switchProfiledFirstRight_common_source A firstBank owner receiver
                move previouslyReceived nextReceiver nextOwner hOne hTwo))
        | _, _ => none
      ((one.1, two.1), next)
  | .bankRight owner receiver _ =>
      let one := switchProfiledBankRightOwnerToBankLeftReceiver A owner receiver
        move previouslyReceived
      let two := switchProfiledBankRightReceiverToBankLeftOwner A receiver
        move.2
      let next :=
        match hOne : one.2, hTwo : two.2 with
        | some nextReceiver, some nextOwner =>
            some (.bankLeft nextReceiver nextOwner
              (switchProfiledBankRight_common_source A owner receiver move
                previouslyReceived nextReceiver nextOwner hOne hTwo))
        | _, _ => none
      ((one.1, two.1), next)
  | .firstLeft _ _ _ => ((default, default), none)
  | .bankLeft _ _ _ => ((default, default), none)

/-- Left-to-right mirror. -/
noncomputable def ProfiledMatchedPhase.reverseLeftToRight
    (phase : ProfiledMatchedPhase A firstBank) (move : In₂ × In₁)
    (previouslyReceived : Bool) :
    (Out₁ × Out₂) × Option (ProfiledMatchedPhase A firstBank) :=
  match phase with
  | .firstLeft receiver owner _ =>
      let one := switchProfiledFirstLeftReceiverToBankRightOwner A receiver
        move.2
      let two := switchProfiledFirstLeftOwnerToBankRightReceiver A firstBank
        owner receiver move previouslyReceived
      let next :=
        match hOne : one.2, hTwo : two.2 with
        | some nextOwner, some nextReceiver =>
            some (.bankRight nextOwner nextReceiver
              (switchProfiledFirstLeft_common_source A firstBank owner receiver
                move previouslyReceived nextReceiver nextOwner hTwo hOne).symm)
        | _, _ => none
      ((one.1, two.1), next)
  | .bankLeft receiver owner _ =>
      let one := switchProfiledBankLeftReceiverToBankRightOwner A receiver
        move.2
      let two := switchProfiledBankLeftOwnerToBankRightReceiver A owner receiver
        move previouslyReceived
      let next :=
        match hOne : one.2, hTwo : two.2 with
        | some nextOwner, some nextReceiver =>
            some (.bankRight nextOwner nextReceiver
              (switchProfiledBankLeft_common_source A owner receiver move
                previouslyReceived nextReceiver nextOwner hTwo hOne).symm)
        | _, _ => none
      ((one.1, two.1), next)
  | .firstRight _ _ _ => ((default, default), none)
  | .bankRight _ _ _ => ((default, default), none)

end


end


end DetParityAutomaton

end DistributedSynthesis
