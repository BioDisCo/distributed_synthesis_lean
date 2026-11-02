/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedInitialPhaseStep

/-!
# Local recurrent reversal steps

At a strict reversal the old receiver retains its staged opposite-bank key
and becomes the new blind owner.  The new receiver reads that same key from
the delivered partner summary.  Both sides initialize and step the new bank
on the current round.  These operations use no graph or leader tag.

At a `both` round the old receiver instead continues the old block while the
other process takes the same `stepRecv` branch as at a strict reversal.  The
single additional law needed for physical consistency is therefore exposed
below as a named boundary-compatibility predicate: the new receiver's first
informed output must equal the old receiver's closing output.  `Allowed`
alone does not state this equality.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Exceptional first right to ordinary left -/

variable (bank : FiniteGuardedFirstControllerBank A)

noncomputable def switchGuardedFirstRightOwnerToBankLeftReceiver
    (owner : GuardedFirstRightOwnerControl A bank)
    (partner : GuardedFirstRightReceiverControl A) (move : In₁ × In₂)
    (previouslyReceived : Bool) : Out₁ × Option (BankLeftReceiverControl A) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepGuardedFirstRightReceiverFor A bank partner.1
        (guardedFirstRightOwnerControlFor A bank partner owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedRightClosingForRow partner.2.1 oldResult.1, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueBankLeftReceiver A
        (initialBankLeftReceiver A target row)
        (initialBankLeftOwner A target) move
      (result.1, some result.2)

noncomputable def switchGuardedFirstRightReceiverToBankLeftOwner
    (receiver : GuardedFirstRightReceiverControl A) (inputTwo : In₂) :
    Out₂ × Option (BankLeftOwnerControl A) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepBankLeftOwner A (initialBankLeftOwner A target) inputTwo
      (result.1, some result.2)

theorem switchGuardedFirstRight_common_source
    (owner : GuardedFirstRightOwnerControl A bank)
    (receiver : GuardedFirstRightReceiverControl A)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (nextReceiver : BankLeftReceiverControl A)
    (nextOwner : BankLeftOwnerControl A)
    (hreceiver : (switchGuardedFirstRightOwnerToBankLeftReceiver A bank owner
      receiver move previouslyReceived).2 = some nextReceiver)
    (howner : (switchGuardedFirstRightReceiverToBankLeftOwner A receiver
      move.2).2 = some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨key, row, monitor, staged⟩
  cases staged with
  | none => simp [switchGuardedFirstRightReceiverToBankLeftOwner] at howner
  | some target =>
      simp only [switchGuardedFirstRightOwnerToBankLeftReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchGuardedFirstRightReceiverToBankLeftOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueBankLeftReceiver_source, stepBankLeftOwner_source]
      rfl

/-- Exact equality needed when the receiving process cannot distinguish a
strict-left reversal from `both`. -/
def GuardedFirstRightBoundaryCompatible
    (owner : GuardedFirstRightOwnerControl A bank)
    (receiver : GuardedFirstRightReceiverControl A)
    (move : In₁ × In₂) (previouslyReceived : Bool) : Prop :=
  (switchGuardedFirstRightOwnerToBankLeftReceiver A bank owner receiver move
      previouslyReceived).1 =
    pairedRightClosingForRow receiver.2.1
      (stepGuardedFirstRightReceiverFor A bank receiver.1
        (guardedFirstRightOwnerControlFor A bank receiver owner)
        receiver.2.1 receiver.2.2.1 (move.2, move.1)).1

/-! ## Exceptional first left to ordinary right -/

noncomputable def switchGuardedFirstLeftOwnerToBankRightReceiver
    (owner : GuardedFirstLeftOwnerControl A bank)
    (partner : GuardedFirstLeftReceiverControl A) (move : In₂ × In₁)
    (previouslyReceived : Bool) : Out₂ × Option (BankRightReceiverControl A) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepGuardedFirstLeftReceiverFor A bank partner.1
        (guardedFirstLeftOwnerControlFor A bank partner owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedLeftClosingForRow partner.2.1 oldResult.1, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueBankRightReceiver A
        (initialBankRightReceiver A target row)
        (initialBankRightOwner A target) move
      (result.1, some result.2)

noncomputable def switchGuardedFirstLeftReceiverToBankRightOwner
    (receiver : GuardedFirstLeftReceiverControl A) (inputOne : In₁) :
    Out₁ × Option (BankRightOwnerControl A) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepBankRightOwner A (initialBankRightOwner A target) inputOne
      (result.1, some result.2)

theorem switchGuardedFirstLeft_common_source
    (owner : GuardedFirstLeftOwnerControl A bank)
    (receiver : GuardedFirstLeftReceiverControl A)
    (move : In₂ × In₁) (previouslyReceived : Bool)
    (nextReceiver : BankRightReceiverControl A)
    (nextOwner : BankRightOwnerControl A)
    (hreceiver : (switchGuardedFirstLeftOwnerToBankRightReceiver A bank owner
      receiver move previouslyReceived).2 = some nextReceiver)
    (howner : (switchGuardedFirstLeftReceiverToBankRightOwner A receiver
      move.2).2 = some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨key, row, monitor, staged⟩
  cases staged with
  | none => simp [switchGuardedFirstLeftReceiverToBankRightOwner] at howner
  | some target =>
      simp only [switchGuardedFirstLeftOwnerToBankRightReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchGuardedFirstLeftReceiverToBankRightOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueBankRightReceiver_source, stepBankRightOwner_source]
      rfl

def GuardedFirstLeftBoundaryCompatible
    (owner : GuardedFirstLeftOwnerControl A bank)
    (receiver : GuardedFirstLeftReceiverControl A)
    (move : In₂ × In₁) (previouslyReceived : Bool) : Prop :=
  (switchGuardedFirstLeftOwnerToBankRightReceiver A bank owner receiver move
      previouslyReceived).1 =
    pairedLeftClosingForRow receiver.2.1
      (stepGuardedFirstLeftReceiverFor A bank receiver.1
        (guardedFirstLeftOwnerControlFor A bank receiver owner)
        receiver.2.1 receiver.2.2.1 (move.2, move.1)).1

/-! ## Ordinary recurrent right to left -/

noncomputable def switchBankRightOwnerToBankLeftReceiver
    (owner : BankRightOwnerControl A) (partner : BankRightReceiverControl A)
    (move : In₁ × In₂) (previouslyReceived : Bool) :
    Out₁ × Option (BankLeftReceiverControl A) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepBankRightReceiverFor A partner.1
        (bankRightOwnerControlFor A partner owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedRightClosingForRow partner.2.1 oldResult.1, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueBankLeftReceiver A
        (initialBankLeftReceiver A target row)
        (initialBankLeftOwner A target) move
      (result.1, some result.2)

noncomputable def switchBankRightReceiverToBankLeftOwner
    (receiver : BankRightReceiverControl A) (inputTwo : In₂) :
    Out₂ × Option (BankLeftOwnerControl A) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepBankLeftOwner A (initialBankLeftOwner A target) inputTwo
      (result.1, some result.2)

theorem switchBankRight_common_source
    (owner : BankRightOwnerControl A) (receiver : BankRightReceiverControl A)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (nextReceiver : BankLeftReceiverControl A) (nextOwner : BankLeftOwnerControl A)
    (hreceiver : (switchBankRightOwnerToBankLeftReceiver A owner receiver move
      previouslyReceived).2 = some nextReceiver)
    (howner : (switchBankRightReceiverToBankLeftOwner A receiver move.2).2 =
      some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨source, row, monitor, staged⟩
  cases staged with
  | none => simp [switchBankRightReceiverToBankLeftOwner] at howner
  | some target =>
      simp only [switchBankRightOwnerToBankLeftReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchBankRightReceiverToBankLeftOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueBankLeftReceiver_source, stepBankLeftOwner_source]
      rfl

def BankRightBoundaryCompatible
    (owner : BankRightOwnerControl A) (receiver : BankRightReceiverControl A)
    (move : In₁ × In₂) (previouslyReceived : Bool) : Prop :=
  (switchBankRightOwnerToBankLeftReceiver A owner receiver move
      previouslyReceived).1 =
    pairedRightClosingForRow receiver.2.1
      (stepBankRightReceiverFor A receiver.1
        (bankRightOwnerControlFor A receiver owner)
        receiver.2.1 receiver.2.2.1 (move.2, move.1)).1

/-! ## Ordinary left to right -/

noncomputable def switchBankLeftOwnerToBankRightReceiver
    (owner : BankLeftOwnerControl A) (partner : BankLeftReceiverControl A)
    (move : In₂ × In₁) (previouslyReceived : Bool) :
    Out₂ × Option (BankRightReceiverControl A) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepBankLeftReceiverFor A partner.1
        (bankLeftOwnerControlFor A partner owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedLeftClosingForRow partner.2.1 oldResult.1, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueBankRightReceiver A
        (initialBankRightReceiver A target row)
        (initialBankRightOwner A target) move
      (result.1, some result.2)

noncomputable def switchBankLeftReceiverToBankRightOwner
    (receiver : BankLeftReceiverControl A) (inputOne : In₁) :
    Out₁ × Option (BankRightOwnerControl A) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepBankRightOwner A (initialBankRightOwner A target) inputOne
      (result.1, some result.2)

theorem switchBankLeft_common_source
    (owner : BankLeftOwnerControl A) (receiver : BankLeftReceiverControl A)
    (move : In₂ × In₁) (previouslyReceived : Bool)
    (nextReceiver : BankRightReceiverControl A) (nextOwner : BankRightOwnerControl A)
    (hreceiver : (switchBankLeftOwnerToBankRightReceiver A owner receiver move
      previouslyReceived).2 = some nextReceiver)
    (howner : (switchBankLeftReceiverToBankRightOwner A receiver move.2).2 =
      some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨source, row, monitor, staged⟩
  cases staged with
  | none => simp [switchBankLeftReceiverToBankRightOwner] at howner
  | some target =>
      simp only [switchBankLeftOwnerToBankRightReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchBankLeftReceiverToBankRightOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueBankRightReceiver_source, stepBankRightOwner_source]
      rfl

def BankLeftBoundaryCompatible
    (owner : BankLeftOwnerControl A) (receiver : BankLeftReceiverControl A)
    (move : In₂ × In₁) (previouslyReceived : Bool) : Prop :=
  (switchBankLeftOwnerToBankRightReceiver A owner receiver move
      previouslyReceived).1 =
    pairedLeftClosingForRow receiver.2.1
      (stepBankLeftReceiverFor A receiver.1
        (bankLeftOwnerControlFor A receiver owner)
        receiver.2.1 receiver.2.2.1 (move.2, move.1)).1

end


end DetParityAutomaton

end DistributedSynthesis
