/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledPhaseCarrier

/-!
# Strict reversal steps for the profiled phase carrier

At a strict reversal the old receiver's staged certificate becomes the common
key of the new owner and receiver.  Both new controls are initialized and
stepped on the reversal round.  The operations below are local: the old
receiver retains the key, while the new receiver reconstructs it from the
delivered partner summary.
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

/-! ## Exceptional right to recurrent left -/

noncomputable def switchProfiledFirstRightOwnerToBankLeftReceiver
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank)
    (partner : ProfiledGuardedFirstRightActiveReceiverControl A)
    (move : In₁ × In₂) (previouslyReceived : Bool) :
    Out₁ × Option (ProfiledBankLeftReceiverControl A) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepProfiledGuardedFirstRightReceiverFor A firstBank
        partner.1
        (profiledGuardedFirstRightOwnerControlFor A firstBank partner owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedRightClosingForRow partner.2.1 oldResult.1.physical, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueProfiledBankLeftReceiver A
        (initialProfiledBankLeftReceiver A target row)
        (initialProfiledBankLeftOwner A target) move
      (result.1, some result.2)

noncomputable def switchProfiledFirstRightReceiverToBankLeftOwner
    (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
    (inputTwo : In₂) : Out₂ × Option (ProfiledBankLeftOwnerControl A) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepProfiledBankLeftOwner A
        (initialProfiledBankLeftOwner A target) inputTwo
      (result.1, some result.2)

theorem switchProfiledFirstRight_common_source
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank)
    (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (nextReceiver : ProfiledBankLeftReceiverControl A)
    (nextOwner : ProfiledBankLeftOwnerControl A)
    (hreceiver :
      (switchProfiledFirstRightOwnerToBankLeftReceiver A firstBank owner
        receiver move previouslyReceived).2 = some nextReceiver)
    (howner :
      (switchProfiledFirstRightReceiverToBankLeftOwner A receiver move.2).2 =
        some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨key, row, monitor, staged⟩
  cases staged with
  | none =>
      simp [switchProfiledFirstRightReceiverToBankLeftOwner] at howner
  | some target =>
      simp only [switchProfiledFirstRightOwnerToBankLeftReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchProfiledFirstRightReceiverToBankLeftOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueProfiledBankLeftReceiver_source,
        stepProfiledBankLeftOwner_source]
      rfl

/-- Physical equality required at an ambiguous synchronization while an
exceptional right block closes into the recurrent left bank. -/
def ProfiledFirstRightBoundaryCompatible
    (owner : ProfiledGuardedFirstRightOwnerControl A firstBank)
    (receiver : ProfiledGuardedFirstRightActiveReceiverControl A)
    (move : In₁ × In₂) (previouslyReceived : Bool) : Prop :=
  (switchProfiledFirstRightOwnerToBankLeftReceiver A firstBank owner receiver
      move previouslyReceived).1 =
    pairedRightClosingForRow receiver.2.1
      (stepProfiledGuardedFirstRightReceiverFor A firstBank receiver.1
        (profiledGuardedFirstRightOwnerControlFor A firstBank receiver owner)
        receiver.2.1 receiver.2.2.1 (move.2, move.1)).1.physical

/-! ## Exceptional left to recurrent right -/

noncomputable def switchProfiledFirstLeftOwnerToBankRightReceiver
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
    (partner : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (move : In₂ × In₁) (previouslyReceived : Bool) :
    Out₂ × Option (ProfiledBankRightReceiverControl A) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepProfiledGuardedFirstLeftReceiverFor A firstBank
        partner.1
        (profiledGuardedFirstLeftOwnerControlFor A firstBank partner owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedLeftClosingForRow partner.2.1 oldResult.1.physical, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueProfiledBankRightReceiver A
        (initialProfiledBankRightReceiver A target row)
        (initialProfiledBankRightOwner A target) move
      (result.1, some result.2)

noncomputable def switchProfiledFirstLeftReceiverToBankRightOwner
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (inputOne : In₁) : Out₁ × Option (ProfiledBankRightOwnerControl A) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepProfiledBankRightOwner A
        (initialProfiledBankRightOwner A target) inputOne
      (result.1, some result.2)

theorem switchProfiledFirstLeft_common_source
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (move : In₂ × In₁) (previouslyReceived : Bool)
    (nextReceiver : ProfiledBankRightReceiverControl A)
    (nextOwner : ProfiledBankRightOwnerControl A)
    (hreceiver :
      (switchProfiledFirstLeftOwnerToBankRightReceiver A firstBank owner
        receiver move previouslyReceived).2 = some nextReceiver)
    (howner :
      (switchProfiledFirstLeftReceiverToBankRightOwner A receiver move.2).2 =
        some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨key, row, monitor, staged⟩
  cases staged with
  | none =>
      simp [switchProfiledFirstLeftReceiverToBankRightOwner] at howner
  | some target =>
      simp only [switchProfiledFirstLeftOwnerToBankRightReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchProfiledFirstLeftReceiverToBankRightOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueProfiledBankRightReceiver_source,
        stepProfiledBankRightOwner_source]
      rfl

def ProfiledFirstLeftBoundaryCompatible
    (owner : ProfiledGuardedFirstLeftOwnerControl A firstBank)
    (receiver : ProfiledGuardedFirstLeftActiveReceiverControl A)
    (move : In₂ × In₁) (previouslyReceived : Bool) : Prop :=
  (switchProfiledFirstLeftOwnerToBankRightReceiver A firstBank owner receiver
      move previouslyReceived).1 =
    pairedLeftClosingForRow receiver.2.1
      (stepProfiledGuardedFirstLeftReceiverFor A firstBank receiver.1
        (profiledGuardedFirstLeftOwnerControlFor A firstBank receiver owner)
        receiver.2.1 receiver.2.2.1 (move.2, move.1)).1.physical

/-! ## Recurrent right to recurrent left -/

noncomputable def switchProfiledBankRightOwnerToBankLeftReceiver
    (owner : ProfiledBankRightOwnerControl A)
    (partner : ProfiledBankRightReceiverControl A)
    (move : In₁ × In₂) (previouslyReceived : Bool) :
    Out₁ × Option (ProfiledBankLeftReceiverControl A) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepProfiledBankRightReceiverFor A partner.1
        (profiledBankRightOwnerControlFor A partner owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedRightClosingForRow partner.2.1 oldResult.1.physical, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueProfiledBankLeftReceiver A
        (initialProfiledBankLeftReceiver A target row)
        (initialProfiledBankLeftOwner A target) move
      (result.1, some result.2)

noncomputable def switchProfiledBankRightReceiverToBankLeftOwner
    (receiver : ProfiledBankRightReceiverControl A) (inputTwo : In₂) :
    Out₂ × Option (ProfiledBankLeftOwnerControl A) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepProfiledBankLeftOwner A
        (initialProfiledBankLeftOwner A target) inputTwo
      (result.1, some result.2)

theorem switchProfiledBankRight_common_source
    (owner : ProfiledBankRightOwnerControl A)
    (receiver : ProfiledBankRightReceiverControl A)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (nextReceiver : ProfiledBankLeftReceiverControl A)
    (nextOwner : ProfiledBankLeftOwnerControl A)
    (hreceiver :
      (switchProfiledBankRightOwnerToBankLeftReceiver A owner receiver move
        previouslyReceived).2 = some nextReceiver)
    (howner :
      (switchProfiledBankRightReceiverToBankLeftOwner A receiver move.2).2 =
        some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨source, row, monitor, staged⟩
  cases staged with
  | none =>
      simp [switchProfiledBankRightReceiverToBankLeftOwner] at howner
  | some target =>
      simp only [switchProfiledBankRightOwnerToBankLeftReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchProfiledBankRightReceiverToBankLeftOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueProfiledBankLeftReceiver_source,
        stepProfiledBankLeftOwner_source]
      rfl

def ProfiledBankRightBoundaryCompatible
    (owner : ProfiledBankRightOwnerControl A)
    (receiver : ProfiledBankRightReceiverControl A)
    (move : In₁ × In₂) (previouslyReceived : Bool) : Prop :=
  (switchProfiledBankRightOwnerToBankLeftReceiver A owner receiver move
      previouslyReceived).1 =
    pairedRightClosingForRow receiver.2.1
      (stepProfiledBankRightReceiverFor A receiver.1
        (profiledBankRightOwnerControlFor A receiver owner)
        receiver.2.1 receiver.2.2.1 (move.2, move.1)).1.physical

/-! ## Recurrent left to recurrent right -/

noncomputable def switchProfiledBankLeftOwnerToBankRightReceiver
    (owner : ProfiledBankLeftOwnerControl A)
    (partner : ProfiledBankLeftReceiverControl A)
    (move : In₂ × In₁) (previouslyReceived : Bool) :
    Out₂ × Option (ProfiledBankRightReceiverControl A) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepProfiledBankLeftReceiverFor A partner.1
        (profiledBankLeftOwnerControlFor A partner owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedLeftClosingForRow partner.2.1 oldResult.1.physical, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueProfiledBankRightReceiver A
        (initialProfiledBankRightReceiver A target row)
        (initialProfiledBankRightOwner A target) move
      (result.1, some result.2)

noncomputable def switchProfiledBankLeftReceiverToBankRightOwner
    (receiver : ProfiledBankLeftReceiverControl A) (inputOne : In₁) :
    Out₁ × Option (ProfiledBankRightOwnerControl A) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepProfiledBankRightOwner A
        (initialProfiledBankRightOwner A target) inputOne
      (result.1, some result.2)

theorem switchProfiledBankLeft_common_source
    (owner : ProfiledBankLeftOwnerControl A)
    (receiver : ProfiledBankLeftReceiverControl A)
    (move : In₂ × In₁) (previouslyReceived : Bool)
    (nextReceiver : ProfiledBankRightReceiverControl A)
    (nextOwner : ProfiledBankRightOwnerControl A)
    (hreceiver :
      (switchProfiledBankLeftOwnerToBankRightReceiver A owner receiver move
        previouslyReceived).2 = some nextReceiver)
    (howner :
      (switchProfiledBankLeftReceiverToBankRightOwner A receiver move.2).2 =
        some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨source, row, monitor, staged⟩
  cases staged with
  | none =>
      simp [switchProfiledBankLeftReceiverToBankRightOwner] at howner
  | some target =>
      simp only [switchProfiledBankLeftOwnerToBankRightReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchProfiledBankLeftReceiverToBankRightOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueProfiledBankRightReceiver_source,
        stepProfiledBankRightOwner_source]
      rfl

def ProfiledBankLeftBoundaryCompatible
    (owner : ProfiledBankLeftOwnerControl A)
    (receiver : ProfiledBankLeftReceiverControl A)
    (move : In₂ × In₁) (previouslyReceived : Bool) : Prop :=
  (switchProfiledBankLeftOwnerToBankRightReceiver A owner receiver move
      previouslyReceived).1 =
    pairedLeftClosingForRow receiver.2.1
      (stepProfiledBankLeftReceiverFor A receiver.1
        (profiledBankLeftOwnerControlFor A receiver owner)
        receiver.2.1 receiver.2.2.1 (move.2, move.1)).1.physical

end


end


end DetParityAutomaton

end DistributedSynthesis
