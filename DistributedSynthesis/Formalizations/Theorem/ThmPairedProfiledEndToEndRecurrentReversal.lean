/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndFirstReversal

/-!
# Recurrent strict reversals in the package-wide bank

The four reversal pairs below cover both orientations below both possible
first-block origins.  In every case the staged macro is already indexed by
the original boundary and guarded child, so initializing the opposite phase
cannot change the rational policy.  The common-source theorems are the local
synchronization invariant needed by the global phase machine.
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

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## Right-origin: recurrent right to recurrent left -/

noncomputable def switchEndToEndRightOriginRightOwnerToLeftReceiver
    (owner : EndToEndRightOriginRecurrentRightOwnerControl A package)
    (partner : EndToEndRightOriginRecurrentRightReceiverControl A package)
    (move : In₁ × In₂) (previouslyReceived : Bool) :
    Out₁ × Option
      (EndToEndRightOriginRecurrentLeftReceiverControl A package) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepEndToEndRightOriginRecurrentRightReceiverFor A
        package partner.1
        (endToEndRightOriginRecurrentRightOwnerControlFor A package partner
          owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedRightClosingForRow partner.2.1 oldResult.1.physical, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueEndToEndRightOriginRecurrentLeftReceiver A package
        (initialEndToEndRightOriginRecurrentLeftReceiver A package target row)
        (initialEndToEndRightOriginRecurrentLeftOwner A package target) move
      (result.1, some result.2)

noncomputable def switchEndToEndRightOriginRightReceiverToLeftOwner
    (receiver : EndToEndRightOriginRecurrentRightReceiverControl A package)
    (inputTwo : In₂) :
    Out₂ × Option (EndToEndRightOriginRecurrentLeftOwnerControl A package) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepEndToEndRightOriginRecurrentLeftOwner A package
        (initialEndToEndRightOriginRecurrentLeftOwner A package target) inputTwo
      (result.1, some result.2)

theorem switchEndToEndRightOriginRight_common_source
    (owner : EndToEndRightOriginRecurrentRightOwnerControl A package)
    (receiver : EndToEndRightOriginRecurrentRightReceiverControl A package)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (nextReceiver : EndToEndRightOriginRecurrentLeftReceiverControl A package)
    (nextOwner : EndToEndRightOriginRecurrentLeftOwnerControl A package)
    (hreceiver :
      (switchEndToEndRightOriginRightOwnerToLeftReceiver A package owner
        receiver move previouslyReceived).2 = some nextReceiver)
    (howner :
      (switchEndToEndRightOriginRightReceiverToLeftOwner A package receiver
        move.2).2 = some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨source, row, monitor, staged⟩
  cases staged with
  | none =>
      simp [switchEndToEndRightOriginRightReceiverToLeftOwner] at howner
  | some target =>
      simp only [switchEndToEndRightOriginRightOwnerToLeftReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchEndToEndRightOriginRightReceiverToLeftOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueEndToEndRightOriginRecurrentLeftReceiver_source,
        stepEndToEndRightOriginRecurrentLeftOwner_source]
      rfl

/-! ## Right-origin: recurrent left to recurrent right -/

noncomputable def switchEndToEndRightOriginLeftOwnerToRightReceiver
    (owner : EndToEndRightOriginRecurrentLeftOwnerControl A package)
    (partner : EndToEndRightOriginRecurrentLeftReceiverControl A package)
    (move : In₂ × In₁) (previouslyReceived : Bool) :
    Out₂ × Option
      (EndToEndRightOriginRecurrentRightReceiverControl A package) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepEndToEndRightOriginRecurrentLeftReceiverFor A
        package partner.1
        (endToEndRightOriginRecurrentLeftOwnerControlFor A package partner
          owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedLeftClosingForRow partner.2.1 oldResult.1.physical, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueEndToEndRightOriginRecurrentRightReceiver A package
        (initialEndToEndRightOriginRecurrentRightReceiver A package target row)
        (initialEndToEndRightOriginRecurrentRightOwner A package target) move
      (result.1, some result.2)

noncomputable def switchEndToEndRightOriginLeftReceiverToRightOwner
    (receiver : EndToEndRightOriginRecurrentLeftReceiverControl A package)
    (inputOne : In₁) :
    Out₁ × Option (EndToEndRightOriginRecurrentRightOwnerControl A package) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepEndToEndRightOriginRecurrentRightOwner A package
        (initialEndToEndRightOriginRecurrentRightOwner A package target) inputOne
      (result.1, some result.2)

theorem switchEndToEndRightOriginLeft_common_source
    (owner : EndToEndRightOriginRecurrentLeftOwnerControl A package)
    (receiver : EndToEndRightOriginRecurrentLeftReceiverControl A package)
    (move : In₂ × In₁) (previouslyReceived : Bool)
    (nextReceiver : EndToEndRightOriginRecurrentRightReceiverControl A package)
    (nextOwner : EndToEndRightOriginRecurrentRightOwnerControl A package)
    (hreceiver :
      (switchEndToEndRightOriginLeftOwnerToRightReceiver A package owner
        receiver move previouslyReceived).2 = some nextReceiver)
    (howner :
      (switchEndToEndRightOriginLeftReceiverToRightOwner A package receiver
        move.2).2 = some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨source, row, monitor, staged⟩
  cases staged with
  | none =>
      simp [switchEndToEndRightOriginLeftReceiverToRightOwner] at howner
  | some target =>
      simp only [switchEndToEndRightOriginLeftOwnerToRightReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchEndToEndRightOriginLeftReceiverToRightOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueEndToEndRightOriginRecurrentRightReceiver_source,
        stepEndToEndRightOriginRecurrentRightOwner_source]
      rfl

/-! ## Left-origin: recurrent right to recurrent left -/

noncomputable def switchEndToEndLeftOriginRightOwnerToLeftReceiver
    (owner : EndToEndLeftOriginRecurrentRightOwnerControl A package)
    (partner : EndToEndLeftOriginRecurrentRightReceiverControl A package)
    (move : In₁ × In₂) (previouslyReceived : Bool) :
    Out₁ × Option
      (EndToEndLeftOriginRecurrentLeftReceiverControl A package) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepEndToEndLeftOriginRecurrentRightReceiverFor A
        package partner.1
        (endToEndLeftOriginRecurrentRightOwnerControlFor A package partner
          owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedRightClosingForRow partner.2.1 oldResult.1.physical, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueEndToEndLeftOriginRecurrentLeftReceiver A package
        (initialEndToEndLeftOriginRecurrentLeftReceiver A package target row)
        (initialEndToEndLeftOriginRecurrentLeftOwner A package target) move
      (result.1, some result.2)

noncomputable def switchEndToEndLeftOriginRightReceiverToLeftOwner
    (receiver : EndToEndLeftOriginRecurrentRightReceiverControl A package)
    (inputTwo : In₂) :
    Out₂ × Option (EndToEndLeftOriginRecurrentLeftOwnerControl A package) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepEndToEndLeftOriginRecurrentLeftOwner A package
        (initialEndToEndLeftOriginRecurrentLeftOwner A package target) inputTwo
      (result.1, some result.2)

theorem switchEndToEndLeftOriginRight_common_source
    (owner : EndToEndLeftOriginRecurrentRightOwnerControl A package)
    (receiver : EndToEndLeftOriginRecurrentRightReceiverControl A package)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (nextReceiver : EndToEndLeftOriginRecurrentLeftReceiverControl A package)
    (nextOwner : EndToEndLeftOriginRecurrentLeftOwnerControl A package)
    (hreceiver :
      (switchEndToEndLeftOriginRightOwnerToLeftReceiver A package owner
        receiver move previouslyReceived).2 = some nextReceiver)
    (howner :
      (switchEndToEndLeftOriginRightReceiverToLeftOwner A package receiver
        move.2).2 = some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨source, row, monitor, staged⟩
  cases staged with
  | none =>
      simp [switchEndToEndLeftOriginRightReceiverToLeftOwner] at howner
  | some target =>
      simp only [switchEndToEndLeftOriginRightOwnerToLeftReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchEndToEndLeftOriginRightReceiverToLeftOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueEndToEndLeftOriginRecurrentLeftReceiver_source,
        stepEndToEndLeftOriginRecurrentLeftOwner_source]
      rfl

/-! ## Left-origin: recurrent left to recurrent right -/

noncomputable def switchEndToEndLeftOriginLeftOwnerToRightReceiver
    (owner : EndToEndLeftOriginRecurrentLeftOwnerControl A package)
    (partner : EndToEndLeftOriginRecurrentLeftReceiverControl A package)
    (move : In₂ × In₁) (previouslyReceived : Bool) :
    Out₂ × Option
      (EndToEndLeftOriginRecurrentRightReceiverControl A package) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepEndToEndLeftOriginRecurrentLeftReceiverFor A
        package partner.1
        (endToEndLeftOriginRecurrentLeftOwnerControlFor A package partner
          owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedLeftClosingForRow partner.2.1 oldResult.1.physical, none)
  | some target =>
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueEndToEndLeftOriginRecurrentRightReceiver A package
        (initialEndToEndLeftOriginRecurrentRightReceiver A package target row)
        (initialEndToEndLeftOriginRecurrentRightOwner A package target) move
      (result.1, some result.2)

noncomputable def switchEndToEndLeftOriginLeftReceiverToRightOwner
    (receiver : EndToEndLeftOriginRecurrentLeftReceiverControl A package)
    (inputOne : In₁) :
    Out₁ × Option (EndToEndLeftOriginRecurrentRightOwnerControl A package) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let result := stepEndToEndLeftOriginRecurrentRightOwner A package
        (initialEndToEndLeftOriginRecurrentRightOwner A package target) inputOne
      (result.1, some result.2)

theorem switchEndToEndLeftOriginLeft_common_source
    (owner : EndToEndLeftOriginRecurrentLeftOwnerControl A package)
    (receiver : EndToEndLeftOriginRecurrentLeftReceiverControl A package)
    (move : In₂ × In₁) (previouslyReceived : Bool)
    (nextReceiver : EndToEndLeftOriginRecurrentRightReceiverControl A package)
    (nextOwner : EndToEndLeftOriginRecurrentRightOwnerControl A package)
    (hreceiver :
      (switchEndToEndLeftOriginLeftOwnerToRightReceiver A package owner
        receiver move previouslyReceived).2 = some nextReceiver)
    (howner :
      (switchEndToEndLeftOriginLeftReceiverToRightOwner A package receiver
        move.2).2 = some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨source, row, monitor, staged⟩
  cases staged with
  | none =>
      simp [switchEndToEndLeftOriginLeftReceiverToRightOwner] at howner
  | some target =>
      simp only [switchEndToEndLeftOriginLeftOwnerToRightReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchEndToEndLeftOriginLeftReceiverToRightOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueEndToEndLeftOriginRecurrentRightReceiver_source,
        stepEndToEndLeftOriginRecurrentRightOwner_source]
      rfl

end


end DetParityAutomaton

end DistributedSynthesis
