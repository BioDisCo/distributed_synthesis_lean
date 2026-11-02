/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndGlobalRecurrentLocalHandoff

/-!
# The first strict reversal into the package-wide recurrent bank

At the reversal, the old receiver retains the staged certified macro while
the new receiver obtains that same finite value through the delivered partner
control.  Both recurrent controls are initialized from it and stepped on the
reversal round.  The common-source theorems verify that the two local updates
install literally the same package-wide macro.
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

/-! ## First right block to recurrent left -/

noncomputable def switchEndToEndFirstRightOwnerToRecurrentLeftReceiver
    (owner : EndToEndGuardedFirstRightOwnerControl A package)
    (partner : EndToEndGuardedFirstRightReceiverControl A package)
    (move : In₁ × In₂) (previouslyReceived : Bool) :
    Out₁ × Option
      (EndToEndRightOriginRecurrentLeftReceiverControl A package) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepEndToEndGuardedFirstRightReceiverFor A package
        partner.1
        (endToEndGuardedFirstRightOwnerControlFor A package partner owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedRightClosingForRow partner.2.1 oldResult.1.physical, none)
  | some target =>
      let source : EndToEndRightOriginRecurrentLeftMacro A package :=
        ⟨partner.1, target⟩
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueEndToEndRightOriginRecurrentLeftReceiver A package
        (initialEndToEndRightOriginRecurrentLeftReceiver A package source row)
        (initialEndToEndRightOriginRecurrentLeftOwner A package source) move
      (result.1, some result.2)

noncomputable def switchEndToEndFirstRightReceiverToRecurrentLeftOwner
    (receiver : EndToEndGuardedFirstRightReceiverControl A package)
    (inputTwo : In₂) :
    Out₂ × Option (EndToEndRightOriginRecurrentLeftOwnerControl A package) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let source : EndToEndRightOriginRecurrentLeftMacro A package :=
        ⟨receiver.1, target⟩
      let result := stepEndToEndRightOriginRecurrentLeftOwner A package
        (initialEndToEndRightOriginRecurrentLeftOwner A package source) inputTwo
      (result.1, some result.2)

theorem switchEndToEndFirstRight_common_source
    (owner : EndToEndGuardedFirstRightOwnerControl A package)
    (receiver : EndToEndGuardedFirstRightReceiverControl A package)
    (move : In₁ × In₂) (previouslyReceived : Bool)
    (nextReceiver : EndToEndRightOriginRecurrentLeftReceiverControl A package)
    (nextOwner : EndToEndRightOriginRecurrentLeftOwnerControl A package)
    (hreceiver :
      (switchEndToEndFirstRightOwnerToRecurrentLeftReceiver A package owner
        receiver move previouslyReceived).2 = some nextReceiver)
    (howner :
      (switchEndToEndFirstRightReceiverToRecurrentLeftOwner A package receiver
        move.2).2 = some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨key, row, monitor, staged⟩
  cases staged with
  | none =>
      simp [switchEndToEndFirstRightReceiverToRecurrentLeftOwner] at howner
  | some target =>
      simp only [switchEndToEndFirstRightOwnerToRecurrentLeftReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchEndToEndFirstRightReceiverToRecurrentLeftOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueEndToEndRightOriginRecurrentLeftReceiver_source,
        stepEndToEndRightOriginRecurrentLeftOwner_source]
      rfl

/-! ## First left block to recurrent right -/

noncomputable def switchEndToEndFirstLeftOwnerToRecurrentRightReceiver
    (owner : EndToEndGuardedFirstLeftOwnerControl A package)
    (partner : EndToEndGuardedFirstLeftReceiverControl A package)
    (move : In₂ × In₁) (previouslyReceived : Bool) :
    Out₂ × Option
      (EndToEndLeftOriginRecurrentRightReceiverControl A package) :=
  match partner.2.2.2 with
  | none =>
      let oldResult := stepEndToEndGuardedFirstLeftReceiverFor A package
        partner.1
        (endToEndGuardedFirstLeftOwnerControlFor A package partner owner)
        partner.2.1 partner.2.2.1 (move.2, move.1)
      (pairedLeftClosingForRow partner.2.1 oldResult.1.physical, none)
  | some target =>
      let source : EndToEndLeftOriginRecurrentRightMacro A package :=
        ⟨partner.1, target⟩
      let row := guardedEntryRowOfReceived previouslyReceived
      let result := continueEndToEndLeftOriginRecurrentRightReceiver A package
        (initialEndToEndLeftOriginRecurrentRightReceiver A package source row)
        (initialEndToEndLeftOriginRecurrentRightOwner A package source) move
      (result.1, some result.2)

noncomputable def switchEndToEndFirstLeftReceiverToRecurrentRightOwner
    (receiver : EndToEndGuardedFirstLeftReceiverControl A package)
    (inputOne : In₁) :
    Out₁ × Option (EndToEndLeftOriginRecurrentRightOwnerControl A package) :=
  match receiver.2.2.2 with
  | none => (default, none)
  | some target =>
      let source : EndToEndLeftOriginRecurrentRightMacro A package :=
        ⟨receiver.1, target⟩
      let result := stepEndToEndLeftOriginRecurrentRightOwner A package
        (initialEndToEndLeftOriginRecurrentRightOwner A package source) inputOne
      (result.1, some result.2)

theorem switchEndToEndFirstLeft_common_source
    (owner : EndToEndGuardedFirstLeftOwnerControl A package)
    (receiver : EndToEndGuardedFirstLeftReceiverControl A package)
    (move : In₂ × In₁) (previouslyReceived : Bool)
    (nextReceiver : EndToEndLeftOriginRecurrentRightReceiverControl A package)
    (nextOwner : EndToEndLeftOriginRecurrentRightOwnerControl A package)
    (hreceiver :
      (switchEndToEndFirstLeftOwnerToRecurrentRightReceiver A package owner
        receiver move previouslyReceived).2 = some nextReceiver)
    (howner :
      (switchEndToEndFirstLeftReceiverToRecurrentRightOwner A package receiver
        move.2).2 = some nextOwner) :
    nextReceiver.1 = nextOwner.1 := by
  rcases receiver with ⟨key, row, monitor, staged⟩
  cases staged with
  | none =>
      simp [switchEndToEndFirstLeftReceiverToRecurrentRightOwner] at howner
  | some target =>
      simp only [switchEndToEndFirstLeftOwnerToRecurrentRightReceiver,
        Option.some.injEq] at hreceiver
      simp only [switchEndToEndFirstLeftReceiverToRecurrentRightOwner,
        Option.some.injEq] at howner
      subst nextReceiver
      subst nextOwner
      rw [continueEndToEndLeftOriginRecurrentRightReceiver_source,
        stepEndToEndLeftOriginRecurrentRightOwner_source]
      rfl

end


end DetParityAutomaton

end DistributedSynthesis
