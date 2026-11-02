/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndGlobalRecurrentBank

/-!
# Local transitions for the package-wide recurrent bank

Each branch delegates its round computation to the local handoff for the one
ordinary policy below its guarded child.  A staged successor is then wrapped
with the unchanged boundary key and unchanged child.  Thus the executable
transition cannot select a new policy at a reversal.
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

/-! ## Initial controls -/

noncomputable def initialEndToEndRightOriginRecurrentRightOwner
    (source : EndToEndRightOriginRecurrentRightMacro A package) :
    EndToEndRightOriginRecurrentRightOwnerControl A package :=
  ⟨source, (endToEndGuardedRightRecurrentRightController A source.2).initial⟩

noncomputable def initialEndToEndRightOriginRecurrentLeftOwner
    (source : EndToEndRightOriginRecurrentLeftMacro A package) :
    EndToEndRightOriginRecurrentLeftOwnerControl A package :=
  ⟨source, (endToEndGuardedRightRecurrentLeftController A source.2).initial⟩

noncomputable def initialEndToEndLeftOriginRecurrentRightOwner
    (source : EndToEndLeftOriginRecurrentRightMacro A package) :
    EndToEndLeftOriginRecurrentRightOwnerControl A package :=
  ⟨source, (endToEndGuardedLeftRecurrentRightController A source.2).initial⟩

noncomputable def initialEndToEndLeftOriginRecurrentLeftOwner
    (source : EndToEndLeftOriginRecurrentLeftMacro A package) :
    EndToEndLeftOriginRecurrentLeftOwnerControl A package :=
  ⟨source, (endToEndGuardedLeftRecurrentLeftController A source.2).initial⟩

noncomputable def initialEndToEndRightOriginRecurrentRightReceiver
    (source : EndToEndRightOriginRecurrentRightMacro A package)
    (row : PairedEntryRow) :
    EndToEndRightOriginRecurrentRightReceiverControl A package :=
  ⟨source, row,
    (endToEndGuardedRightRecurrentRightMonitor A source.2).initial, none⟩

noncomputable def initialEndToEndRightOriginRecurrentLeftReceiver
    (source : EndToEndRightOriginRecurrentLeftMacro A package)
    (row : PairedEntryRow) :
    EndToEndRightOriginRecurrentLeftReceiverControl A package :=
  ⟨source, row,
    (endToEndGuardedRightRecurrentLeftMonitor A source.2).initial, none⟩

noncomputable def initialEndToEndLeftOriginRecurrentRightReceiver
    (source : EndToEndLeftOriginRecurrentRightMacro A package)
    (row : PairedEntryRow) :
    EndToEndLeftOriginRecurrentRightReceiverControl A package :=
  ⟨source, row,
    (endToEndGuardedLeftRecurrentRightMonitor A source.2).initial, none⟩

noncomputable def initialEndToEndLeftOriginRecurrentLeftReceiver
    (source : EndToEndLeftOriginRecurrentLeftMacro A package)
    (row : PairedEntryRow) :
    EndToEndLeftOriginRecurrentLeftReceiverControl A package :=
  ⟨source, row,
    (endToEndGuardedLeftRecurrentLeftMonitor A source.2).initial, none⟩

/-! ## Owner steps -/

noncomputable def stepEndToEndRightOriginRecurrentRightOwner
    (owner : EndToEndRightOriginRecurrentRightOwnerControl A package)
    (input : In₁) :
    Out₁ × EndToEndRightOriginRecurrentRightOwnerControl A package :=
  let controller := endToEndGuardedRightRecurrentRightController A owner.1.2
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

noncomputable def stepEndToEndRightOriginRecurrentLeftOwner
    (owner : EndToEndRightOriginRecurrentLeftOwnerControl A package)
    (input : In₂) :
    Out₂ × EndToEndRightOriginRecurrentLeftOwnerControl A package :=
  let controller := endToEndGuardedRightRecurrentLeftController A owner.1.2
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

noncomputable def stepEndToEndLeftOriginRecurrentRightOwner
    (owner : EndToEndLeftOriginRecurrentRightOwnerControl A package)
    (input : In₁) :
    Out₁ × EndToEndLeftOriginRecurrentRightOwnerControl A package :=
  let controller := endToEndGuardedLeftRecurrentRightController A owner.1.2
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

noncomputable def stepEndToEndLeftOriginRecurrentLeftOwner
    (owner : EndToEndLeftOriginRecurrentLeftOwnerControl A package)
    (input : In₂) :
    Out₂ × EndToEndLeftOriginRecurrentLeftOwnerControl A package :=
  let controller := endToEndGuardedLeftRecurrentLeftController A owner.1.2
  let label := controller.labelOf owner.2
  (label.1 input, ⟨owner.1, controller.step owner.2 input⟩)

@[simp] theorem stepEndToEndRightOriginRecurrentRightOwner_source
    (owner : EndToEndRightOriginRecurrentRightOwnerControl A package)
    (input : In₁) :
    (stepEndToEndRightOriginRecurrentRightOwner A package owner input).2.1 =
      owner.1 := rfl

@[simp] theorem stepEndToEndRightOriginRecurrentLeftOwner_source
    (owner : EndToEndRightOriginRecurrentLeftOwnerControl A package)
    (input : In₂) :
    (stepEndToEndRightOriginRecurrentLeftOwner A package owner input).2.1 =
      owner.1 := rfl

@[simp] theorem stepEndToEndLeftOriginRecurrentRightOwner_source
    (owner : EndToEndLeftOriginRecurrentRightOwnerControl A package)
    (input : In₁) :
    (stepEndToEndLeftOriginRecurrentRightOwner A package owner input).2.1 =
      owner.1 := rfl

@[simp] theorem stepEndToEndLeftOriginRecurrentLeftOwner_source
    (owner : EndToEndLeftOriginRecurrentLeftOwnerControl A package)
    (input : In₂) :
    (stepEndToEndLeftOriginRecurrentLeftOwner A package owner input).2.1 =
      owner.1 := rfl

/-! ## Receiver round computations -/

abbrev EndToEndRightOriginRecurrentRightRoundResult
    (source : EndToEndRightOriginRecurrentRightMacro A package) :=
  ProfiledRightReceiverOutput A ×
    (endToEndGuardedRightRecurrentRightMonitor A source.2).State ×
      Option (EndToEndRightOriginRecurrentLeftMacro A package)

abbrev EndToEndRightOriginRecurrentLeftRoundResult
    (source : EndToEndRightOriginRecurrentLeftMacro A package) :=
  ProfiledLeftReceiverOutput A ×
    (endToEndGuardedRightRecurrentLeftMonitor A source.2).State ×
      Option (EndToEndRightOriginRecurrentRightMacro A package)

abbrev EndToEndLeftOriginRecurrentRightRoundResult
    (source : EndToEndLeftOriginRecurrentRightMacro A package) :=
  ProfiledRightReceiverOutput A ×
    (endToEndGuardedLeftRecurrentRightMonitor A source.2).State ×
      Option (EndToEndLeftOriginRecurrentLeftMacro A package)

abbrev EndToEndLeftOriginRecurrentLeftRoundResult
    (source : EndToEndLeftOriginRecurrentLeftMacro A package) :=
  ProfiledLeftReceiverOutput A ×
    (endToEndGuardedLeftRecurrentLeftMonitor A source.2).State ×
      Option (EndToEndLeftOriginRecurrentRightMacro A package)

noncomputable def stepEndToEndRightOriginRecurrentRightReceiverFor
    (source : EndToEndRightOriginRecurrentRightMacro A package)
    (ownerControl :
      (endToEndGuardedRightRecurrentRightController A source.2).Control)
    (row : PairedEntryRow)
    (monitorState :
      (endToEndGuardedRightRecurrentRightMonitor A source.2).State)
    (move : In₂ × In₁) :
    EndToEndRightOriginRecurrentRightRoundResult A package source :=
  let result := stepProfiledPolicyRightReceiverFor A (source.2.1.policy A)
    source.2.2 ownerControl row monitorState move
  (result.1, result.2.1,
    result.2.2.map fun target => ⟨source.1, source.2.1, target⟩)

noncomputable def stepEndToEndRightOriginRecurrentLeftReceiverFor
    (source : EndToEndRightOriginRecurrentLeftMacro A package)
    (ownerControl :
      (endToEndGuardedRightRecurrentLeftController A source.2).Control)
    (row : PairedEntryRow)
    (monitorState :
      (endToEndGuardedRightRecurrentLeftMonitor A source.2).State)
    (move : In₁ × In₂) :
    EndToEndRightOriginRecurrentLeftRoundResult A package source :=
  let result := stepProfiledPolicyLeftReceiverFor A (source.2.1.policy A)
    source.2.2 ownerControl row monitorState move
  (result.1, result.2.1,
    result.2.2.map fun target => ⟨source.1, source.2.1, target⟩)

noncomputable def stepEndToEndLeftOriginRecurrentRightReceiverFor
    (source : EndToEndLeftOriginRecurrentRightMacro A package)
    (ownerControl :
      (endToEndGuardedLeftRecurrentRightController A source.2).Control)
    (row : PairedEntryRow)
    (monitorState :
      (endToEndGuardedLeftRecurrentRightMonitor A source.2).State)
    (move : In₂ × In₁) :
    EndToEndLeftOriginRecurrentRightRoundResult A package source :=
  let result := stepProfiledPolicyRightReceiverFor A (source.2.1.policy A)
    source.2.2 ownerControl row monitorState move
  (result.1, result.2.1,
    result.2.2.map fun target => ⟨source.1, source.2.1, target⟩)

noncomputable def stepEndToEndLeftOriginRecurrentLeftReceiverFor
    (source : EndToEndLeftOriginRecurrentLeftMacro A package)
    (ownerControl :
      (endToEndGuardedLeftRecurrentLeftController A source.2).Control)
    (row : PairedEntryRow)
    (monitorState :
      (endToEndGuardedLeftRecurrentLeftMonitor A source.2).State)
    (move : In₁ × In₂) :
    EndToEndLeftOriginRecurrentLeftRoundResult A package source :=
  let result := stepProfiledPolicyLeftReceiverFor A (source.2.1.policy A)
    source.2.2 ownerControl row monitorState move
  (result.1, result.2.1,
    result.2.2.map fun target => ⟨source.1, source.2.1, target⟩)

/-! ## Matched lookup and continuing receiver steps -/

noncomputable def endToEndRightOriginRecurrentRightOwnerControlFor
    (receiver : EndToEndRightOriginRecurrentRightReceiverControl A package)
    (owner : EndToEndRightOriginRecurrentRightOwnerControl A package) :
    (endToEndGuardedRightRecurrentRightController A receiver.1.2).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (endToEndGuardedRightRecurrentRightController A receiver.1.2).initial

noncomputable def endToEndRightOriginRecurrentLeftOwnerControlFor
    (receiver : EndToEndRightOriginRecurrentLeftReceiverControl A package)
    (owner : EndToEndRightOriginRecurrentLeftOwnerControl A package) :
    (endToEndGuardedRightRecurrentLeftController A receiver.1.2).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (endToEndGuardedRightRecurrentLeftController A receiver.1.2).initial

noncomputable def endToEndLeftOriginRecurrentRightOwnerControlFor
    (receiver : EndToEndLeftOriginRecurrentRightReceiverControl A package)
    (owner : EndToEndLeftOriginRecurrentRightOwnerControl A package) :
    (endToEndGuardedLeftRecurrentRightController A receiver.1.2).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (endToEndGuardedLeftRecurrentRightController A receiver.1.2).initial

noncomputable def endToEndLeftOriginRecurrentLeftOwnerControlFor
    (receiver : EndToEndLeftOriginRecurrentLeftReceiverControl A package)
    (owner : EndToEndLeftOriginRecurrentLeftOwnerControl A package) :
    (endToEndGuardedLeftRecurrentLeftController A receiver.1.2).Control := by
  classical
  exact if h : owner.1 = receiver.1 then h ▸ owner.2
    else (endToEndGuardedLeftRecurrentLeftController A receiver.1.2).initial

noncomputable def continueEndToEndRightOriginRecurrentRightReceiver
    (receiver : EndToEndRightOriginRecurrentRightReceiverControl A package)
    (owner : EndToEndRightOriginRecurrentRightOwnerControl A package)
    (move : In₂ × In₁) :
    Out₂ × EndToEndRightOriginRecurrentRightReceiverControl A package :=
  let result := stepEndToEndRightOriginRecurrentRightReceiverFor A package
    receiver.1
    (endToEndRightOriginRecurrentRightOwnerControlFor A package receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedRightInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

noncomputable def continueEndToEndRightOriginRecurrentLeftReceiver
    (receiver : EndToEndRightOriginRecurrentLeftReceiverControl A package)
    (owner : EndToEndRightOriginRecurrentLeftOwnerControl A package)
    (move : In₁ × In₂) :
    Out₁ × EndToEndRightOriginRecurrentLeftReceiverControl A package :=
  let result := stepEndToEndRightOriginRecurrentLeftReceiverFor A package
    receiver.1
    (endToEndRightOriginRecurrentLeftOwnerControlFor A package receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedLeftInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

noncomputable def continueEndToEndLeftOriginRecurrentRightReceiver
    (receiver : EndToEndLeftOriginRecurrentRightReceiverControl A package)
    (owner : EndToEndLeftOriginRecurrentRightOwnerControl A package)
    (move : In₂ × In₁) :
    Out₂ × EndToEndLeftOriginRecurrentRightReceiverControl A package :=
  let result := stepEndToEndLeftOriginRecurrentRightReceiverFor A package
    receiver.1
    (endToEndLeftOriginRecurrentRightOwnerControlFor A package receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedRightInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

noncomputable def continueEndToEndLeftOriginRecurrentLeftReceiver
    (receiver : EndToEndLeftOriginRecurrentLeftReceiverControl A package)
    (owner : EndToEndLeftOriginRecurrentLeftOwnerControl A package)
    (move : In₁ × In₂) :
    Out₁ × EndToEndLeftOriginRecurrentLeftReceiverControl A package :=
  let result := stepEndToEndLeftOriginRecurrentLeftReceiverFor A package
    receiver.1
    (endToEndLeftOriginRecurrentLeftOwnerControlFor A package receiver owner)
    receiver.2.1 receiver.2.2.1 move
  (pairedLeftInformedForRow receiver.2.1 result.1.physical,
    ⟨receiver.1, receiver.2.1, result.2.1, result.2.2⟩)

@[simp] theorem continueEndToEndRightOriginRecurrentRightReceiver_source
    (receiver : EndToEndRightOriginRecurrentRightReceiverControl A package)
    (owner : EndToEndRightOriginRecurrentRightOwnerControl A package)
    (move : In₂ × In₁) :
    (continueEndToEndRightOriginRecurrentRightReceiver A package receiver owner
      move).2.1 = receiver.1 := rfl

@[simp] theorem continueEndToEndRightOriginRecurrentLeftReceiver_source
    (receiver : EndToEndRightOriginRecurrentLeftReceiverControl A package)
    (owner : EndToEndRightOriginRecurrentLeftOwnerControl A package)
    (move : In₁ × In₂) :
    (continueEndToEndRightOriginRecurrentLeftReceiver A package receiver owner
      move).2.1 = receiver.1 := rfl

@[simp] theorem continueEndToEndLeftOriginRecurrentRightReceiver_source
    (receiver : EndToEndLeftOriginRecurrentRightReceiverControl A package)
    (owner : EndToEndLeftOriginRecurrentRightOwnerControl A package)
    (move : In₂ × In₁) :
    (continueEndToEndLeftOriginRecurrentRightReceiver A package receiver owner
      move).2.1 = receiver.1 := rfl

@[simp] theorem continueEndToEndLeftOriginRecurrentLeftReceiver_source
    (receiver : EndToEndLeftOriginRecurrentLeftReceiverControl A package)
    (owner : EndToEndLeftOriginRecurrentLeftOwnerControl A package)
    (move : In₁ × In₂) :
    (continueEndToEndLeftOriginRecurrentLeftReceiver A package receiver owner
      move).2.1 = receiver.1 := rfl

end


end DetParityAutomaton

end DistributedSynthesis
