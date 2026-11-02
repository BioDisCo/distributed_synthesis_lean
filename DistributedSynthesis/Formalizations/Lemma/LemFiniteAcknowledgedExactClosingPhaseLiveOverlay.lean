/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredMemberControl

/-!
# A reusable live-receiver overlay for deferred exact closing

The basic deferred carrier advances a blind sender while deliberately keeping
its activation payload inert.  A concrete table implementation may additionally
need to retain the receiver which is physically live during a homogeneous
one-way block.  `PhaseLiveShared` is the finite wrapper for that purpose.

It stores the underlying shared sender and payload, one endpoint-local phase
bit, and the open/closed interpretations of the retained receiver.  Blind
evolution advances only the underlying sender, retains the payload and both
receiver interpretations, and writes the endpoint's fixed blind phase.  The
underlying member-coherence laws therefore lift without any new assumption.

The phase bit is written by the local receive/no-receive transition which is
already being executed.  No definition below receives a graph, orientation,
hierarchy side, leader bit, strict-leader bit, history, or semantic view.
-/

namespace DistributedSynthesis

universe u v w x y

namespace FiniteAcknowledgedDelayedCarrier

/-- Finite state retained around one deferred sender/receiver table.

`receiverFork` contains the receiver to use under the unresolved outer table
member: the open interpretation is selected by `false`, and the simultaneous
close interpretation by `true`. -/
structure PhaseLiveShared
    (BaseShared : Type u) (BasePayload : Type v) (Receiver : Type w) where
  baseShared : BaseShared
  basePayload : BasePayload
  localPhase : Bool
  receiverFork : FiniteDelayedFork Receiver

variable {BaseShared : Type u} {BasePayload : Type v}
variable {Receiver : Type w} {Input : Type x} {Output : Type y}

noncomputable instance [Fintype BaseShared] [Fintype BasePayload]
    [Fintype Receiver] :
    Fintype (PhaseLiveShared BaseShared BasePayload Receiver) := by
  let encode : PhaseLiveShared BaseShared BasePayload Receiver →
      BaseShared × BasePayload × Bool × FiniteDelayedFork Receiver :=
    fun state ↦
      (state.baseShared, state.basePayload, state.localPhase,
        state.receiverFork)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

/-- The canonical outer deferred control for a live overlay.  All semantic
activation data has moved into the common shared wrapper, so the generic outer
payload is a singleton. -/
abbrev PhaseLivePending :=
  DeferredMemberControl
    (PhaseLiveShared BaseShared BasePayload Receiver) PUnit

namespace PhaseLiveShared

/-- Reconstruct the underlying deferred control selected by the outer member. -/
def basePending
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (member : Bool) : DeferredMemberControl BaseShared BasePayload :=
  (member, shared.baseShared, shared.basePayload)

/-- Select the physically meaningful retained receiver for the outer member. -/
def receiver
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (member : Bool) : Receiver :=
  shared.receiverFork.candidate member

/-- Select the retained receiver on a repeated local receive and a freshly
installed receiver after a local phase change.  `samePhase` is an endpoint
constant; the test uses only the endpoint's stored phase. -/
def receiverForReceive
    (samePhase : Bool)
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (member : Bool) (switched : Receiver) : Receiver :=
  if shared.localPhase = samePhase then shared.receiver member else switched

@[simp] theorem basePending_member
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (member : Bool) :
    (shared.basePending member).1 = member :=
  rfl

@[simp] theorem basePending_shared
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (member : Bool) :
    (shared.basePending member).2.1 = shared.baseShared :=
  rfl

@[simp] theorem basePending_payload
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (member : Bool) :
    (shared.basePending member).2.2 = shared.basePayload :=
  rfl

@[simp] theorem receiver_false
    (shared : PhaseLiveShared BaseShared BasePayload Receiver) :
    shared.receiver false = shared.receiverFork.openControl :=
  rfl

@[simp] theorem receiver_true
    (shared : PhaseLiveShared BaseShared BasePayload Receiver) :
    shared.receiver true = shared.receiverFork.closedControl :=
  rfl

@[simp] theorem receiverForReceive_same
    (samePhase : Bool)
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (member : Bool) (switched : Receiver)
    (hphase : shared.localPhase = samePhase) :
    shared.receiverForReceive samePhase member switched =
      shared.receiver member := by
  simp [receiverForReceive, hphase]

@[simp] theorem receiverForReceive_switch
    (samePhase : Bool)
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (member : Bool) (switched : Receiver)
    (hphase : shared.localPhase ≠ samePhase) :
    shared.receiverForReceive samePhase member switched = switched := by
  simp [receiverForReceive, hphase]

/-- Construct one shared value from the two receiver interpretations prepared
by a local receive. -/
def fresh
    (baseShared : BaseShared) (basePayload : BasePayload) (localPhase : Bool)
    (openReceiver closedReceiver : Receiver) :
    PhaseLiveShared BaseShared BasePayload Receiver :=
  { baseShared
    basePayload
    localPhase
    receiverFork := ⟨openReceiver, closedReceiver⟩ }

@[simp] theorem fresh_receiver_false
    (baseShared : BaseShared) (basePayload : BasePayload) (phase : Bool)
    (openReceiver closedReceiver : Receiver) :
    (fresh baseShared basePayload phase openReceiver closedReceiver).receiver
        false = openReceiver :=
  rfl

@[simp] theorem fresh_receiver_true
    (baseShared : BaseShared) (basePayload : BasePayload) (phase : Bool)
    (openReceiver closedReceiver : Receiver) :
    (fresh baseShared basePayload phase openReceiver closedReceiver).receiver
        true = closedReceiver :=
  rfl

end PhaseLiveShared

/-! ## Canonical outer member -/

/-- Put one shared overlay under an explicitly selected unresolved member. -/
def phaseLivePending
    (member : Bool)
    (shared : PhaseLiveShared BaseShared BasePayload Receiver) :
    PhaseLivePending (BaseShared := BaseShared) (BasePayload := BasePayload)
      (Receiver := Receiver) :=
  (member, shared, PUnit.unit)

/-- The ordinary/simultaneous interpretations of one common live overlay. -/
def phaseLiveFork
    (shared : PhaseLiveShared BaseShared BasePayload Receiver) :
    FiniteDelayedFork
      (PhaseLivePending (BaseShared := BaseShared)
        (BasePayload := BasePayload) (Receiver := Receiver)) :=
  deferredMemberFork shared PUnit.unit

@[simp] theorem phaseLiveFork_candidate
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (member : Bool) :
    (phaseLiveFork shared).candidate member = phaseLivePending member shared := by
  cases member <;> rfl

@[simp] theorem phaseLiveFork_candidate_basePending
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (member : Bool) :
    ((phaseLiveFork shared).candidate member).2.1.basePending member =
      (member, shared.baseShared, shared.basePayload) := by
  cases member <;> rfl

@[simp] theorem phaseLiveFork_candidate_receiver
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (member : Bool) :
    ((phaseLiveFork shared).candidate member).2.1.receiver member =
      shared.receiverFork.candidate member := by
  cases member <;> rfl

/-! ## Blind evolution -/

/-- Lift a deferred sender step through the live-receiver wrapper.

The receiver fork is deliberately inert on a blind round: it belongs to the
other local role.  The endpoint records `blindPhase`, making a later receive
able to distinguish a repeated receive from a local role switch without
learning any global orientation. -/
def phaseLivePendingStep
    (blindPhase : Bool)
    (baseStep : Bool → BaseShared → Input → BaseShared × Output)
    (member : Bool)
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (input : Input) :
    PhaseLiveShared BaseShared BasePayload Receiver × Output :=
  let next := baseStep member shared.baseShared input
  ({ baseShared := next.1
     basePayload := shared.basePayload
     localPhase := blindPhase
     receiverFork := shared.receiverFork },
    next.2)

@[simp] theorem phaseLivePendingStep_baseShared
    (blindPhase : Bool)
    (baseStep : Bool → BaseShared → Input → BaseShared × Output)
    (member : Bool)
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (input : Input) :
    (phaseLivePendingStep blindPhase baseStep member shared input).1.baseShared =
      (baseStep member shared.baseShared input).1 :=
  rfl

@[simp] theorem phaseLivePendingStep_basePayload
    (blindPhase : Bool)
    (baseStep : Bool → BaseShared → Input → BaseShared × Output)
    (member : Bool)
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (input : Input) :
    (phaseLivePendingStep blindPhase baseStep member shared input).1.basePayload =
      shared.basePayload :=
  rfl

@[simp] theorem phaseLivePendingStep_localPhase
    (blindPhase : Bool)
    (baseStep : Bool → BaseShared → Input → BaseShared × Output)
    (member : Bool)
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (input : Input) :
    (phaseLivePendingStep blindPhase baseStep member shared input).1.localPhase =
      blindPhase :=
  rfl

@[simp] theorem phaseLivePendingStep_receiverFork
    (blindPhase : Bool)
    (baseStep : Bool → BaseShared → Input → BaseShared × Output)
    (member : Bool)
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (input : Input) :
    (phaseLivePendingStep blindPhase baseStep member shared input).1.receiverFork =
      shared.receiverFork :=
  rfl

@[simp] theorem phaseLivePendingStep_output
    (blindPhase : Bool)
    (baseStep : Bool → BaseShared → Input → BaseShared × Output)
    (member : Bool)
    (shared : PhaseLiveShared BaseShared BasePayload Receiver)
    (input : Input) :
    (phaseLivePendingStep blindPhase baseStep member shared input).2 =
      (baseStep member shared.baseShared input).2 :=
  rfl

/-- Member-coherent sender evolution remains member-coherent after adding the
finite local phase and receiver cache. -/
theorem phaseLivePendingStep_laws
    (blindPhase : Bool)
    (baseStep : Bool → BaseShared → Input → BaseShared × Output)
    (laws : DeferredMemberStepLaws baseStep) :
    DeferredMemberStepLaws (phaseLivePendingStep
      (BasePayload := BasePayload) (Receiver := Receiver) blindPhase
        baseStep) := by
  refine { outputEq := ?_, stateEq := ?_ }
  · intro shared input
    exact laws.outputEq shared.baseShared input
  · intro shared input
    have hstate := laws.stateEq shared.baseShared input
    simpa only [phaseLivePendingStep] using congrArg
      (fun nextShared ↦
        ({ baseShared := nextShared
           basePayload := shared.basePayload
           localPhase := blindPhase
           receiverFork := shared.receiverFork } :
          PhaseLiveShared BaseShared BasePayload Receiver)) hstate

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
