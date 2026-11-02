/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDelayedBitResolver

/-!
# Symmetric finite carrier for one identified delayed receive bit

An endpoint that receives in a locally ambiguous round retains a
`FiniteDelayedFork`.  A strict round gives the non-receiving endpoint one
known open continuation, whereas a simultaneous round gives both endpoints
forks carrying the same finite identifier.

Two forks do **not** by themselves prove a simultaneous predecessor: after an
immediate strict reversal an old fork and a fresh fork can coexist.  Therefore
fork/fork resolution selects the closed controls only when their finite IDs
are equal.  Mismatched forks select their open controls, exactly like the
charged-shadow resolver.

The constructors and IDs are finite local data.  No map here accepts a graph,
orientation, leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v w x y z i

variable {ForkId : Type i} {Control : Type u} {Delivered : Type v}
variable {Input : Type w} {Output : Type x}
variable {OwnInput : Type w} {DeliveredInput : Type y} {Next : Type z}

/-- A known open control, or two continuations tagged by the finite identity
of the locally ambiguous receive that created them. -/
inductive FiniteSymmetricDelayedCarrier (ForkId : Type i) (Control : Type u)
    where
  | known (control : Control)
  | fork (id : ForkId) (state : FiniteDelayedFork Control)

noncomputable instance [Fintype ForkId] [Fintype Control] :
    Fintype (FiniteSymmetricDelayedCarrier ForkId Control) := by
  let encode : FiniteSymmetricDelayedCarrier ForkId Control →
      Control ⊕ (ForkId × FiniteDelayedFork Control)
    | .known control => .inl control
    | .fork id state => .inr (id, state)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left <;> cases right <;> cases heq <;> rfl)

namespace FiniteSymmetricDelayedCarrier

/-- The identifier is present precisely on an unresolved receive state. -/
def forkId? : FiniteSymmetricDelayedCarrier ForkId Control → Option ForkId
  | .known _ => none
  | .fork id _ => some id

/-- Select one branch of this endpoint's old continuation.  Known states have
no unresolved coordinate. -/
def resolveWith
    (state : FiniteSymmetricDelayedCarrier ForkId Control)
    (closed : Bool) : Control :=
  match state with
  | .known control => control
  | .fork _ unresolved => unresolved.candidate closed

@[simp] theorem forkId?_known (control : Control) :
    (known (ForkId := ForkId) control).forkId? = none :=
  rfl

@[simp] theorem forkId?_fork
    (id : ForkId) (state : FiniteDelayedFork Control) :
    (fork id state).forkId? = some id :=
  rfl

@[simp] theorem resolveWith_known
    (control : Control) (closed : Bool) :
    (known (ForkId := ForkId) control).resolveWith closed = control :=
  rfl

@[simp] theorem resolveWith_fork_false
    (id : ForkId) (state : FiniteDelayedFork Control) :
    (fork id state).resolveWith false = state.openControl := by
  simp [resolveWith]

@[simp] theorem resolveWith_fork_true
    (id : ForkId) (state : FiniteDelayedFork Control) :
    (fork id state).resolveWith true = state.closedControl := by
  simp [resolveWith]

/-! ## Graph-blind no-receive update -/

/-- A no-receive advances both unresolved candidates but preserves the ID of
the old ambiguous event. -/
def noRecv
    (transition : Control → Input → Output × Control)
    (state : FiniteSymmetricDelayedCarrier ForkId Control) (input : Input) :
    Output × FiniteSymmetricDelayedCarrier ForkId Control :=
  match state with
  | .known control =>
      let result := transition control input
      (result.1, .known result.2)
  | .fork id unresolved =>
      let result := unresolved.noRecv transition input
      (result.1, .fork id result.2)

@[simp] theorem noRecv_known
    (transition : Control → Input → Output × Control)
    (control : Control) (input : Input) :
    (known (ForkId := ForkId) control).noRecv transition input =
      ((transition control input).1, .known (transition control input).2) := by
  rfl

@[simp] theorem noRecv_fork
    (transition : Control → Input → Output × Control)
    (id : ForkId) (state : FiniteDelayedFork Control) (input : Input) :
    (fork id state).noRecv transition input =
      ((state.noRecv transition input).1,
        .fork id (state.noRecv transition input).2) := by
  rfl

/-! ## Symmetric next-receive resolution -/

/-- The actual old pair named by the two local constructors and fork IDs.
Equal fork IDs select the closed pair; every other reachable shape selects
the open interpretation of each fork. -/
noncomputable def resolvePair
    [DecidableEq ForkId]
    (one : FiniteSymmetricDelayedCarrier ForkId Control)
    (two : FiniteSymmetricDelayedCarrier ForkId Delivered) :
    Control × Delivered :=
  match one, two with
  | .known oneControl, .known twoControl => (oneControl, twoControl)
  | .fork _ oneFork, .known twoControl =>
      (oneFork.openControl, twoControl)
  | .known oneControl, .fork _ twoFork =>
      (oneControl, twoFork.openControl)
  | .fork oneId oneFork, .fork twoId twoFork =>
      if oneId = twoId then
        (oneFork.closedControl, twoFork.closedControl)
      else
        (oneFork.openControl, twoFork.openControl)

@[simp] theorem resolvePair_known_known
    [DecidableEq ForkId] (one : Control) (two : Delivered) :
    resolvePair (known (ForkId := ForkId) one) (.known two) = (one, two) :=
  rfl

@[simp] theorem resolvePair_fork_known
    [DecidableEq ForkId] (id : ForkId)
    (one : FiniteDelayedFork Control) (two : Delivered) :
    resolvePair (fork id one) (.known two) = (one.openControl, two) :=
  rfl

@[simp] theorem resolvePair_known_fork
    [DecidableEq ForkId] (one : Control) (id : ForkId)
    (two : FiniteDelayedFork Delivered) :
    resolvePair (known (ForkId := ForkId) one) (.fork id two) =
      (one, two.openControl) :=
  rfl

@[simp] theorem resolvePair_fork_fork_eq
    [DecidableEq ForkId] (id : ForkId)
    (one : FiniteDelayedFork Control)
    (two : FiniteDelayedFork Delivered) :
    resolvePair (fork id one) (.fork id two) =
      (one.closedControl, two.closedControl) := by
  simp [resolvePair]

theorem resolvePair_fork_fork_ne
    [DecidableEq ForkId] {oneId twoId : ForkId}
    (hne : oneId ≠ twoId) (one : FiniteDelayedFork Control)
    (two : FiniteDelayedFork Delivered) :
    resolvePair (fork oneId one) (.fork twoId two) =
      (one.openControl, two.openControl) := by
  simp [resolvePair, hne]

/-- Resolve the old bit before evaluating the current receive output. -/
noncomputable def recv
    [DecidableEq ForkId]
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Output × Next)
    (one : FiniteSymmetricDelayedCarrier ForkId Control)
    (ownInput : OwnInput)
    (two : FiniteSymmetricDelayedCarrier ForkId Delivered)
    (deliveredInput : DeliveredInput) : Output × Next :=
  let resolved := resolvePair one two
  transition resolved.1 ownInput resolved.2 deliveredInput

@[simp] theorem recv_known_known
    [DecidableEq ForkId]
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Output × Next)
    (one : Control) (ownInput : OwnInput) (two : Delivered)
    (deliveredInput : DeliveredInput) :
    recv transition (known (ForkId := ForkId) one) ownInput (.known two)
        deliveredInput =
      transition one ownInput two deliveredInput :=
  rfl

@[simp] theorem recv_fork_known
    [DecidableEq ForkId]
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Output × Next)
    (id : ForkId) (one : FiniteDelayedFork Control) (ownInput : OwnInput)
    (two : Delivered) (deliveredInput : DeliveredInput) :
    recv transition (fork id one) ownInput (.known two) deliveredInput =
      transition one.openControl ownInput two deliveredInput :=
  rfl

@[simp] theorem recv_known_fork
    [DecidableEq ForkId]
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Output × Next)
    (one : Control) (ownInput : OwnInput) (id : ForkId)
    (two : FiniteDelayedFork Delivered) (deliveredInput : DeliveredInput) :
    recv transition (known (ForkId := ForkId) one) ownInput (.fork id two)
        deliveredInput =
      transition one ownInput two.openControl deliveredInput :=
  rfl

@[simp] theorem recv_fork_fork_eq
    [DecidableEq ForkId]
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Output × Next)
    (id : ForkId) (one : FiniteDelayedFork Control) (ownInput : OwnInput)
    (two : FiniteDelayedFork Delivered)
    (deliveredInput : DeliveredInput) :
    recv transition (fork id one) ownInput (.fork id two) deliveredInput =
      transition one.closedControl ownInput two.closedControl
        deliveredInput := by
  simp [recv]

theorem recv_fork_fork_ne
    [DecidableEq ForkId]
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Output × Next)
    {oneId twoId : ForkId} (hne : oneId ≠ twoId)
    (one : FiniteDelayedFork Control) (ownInput : OwnInput)
    (two : FiniteDelayedFork Delivered)
    (deliveredInput : DeliveredInput) :
    recv transition (fork oneId one) ownInput (.fork twoId two)
        deliveredInput =
      transition one.openControl ownInput two.openControl deliveredInput := by
  simp [recv, resolvePair, hne]

end FiniteSymmetricDelayedCarrier

end DistributedSynthesis
