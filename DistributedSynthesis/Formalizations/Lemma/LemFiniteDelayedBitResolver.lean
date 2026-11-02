/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPendingBitResolution

/-!
# A finite one-transition delayed-bit resolver

At a locally ambiguous receive, one endpoint keeps the two possible finite
continuations.  The other endpoint distinguishes the two cases by its own
local event and carries that Boolean together with its actual finite control.
While the first endpoint does not receive, it advances both candidates and
emits their common output.  At its next receive, the delivered tagged control
selects the correct candidate *before* the receive output is computed.

All maps in this file are genuinely local.  They take finite controls and the
inputs available at the corresponding local event; no map takes a graph,
orientation, leader, strict-leader, hidden member, or semantic history.
-/

namespace DistributedSynthesis

universe u v w x y z

/-- The two finite meanings of one unresolved old bit. -/
structure FiniteDelayedFork (Control : Type u) where
  openControl : Control
  closedControl : Control

/-- The endpoint that already knows the old bit carries it with its actual
finite control.  The Boolean is produced by distinct local receive/no-receive
handlers; it is not an observed graph or leader flag. -/
structure FiniteDelayedTagged (Control : Type u) where
  bit : Bool
  control : Control

variable {Control : Type u}
variable {Input OwnInput : Type v}
variable {Delivered : Type w}
variable {Output : Type x} {Next : Type y}
variable {DeliveredInput : Type z}

noncomputable instance [Fintype Control] :
    Fintype (FiniteDelayedFork Control) := by
  let encode : FiniteDelayedFork Control → Control × Control :=
    fun state ↦ (state.openControl, state.closedControl)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

noncomputable instance [Fintype Control] :
    Fintype (FiniteDelayedTagged Control) := by
  let encode : FiniteDelayedTagged Control → Bool × Control :=
    fun state ↦ (state.bit, state.control)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

namespace FiniteDelayedTagged

/-- The known one-way interpretation. -/
def openBranch (control : Control) : FiniteDelayedTagged Control :=
  ⟨false, control⟩

/-- The known simultaneous-close interpretation. -/
def closedBranch (control : Control) : FiniteDelayedTagged Control :=
  ⟨true, control⟩

@[simp] theorem openBranch_bit (control : Control) :
    (openBranch control).bit = false :=
  rfl

@[simp] theorem openBranch_control (control : Control) :
    (openBranch control).control = control :=
  rfl

@[simp] theorem closedBranch_bit (control : Control) :
    (closedBranch control).bit = true :=
  rfl

@[simp] theorem closedBranch_control (control : Control) :
    (closedBranch control).control = control :=
  rfl

/-- A local transition of the informed endpoint retains the already resolved
old bit. -/
def step
    (transition : Control → Input → Output × Next)
    (state : FiniteDelayedTagged Control) (input : Input) :
    Output × FiniteDelayedTagged Next :=
  let result := transition state.control input
  (result.1, ⟨state.bit, result.2⟩)

@[simp] theorem step_bit
    (transition : Control → Input → Output × Next)
    (state : FiniteDelayedTagged Control) (input : Input) :
    (state.step transition input).2.bit = state.bit :=
  rfl

@[simp] theorem step_control
    (transition : Control → Input → Output × Next)
    (state : FiniteDelayedTagged Control) (input : Input) :
    (state.step transition input).2.control =
      (transition state.control input).2 :=
  rfl

/-- State-first variant matching `FinitePairedMealyController`. -/
def stepMealy
    (transition : Control → Input → Next × Output)
    (state : FiniteDelayedTagged Control) (input : Input) :
    FiniteDelayedTagged Next × Output :=
  let result := transition state.control input
  (⟨state.bit, result.1⟩, result.2)

@[simp] theorem stepMealy_bit
    (transition : Control → Input → Next × Output)
    (state : FiniteDelayedTagged Control) (input : Input) :
    (state.stepMealy transition input).1.bit = state.bit :=
  rfl

@[simp] theorem stepMealy_control
    (transition : Control → Input → Next × Output)
    (state : FiniteDelayedTagged Control) (input : Input) :
    (state.stepMealy transition input).1.control =
      (transition state.control input).1 :=
  rfl

end FiniteDelayedTagged

namespace FiniteDelayedFork

/-- Read one of the two correlated finite continuations. -/
def candidate (state : FiniteDelayedFork Control) (bit : Bool) : Control :=
  if bit then state.closedControl else state.openControl

@[simp] theorem candidate_false (state : FiniteDelayedFork Control) :
    state.candidate false = state.openControl := by
  simp [candidate]

@[simp] theorem candidate_true (state : FiniteDelayedFork Control) :
    state.candidate true = state.closedControl := by
  simp [candidate]

/-- Evaluate the graph-blind non-receive transition under either old-bit
interpretation. -/
def noRecvTable
    (transition : Control → Input → Output × Control)
    (state : FiniteDelayedFork Control) (input : Input) (bit : Bool) :
    Output × Control :=
  transition (state.candidate bit) input

/-- The exact invariant needed while the bit is hidden: both represented
local histories emit the same non-receive output. -/
def NoRecvOutputCoherent
    (transition : Control → Input → Output × Control)
    (state : FiniteDelayedFork Control) (input : Input) : Prop :=
  (state.noRecvTable transition input false).1 =
    (state.noRecvTable transition input true).1

/-- Advance both finite candidates on a no-receive and emit the open
candidate's output.  Reachable coherence proves that this is also the closed
candidate's output. -/
def noRecv
    (transition : Control → Input → Output × Control)
    (state : FiniteDelayedFork Control) (input : Input) :
    Output × FiniteDelayedFork Control :=
  let openResult := state.noRecvTable transition input false
  let closedResult := state.noRecvTable transition input true
  (openResult.1, ⟨openResult.2, closedResult.2⟩)

@[simp] theorem noRecv_candidate
    (transition : Control → Input → Output × Control)
    (state : FiniteDelayedFork Control) (input : Input) (bit : Bool) :
    (state.noRecv transition input).2.candidate bit =
      (state.noRecvTable transition input bit).2 := by
  cases bit <;> rfl

theorem noRecv_output_eq_candidate
    (transition : Control → Input → Output × Control)
    (state : FiniteDelayedFork Control) (input : Input)
    (hcoherent : state.NoRecvOutputCoherent transition input)
    (bit : Bool) :
    (state.noRecv transition input).1 =
      (state.noRecvTable transition input bit).1 := by
  cases bit
  · rfl
  · exact hcoherent

/-! ### State-first Mealy form -/

/-- Branchwise no-receive table in the state-first convention used by
`FinitePairedMealyController`. -/
def noRecvMealyTable
    (transition : Control → Input → Control × Output)
    (state : FiniteDelayedFork Control) (input : Input) (bit : Bool) :
    Control × Output :=
  transition (state.candidate bit) input

def NoRecvMealyOutputCoherent
    (transition : Control → Input → Control × Output)
    (state : FiniteDelayedFork Control) (input : Input) : Prop :=
  (state.noRecvMealyTable transition input false).2 =
    (state.noRecvMealyTable transition input true).2

/-- Graph-blind state-first no-receive update. -/
def noRecvMealy
    (transition : Control → Input → Control × Output)
    (state : FiniteDelayedFork Control) (input : Input) :
    FiniteDelayedFork Control × Output :=
  let openResult := state.noRecvMealyTable transition input false
  let closedResult := state.noRecvMealyTable transition input true
  (⟨openResult.1, closedResult.1⟩, openResult.2)

@[simp] theorem noRecvMealy_candidate
    (transition : Control → Input → Control × Output)
    (state : FiniteDelayedFork Control) (input : Input) (bit : Bool) :
    (state.noRecvMealy transition input).1.candidate bit =
      (state.noRecvMealyTable transition input bit).1 := by
  cases bit <;> rfl

theorem noRecvMealy_output_eq_candidate
    (transition : Control → Input → Control × Output)
    (state : FiniteDelayedFork Control) (input : Input)
    (hcoherent : state.NoRecvMealyOutputCoherent transition input)
    (bit : Bool) :
    (state.noRecvMealy transition input).2 =
      (state.noRecvMealyTable transition input bit).2 := by
  cases bit
  · rfl
  · exact hcoherent

/-- Resolve the old bit from the partner's delivered finite tag. -/
def resolve
    (state : FiniteDelayedFork Control)
    (delivered : FiniteDelayedTagged Delivered) : Control :=
  state.candidate delivered.bit

@[simp] theorem resolve_open
    (state : FiniteDelayedFork Control) (delivered : Delivered) :
    state.resolve (FiniteDelayedTagged.openBranch delivered) =
      state.openControl := by
  simp [resolve]

@[simp] theorem resolve_closed
    (state : FiniteDelayedFork Control) (delivered : Delivered) :
    state.resolve (FiniteDelayedTagged.closedBranch delivered) =
      state.closedControl := by
  simp [resolve]

/-- The next receive resolves the old branch before computing its output.
The receive transition sees precisely the two local controls and two inputs
available at a physical receive. -/
def recv
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Output × Next)
    (state : FiniteDelayedFork Control) (ownInput : OwnInput)
    (delivered : FiniteDelayedTagged Delivered)
    (deliveredInput : DeliveredInput) : Output × Next :=
  transition (state.resolve delivered) ownInput delivered.control
    deliveredInput

/-- Exact one-way next-receive equation. -/
@[simp] theorem recv_open
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Output × Next)
    (state : FiniteDelayedFork Control) (ownInput : OwnInput)
    (delivered : Delivered) (deliveredInput : DeliveredInput) :
    state.recv transition ownInput
        (FiniteDelayedTagged.openBranch delivered) deliveredInput =
      transition state.openControl ownInput delivered deliveredInput := by
  rfl

/-- Exact simultaneous-close next-receive equation.  No equality between the
open and closed receiver outputs is asserted or needed. -/
@[simp] theorem recv_closed
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Output × Next)
    (state : FiniteDelayedFork Control) (ownInput : OwnInput)
    (delivered : Delivered) (deliveredInput : DeliveredInput) :
    state.recv transition ownInput
        (FiniteDelayedTagged.closedBranch delivered) deliveredInput =
      transition state.closedControl ownInput delivered deliveredInput := by
  rfl

/-- Pointwise form: the result is the receive transition of the branch named
by the delivered finite tag. -/
theorem recv_eq_candidate
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Output × Next)
    (state : FiniteDelayedFork Control) (ownInput : OwnInput)
    (delivered : FiniteDelayedTagged Delivered)
    (deliveredInput : DeliveredInput) :
    state.recv transition ownInput delivered deliveredInput =
      transition (state.candidate delivered.bit) ownInput delivered.control
        deliveredInput :=
  rfl

/-- State-first receive resolver for direct use as a
`FinitePairedMealyController.recvOne`/`recvTwo` field. -/
def recvMealy
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Next × Output)
    (state : FiniteDelayedFork Control) (ownInput : OwnInput)
    (delivered : FiniteDelayedTagged Delivered)
    (deliveredInput : DeliveredInput) : Next × Output :=
  transition (state.resolve delivered) ownInput delivered.control
    deliveredInput

@[simp] theorem recvMealy_open
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Next × Output)
    (state : FiniteDelayedFork Control) (ownInput : OwnInput)
    (delivered : Delivered) (deliveredInput : DeliveredInput) :
    state.recvMealy transition ownInput
        (FiniteDelayedTagged.openBranch delivered) deliveredInput =
      transition state.openControl ownInput delivered deliveredInput :=
  rfl

@[simp] theorem recvMealy_closed
    (transition :
      Control → OwnInput → Delivered → DeliveredInput → Next × Output)
    (state : FiniteDelayedFork Control) (ownInput : OwnInput)
    (delivered : Delivered) (deliveredInput : DeliveredInput) :
    state.recvMealy transition ownInput
        (FiniteDelayedTagged.closedBranch delivered) deliveredInput =
      transition state.closedControl ownInput delivered deliveredInput :=
  rfl

end FiniteDelayedFork

end DistributedSynthesis
