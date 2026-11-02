/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingBlindForkInvariant

/-!
# Shared pending members for deferred exact-close activation

At a seam reversal, immediately replacing the open candidate by a recurrent
control can create an unresolved recurrent/table fork.  Such a fork need not
have one blind output.  The safe finite representation keeps both candidates
in one member-tagged table state until a later receive resolves the member.

`DeferredMemberControl Shared Payload` stores the hidden member bit, one
shared table control, and finite payload retained for the later receive.  A
model supplies a member-indexed table step and proves that its two members
have the same output and the same next shared control.  This file then proves
once and for all that the canonical false/true fork is output coherent at
arbitrary blind depth.

The optional `DeferredOrRecurrent` layer adds already recurrent controls.
Its blind relation uses shared-state agreement on pending controls and
ordinary equality on recurrent controls.  Receive-time normalization is
deliberately not defined here: in the literal construction it needs the
partner control delivered at that receive, including its latest staged
target.

The member bit is stored finite control, not an observed graph or hierarchy
signal.  No executable map in this module receives a graph, orientation,
leader, strict-leader, history, or view.
-/

namespace DistributedSynthesis

universe u v w x y z

namespace FiniteAcknowledgedDelayedCarrier

/-! ## A shared, member-tagged pending control -/

/-- A pending candidate consists of its proof-side member, one shared table
control, and finite payload needed when a later receive activates it. -/
abbrev DeferredMemberControl
    (Shared : Type u) (Payload : Type v) :=
  Bool × Shared × Payload

variable {Shared : Type u} {Payload : Type v}
variable {Input : Type w} {Output : Type x}

/-- The exact replace-not-accumulate laws for the two table members. -/
structure DeferredMemberStepLaws
    (step : Bool → Shared → Input → Shared × Output) : Prop where
  outputEq : ∀ shared input,
    (step false shared input).2 = (step true shared input).2
  stateEq : ∀ shared input,
    (step false shared input).1 = (step true shared input).1

namespace DeferredMemberStepLaws

variable {step : Bool → Shared → Input → Shared × Output}

/-- The output equality extends from the canonical false/true pair to any
two member bits. -/
theorem output_eq (laws : DeferredMemberStepLaws step)
    (left right : Bool) (shared : Shared) (input : Input) :
    (step left shared input).2 = (step right shared input).2 := by
  cases left <;> cases right
  · rfl
  · exact laws.outputEq shared input
  · exact (laws.outputEq shared input).symm
  · rfl

/-- The shared next-state equality likewise holds for any two member bits. -/
theorem state_eq (laws : DeferredMemberStepLaws step)
    (left right : Bool) (shared : Shared) (input : Input) :
    (step left shared input).1 = (step right shared input).1 := by
  cases left <;> cases right
  · rfl
  · exact laws.stateEq shared input
  · exact (laws.stateEq shared input).symm
  · rfl

end DeferredMemberStepLaws

/-- State-first blind evolution.  The member and payload are retained; only
the shared table control advances. -/
def deferredMemberNoRecv
    (step : Bool → Shared → Input → Shared × Output)
    (state : DeferredMemberControl Shared Payload) (input : Input) :
    DeferredMemberControl Shared Payload × Output :=
  let next := step state.1 state.2.1 input
  ((state.1, next.1, state.2.2), next.2)

@[simp] theorem deferredMemberNoRecv_member
    (step : Bool → Shared → Input → Shared × Output)
    (state : DeferredMemberControl Shared Payload) (input : Input) :
    (deferredMemberNoRecv step state input).1.1 = state.1 :=
  rfl

@[simp] theorem deferredMemberNoRecv_shared
    (step : Bool → Shared → Input → Shared × Output)
    (state : DeferredMemberControl Shared Payload) (input : Input) :
    (deferredMemberNoRecv step state input).1.2.1 =
      (step state.1 state.2.1 input).1 :=
  rfl

@[simp] theorem deferredMemberNoRecv_payload
    (step : Bool → Shared → Input → Shared × Output)
    (state : DeferredMemberControl Shared Payload) (input : Input) :
    (deferredMemberNoRecv step state input).1.2.2 = state.2.2 :=
  rfl

@[simp] theorem deferredMemberNoRecv_output
    (step : Bool → Shared → Input → Shared × Output)
    (state : DeferredMemberControl Shared Payload) (input : Input) :
    (deferredMemberNoRecv step state input).2 =
      (step state.1 state.2.1 input).2 :=
  rfl

/-- Pending controls are blind-related exactly when their executable shared
state and retained activation payload agree.  The member bits may differ. -/
def DeferredMemberBlind
    (left right : DeferredMemberControl Shared Payload) : Prop :=
  left.2.1 = right.2.1 ∧ left.2.2 = right.2.2

/-- The canonical unresolved pending fork. -/
def deferredMemberFork (shared : Shared) (payload : Payload) :
    FiniteDelayedFork (DeferredMemberControl Shared Payload) :=
  ⟨(false, shared, payload), (true, shared, payload)⟩

@[simp] theorem deferredMemberFork_open
    (shared : Shared) (payload : Payload) :
    (deferredMemberFork shared payload).openControl =
      ((false, shared, payload) : DeferredMemberControl Shared Payload) :=
  rfl

@[simp] theorem deferredMemberFork_closed
    (shared : Shared) (payload : Payload) :
    (deferredMemberFork shared payload).closedControl =
      ((true, shared, payload) : DeferredMemberControl Shared Payload) :=
  rfl

@[simp] theorem deferredMemberFork_candidate
    (shared : Shared) (payload : Payload) (member : Bool) :
    (deferredMemberFork shared payload).candidate member =
      ((member, shared, payload) : DeferredMemberControl Shared Payload) := by
  cases member <;> rfl

theorem deferredMemberFork_blind
    (shared : Shared) (payload : Payload) :
    DeferredMemberBlind
      (deferredMemberFork shared payload).openControl
      (deferredMemberFork shared payload).closedControl := by
  exact ⟨rfl, rfl⟩

/-- Blind-related pending controls emit one output and remain blind-related
after a no-receive. -/
theorem deferredMemberBlind_noRecv
    (step : Bool → Shared → Input → Shared × Output)
    (laws : DeferredMemberStepLaws step)
    (left right : DeferredMemberControl Shared Payload) (input : Input)
    (hblind : DeferredMemberBlind left right) :
    (deferredMemberNoRecv step left input).2 =
        (deferredMemberNoRecv step right input).2 ∧
      DeferredMemberBlind
        (deferredMemberNoRecv step left input).1
        (deferredMemberNoRecv step right input).1 := by
  rcases left with ⟨leftMember, leftShared, leftPayload⟩
  rcases right with ⟨rightMember, rightShared, rightPayload⟩
  rcases hblind with ⟨hshared, hpayload⟩
  change leftShared = rightShared at hshared
  change leftPayload = rightPayload at hpayload
  subst rightShared
  subst rightPayload
  exact ⟨laws.output_eq leftMember rightMember leftShared input,
    ⟨laws.state_eq leftMember rightMember leftShared input, rfl⟩⟩

/-- The canonical fork has a coherent physical output for every input. -/
theorem deferredMemberFork_noRecvOutputCoherent
    (step : Bool → Shared → Input → Shared × Output)
    (laws : DeferredMemberStepLaws step)
    (shared : Shared) (payload : Payload) (input : Input) :
    (deferredMemberFork shared payload).NoRecvMealyOutputCoherent
      (deferredMemberNoRecv step) input := by
  exact laws.outputEq shared input

/-- One blind step produces the same canonical false/true fork at the common
next shared state. -/
theorem deferredMemberFork_noRecvMealy
    (step : Bool → Shared → Input → Shared × Output)
    (laws : DeferredMemberStepLaws step)
    (shared : Shared) (payload : Payload) (input : Input) :
    (deferredMemberFork shared payload).noRecvMealy
        (deferredMemberNoRecv step) input =
      (deferredMemberFork (step false shared input).1 payload,
        (step false shared input).2) := by
  simp only [FiniteDelayedFork.noRecvMealy,
    FiniteDelayedFork.noRecvMealyTable, FiniteDelayedFork.candidate,
    deferredMemberFork, deferredMemberNoRecv, Bool.false_eq_true, ↓reduceIte]
  rw [laws.stateEq shared input]

/-- Therefore the canonical fork remains coherent after any current blind
step, uniformly in the next private input. -/
theorem deferredMemberFork_noRecv_preserves_coherent
    (step : Bool → Shared → Input → Shared × Output)
    (laws : DeferredMemberStepLaws step)
    (shared : Shared) (payload : Payload) (input nextInput : Input) :
    ((deferredMemberFork shared payload).noRecvMealy
        (deferredMemberNoRecv step) input).1.NoRecvMealyOutputCoherent
      (deferredMemberNoRecv step) nextInput := by
  rw [deferredMemberFork_noRecvMealy step laws shared payload input]
  exact deferredMemberFork_noRecvOutputCoherent step laws _ payload nextInput

/-! ## Dependent-key repacking

Concrete seam tables naturally store their key outside the member bit:
`(Σ key, Bool × Shared key) × Payload`.  The generic carrier puts the bit
first.  The following equivalence and commuting equations are the only
adapter needed between these presentations. -/

/-- The dependent-key presentation used by concrete heterogeneous tables. -/
abbrev KeyedDeferredMemberControl
    (Key : Type z) (Shared : Key → Type u) (Payload : Type v) :=
  (Σ key : Key, Bool × Shared key) × Payload

variable {Key : Type z} {KeyedShared : Key → Type u}

/-- Move the member outside the dependent key without changing any data. -/
def keyedDeferredToMember
    (state : KeyedDeferredMemberControl Key KeyedShared Payload) :
    DeferredMemberControl (Σ key : Key, KeyedShared key) Payload :=
  (state.1.2.1, ⟨state.1.1, state.1.2.2⟩, state.2)

/-- Inverse repacking into the concrete dependent-key presentation. -/
def memberToKeyedDeferred
    (state : DeferredMemberControl (Σ key : Key, KeyedShared key) Payload) :
    KeyedDeferredMemberControl Key KeyedShared Payload :=
  (⟨state.2.1.1, state.1, state.2.1.2⟩, state.2.2)

/-- The two pending-control presentations are exactly equivalent. -/
def keyedDeferredMemberEquiv :
    KeyedDeferredMemberControl Key KeyedShared Payload ≃
      DeferredMemberControl (Σ key : Key, KeyedShared key) Payload where
  toFun := keyedDeferredToMember
  invFun := memberToKeyedDeferred
  left_inv := by
    rintro ⟨⟨key, member, shared⟩, payload⟩
    rfl
  right_inv := by
    rintro ⟨member, ⟨key, shared⟩, payload⟩
    rfl

/-- Lift a key-indexed member step to the sigma of shared controls. -/
def keyedDeferredSharedStep
    (step : ∀ key : Key,
      Bool → KeyedShared key → Input → KeyedShared key × Output)
    (member : Bool) (shared : Σ key : Key, KeyedShared key) (input : Input) :
    (Σ key : Key, KeyedShared key) × Output :=
  let next := step shared.1 member shared.2 input
  (⟨shared.1, next.1⟩, next.2)

/-- Pointwise member laws imply the generic laws after sigma packing. -/
theorem keyedDeferredSharedStep_laws
    (step : ∀ key : Key,
      Bool → KeyedShared key → Input → KeyedShared key × Output)
    (laws : ∀ key, DeferredMemberStepLaws (step key)) :
    DeferredMemberStepLaws (keyedDeferredSharedStep step) := by
  refine { outputEq := ?_, stateEq := ?_ }
  · rintro ⟨key, shared⟩ input
    exact (laws key).outputEq shared input
  · rintro ⟨key, shared⟩ input
    change
      (⟨key, (step key false shared input).1⟩ :
          Σ key : Key, KeyedShared key) =
        ⟨key, (step key true shared input).1⟩
    rw [(laws key).stateEq shared input]

/-- Direct no-receive in the concrete dependent-key presentation. -/
def keyedDeferredMemberNoRecv
    (step : ∀ key : Key,
      Bool → KeyedShared key → Input → KeyedShared key × Output)
    (state : KeyedDeferredMemberControl Key KeyedShared Payload)
    (input : Input) :
    KeyedDeferredMemberControl Key KeyedShared Payload × Output :=
  let next := step state.1.1 state.1.2.1 state.1.2.2 input
  ((⟨state.1.1, state.1.2.1, next.1⟩, state.2), next.2)

/-- Repacking commutes definitionally with the member-dependent no-receive. -/
theorem keyedDeferredMemberNoRecv_repack
    (step : ∀ key : Key,
      Bool → KeyedShared key → Input → KeyedShared key × Output)
    (state : KeyedDeferredMemberControl Key KeyedShared Payload)
    (input : Input) :
    (keyedDeferredToMember
        (keyedDeferredMemberNoRecv step state input).1,
      (keyedDeferredMemberNoRecv step state input).2) =
      deferredMemberNoRecv (keyedDeferredSharedStep step)
        (keyedDeferredToMember state) input := by
  rcases state with ⟨⟨key, member, shared⟩, payload⟩
  rfl

/-- Canonical false/true fork in the concrete dependent-key order. -/
def keyedDeferredMemberFork
    (key : Key) (shared : KeyedShared key) (payload : Payload) :
    FiniteDelayedFork (KeyedDeferredMemberControl Key KeyedShared Payload) :=
  ⟨(⟨key, false, shared⟩, payload),
    (⟨key, true, shared⟩, payload)⟩

/-- Repack both candidates of a dependent-key fork. -/
def repackKeyedDeferredFork
    (fork : FiniteDelayedFork
      (KeyedDeferredMemberControl Key KeyedShared Payload)) :
    FiniteDelayedFork
      (DeferredMemberControl (Σ key : Key, KeyedShared key) Payload) :=
  ⟨keyedDeferredToMember fork.openControl,
    keyedDeferredToMember fork.closedControl⟩

/-- The concrete canonical fork repacks to the generic canonical fork. -/
@[simp] theorem repackKeyedDeferredFork_canonical
    (key : Key) (shared : KeyedShared key) (payload : Payload) :
    repackKeyedDeferredFork (keyedDeferredMemberFork key shared payload) =
      deferredMemberFork (⟨key, shared⟩ : Σ key : Key, KeyedShared key)
        payload :=
  rfl

/-! ## Optional pending/recurrent sum -/

variable {Recurrent : Type y}

/-- A local control is either still in the shared pending table or has been
normalized to recurrent form by a receive that saw the selected member and
the delivered partner stage. -/
abbrev DeferredOrRecurrent
    (Shared : Type u) (Payload : Type v) (Recurrent : Type y) :=
  DeferredMemberControl Shared Payload ⊕ Recurrent

/-- No-receive is closed separately in each phase. -/
def deferredOrRecurrentNoRecv
    (pendingStep : Bool → Shared → Input → Shared × Output)
    (recurrentStep : Recurrent → Input → Recurrent × Output)
    (state : DeferredOrRecurrent Shared Payload Recurrent) (input : Input) :
    DeferredOrRecurrent Shared Payload Recurrent × Output :=
  match state with
  | .inl pending =>
      let next := deferredMemberNoRecv pendingStep pending input
      (.inl next.1, next.2)
  | .inr recurrent =>
      let next := recurrentStep recurrent input
      (.inr next.1, next.2)

/-- Pending controls use shared-state agreement, recurrent controls use
equality, and controls in different phases are never blind-related. -/
def DeferredOrRecurrentBlind
    (left right : DeferredOrRecurrent Shared Payload Recurrent) : Prop :=
  match left, right with
  | .inl left, .inl right => DeferredMemberBlind left right
  | .inr left, .inr right => left = right
  | _, _ => False

/-- The canonical pending fork embedded in the phase sum. -/
def deferredOrRecurrentFork
    (shared : Shared) (payload : Payload) :
    FiniteDelayedFork (DeferredOrRecurrent Shared Payload Recurrent) :=
  ⟨.inl (false, shared, payload), .inl (true, shared, payload)⟩

@[simp] theorem deferredOrRecurrentFork_candidate
    (shared : Shared) (payload : Payload) (member : Bool) :
    (deferredOrRecurrentFork (Recurrent := Recurrent) shared payload
      ).candidate member =
      (.inl (member, shared, payload) :
        DeferredOrRecurrent Shared Payload Recurrent) := by
  cases member <;> rfl

theorem deferredOrRecurrentFork_blind
    (shared : Shared) (payload : Payload) :
    DeferredOrRecurrentBlind
      (deferredOrRecurrentFork (Recurrent := Recurrent) shared payload
        ).openControl
      (deferredOrRecurrentFork (Recurrent := Recurrent) shared payload
        ).closedControl := by
  exact ⟨rfl, rfl⟩

/-- The pending/recurrent sum relation is a no-receive bisimulation. -/
theorem deferredOrRecurrentBlind_noRecv
    (pendingStep : Bool → Shared → Input → Shared × Output)
    (pendingLaws : DeferredMemberStepLaws pendingStep)
    (recurrentStep : Recurrent → Input → Recurrent × Output)
    (left right : DeferredOrRecurrent Shared Payload Recurrent)
    (input : Input) (hblind : DeferredOrRecurrentBlind left right) :
    (deferredOrRecurrentNoRecv pendingStep recurrentStep left input).2 =
        (deferredOrRecurrentNoRecv pendingStep recurrentStep right input).2 ∧
      DeferredOrRecurrentBlind
        (deferredOrRecurrentNoRecv pendingStep recurrentStep left input).1
        (deferredOrRecurrentNoRecv pendingStep recurrentStep right input).1 := by
  cases left with
  | inl left =>
      cases right with
      | inl right =>
          exact deferredMemberBlind_noRecv pendingStep pendingLaws left right
            input hblind
      | inr right => exact False.elim hblind
  | inr left =>
      cases right with
      | inl right => exact False.elim hblind
      | inr right =>
          subst right
          exact ⟨rfl, rfl⟩

/-- Embedding the pending fork into the phase sum preserves its coherent
physical output. -/
theorem deferredOrRecurrentFork_noRecvOutputCoherent
    (pendingStep : Bool → Shared → Input → Shared × Output)
    (pendingLaws : DeferredMemberStepLaws pendingStep)
    (recurrentStep : Recurrent → Input → Recurrent × Output)
    (shared : Shared) (payload : Payload) (input : Input) :
    (deferredOrRecurrentFork (Recurrent := Recurrent) shared payload
      ).NoRecvMealyOutputCoherent
        (deferredOrRecurrentNoRecv pendingStep recurrentStep) input := by
  exact pendingLaws.outputEq shared input

/-- One sum-level blind step still produces the canonical pending fork; no
recurrent branch is manufactured before acknowledgement. -/
theorem deferredOrRecurrentFork_noRecvMealy
    (pendingStep : Bool → Shared → Input → Shared × Output)
    (pendingLaws : DeferredMemberStepLaws pendingStep)
    (recurrentStep : Recurrent → Input → Recurrent × Output)
    (shared : Shared) (payload : Payload) (input : Input) :
    (deferredOrRecurrentFork (Recurrent := Recurrent) shared payload
      ).noRecvMealy
        (deferredOrRecurrentNoRecv pendingStep recurrentStep) input =
      (deferredOrRecurrentFork (Recurrent := Recurrent)
          (pendingStep false shared input).1 payload,
        (pendingStep false shared input).2) := by
  simp only [FiniteDelayedFork.noRecvMealy,
    FiniteDelayedFork.noRecvMealyTable, FiniteDelayedFork.candidate,
    deferredOrRecurrentFork, deferredOrRecurrentNoRecv,
    deferredMemberNoRecv, Bool.false_eq_true, ↓reduceIte]
  rw [pendingLaws.stateEq shared input]

/-- Arbitrary-depth pending coherence inside the phase sum. -/
theorem deferredOrRecurrentFork_noRecv_preserves_coherent
    (pendingStep : Bool → Shared → Input → Shared × Output)
    (pendingLaws : DeferredMemberStepLaws pendingStep)
    (recurrentStep : Recurrent → Input → Recurrent × Output)
    (shared : Shared) (payload : Payload) (input nextInput : Input) :
    ((deferredOrRecurrentFork (Recurrent := Recurrent) shared payload
      ).noRecvMealy
        (deferredOrRecurrentNoRecv pendingStep recurrentStep) input
      ).1.NoRecvMealyOutputCoherent
        (deferredOrRecurrentNoRecv pendingStep recurrentStep) nextInput := by
  rw [deferredOrRecurrentFork_noRecvMealy pendingStep pendingLaws
    recurrentStep shared payload input]
  exact deferredOrRecurrentFork_noRecvOutputCoherent pendingStep pendingLaws
    recurrentStep _ payload nextInput

/-- Two endpoint-local pending/recurrent constructions assemble directly
into the generic blind no-receive law bundle. -/
def deferredOrRecurrentBlindNoRecvLaws
    {SharedOne : Type u} {PayloadOne : Type v} {RecurrentOne : Type y}
    {SharedTwo : Type z} {PayloadTwo : Type u} {RecurrentTwo : Type v}
    {InputOne : Type w} {InputTwo : Type z}
    {OutputOne : Type x} {OutputTwo : Type y}
    (pendingStepOne :
      Bool → SharedOne → InputOne → SharedOne × OutputOne)
    (pendingLawsOne : DeferredMemberStepLaws pendingStepOne)
    (recurrentStepOne :
      RecurrentOne → InputOne → RecurrentOne × OutputOne)
    (pendingStepTwo :
      Bool → SharedTwo → InputTwo → SharedTwo × OutputTwo)
    (pendingLawsTwo : DeferredMemberStepLaws pendingStepTwo)
    (recurrentStepTwo :
      RecurrentTwo → InputTwo → RecurrentTwo × OutputTwo) :
    BlindNoRecvLaws
      (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
      (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
      (DeferredOrRecurrentBlind :
        DeferredOrRecurrent SharedOne PayloadOne RecurrentOne →
          DeferredOrRecurrent SharedOne PayloadOne RecurrentOne → Prop)
      (DeferredOrRecurrentBlind :
        DeferredOrRecurrent SharedTwo PayloadTwo RecurrentTwo →
          DeferredOrRecurrent SharedTwo PayloadTwo RecurrentTwo → Prop) where
  one := deferredOrRecurrentBlind_noRecv pendingStepOne pendingLawsOne
    recurrentStepOne
  two := deferredOrRecurrentBlind_noRecv pendingStepTwo pendingLawsTwo
    recurrentStepTwo

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
