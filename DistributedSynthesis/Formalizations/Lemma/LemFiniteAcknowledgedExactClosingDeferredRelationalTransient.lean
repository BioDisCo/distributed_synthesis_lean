/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredBankSelectedTraceLaws

/-!
# Relational transients for deferred exact closing

A runtime endpoint need not enter a recurrent control at the instant at which
the proof-side staged execution does.  In particular, after an ambiguous
nonreceive it may safely retain and advance its pending table.  What the trace
argument needs is weaker: that pending table represents the staged recurrent
control, emits the same selected physical output, and represents the next
staged control after every local transition.

This file packages exactly that simulation.  `DeferredRepresents` interprets
a pending control through a caller-supplied relation and a recurrent control
by equality.  `DeferredRelationalSimulationLaws` asks for representation
preservation and selected-output equality in the three physical cases.  The
generic adapter then lifts any recurrent selected trace to the runtime
deferred controls and, in one further arrow, through the existing dependent
bank trace adapter.

No runtime function is defined here.  In particular there is no phase-only
dispatch and no graph, orientation, leader, history, or view argument.
-/

namespace DistributedSynthesis

universe u v x y k a b c d e f

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {SharedOne : Type a} {PayloadOne : Type b} {RecurrentOne : Type c}
variable {SharedTwo : Type d} {PayloadTwo : Type e} {RecurrentTwo : Type f}

private abbrev OnePending :=
  DeferredMemberControl SharedOne PayloadOne

private abbrev TwoPending :=
  DeferredMemberControl SharedTwo PayloadTwo

private abbrev OneControl :=
  DeferredOrRecurrent SharedOne PayloadOne RecurrentOne

private abbrev TwoControl :=
  DeferredOrRecurrent SharedTwo PayloadTwo RecurrentTwo

/-! ## A pending table may denote a recurrent staged control -/

/-- Interpret a runtime deferred control as a proof-side recurrent control.
Pending controls use the supplied transient relation; recurrent controls
denote themselves. -/
def DeferredRepresents
    (PendingRep : DeferredMemberControl SharedOne PayloadOne →
      RecurrentOne → Prop)
    (control : DeferredOrRecurrent SharedOne PayloadOne RecurrentOne)
    (semantic : RecurrentOne) : Prop :=
  match control with
  | .inl pending => PendingRep pending semantic
  | .inr recurrent => recurrent = semantic

@[simp] theorem deferredRepresents_pending
    (PendingRep : DeferredMemberControl SharedOne PayloadOne →
      RecurrentOne → Prop)
    (pending : DeferredMemberControl SharedOne PayloadOne)
    (semantic : RecurrentOne) :
    DeferredRepresents PendingRep (.inl pending) semantic ↔
      PendingRep pending semantic :=
  Iff.rfl

@[simp] theorem deferredRepresents_recurrent
    (PendingRep : DeferredMemberControl SharedOne PayloadOne →
      RecurrentOne → Prop)
    (recurrent semantic : RecurrentOne) :
    DeferredRepresents PendingRep (.inr recurrent) semantic ↔
      recurrent = semantic :=
  Iff.rfl

/-- The runtime selected predicate induced by two transient representation
relations and one semantic predicate on recurrent staged controls. -/
def DeferredRelationalSelected
    (PendingRepOne : OnePending (SharedOne := SharedOne)
      (PayloadOne := PayloadOne) → RecurrentOne → Prop)
    (PendingRepTwo : TwoPending (SharedTwo := SharedTwo)
      (PayloadTwo := PayloadTwo) → RecurrentTwo → Prop)
    (SemanticSelected : RecurrentOne → RecurrentTwo → Nat → Prop)
    (one : OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
      (RecurrentOne := RecurrentOne))
    (two : TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
      (RecurrentTwo := RecurrentTwo))
    (n : Nat) : Prop :=
  ∃ semanticOne semanticTwo,
    DeferredRepresents PendingRepOne one semanticOne ∧
      DeferredRepresents PendingRepTwo two semanticTwo ∧
      SemanticSelected semanticOne semanticTwo n

/-! ## Operational simulation -/

/-- Runtime pending/recurrent controls simulate one recurrent staged pair.

The strict fields deliberately compare the runtime no-receive/receive pair
with the corresponding semantic pair.  Thus a concrete proof may keep the
blind runtime endpoint pending while relating it to the semantic recurrent
postcontrol.  The simultaneous field compares runtime and semantic close
postcontrols, while outputs still come from the ordinary receive projections. -/
structure DeferredRelationalSimulationLaws
    (initialOne : OneControl (SharedOne := SharedOne)
      (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne))
    (initialTwo : TwoControl (SharedTwo := SharedTwo)
      (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo))
    (noRecvOne : OneControl (SharedOne := SharedOne)
      (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
        OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
          (RecurrentOne := RecurrentOne) × Out₁)
    (noRecvTwo : TwoControl (SharedTwo := SharedTwo)
      (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo) → In₂ →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) × Out₂)
    (openRecvOne : OneControl (SharedOne := SharedOne)
      (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) → In₂ →
        OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
          (RecurrentOne := RecurrentOne) × Out₁)
    (openRecvTwo : TwoControl (SharedTwo := SharedTwo)
      (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo) → In₂ →
        OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
          (RecurrentOne := RecurrentOne) → In₁ →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) × Out₂)
    (close : OneControl (SharedOne := SharedOne)
      (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) → In₂ →
        OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
            (RecurrentOne := RecurrentOne) ×
          TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
            (RecurrentTwo := RecurrentTwo))
    (Rel : OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
      (RecurrentOne := RecurrentOne) →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) → Prop)
    (semanticInitialOne : RecurrentOne)
    (semanticInitialTwo : RecurrentTwo)
    (semanticNoRecvOne : RecurrentOne → In₁ → RecurrentOne × Out₁)
    (semanticNoRecvTwo : RecurrentTwo → In₂ → RecurrentTwo × Out₂)
    (semanticOpenRecvOne : RecurrentOne → In₁ → RecurrentTwo → In₂ →
      RecurrentOne × Out₁)
    (semanticOpenRecvTwo : RecurrentTwo → In₂ → RecurrentOne → In₁ →
      RecurrentTwo × Out₂)
    (semanticClose : RecurrentOne → In₁ → RecurrentTwo → In₂ →
      RecurrentOne × RecurrentTwo)
    (PendingRepOne : OnePending (SharedOne := SharedOne)
      (PayloadOne := PayloadOne) → RecurrentOne → Prop)
    (PendingRepTwo : TwoPending (SharedTwo := SharedTwo)
      (PayloadTwo := PayloadTwo) → RecurrentTwo → Prop) : Prop where
  initialOne : DeferredRepresents PendingRepOne initialOne semanticInitialOne
  initialTwo : DeferredRepresents PendingRepTwo initialTwo semanticInitialTwo
  strictRight : ∀ one inputOne two inputTwo semanticOne semanticTwo,
    Rel one two →
      DeferredRepresents PendingRepOne one semanticOne →
      DeferredRepresents PendingRepTwo two semanticTwo →
      DeferredRepresents PendingRepOne
          (noRecvOne one inputOne).1
          (semanticNoRecvOne semanticOne inputOne).1 ∧
        DeferredRepresents PendingRepTwo
          (openRecvTwo two inputTwo one inputOne).1
          (semanticOpenRecvTwo semanticTwo inputTwo semanticOne inputOne).1 ∧
        (noRecvOne one inputOne).2 =
          (semanticNoRecvOne semanticOne inputOne).2 ∧
        (openRecvTwo two inputTwo one inputOne).2 =
          (semanticOpenRecvTwo semanticTwo inputTwo semanticOne inputOne).2
  strictLeft : ∀ one inputOne two inputTwo semanticOne semanticTwo,
    Rel one two →
      DeferredRepresents PendingRepOne one semanticOne →
      DeferredRepresents PendingRepTwo two semanticTwo →
      DeferredRepresents PendingRepOne
          (openRecvOne one inputOne two inputTwo).1
          (semanticOpenRecvOne semanticOne inputOne semanticTwo inputTwo).1 ∧
        DeferredRepresents PendingRepTwo
          (noRecvTwo two inputTwo).1
          (semanticNoRecvTwo semanticTwo inputTwo).1 ∧
        (openRecvOne one inputOne two inputTwo).2 =
          (semanticOpenRecvOne semanticOne inputOne semanticTwo inputTwo).2 ∧
        (noRecvTwo two inputTwo).2 =
          (semanticNoRecvTwo semanticTwo inputTwo).2
  both : ∀ one inputOne two inputTwo semanticOne semanticTwo,
    Rel one two →
      DeferredRepresents PendingRepOne one semanticOne →
      DeferredRepresents PendingRepTwo two semanticTwo →
      DeferredRepresents PendingRepOne
          (close one inputOne two inputTwo).1
          (semanticClose semanticOne inputOne semanticTwo inputTwo).1 ∧
        DeferredRepresents PendingRepTwo
          (close one inputOne two inputTwo).2
          (semanticClose semanticOne inputOne semanticTwo inputTwo).2 ∧
        (openRecvOne one inputOne two inputTwo).2 =
          (semanticOpenRecvOne semanticOne inputOne semanticTwo inputTwo).2 ∧
        (openRecvTwo two inputTwo one inputOne).2 =
          (semanticOpenRecvTwo semanticTwo inputTwo semanticOne inputOne).2

namespace DeferredRelationalSimulationLaws

variable
  {initialOne : OneControl (SharedOne := SharedOne)
    (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne)}
  {initialTwo : TwoControl (SharedTwo := SharedTwo)
    (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo)}
  {noRecvOne : OneControl (SharedOne := SharedOne)
    (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
      OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
        (RecurrentOne := RecurrentOne) × Out₁}
  {noRecvTwo : TwoControl (SharedTwo := SharedTwo)
    (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo) → In₂ →
      TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
        (RecurrentTwo := RecurrentTwo) × Out₂}
  {openRecvOne : OneControl (SharedOne := SharedOne)
    (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
      TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
        (RecurrentTwo := RecurrentTwo) → In₂ →
      OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
        (RecurrentOne := RecurrentOne) × Out₁}
  {openRecvTwo : TwoControl (SharedTwo := SharedTwo)
    (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo) → In₂ →
      OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
        (RecurrentOne := RecurrentOne) → In₁ →
      TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
        (RecurrentTwo := RecurrentTwo) × Out₂}
  {close : OneControl (SharedOne := SharedOne)
    (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
      TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
        (RecurrentTwo := RecurrentTwo) → In₂ →
      OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
          (RecurrentOne := RecurrentOne) ×
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo)}
  {Rel : OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
    (RecurrentOne := RecurrentOne) →
      TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
        (RecurrentTwo := RecurrentTwo) → Prop}
  {semanticInitialOne : RecurrentOne}
  {semanticInitialTwo : RecurrentTwo}
  {semanticNoRecvOne : RecurrentOne → In₁ → RecurrentOne × Out₁}
  {semanticNoRecvTwo : RecurrentTwo → In₂ → RecurrentTwo × Out₂}
  {semanticOpenRecvOne : RecurrentOne → In₁ → RecurrentTwo → In₂ →
    RecurrentOne × Out₁}
  {semanticOpenRecvTwo : RecurrentTwo → In₂ → RecurrentOne → In₁ →
    RecurrentTwo × Out₂}
  {semanticClose : RecurrentOne → In₁ → RecurrentTwo → In₂ →
    RecurrentOne × RecurrentTwo}
  {PendingRepOne : OnePending (SharedOne := SharedOne)
    (PayloadOne := PayloadOne) → RecurrentOne → Prop}
  {PendingRepTwo : TwoPending (SharedTwo := SharedTwo)
    (PayloadTwo := PayloadTwo) → RecurrentTwo → Prop}

/-- Relational simulation lifts a semantic recurrent trace to the actual
pending/recurrent runtime controls. -/
def toExactClosingSelectedTraceLaws
    (laws : DeferredRelationalSimulationLaws initialOne initialTwo noRecvOne
      noRecvTwo openRecvOne openRecvTwo close Rel semanticInitialOne
      semanticInitialTwo semanticNoRecvOne semanticNoRecvTwo
      semanticOpenRecvOne semanticOpenRecvTwo semanticClose PendingRepOne
      PendingRepTwo)
    (SemanticSelected : RecurrentOne → RecurrentTwo → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (semanticTrace : ExactClosingSelectedTraceLaws semanticInitialOne
      semanticInitialTwo semanticNoRecvOne semanticNoRecvTwo
      semanticOpenRecvOne semanticOpenRecvTwo semanticClose (fun _ _ ↦ True)
      SemanticSelected env expectedOutputOne expectedOutputTwo) :
    ExactClosingSelectedTraceLaws initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close Rel
      (DeferredRelationalSelected PendingRepOne PendingRepTwo SemanticSelected)
      env expectedOutputOne expectedOutputTwo where
  initial := ⟨semanticInitialOne, semanticInitialTwo, laws.initialOne,
    laws.initialTwo, semanticTrace.initial⟩
  strictRight := by
    intro n one two hrel hselected hgraph
    rcases hselected with
      ⟨semanticOne, semanticTwo, hone, htwo, hsemantic⟩
    have hsim := laws.strictRight one (env n).inputOne two (env n).inputTwo
      semanticOne semanticTwo hrel hone htwo
    have hnext := semanticTrace.strictRight n semanticOne semanticTwo trivial
      hsemantic hgraph
    exact ⟨
      ⟨(semanticNoRecvOne semanticOne (env n).inputOne).1,
        (semanticOpenRecvTwo semanticTwo (env n).inputTwo semanticOne
          (env n).inputOne).1,
        hsim.1, hsim.2.1, hnext.1⟩,
      hsim.2.2.1.trans hnext.2.1,
      hsim.2.2.2.trans hnext.2.2⟩
  strictLeft := by
    intro n one two hrel hselected hgraph
    rcases hselected with
      ⟨semanticOne, semanticTwo, hone, htwo, hsemantic⟩
    have hsim := laws.strictLeft one (env n).inputOne two (env n).inputTwo
      semanticOne semanticTwo hrel hone htwo
    have hnext := semanticTrace.strictLeft n semanticOne semanticTwo trivial
      hsemantic hgraph
    exact ⟨
      ⟨(semanticOpenRecvOne semanticOne (env n).inputOne semanticTwo
          (env n).inputTwo).1,
        (semanticNoRecvTwo semanticTwo (env n).inputTwo).1,
        hsim.1, hsim.2.1, hnext.1⟩,
      hsim.2.2.1.trans hnext.2.1,
      hsim.2.2.2.trans hnext.2.2⟩
  both := by
    intro n one two hrel hselected hgraph
    rcases hselected with
      ⟨semanticOne, semanticTwo, hone, htwo, hsemantic⟩
    have hsim := laws.both one (env n).inputOne two (env n).inputTwo
      semanticOne semanticTwo hrel hone htwo
    have hnext := semanticTrace.both n semanticOne semanticTwo trivial
      hsemantic hgraph
    exact ⟨
      ⟨(semanticClose semanticOne (env n).inputOne semanticTwo
          (env n).inputTwo).1,
        (semanticClose semanticOne (env n).inputOne semanticTwo
          (env n).inputTwo).2,
        hsim.1, hsim.2.1, hnext.1⟩,
      hsim.2.2.1.trans hnext.2.1,
      hsim.2.2.2.trans hnext.2.2⟩

end DeferredRelationalSimulationLaws

/-! ## Joint representation, without endpointwise determinacy -/

/-- The selected runtime predicate induced by one genuinely joint
representation relation.  This is the appropriate interface when a staged
matched pair is pinned by data stored at only one endpoint: neither marginal
representation needs to determine its semantic control on its own. -/
def DeferredJointRelationalSelected
    (JointRep :
      OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
          (RecurrentOne := RecurrentOne) →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) →
        RecurrentOne → RecurrentTwo → Prop)
    (SemanticSelected : RecurrentOne → RecurrentTwo → Nat → Prop)
    (one : OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
      (RecurrentOne := RecurrentOne))
    (two : TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
      (RecurrentTwo := RecurrentTwo))
    (n : Nat) : Prop :=
  ∃ semanticOne semanticTwo,
    JointRep one two semanticOne semanticTwo ∧
      SemanticSelected semanticOne semanticTwo n

/-- Joint relational simulation between deferred runtime pairs and recurrent
semantic pairs.  The residual obligations are exactly one initial joint
representation and, for each physical case, one next joint representation
plus the two selected-output equalities. -/
structure DeferredJointRelationalSimulationLaws
    (initialOne : OneControl (SharedOne := SharedOne)
      (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne))
    (initialTwo : TwoControl (SharedTwo := SharedTwo)
      (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo))
    (noRecvOne : OneControl (SharedOne := SharedOne)
      (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
        OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
          (RecurrentOne := RecurrentOne) × Out₁)
    (noRecvTwo : TwoControl (SharedTwo := SharedTwo)
      (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo) → In₂ →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) × Out₂)
    (openRecvOne : OneControl (SharedOne := SharedOne)
      (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) → In₂ →
        OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
          (RecurrentOne := RecurrentOne) × Out₁)
    (openRecvTwo : TwoControl (SharedTwo := SharedTwo)
      (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo) → In₂ →
        OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
          (RecurrentOne := RecurrentOne) → In₁ →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) × Out₂)
    (close : OneControl (SharedOne := SharedOne)
      (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) → In₂ →
        OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
            (RecurrentOne := RecurrentOne) ×
          TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
            (RecurrentTwo := RecurrentTwo))
    (Rel : OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
      (RecurrentOne := RecurrentOne) →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) → Prop)
    (semanticInitialOne : RecurrentOne)
    (semanticInitialTwo : RecurrentTwo)
    (semanticNoRecvOne : RecurrentOne → In₁ → RecurrentOne × Out₁)
    (semanticNoRecvTwo : RecurrentTwo → In₂ → RecurrentTwo × Out₂)
    (semanticOpenRecvOne : RecurrentOne → In₁ → RecurrentTwo → In₂ →
      RecurrentOne × Out₁)
    (semanticOpenRecvTwo : RecurrentTwo → In₂ → RecurrentOne → In₁ →
      RecurrentTwo × Out₂)
    (semanticClose : RecurrentOne → In₁ → RecurrentTwo → In₂ →
      RecurrentOne × RecurrentTwo)
    (JointRep :
      OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
          (RecurrentOne := RecurrentOne) →
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo) →
        RecurrentOne → RecurrentTwo → Prop) : Prop where
  initial : JointRep initialOne initialTwo semanticInitialOne semanticInitialTwo
  strictRight : ∀ one inputOne two inputTwo semanticOne semanticTwo,
    Rel one two → JointRep one two semanticOne semanticTwo →
      JointRep (noRecvOne one inputOne).1
          (openRecvTwo two inputTwo one inputOne).1
          (semanticNoRecvOne semanticOne inputOne).1
          (semanticOpenRecvTwo semanticTwo inputTwo semanticOne inputOne).1 ∧
        (noRecvOne one inputOne).2 =
          (semanticNoRecvOne semanticOne inputOne).2 ∧
        (openRecvTwo two inputTwo one inputOne).2 =
          (semanticOpenRecvTwo semanticTwo inputTwo semanticOne inputOne).2
  strictLeft : ∀ one inputOne two inputTwo semanticOne semanticTwo,
    Rel one two → JointRep one two semanticOne semanticTwo →
      JointRep (openRecvOne one inputOne two inputTwo).1
          (noRecvTwo two inputTwo).1
          (semanticOpenRecvOne semanticOne inputOne semanticTwo inputTwo).1
          (semanticNoRecvTwo semanticTwo inputTwo).1 ∧
        (openRecvOne one inputOne two inputTwo).2 =
          (semanticOpenRecvOne semanticOne inputOne semanticTwo inputTwo).2 ∧
        (noRecvTwo two inputTwo).2 =
          (semanticNoRecvTwo semanticTwo inputTwo).2
  both : ∀ one inputOne two inputTwo semanticOne semanticTwo,
    Rel one two → JointRep one two semanticOne semanticTwo →
      JointRep (close one inputOne two inputTwo).1
          (close one inputOne two inputTwo).2
          (semanticClose semanticOne inputOne semanticTwo inputTwo).1
          (semanticClose semanticOne inputOne semanticTwo inputTwo).2 ∧
        (openRecvOne one inputOne two inputTwo).2 =
          (semanticOpenRecvOne semanticOne inputOne semanticTwo inputTwo).2 ∧
        (openRecvTwo two inputTwo one inputOne).2 =
          (semanticOpenRecvTwo semanticTwo inputTwo semanticOne inputOne).2

namespace DeferredJointRelationalSimulationLaws

variable
  {initialOne : OneControl (SharedOne := SharedOne)
    (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne)}
  {initialTwo : TwoControl (SharedTwo := SharedTwo)
    (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo)}
  {noRecvOne : OneControl (SharedOne := SharedOne)
    (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
      OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
        (RecurrentOne := RecurrentOne) × Out₁}
  {noRecvTwo : TwoControl (SharedTwo := SharedTwo)
    (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo) → In₂ →
      TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
        (RecurrentTwo := RecurrentTwo) × Out₂}
  {openRecvOne : OneControl (SharedOne := SharedOne)
    (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
      TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
        (RecurrentTwo := RecurrentTwo) → In₂ →
      OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
        (RecurrentOne := RecurrentOne) × Out₁}
  {openRecvTwo : TwoControl (SharedTwo := SharedTwo)
    (PayloadTwo := PayloadTwo) (RecurrentTwo := RecurrentTwo) → In₂ →
      OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
        (RecurrentOne := RecurrentOne) → In₁ →
      TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
        (RecurrentTwo := RecurrentTwo) × Out₂}
  {close : OneControl (SharedOne := SharedOne)
    (PayloadOne := PayloadOne) (RecurrentOne := RecurrentOne) → In₁ →
      TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
        (RecurrentTwo := RecurrentTwo) → In₂ →
      OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
          (RecurrentOne := RecurrentOne) ×
        TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
          (RecurrentTwo := RecurrentTwo)}
  {Rel : OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
    (RecurrentOne := RecurrentOne) →
      TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
        (RecurrentTwo := RecurrentTwo) → Prop}
  {semanticInitialOne : RecurrentOne}
  {semanticInitialTwo : RecurrentTwo}
  {semanticNoRecvOne : RecurrentOne → In₁ → RecurrentOne × Out₁}
  {semanticNoRecvTwo : RecurrentTwo → In₂ → RecurrentTwo × Out₂}
  {semanticOpenRecvOne : RecurrentOne → In₁ → RecurrentTwo → In₂ →
    RecurrentOne × Out₁}
  {semanticOpenRecvTwo : RecurrentTwo → In₂ → RecurrentOne → In₁ →
    RecurrentTwo × Out₂}
  {semanticClose : RecurrentOne → In₁ → RecurrentTwo → In₂ →
    RecurrentOne × RecurrentTwo}
  {JointRep :
    OneControl (SharedOne := SharedOne) (PayloadOne := PayloadOne)
        (RecurrentOne := RecurrentOne) →
      TwoControl (SharedTwo := SharedTwo) (PayloadTwo := PayloadTwo)
        (RecurrentTwo := RecurrentTwo) →
      RecurrentOne → RecurrentTwo → Prop}

/-- Lift a genuinely joint representation simulation to the existing
selected-control trace interface. -/
def toExactClosingSelectedTraceLaws
    (laws : DeferredJointRelationalSimulationLaws initialOne initialTwo
      noRecvOne noRecvTwo openRecvOne openRecvTwo close Rel semanticInitialOne
      semanticInitialTwo semanticNoRecvOne semanticNoRecvTwo
      semanticOpenRecvOne semanticOpenRecvTwo semanticClose JointRep)
    (SemanticSelected : RecurrentOne → RecurrentTwo → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (semanticTrace : ExactClosingSelectedTraceLaws semanticInitialOne
      semanticInitialTwo semanticNoRecvOne semanticNoRecvTwo
      semanticOpenRecvOne semanticOpenRecvTwo semanticClose (fun _ _ ↦ True)
      SemanticSelected env expectedOutputOne expectedOutputTwo) :
    ExactClosingSelectedTraceLaws initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close Rel
      (DeferredJointRelationalSelected JointRep SemanticSelected) env
      expectedOutputOne expectedOutputTwo where
  initial := ⟨semanticInitialOne, semanticInitialTwo, laws.initial,
    semanticTrace.initial⟩
  strictRight := by
    intro n one two hrel hselected hgraph
    rcases hselected with ⟨semanticOne, semanticTwo, hrep, hsemantic⟩
    have hsim := laws.strictRight one (env n).inputOne two (env n).inputTwo
      semanticOne semanticTwo hrel hrep
    have hnext := semanticTrace.strictRight n semanticOne semanticTwo trivial
      hsemantic hgraph
    exact ⟨
      ⟨(semanticNoRecvOne semanticOne (env n).inputOne).1,
        (semanticOpenRecvTwo semanticTwo (env n).inputTwo semanticOne
          (env n).inputOne).1, hsim.1, hnext.1⟩,
      hsim.2.1.trans hnext.2.1,
      hsim.2.2.trans hnext.2.2⟩
  strictLeft := by
    intro n one two hrel hselected hgraph
    rcases hselected with ⟨semanticOne, semanticTwo, hrep, hsemantic⟩
    have hsim := laws.strictLeft one (env n).inputOne two (env n).inputTwo
      semanticOne semanticTwo hrel hrep
    have hnext := semanticTrace.strictLeft n semanticOne semanticTwo trivial
      hsemantic hgraph
    exact ⟨
      ⟨(semanticOpenRecvOne semanticOne (env n).inputOne semanticTwo
          (env n).inputTwo).1,
        (semanticNoRecvTwo semanticTwo (env n).inputTwo).1, hsim.1,
        hnext.1⟩,
      hsim.2.1.trans hnext.2.1,
      hsim.2.2.trans hnext.2.2⟩
  both := by
    intro n one two hrel hselected hgraph
    rcases hselected with ⟨semanticOne, semanticTwo, hrep, hsemantic⟩
    have hsim := laws.both one (env n).inputOne two (env n).inputTwo
      semanticOne semanticTwo hrel hrep
    have hnext := semanticTrace.both n semanticOne semanticTwo trivial
      hsemantic hgraph
    exact ⟨
      ⟨(semanticClose semanticOne (env n).inputOne semanticTwo
          (env n).inputTwo).1,
        (semanticClose semanticOne (env n).inputOne semanticTwo
          (env n).inputTwo).2, hsim.1, hnext.1⟩,
      hsim.2.1.trans hnext.2.1,
      hsim.2.2.trans hnext.2.2⟩

end DeferredJointRelationalSimulationLaws

/-! ## One-arrow dependent-bank consumption -/

namespace FiniteDeferredExactClosingFamily

variable {Key : Type k}
variable
  (family : FiniteDeferredExactClosingFamily.{u, v, x, y, k, a, b, c, d, e, f}
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) Key)

noncomputable section

/-- A relational transient proof in one deferred fibre feeds directly through
the fixed-fibre bank adapter to the executable literal-cross Mealy trace. -/
noncomputable def bankMealyTraceInvariant_of_relational_fibre
    [Fintype Key]
    (key : Key)
    (semanticInitialOne : family.RecurrentOne key)
    (semanticInitialTwo : family.RecurrentTwo key)
    (semanticNoRecvOne : family.RecurrentOne key → In₁ →
      family.RecurrentOne key × Out₁)
    (semanticNoRecvTwo : family.RecurrentTwo key → In₂ →
      family.RecurrentTwo key × Out₂)
    (semanticOpenRecvOne : family.RecurrentOne key → In₁ →
      family.RecurrentTwo key → In₂ → family.RecurrentOne key × Out₁)
    (semanticOpenRecvTwo : family.RecurrentTwo key → In₂ →
      family.RecurrentOne key → In₁ → family.RecurrentTwo key × Out₂)
    (semanticClose : family.RecurrentOne key → In₁ →
      family.RecurrentTwo key → In₂ →
        family.RecurrentOne key × family.RecurrentTwo key)
    (PendingRepOne : DeferredMemberControl (family.SharedOne key)
      (family.PayloadOne key) → family.RecurrentOne key → Prop)
    (PendingRepTwo : DeferredMemberControl (family.SharedTwo key)
      (family.PayloadTwo key) → family.RecurrentTwo key → Prop)
    (SemanticSelected : family.RecurrentOne key →
      family.RecurrentTwo key → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (simulation : DeferredRelationalSimulationLaws
      (family.initialOne key) (family.initialTwo key)
      (deferredOrRecurrentNoRecv (family.pendingStepOne key)
        (family.recurrentStepOne key))
      (deferredOrRecurrentNoRecv (family.pendingStepTwo key)
        (family.recurrentStepTwo key))
      (family.openRecvOne key) (family.openRecvTwo key) (family.close key)
      (family.Rel key) semanticInitialOne semanticInitialTwo semanticNoRecvOne
      semanticNoRecvTwo semanticOpenRecvOne semanticOpenRecvTwo semanticClose
      PendingRepOne PendingRepTwo)
    (semanticTrace : ExactClosingSelectedTraceLaws semanticInitialOne
      semanticInitialTwo semanticNoRecvOne semanticNoRecvTwo
      semanticOpenRecvOne semanticOpenRecvTwo semanticClose (fun _ _ ↦ True)
      SemanticSelected env expectedOutputOne expectedOutputTwo) :
    (family.toExactClosingBlindFamily.base.bankPairedMealyController key
      ).LiteralCrossMealyTraceInvariant env :=
  family.bankMealyTraceInvariant_of_fibre key
    (DeferredRelationalSelected PendingRepOne PendingRepTwo SemanticSelected)
    env expectedOutputOne expectedOutputTwo
      (simulation.toExactClosingSelectedTraceLaws SemanticSelected env
        expectedOutputOne expectedOutputTwo semanticTrace)

/-- Joint-representation variant of the bank endpoint.  It imposes no
endpointwise determinacy: the two runtime controls together may pin the one
semantic recurrent pair. -/
noncomputable def bankMealyTraceInvariant_of_joint_relational_fibre
    [Fintype Key]
    (key : Key)
    (semanticInitialOne : family.RecurrentOne key)
    (semanticInitialTwo : family.RecurrentTwo key)
    (semanticNoRecvOne : family.RecurrentOne key → In₁ →
      family.RecurrentOne key × Out₁)
    (semanticNoRecvTwo : family.RecurrentTwo key → In₂ →
      family.RecurrentTwo key × Out₂)
    (semanticOpenRecvOne : family.RecurrentOne key → In₁ →
      family.RecurrentTwo key → In₂ → family.RecurrentOne key × Out₁)
    (semanticOpenRecvTwo : family.RecurrentTwo key → In₂ →
      family.RecurrentOne key → In₁ → family.RecurrentTwo key × Out₂)
    (semanticClose : family.RecurrentOne key → In₁ →
      family.RecurrentTwo key → In₂ →
        family.RecurrentOne key × family.RecurrentTwo key)
    (JointRep :
      DeferredOrRecurrent (family.SharedOne key) (family.PayloadOne key)
          (family.RecurrentOne key) →
        DeferredOrRecurrent (family.SharedTwo key) (family.PayloadTwo key)
          (family.RecurrentTwo key) →
        family.RecurrentOne key → family.RecurrentTwo key → Prop)
    (SemanticSelected : family.RecurrentOne key →
      family.RecurrentTwo key → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (simulation : DeferredJointRelationalSimulationLaws
      (family.initialOne key) (family.initialTwo key)
      (deferredOrRecurrentNoRecv (family.pendingStepOne key)
        (family.recurrentStepOne key))
      (deferredOrRecurrentNoRecv (family.pendingStepTwo key)
        (family.recurrentStepTwo key))
      (family.openRecvOne key) (family.openRecvTwo key) (family.close key)
      (family.Rel key) semanticInitialOne semanticInitialTwo semanticNoRecvOne
      semanticNoRecvTwo semanticOpenRecvOne semanticOpenRecvTwo semanticClose
      JointRep)
    (semanticTrace : ExactClosingSelectedTraceLaws semanticInitialOne
      semanticInitialTwo semanticNoRecvOne semanticNoRecvTwo
      semanticOpenRecvOne semanticOpenRecvTwo semanticClose (fun _ _ ↦ True)
      SemanticSelected env expectedOutputOne expectedOutputTwo) :
    (family.toExactClosingBlindFamily.base.bankPairedMealyController key
      ).LiteralCrossMealyTraceInvariant env :=
  family.bankMealyTraceInvariant_of_fibre key
    (DeferredJointRelationalSelected JointRep SemanticSelected) env
    expectedOutputOne expectedOutputTwo
      (simulation.toExactClosingSelectedTraceLaws SemanticSelected env
        expectedOutputOne expectedOutputTwo semanticTrace)

end

end FiniteDeferredExactClosingFamily

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
