/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalFreshHandlers
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalSelectedTrace

/-!
# Canonical exact closing without an ordinary recurrent phase

The positive literal construction keeps executing a shared finite table for
the whole homogeneous epoch.  At the next receive it installs another shared
table; it must not jump to an independently rationalized ordinary policy.

This file makes that discipline an invariant of the generic acknowledged
controller.  `DeferredControlIsPending` recognizes the table half of a
`DeferredOrRecurrent` control.  Canonical fresh handlers always return that
half, and a no-receive step cannot leave it.  Consequently an initially
pending canonical controller remains pending on every graph sequence.  The
ordinary recurrent functions are totalization data only and are unreachable
under the proved relation.

No executable map receives a graph, orientation, hierarchy side, leader bit,
strict-leader bit, history, or view.  The graph is inspected only by the
proof-side canonical trace.
-/

namespace DistributedSynthesis

universe u v x y a b c d e f

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {SharedOne : Type a} {PayloadOne : Type b} {RecurrentOne : Type c}
variable {SharedTwo : Type d} {PayloadTwo : Type e} {RecurrentTwo : Type f}

private abbrev OneControl
    (SharedOne : Type a) (PayloadOne : Type b) (RecurrentOne : Type c) :=
  DeferredOrRecurrent SharedOne PayloadOne RecurrentOne

private abbrev TwoControl
    (SharedTwo : Type d) (PayloadTwo : Type e) (RecurrentTwo : Type f) :=
  DeferredOrRecurrent SharedTwo PayloadTwo RecurrentTwo

/-! ## The pending-only invariant -/

/-- A deferred control is still executing its shared table. -/
def DeferredControlIsPending
    {Shared : Type a} {Payload : Type b} {Recurrent : Type c} :
    DeferredOrRecurrent Shared Payload Recurrent → Prop
  | .inl _ => True
  | .inr _ => False

@[simp] theorem deferredControlIsPending_inl
    {Shared : Type a} {Payload : Type b} {Recurrent : Type c}
    (pending : DeferredMemberControl Shared Payload) :
    DeferredControlIsPending
      (.inl pending : DeferredOrRecurrent Shared Payload Recurrent) :=
  trivial

@[simp] theorem not_deferredControlIsPending_inr
    {Shared : Type a} {Payload : Type b} {Recurrent : Type c}
    (recurrent : Recurrent) :
    ¬ DeferredControlIsPending
      (.inr recurrent : DeferredOrRecurrent Shared Payload Recurrent) := by
  simp [DeferredControlIsPending]

/-- Both endpoints are executing shared tables. -/
def DeferredPairIsPending
    (one : OneControl SharedOne PayloadOne RecurrentOne)
    (two : TwoControl SharedTwo PayloadTwo RecurrentTwo) : Prop :=
  DeferredControlIsPending one ∧ DeferredControlIsPending two

/-- A no-receive step preserves the table half of the sum. -/
theorem deferredOrRecurrentNoRecv_isPending
    {Shared : Type a} {Payload : Type b} {Recurrent : Type c}
    {Input : Type u} {Output : Type x}
    (pendingStep : Bool → Shared → Input → Shared × Output)
    (recurrentStep : Recurrent → Input → Recurrent × Output)
    (control : DeferredOrRecurrent Shared Payload Recurrent) (input : Input)
    (hpending : DeferredControlIsPending control) :
    DeferredControlIsPending
      (deferredOrRecurrentNoRecv pendingStep recurrentStep control input).1 := by
  cases control with
  | inl pending => trivial
  | inr recurrent => exact False.elim hpending

/-! ## Every unresolved relay candidate is pending -/

/-- A local acknowledged relay contains only controls satisfying `P`.

For a resolved relay this asks for `P` of its unique control.  For an
unresolved relay it asks for `P` of both meanings of the hidden bit.  The
acknowledgement metadata is deliberately irrelevant. -/
def CarrierAll
    {ForkId : Type u} {Control : Type v}
    (P : Control → Prop)
    (state : FiniteAcknowledgedDelayedCarrier ForkId Control) : Prop :=
  match state.current with
  | .known control => P control
  | .fork _ candidates =>
      P candidates.openControl ∧ P candidates.closedControl

@[simp] theorem carrierAll_known
    {ForkId : Type u} {Control : Type v}
    (P : Control → Prop) (control : Control)
    (ack : Option (ForkId × Bool)) :
    CarrierAll P ⟨.known control, ack⟩ ↔ P control :=
  Iff.rfl

@[simp] theorem carrierAll_fork
    {ForkId : Type u} {Control : Type v}
    (P : Control → Prop) (id : ForkId)
    (candidates : FiniteDelayedFork Control)
    (ack : Option (ForkId × Bool)) :
    CarrierAll P ⟨.fork id candidates, ack⟩ ↔
      P candidates.openControl ∧ P candidates.closedControl :=
  Iff.rfl

/-- Whichever meaning a delivered relay selects, it satisfies `P` when all
locally stored meanings do. -/
theorem carrierAll_resolvedControl
    {ForkId : Type u} {Control : Type v} {Delivered : Type x}
    [DecidableEq ForkId]
    (P : Control → Prop)
    (state : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (partner : FiniteAcknowledgedDelayedCarrier ForkId Delivered)
    (hall : CarrierAll P state) :
    P (resolvedControl state partner) := by
  rcases state with ⟨current, ack⟩
  cases current with
  | known control => exact hall
  | fork id candidates =>
      change P candidates.openControl ∧ P candidates.closedControl at hall
      cases hbit : resolutionBit
          (⟨.fork id candidates, ack⟩ :
            FiniteAcknowledgedDelayedCarrier ForkId Control) partner <;>
        simp [resolvedControl, hbit, FiniteDelayedFork.candidate, hall.1, hall.2]

/-- A graph-blind no-receive step advances every stored meaning inside the
same predicate. -/
theorem carrierAll_noRecvMealy
    {ForkId : Type u} {Control : Type v} {Input : Type x} {Output : Type y}
    (P : Control → Prop)
    (transition : Control → Input → Control × Output)
    (state : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (input : Input)
    (hstep : ∀ control, P control → P (transition control input).1)
    (hall : CarrierAll P state) :
    CarrierAll P (noRecvMealy transition state input).1 := by
  rcases state with ⟨current, ack⟩
  cases current with
  | known control => exact hstep control hall
  | fork id candidates =>
      exact ⟨hstep candidates.openControl hall.1,
        hstep candidates.closedControl hall.2⟩

/-- Reforking contains only `P`-controls exactly when both newly installed
meanings satisfy `P`. -/
@[simp] theorem carrierAll_refork
    {Control : Type u} {Delivered : Type v} {Next : Type x}
    (P : Next → Prop)
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (next : FiniteDelayedFork Next) :
    CarrierAll P (refork own partner next) ↔
      P next.openControl ∧ P next.closedControl :=
  Iff.rfl

/-- A receive/refork step preserves an arbitrary predicate as soon as the
two freshly computed meanings satisfy it. -/
theorem carrierAll_recvReforkMealy
    {Control : Type u} {Delivered : Type v}
    {Input : Type x} {DeliveredInput : Type y}
    {Next : Type a} {Output : Type b}
    (P : Next → Prop)
    (transition : Control → Input → Delivered → DeliveredInput →
      FiniteDelayedFork Next × Output)
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (input : Input)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (deliveredInput : DeliveredInput)
    (hnext :
      let next := transition (resolvedControl own partner) input
        (resolvedControl partner own) deliveredInput
      P next.1.openControl ∧ P next.1.closedControl) :
    CarrierAll P
      (recvReforkMealy transition own input partner deliveredInput).1 := by
  exact hnext

/-! ## Canonical fresh handlers preserve pending-only execution -/

variable
  (pendingStepOne : Bool → SharedOne → In₁ → SharedOne × Out₁)
  (recurrentStepOne : RecurrentOne → In₁ → RecurrentOne × Out₁)
  (pendingStepTwo : Bool → SharedTwo → In₂ → SharedTwo × Out₂)
  (recurrentStepTwo : RecurrentTwo → In₂ → RecurrentTwo × Out₂)
  (freshOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
    TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
    SharedOne × PayloadOne)
  (freshTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
    OneControl SharedOne PayloadOne RecurrentOne → In₁ →
    SharedTwo × PayloadTwo)
  (outputOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
    TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ → Out₁)
  (outputTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
    OneControl SharedOne PayloadOne RecurrentOne → In₁ → Out₂)

/-! ## The executable acknowledgement relays are pending-only -/

/-- Advancing an acknowledged relay without receiving preserves the stronger
statement that every stored interpretation remains in the shared-table half. -/
theorem deferredRelayNoRecv_allPending
    {Shared : Type a} {Payload : Type b} {Recurrent : Type c}
    {Input : Type u} {Output : Type x}
    (pendingStep : Bool → Shared → Input → Shared × Output)
    (recurrentStep : Recurrent → Input → Recurrent × Output)
    (state : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (DeferredOrRecurrent Shared Payload Recurrent))
    (input : Input)
    (hall : CarrierAll DeferredControlIsPending state) :
    CarrierAll DeferredControlIsPending
      (noRecvMealy
        (deferredOrRecurrentNoRecv pendingStep recurrentStep) state input).1 := by
  exact carrierAll_noRecvMealy DeferredControlIsPending
    (deferredOrRecurrentNoRecv pendingStep recurrentStep) state input
    (fun control hpending ↦
      deferredOrRecurrentNoRecv_isPending pendingStep recurrentStep control
        input hpending)
    hall

/-- Process one's canonical receive/refork stores two pending meanings,
independently of how either old relay is resolved. -/
theorem canonicalDeferredRecvOne_allPending
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (OneControl SharedOne PayloadOne RecurrentOne))
    (inputOne : In₁)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (TwoControl SharedTwo PayloadTwo RecurrentTwo))
    (inputTwo : In₂) :
    CarrierAll DeferredControlIsPending
      (recvReforkMealy
        (exactClosingRecvForkOne
          (canonicalDeferredOpenRecvOne freshOne outputOne)
          (canonicalDeferredClose freshOne freshTwo))
        own inputOne partner inputTwo).1 := by
  apply carrierAll_recvReforkMealy
  exact ⟨trivial, trivial⟩

/-- Process-two mirror of `canonicalDeferredRecvOne_allPending`. -/
theorem canonicalDeferredRecvTwo_allPending
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (TwoControl SharedTwo PayloadTwo RecurrentTwo))
    (inputTwo : In₂)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (OneControl SharedOne PayloadOne RecurrentOne))
    (inputOne : In₁) :
    CarrierAll DeferredControlIsPending
      (recvReforkMealy
        (exactClosingRecvForkTwo
          (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
          (canonicalDeferredClose freshOne freshTwo))
        own inputTwo partner inputOne).1 := by
  apply carrierAll_recvReforkMealy
  exact ⟨trivial, trivial⟩

/-- Strong runtime invariant for the two actual finite acknowledgement
relays: even dormant interpretations remain shared tables. -/
def DeferredRelayPairAllPending
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (OneControl SharedOne PayloadOne RecurrentOne))
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (TwoControl SharedTwo PayloadTwo RecurrentTwo)) : Prop :=
  CarrierAll DeferredControlIsPending one ∧
    CarrierAll DeferredControlIsPending two

@[simp] theorem deferredRelayPairAllPending_initial
    (initialOne : DeferredMemberControl SharedOne PayloadOne)
    (initialTwo : DeferredMemberControl SharedTwo PayloadTwo) :
    DeferredRelayPairAllPending
      (⟨.known (.inl initialOne), none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5)
          (OneControl SharedOne PayloadOne RecurrentOne))
      (⟨.known (.inl initialTwo), none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5)
          (TwoControl SharedTwo PayloadTwo RecurrentTwo)) :=
  ⟨trivial, trivial⟩

/-- Strict-right physical preservation: process one advances every old table
candidate and process two installs a fresh two-candidate table. -/
theorem deferredRelayPairAllPending_strictRight
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (OneControl SharedOne PayloadOne RecurrentOne))
    (inputOne : In₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (TwoControl SharedTwo PayloadTwo RecurrentTwo))
    (inputTwo : In₂)
    (hall : DeferredRelayPairAllPending one two) :
    DeferredRelayPairAllPending
      (noRecvMealy
        (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
        one inputOne).1
      (recvReforkMealy
        (exactClosingRecvForkTwo
          (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
          (canonicalDeferredClose freshOne freshTwo))
        two inputTwo one inputOne).1 := by
  exact ⟨
    deferredRelayNoRecv_allPending pendingStepOne recurrentStepOne one inputOne
      hall.1,
    canonicalDeferredRecvTwo_allPending freshOne freshTwo outputTwo two
      inputTwo one inputOne⟩

/-- Strict-left mirror. -/
theorem deferredRelayPairAllPending_strictLeft
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (OneControl SharedOne PayloadOne RecurrentOne))
    (inputOne : In₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (TwoControl SharedTwo PayloadTwo RecurrentTwo))
    (inputTwo : In₂)
    (hall : DeferredRelayPairAllPending one two) :
    DeferredRelayPairAllPending
      (recvReforkMealy
        (exactClosingRecvForkOne
          (canonicalDeferredOpenRecvOne freshOne outputOne)
          (canonicalDeferredClose freshOne freshTwo))
        one inputOne two inputTwo).1
      (noRecvMealy
        (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
        two inputTwo).1 := by
  exact ⟨
    canonicalDeferredRecvOne_allPending freshOne freshTwo outputOne one
      inputOne two inputTwo,
    deferredRelayNoRecv_allPending pendingStepTwo recurrentStepTwo two inputTwo
      hall.2⟩

/-- Simultaneous-receive preservation.  Both relays are replaced by fresh
pending-only forks. -/
theorem deferredRelayPairAllPending_both
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (OneControl SharedOne PayloadOne RecurrentOne))
    (inputOne : In₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (TwoControl SharedTwo PayloadTwo RecurrentTwo))
    (inputTwo : In₂) :
    DeferredRelayPairAllPending
      (recvReforkMealy
        (exactClosingRecvForkOne
          (canonicalDeferredOpenRecvOne freshOne outputOne)
          (canonicalDeferredClose freshOne freshTwo))
        one inputOne two inputTwo).1
      (recvReforkMealy
        (exactClosingRecvForkTwo
          (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
          (canonicalDeferredClose freshOne freshTwo))
        two inputTwo one inputOne).1 := by
  exact ⟨
    canonicalDeferredRecvOne_allPending freshOne freshTwo outputOne one
      inputOne two inputTwo,
    canonicalDeferredRecvTwo_allPending freshOne freshTwo outputTwo two
      inputTwo one inputOne⟩

/-! ## The actual relay trace never contains an ordinary candidate -/

/-- Proof-side recursion of the two *executable acknowledgement relays*.
Unlike `exactClosingSemanticPairTrace`, this retains fresh IDs,
acknowledgements, and both unresolved meanings. -/
noncomputable def canonicalDeferredRelayPairTrace
    (initialOne : DeferredMemberControl SharedOne PayloadOne)
    (initialTwo : DeferredMemberControl SharedTwo PayloadTwo)
    (env : EnvironmentSequence In₁ In₂) : Nat →
      FiniteAcknowledgedDelayedCarrier (Fin 5)
          (OneControl SharedOne PayloadOne RecurrentOne) ×
        FiniteAcknowledgedDelayedCarrier (Fin 5)
          (TwoControl SharedTwo PayloadTwo RecurrentTwo)
  | 0 =>
      (⟨.known (.inl initialOne), none⟩,
        ⟨.known (.inl initialTwo), none⟩)
  | n + 1 =>
      let prior := canonicalDeferredRelayPairTrace initialOne initialTwo env n
      match (env n).graph with
      | .right =>
          ((noRecvMealy
              (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
              prior.1 (env n).inputOne).1,
            (recvReforkMealy
              (exactClosingRecvForkTwo
                (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
                (canonicalDeferredClose freshOne freshTwo))
              prior.2 (env n).inputTwo prior.1 (env n).inputOne).1)
      | .left =>
          ((recvReforkMealy
              (exactClosingRecvForkOne
                (canonicalDeferredOpenRecvOne freshOne outputOne)
                (canonicalDeferredClose freshOne freshTwo))
              prior.1 (env n).inputOne prior.2 (env n).inputTwo).1,
            (noRecvMealy
              (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
              prior.2 (env n).inputTwo).1)
      | .both =>
          ((recvReforkMealy
              (exactClosingRecvForkOne
                (canonicalDeferredOpenRecvOne freshOne outputOne)
                (canonicalDeferredClose freshOne freshTwo))
              prior.1 (env n).inputOne prior.2 (env n).inputTwo).1,
            (recvReforkMealy
              (exactClosingRecvForkTwo
                (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
                (canonicalDeferredClose freshOne freshTwo))
              prior.2 (env n).inputTwo prior.1 (env n).inputOne).1)

/-- At every physical time, every live or dormant runtime interpretation is
still a shared-table control.  Hence the ordinary summand is unreachable not
only for the selected semantic trace, but in the real finite relay state. -/
theorem canonicalDeferredRelayPairTrace_allPending
    (initialOne : DeferredMemberControl SharedOne PayloadOne)
    (initialTwo : DeferredMemberControl SharedTwo PayloadTwo)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n,
      DeferredRelayPairAllPending
        (canonicalDeferredRelayPairTrace pendingStepOne recurrentStepOne
          pendingStepTwo recurrentStepTwo freshOne freshTwo outputOne
          outputTwo initialOne initialTwo env n).1
        (canonicalDeferredRelayPairTrace pendingStepOne recurrentStepOne
          pendingStepTwo recurrentStepTwo freshOne freshTwo outputOne
          outputTwo initialOne initialTwo env n).2 := by
  intro n
  induction n with
  | zero => exact deferredRelayPairAllPending_initial initialOne initialTwo
  | succ n ih =>
      rw [canonicalDeferredRelayPairTrace]
      split <;> rename_i hgraph
      · exact deferredRelayPairAllPending_strictRight pendingStepOne
          recurrentStepOne freshOne freshTwo outputTwo _ _ _ _ ih
      · exact deferredRelayPairAllPending_strictLeft pendingStepTwo
          recurrentStepTwo freshOne freshTwo outputOne _ _ _ _ ih
      · exact deferredRelayPairAllPending_both freshOne freshTwo outputOne
          outputTwo _ _ _ _

/-- The canonical handlers preserve the pending-only relation in all three
physical cases. -/
def canonicalDeferredPendingRelationLaws
    (initialOne : DeferredMemberControl SharedOne PayloadOne)
    (initialTwo : DeferredMemberControl SharedTwo PayloadTwo) :
    ExactClosingRelationLaws
      (.inl initialOne : OneControl SharedOne PayloadOne RecurrentOne)
      (.inl initialTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo)
      (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
      (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
      (canonicalDeferredOpenRecvOne freshOne outputOne)
      (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
      (canonicalDeferredClose freshOne freshTwo)
      (DeferredPairIsPending :
        OneControl SharedOne PayloadOne RecurrentOne →
          TwoControl SharedTwo PayloadTwo RecurrentTwo → Prop) where
  initial := ⟨trivial, trivial⟩
  strictRight := by
    intro one inputOne two inputTwo hpending
    exact ⟨
      deferredOrRecurrentNoRecv_isPending pendingStepOne recurrentStepOne one
        inputOne hpending.1,
      trivial⟩
  strictLeft := by
    intro one inputOne two inputTwo hpending
    exact ⟨trivial,
      deferredOrRecurrentNoRecv_isPending pendingStepTwo recurrentStepTwo two
        inputTwo hpending.2⟩
  both := by
    intro one inputOne two inputTwo hpending
    exact ⟨trivial, trivial⟩

/-- The canonical false/true re-encapsulation law is valid relative to the
strong pending-only relation, not merely the trivial relation. -/
def canonicalDeferredPendingFreshReceiveLaws :
    DeferredFreshReceiveLaws
      (canonicalDeferredOpenRecvOne freshOne outputOne)
      (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
      (canonicalDeferredClose freshOne freshTwo)
      (DeferredPairIsPending :
        OneControl SharedOne PayloadOne RecurrentOne →
          TwoControl SharedTwo PayloadTwo RecurrentTwo → Prop) where
  one := by
    intro one inputOne two inputTwo hrel
    exact ⟨(freshOne one inputOne two inputTwo).1,
      (freshOne one inputOne two inputTwo).2, rfl, rfl⟩
  two := by
    intro one inputOne two inputTwo hrel
    exact ⟨(freshTwo two inputTwo one inputOne).1,
      (freshTwo two inputTwo one inputOne).2, rfl, rfl⟩

/-- One-arrow law bundle for a controller whose related executions never use
the ordinary recurrent phase. -/
def canonicalDeferredPendingExactClosingForkLaws
    (initialOne : DeferredMemberControl SharedOne PayloadOne)
    (initialTwo : DeferredMemberControl SharedTwo PayloadTwo)
    (pendingLawsOne : DeferredMemberStepLaws pendingStepOne)
    (pendingLawsTwo : DeferredMemberStepLaws pendingStepTwo) :
    DeferredExactClosingForkLaws
      (.inl initialOne : OneControl SharedOne PayloadOne RecurrentOne)
      (.inl initialTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo)
      pendingStepOne recurrentStepOne pendingStepTwo recurrentStepTwo
      (canonicalDeferredOpenRecvOne freshOne outputOne)
      (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
      (canonicalDeferredClose freshOne freshTwo)
      (DeferredPairIsPending :
        OneControl SharedOne PayloadOne RecurrentOne →
          TwoControl SharedTwo PayloadTwo RecurrentTwo → Prop) where
  relation := canonicalDeferredPendingRelationLaws pendingStepOne
    recurrentStepOne pendingStepTwo recurrentStepTwo freshOne freshTwo
    outputOne outputTwo initialOne initialTwo
  pendingOne := pendingLawsOne
  pendingTwo := pendingLawsTwo
  receive := canonicalDeferredPendingFreshReceiveLaws freshOne freshTwo
    outputOne outputTwo

/-! ## The proof-side canonical trace never reaches ordinary controls -/

/-- Starting from two shared tables, the canonical exact-closing trace stays
in shared tables for every environment sequence. -/
theorem exactClosingSemanticPairTrace_pending
    (initialOne : DeferredMemberControl SharedOne PayloadOne)
    (initialTwo : DeferredMemberControl SharedTwo PayloadTwo)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n,
      DeferredPairIsPending
        (exactClosingSemanticPairTrace
          (.inl initialOne : OneControl SharedOne PayloadOne RecurrentOne)
          (.inl initialTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo)
          (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
          (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
          (canonicalDeferredOpenRecvOne freshOne outputOne)
          (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
          (canonicalDeferredClose freshOne freshTwo) env n).1
        (exactClosingSemanticPairTrace
          (.inl initialOne : OneControl SharedOne PayloadOne RecurrentOne)
          (.inl initialTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo)
          (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
          (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
          (canonicalDeferredOpenRecvOne freshOne outputOne)
          (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
          (canonicalDeferredClose freshOne freshTwo) env n).2 := by
  intro n
  let laws := canonicalDeferredPendingRelationLaws pendingStepOne
    recurrentStepOne pendingStepTwo recurrentStepTwo freshOne freshTwo
    outputOne outputTwo initialOne initialTwo
  induction n with
  | zero => exact laws.initial
  | succ n ih =>
      rw [exactClosingSemanticPairTrace]
      split <;> rename_i hgraph
      · exact laws.strictRight _ _ _ _ ih
      · exact laws.strictLeft _ _ _ _ ih
      · exact laws.both _ _ _ _ ih

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
