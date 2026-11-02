/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredMemberControl

/-!
# Fresh receive re-encapsulation for deferred exact closing

A receive at a new seam must not expose a recurrent/table fork to a blind
endpoint.  Instead its ordinary and exact continuations are re-encapsulated
as the false and true members of one pending shared control with one payload.
This file states precisely that local law and proves that it supplies the
blind-receive field of the acknowledged exact-close invariant.

The final bundle combines this re-encapsulation law with the semantic
relation laws and the generic pending/recurrent no-receive bisimulation.
Thus a concrete model only owes its relation preservation and the two fresh
receive equations; arbitrary blind depth is discharged generically.

The member is stored finite control selected later by acknowledgement.  No
map here receives a graph, orientation, hierarchy side, leader bit,
strict-leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y a b c d e f

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {SharedOne : Type a} {PayloadOne : Type b} {RecurrentOne : Type c}
variable {SharedTwo : Type d} {PayloadTwo : Type e} {RecurrentTwo : Type f}

private abbrev OneControl
    (Shared : Type a) (Payload : Type b) (Recurrent : Type c) :=
  DeferredOrRecurrent Shared Payload Recurrent

private abbrev TwoControl
    (Shared : Type d) (Payload : Type e) (Recurrent : Type f) :=
  DeferredOrRecurrent Shared Payload Recurrent

/-- At each endpoint, the ordinary receive branch and the exact joint-close
branch are the false/true members of one fresh pending shared state and
payload.  The two endpoints may use different shared and payload types. -/
structure DeferredFreshReceiveLaws
    (openRecvOne :
      OneControl SharedOne PayloadOne RecurrentOne → In₁ →
        TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
          OneControl SharedOne PayloadOne RecurrentOne × Out₁)
    (openRecvTwo :
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
        OneControl SharedOne PayloadOne RecurrentOne → In₁ →
          TwoControl SharedTwo PayloadTwo RecurrentTwo × Out₂)
    (close :
      OneControl SharedOne PayloadOne RecurrentOne → In₁ →
        TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
          OneControl SharedOne PayloadOne RecurrentOne ×
            TwoControl SharedTwo PayloadTwo RecurrentTwo)
    (Rel : OneControl SharedOne PayloadOne RecurrentOne →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → Prop) : Prop where
  one : ∀ one inputOne two inputTwo,
    Rel one two →
      ∃ shared : SharedOne, ∃ payload : PayloadOne,
        (openRecvOne one inputOne two inputTwo).1 =
            (.inl (false, shared, payload) :
              OneControl SharedOne PayloadOne RecurrentOne) ∧
          (close one inputOne two inputTwo).1 =
            (.inl (true, shared, payload) :
              OneControl SharedOne PayloadOne RecurrentOne)
  two : ∀ one inputOne two inputTwo,
    Rel one two →
      ∃ shared : SharedTwo, ∃ payload : PayloadTwo,
        (openRecvTwo two inputTwo one inputOne).1 =
            (.inl (false, shared, payload) :
              TwoControl SharedTwo PayloadTwo RecurrentTwo) ∧
          (close one inputOne two inputTwo).2 =
            (.inl (true, shared, payload) :
              TwoControl SharedTwo PayloadTwo RecurrentTwo)

namespace DeferredFreshReceiveLaws

variable
  {openRecvOne :
    OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
        OneControl SharedOne PayloadOne RecurrentOne × Out₁}
  {openRecvTwo :
    TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      OneControl SharedOne PayloadOne RecurrentOne → In₁ →
        TwoControl SharedTwo PayloadTwo RecurrentTwo × Out₂}
  {close :
    OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
        OneControl SharedOne PayloadOne RecurrentOne ×
          TwoControl SharedTwo PayloadTwo RecurrentTwo}
  {Rel : OneControl SharedOne PayloadOne RecurrentOne →
    TwoControl SharedTwo PayloadTwo RecurrentTwo → Prop}

/-- Fresh pending re-encapsulation is exactly the blind compatibility needed
by `ExactClosingBlindReceiveLaws`. -/
theorem toExactClosingBlindReceiveLaws
    (laws : DeferredFreshReceiveLaws openRecvOne openRecvTwo close Rel) :
    ExactClosingBlindReceiveLaws openRecvOne openRecvTwo close Rel
      (DeferredOrRecurrentBlind :
        OneControl SharedOne PayloadOne RecurrentOne →
          OneControl SharedOne PayloadOne RecurrentOne → Prop)
      (DeferredOrRecurrentBlind :
        TwoControl SharedTwo PayloadTwo RecurrentTwo →
          TwoControl SharedTwo PayloadTwo RecurrentTwo → Prop) where
  one := by
    intro one inputOne two inputTwo hrel
    obtain ⟨shared, payload, hopen, hclose⟩ :=
      laws.one one inputOne two inputTwo hrel
    rw [hopen, hclose]
    exact ⟨rfl, rfl⟩
  two := by
    intro one inputOne two inputTwo hrel
    obtain ⟨shared, payload, hopen, hclose⟩ :=
      laws.two one inputOne two inputTwo hrel
    rw [hopen, hclose]
    exact ⟨rfl, rfl⟩

end DeferredFreshReceiveLaws

/-! ## Complete law bundle with generic blind no-receive closure -/

/-- The model-facing obligations for a pending/recurrent exact-close family.
No blind no-receive field appears: it follows from the member step laws. -/
structure DeferredExactClosingForkLaws
    (initialOne : OneControl SharedOne PayloadOne RecurrentOne)
    (initialTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo)
    (pendingStepOne :
      Bool → SharedOne → In₁ → SharedOne × Out₁)
    (recurrentStepOne :
      RecurrentOne → In₁ → RecurrentOne × Out₁)
    (pendingStepTwo :
      Bool → SharedTwo → In₂ → SharedTwo × Out₂)
    (recurrentStepTwo :
      RecurrentTwo → In₂ → RecurrentTwo × Out₂)
    (openRecvOne :
      OneControl SharedOne PayloadOne RecurrentOne → In₁ →
        TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
          OneControl SharedOne PayloadOne RecurrentOne × Out₁)
    (openRecvTwo :
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
        OneControl SharedOne PayloadOne RecurrentOne → In₁ →
          TwoControl SharedTwo PayloadTwo RecurrentTwo × Out₂)
    (close :
      OneControl SharedOne PayloadOne RecurrentOne → In₁ →
        TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
          OneControl SharedOne PayloadOne RecurrentOne ×
            TwoControl SharedTwo PayloadTwo RecurrentTwo)
    (Rel : OneControl SharedOne PayloadOne RecurrentOne →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → Prop) : Prop where
  relation :
    ExactClosingRelationLaws initialOne initialTwo
      (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
      (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
      openRecvOne openRecvTwo close Rel
  pendingOne : DeferredMemberStepLaws pendingStepOne
  pendingTwo : DeferredMemberStepLaws pendingStepTwo
  receive : DeferredFreshReceiveLaws openRecvOne openRecvTwo close Rel

namespace DeferredExactClosingForkLaws

variable
  {initialOne : OneControl SharedOne PayloadOne RecurrentOne}
  {initialTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo}
  {pendingStepOne :
    Bool → SharedOne → In₁ → SharedOne × Out₁}
  {recurrentStepOne :
    RecurrentOne → In₁ → RecurrentOne × Out₁}
  {pendingStepTwo :
    Bool → SharedTwo → In₂ → SharedTwo × Out₂}
  {recurrentStepTwo :
    RecurrentTwo → In₂ → RecurrentTwo × Out₂}
  {openRecvOne :
    OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
        OneControl SharedOne PayloadOne RecurrentOne × Out₁}
  {openRecvTwo :
    TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      OneControl SharedOne PayloadOne RecurrentOne → In₁ →
        TwoControl SharedTwo PayloadTwo RecurrentTwo × Out₂}
  {close :
    OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
        OneControl SharedOne PayloadOne RecurrentOne ×
          TwoControl SharedTwo PayloadTwo RecurrentTwo}
  {Rel : OneControl SharedOne PayloadOne RecurrentOne →
    TwoControl SharedTwo PayloadTwo RecurrentTwo → Prop}

/-- Assemble the complete exact-close blind-fork laws.  The arbitrary-depth
no-receive proof is inherited from the generic pending/recurrent sum. -/
def toExactClosingBlindForkLaws
    (laws : DeferredExactClosingForkLaws initialOne initialTwo
      pendingStepOne recurrentStepOne pendingStepTwo recurrentStepTwo
      openRecvOne openRecvTwo close Rel) :
    ExactClosingBlindForkLaws initialOne initialTwo
      (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
      (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
      openRecvOne openRecvTwo close Rel
      (DeferredOrRecurrentBlind :
        OneControl SharedOne PayloadOne RecurrentOne →
          OneControl SharedOne PayloadOne RecurrentOne → Prop)
      (DeferredOrRecurrentBlind :
        TwoControl SharedTwo PayloadTwo RecurrentTwo →
          TwoControl SharedTwo PayloadTwo RecurrentTwo → Prop) where
  relation := laws.relation
  noRecv := {
    one := deferredOrRecurrentBlind_noRecv pendingStepOne laws.pendingOne
      recurrentStepOne
    two := deferredOrRecurrentBlind_noRecv pendingStepTwo laws.pendingTwo
      recurrentStepTwo }
  receive := laws.receive.toExactClosingBlindReceiveLaws

end DeferredExactClosingForkLaws

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
