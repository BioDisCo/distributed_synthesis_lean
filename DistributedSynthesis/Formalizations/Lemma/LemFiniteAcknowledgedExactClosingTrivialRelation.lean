/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredFreshReceive

/-!
# Trivial relay relation for deferred exact closing

The exact-closing relay relation is used only to show that resolving an old
acknowledged fork leaves a pair on which the next local handler is defined.
The model's semantic occurrence invariant need not be duplicated there: it
belongs in the indexed `Selected` predicate of the trace proof.

When every total handler immediately produces another well-typed pair, the
constant-true relation is therefore sufficient.  This file packages that
structural fact and combines it with fresh false/true re-encapsulation.  It
does not weaken the later selected-trace obligations.

No executable map receives a graph, orientation, hierarchy side, leader bit,
strict-leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂ a b c d e f

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Control₁ : Type c₁} {Control₂ : Type c₂}

/-- Every total exact-close handler preserves the constant-true relation. -/
def exactClosingRelationLaws_true
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂) :
    ExactClosingRelationLaws initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close (fun _ _ ↦ True) where
  initial := trivial
  strictRight := by
    intro one inputOne two inputTwo hrel
    trivial
  strictLeft := by
    intro one inputOne two inputTwo hrel
    trivial
  both := by
    intro one inputOne two inputTwo hrel
    trivial

variable {SharedOne : Type a} {PayloadOne : Type b} {RecurrentOne : Type c}
variable {SharedTwo : Type d} {PayloadTwo : Type e} {RecurrentTwo : Type f}

/-- Build the complete deferred exact-closing law bundle when semantic
coupling is carried by the later selected trace rather than by `Rel`. -/
def deferredExactClosingForkLaws_true
    (initialOne : DeferredOrRecurrent SharedOne PayloadOne RecurrentOne)
    (initialTwo : DeferredOrRecurrent SharedTwo PayloadTwo RecurrentTwo)
    (pendingStepOne :
      Bool → SharedOne → In₁ → SharedOne × Out₁)
    (pendingLawsOne : DeferredMemberStepLaws pendingStepOne)
    (recurrentStepOne :
      RecurrentOne → In₁ → RecurrentOne × Out₁)
    (pendingStepTwo :
      Bool → SharedTwo → In₂ → SharedTwo × Out₂)
    (pendingLawsTwo : DeferredMemberStepLaws pendingStepTwo)
    (recurrentStepTwo :
      RecurrentTwo → In₂ → RecurrentTwo × Out₂)
    (openRecvOne :
      DeferredOrRecurrent SharedOne PayloadOne RecurrentOne → In₁ →
        DeferredOrRecurrent SharedTwo PayloadTwo RecurrentTwo → In₂ →
          DeferredOrRecurrent SharedOne PayloadOne RecurrentOne × Out₁)
    (openRecvTwo :
      DeferredOrRecurrent SharedTwo PayloadTwo RecurrentTwo → In₂ →
        DeferredOrRecurrent SharedOne PayloadOne RecurrentOne → In₁ →
          DeferredOrRecurrent SharedTwo PayloadTwo RecurrentTwo × Out₂)
    (close :
      DeferredOrRecurrent SharedOne PayloadOne RecurrentOne → In₁ →
        DeferredOrRecurrent SharedTwo PayloadTwo RecurrentTwo → In₂ →
          DeferredOrRecurrent SharedOne PayloadOne RecurrentOne ×
            DeferredOrRecurrent SharedTwo PayloadTwo RecurrentTwo)
    (fresh : DeferredFreshReceiveLaws openRecvOne openRecvTwo close
      (fun _ _ ↦ True)) :
    DeferredExactClosingForkLaws initialOne initialTwo
      pendingStepOne recurrentStepOne pendingStepTwo recurrentStepTwo
      openRecvOne openRecvTwo close (fun _ _ ↦ True) where
  relation := exactClosingRelationLaws_true initialOne initialTwo
    (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
    (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
    openRecvOne openRecvTwo close
  pendingOne := pendingLawsOne
  pendingTwo := pendingLawsTwo
  receive := fresh

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
