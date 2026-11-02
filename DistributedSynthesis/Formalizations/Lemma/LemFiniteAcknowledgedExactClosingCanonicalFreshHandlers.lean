/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingTrivialRelation

/-!
# Canonical total handlers for a fresh deferred receive

A concrete receive computes two kinds of data from the old resolved local
controls and the current delivered inputs:

* the physical output emitted for the old occurrence; and
* one fresh shared table and payload for the new occurrence.

The ordinary receive stores the false member of that fresh value, while the
exact joint close stores its true member.  This file defines those three
handlers from a single pair of fresh-data functions.  Their false/true
re-encapsulation law is definitional, including on totalized unreachable
controls.

The functions are endpoint-local executable functions over finite controls.
No graph, orientation, hierarchy side, leader bit, strict-leader bit, history,
or view is supplied.
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

/-- Ordinary process-one receive: emit the old-occurrence output and install
the false member of the freshly computed process-one table. -/
def canonicalDeferredOpenRecvOne
    (freshOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      SharedOne × PayloadOne)
    (outputOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ → Out₁)
    (one : OneControl SharedOne PayloadOne RecurrentOne) (inputOne : In₁)
    (two : TwoControl SharedTwo PayloadTwo RecurrentTwo) (inputTwo : In₂) :
    OneControl SharedOne PayloadOne RecurrentOne × Out₁ :=
  let fresh := freshOne one inputOne two inputTwo
  (.inl (false, fresh.1, fresh.2), outputOne one inputOne two inputTwo)

/-- Process-two mirror. -/
def canonicalDeferredOpenRecvTwo
    (freshTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      SharedTwo × PayloadTwo)
    (outputTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      OneControl SharedOne PayloadOne RecurrentOne → In₁ → Out₂)
    (two : TwoControl SharedTwo PayloadTwo RecurrentTwo) (inputTwo : In₂)
    (one : OneControl SharedOne PayloadOne RecurrentOne) (inputOne : In₁) :
    TwoControl SharedTwo PayloadTwo RecurrentTwo × Out₂ :=
  let fresh := freshTwo two inputTwo one inputOne
  (.inl (false, fresh.1, fresh.2), outputTwo two inputTwo one inputOne)

/-- Exact simultaneous close.  Both projections call the same fresh-data
functions as their ordinary receive counterparts and store the true member. -/
def canonicalDeferredClose
    (freshOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      SharedOne × PayloadOne)
    (freshTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      SharedTwo × PayloadTwo)
    (one : OneControl SharedOne PayloadOne RecurrentOne) (inputOne : In₁)
    (two : TwoControl SharedTwo PayloadTwo RecurrentTwo) (inputTwo : In₂) :
    OneControl SharedOne PayloadOne RecurrentOne ×
      TwoControl SharedTwo PayloadTwo RecurrentTwo :=
  let freshOne' := freshOne one inputOne two inputTwo
  let freshTwo' := freshTwo two inputTwo one inputOne
  (.inl (true, freshOne'.1, freshOne'.2),
    .inl (true, freshTwo'.1, freshTwo'.2))

/-- The canonical handlers satisfy the fresh receive law for every totalized
control pair. -/
def canonicalDeferredFreshReceiveLaws
    (freshOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      SharedOne × PayloadOne)
    (freshTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      SharedTwo × PayloadTwo)
    (outputOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ → Out₁)
    (outputTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      OneControl SharedOne PayloadOne RecurrentOne → In₁ → Out₂) :
    DeferredFreshReceiveLaws
      (canonicalDeferredOpenRecvOne freshOne outputOne)
      (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
      (canonicalDeferredClose freshOne freshTwo)
      (fun _ _ ↦ True) where
  one := by
    intro one inputOne two inputTwo hrel
    exact ⟨(freshOne one inputOne two inputTwo).1,
      (freshOne one inputOne two inputTwo).2, rfl, rfl⟩
  two := by
    intro one inputOne two inputTwo hrel
    exact ⟨(freshTwo two inputTwo one inputOne).1,
      (freshTwo two inputTwo one inputOne).2, rfl, rfl⟩

/-- One-arrow complete law bundle for canonical fresh handlers. -/
def canonicalDeferredExactClosingForkLaws
    (initialOne : OneControl SharedOne PayloadOne RecurrentOne)
    (initialTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo)
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
    (freshOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      SharedOne × PayloadOne)
    (freshTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      SharedTwo × PayloadTwo)
    (outputOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ → Out₁)
    (outputTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      OneControl SharedOne PayloadOne RecurrentOne → In₁ → Out₂) :
    DeferredExactClosingForkLaws initialOne initialTwo
      pendingStepOne recurrentStepOne pendingStepTwo recurrentStepTwo
      (canonicalDeferredOpenRecvOne freshOne outputOne)
      (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
      (canonicalDeferredClose freshOne freshTwo) (fun _ _ ↦ True) :=
  deferredExactClosingForkLaws_true initialOne initialTwo pendingStepOne
    pendingLawsOne recurrentStepOne pendingStepTwo pendingLawsTwo
    recurrentStepTwo (canonicalDeferredOpenRecvOne freshOne outputOne)
      (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
      (canonicalDeferredClose freshOne freshTwo)
      (canonicalDeferredFreshReceiveLaws freshOne freshTwo outputOne outputTwo)

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
