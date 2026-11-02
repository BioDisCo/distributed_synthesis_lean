/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredFreshReceive
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDependentBank

/-!
# Finite dependent families from deferred exact-closing fibres

The concrete literal construction has one finite fibre for every retained
package key.  Inside a fibre, each endpoint is either a member of the fresh
shared pending table or an already recurrent control.  The generic deferred
receive theorem proves all blind-fork obligations from the two member-step
laws and the exact false/true re-encapsulation equations.

This file is the family-level adapter.  A caller supplies those data
pointwise in the finite key; the adapter produces the existing
`FiniteExactClosingBlindFamily`, ready for dependent banking and the Fin-5
acknowledgement relay.  There is no additional mathematical premise.

The key and the pending member are finite stored control.  No executable map
receives a graph, orientation, hierarchy side, leader bit, strict-leader bit,
history, or view.
-/

namespace DistributedSynthesis

universe u v x y k a b c d e f

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- A finite key-indexed collection of deferred exact-closing fibres.

The law field is deliberately the only proof field.  In particular,
arbitrary blind-depth coherence is not repeated at family level. -/
structure FiniteDeferredExactClosingFamily (Key : Type k) where
  SharedOne : Key → Type a
  PayloadOne : Key → Type b
  RecurrentOne : Key → Type c
  SharedTwo : Key → Type d
  PayloadTwo : Key → Type e
  RecurrentTwo : Key → Type f
  oneFinite : ∀ key,
    Fintype (DeferredOrRecurrent (SharedOne key) (PayloadOne key)
      (RecurrentOne key))
  twoFinite : ∀ key,
    Fintype (DeferredOrRecurrent (SharedTwo key) (PayloadTwo key)
      (RecurrentTwo key))
  initialOne : ∀ key,
    DeferredOrRecurrent (SharedOne key) (PayloadOne key) (RecurrentOne key)
  initialTwo : ∀ key,
    DeferredOrRecurrent (SharedTwo key) (PayloadTwo key) (RecurrentTwo key)
  pendingStepOne : ∀ key,
    Bool → SharedOne key → In₁ → SharedOne key × Out₁
  recurrentStepOne : ∀ key,
    RecurrentOne key → In₁ → RecurrentOne key × Out₁
  pendingStepTwo : ∀ key,
    Bool → SharedTwo key → In₂ → SharedTwo key × Out₂
  recurrentStepTwo : ∀ key,
    RecurrentTwo key → In₂ → RecurrentTwo key × Out₂
  openRecvOne : ∀ key,
    DeferredOrRecurrent (SharedOne key) (PayloadOne key) (RecurrentOne key) →
      In₁ →
      DeferredOrRecurrent (SharedTwo key) (PayloadTwo key) (RecurrentTwo key) →
      In₂ →
      DeferredOrRecurrent (SharedOne key) (PayloadOne key) (RecurrentOne key) ×
        Out₁
  openRecvTwo : ∀ key,
    DeferredOrRecurrent (SharedTwo key) (PayloadTwo key) (RecurrentTwo key) →
      In₂ →
      DeferredOrRecurrent (SharedOne key) (PayloadOne key) (RecurrentOne key) →
      In₁ →
      DeferredOrRecurrent (SharedTwo key) (PayloadTwo key) (RecurrentTwo key) ×
        Out₂
  close : ∀ key,
    DeferredOrRecurrent (SharedOne key) (PayloadOne key) (RecurrentOne key) →
      In₁ →
      DeferredOrRecurrent (SharedTwo key) (PayloadTwo key) (RecurrentTwo key) →
      In₂ →
      DeferredOrRecurrent (SharedOne key) (PayloadOne key) (RecurrentOne key) ×
        DeferredOrRecurrent (SharedTwo key) (PayloadTwo key) (RecurrentTwo key)
  Rel : ∀ key,
    DeferredOrRecurrent (SharedOne key) (PayloadOne key) (RecurrentOne key) →
      DeferredOrRecurrent (SharedTwo key) (PayloadTwo key) (RecurrentTwo key) →
      Prop
  laws : ∀ key,
    DeferredExactClosingForkLaws (initialOne key) (initialTwo key)
      (pendingStepOne key) (recurrentStepOne key)
      (pendingStepTwo key) (recurrentStepTwo key)
      (openRecvOne key) (openRecvTwo key) (close key) (Rel key)

namespace FiniteDeferredExactClosingFamily

variable {Key : Type k}
variable
  (family : FiniteDeferredExactClosingFamily.{u, v, x, y, k, a, b, c, d, e, f}
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      Key)

/-- Forget the deferred presentation and obtain the standard finite
exact-closing family. -/
noncomputable def toExactClosingFamily :
    FiniteExactClosingFamily (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂) Key where
  ControlOne key :=
    DeferredOrRecurrent (family.SharedOne key) (family.PayloadOne key)
      (family.RecurrentOne key)
  ControlTwo key :=
    DeferredOrRecurrent (family.SharedTwo key) (family.PayloadTwo key)
      (family.RecurrentTwo key)
  oneFinite := family.oneFinite
  twoFinite := family.twoFinite
  initialOne := family.initialOne
  initialTwo := family.initialTwo
  noRecvOne key := deferredOrRecurrentNoRecv
    (family.pendingStepOne key) (family.recurrentStepOne key)
  noRecvTwo key := deferredOrRecurrentNoRecv
    (family.pendingStepTwo key) (family.recurrentStepTwo key)
  openRecvOne := family.openRecvOne
  openRecvTwo := family.openRecvTwo
  close := family.close
  Rel := family.Rel
  laws key := (family.laws key).relation

/-- The complete blind family follows pointwise.  Its receive law is the
fresh false/true table equation and its no-receive law is the generic
deferred-member bisimulation. -/
noncomputable def toExactClosingBlindFamily :
    FiniteExactClosingBlindFamily (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂) Key where
  base := family.toExactClosingFamily
  BlindOne _ := DeferredOrRecurrentBlind
  BlindTwo _ := DeferredOrRecurrentBlind
  noRecvLaws key := (family.laws key).toExactClosingBlindForkLaws.noRecv
  receiveLaws key :=
    (family.laws key).toExactClosingBlindForkLaws.receive

@[simp] theorem toExactClosingBlindFamily_initialOne (key : Key) :
    family.toExactClosingBlindFamily.base.initialOne key =
      family.initialOne key :=
  rfl

@[simp] theorem toExactClosingBlindFamily_initialTwo (key : Key) :
    family.toExactClosingBlindFamily.base.initialTwo key =
      family.initialTwo key :=
  rfl

@[simp] theorem toExactClosingBlindFamily_noRecvOne (key : Key) :
    family.toExactClosingBlindFamily.base.noRecvOne key =
      deferredOrRecurrentNoRecv (family.pendingStepOne key)
        (family.recurrentStepOne key) :=
  rfl

@[simp] theorem toExactClosingBlindFamily_noRecvTwo (key : Key) :
    family.toExactClosingBlindFamily.base.noRecvTwo key =
      deferredOrRecurrentNoRecv (family.pendingStepTwo key)
        (family.recurrentStepTwo key) :=
  rfl

@[simp] theorem toExactClosingBlindFamily_openRecvOne (key : Key) :
    family.toExactClosingBlindFamily.base.openRecvOne key =
      family.openRecvOne key :=
  rfl

@[simp] theorem toExactClosingBlindFamily_openRecvTwo (key : Key) :
    family.toExactClosingBlindFamily.base.openRecvTwo key =
      family.openRecvTwo key :=
  rfl

@[simp] theorem toExactClosingBlindFamily_close (key : Key) :
    family.toExactClosingBlindFamily.base.close key = family.close key :=
  rfl

@[simp] theorem toExactClosingBlindFamily_rel (key : Key) :
    family.toExactClosingBlindFamily.base.Rel key = family.Rel key :=
  rfl

/-- Pointwise access to the complete law bundle with no family-level
reconstruction.  This is the handoff used by concrete trace proofs. -/
noncomputable def exactClosingBlindForkLaws (key : Key) :
    ExactClosingBlindForkLaws
      (family.toExactClosingBlindFamily.base.initialOne key)
      (family.toExactClosingBlindFamily.base.initialTwo key)
      (family.toExactClosingBlindFamily.base.noRecvOne key)
      (family.toExactClosingBlindFamily.base.noRecvTwo key)
      (family.toExactClosingBlindFamily.base.openRecvOne key)
      (family.toExactClosingBlindFamily.base.openRecvTwo key)
      (family.toExactClosingBlindFamily.base.close key)
      (family.toExactClosingBlindFamily.base.Rel key)
      (family.toExactClosingBlindFamily.BlindOne key)
      (family.toExactClosingBlindFamily.BlindTwo key) :=
  (family.laws key).toExactClosingBlindForkLaws

end FiniteDeferredExactClosingFamily

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
