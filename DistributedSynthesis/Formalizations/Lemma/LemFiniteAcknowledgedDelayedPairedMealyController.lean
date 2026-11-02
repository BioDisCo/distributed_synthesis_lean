/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedDelayedCarrier
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyController

/-!
# Paired Mealy controller carried by finite acknowledgement relays

This file is the generic executable shell for the occurrence-sensitive
delayed-bit construction.  Each endpoint stores a finite acknowledged relay.
A no-receive advances only that endpoint's current candidate(s) and preserves
its acknowledgement.  A receive resolves both delivered old relays, evaluates
one endpoint-local transition, and installs a fresh fork together with the
acknowledgement of the delivered partner fork.

The two receive functions have precisely the information available at their
respective endpoints.  In particular none of the maps below accepts a graph,
orientation, leader bit, strict-leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Control₁ : Type c₁} {Control₂ : Type c₂}

/-! ## The generic paired controller -/

/-- Assemble the two local acknowledgement relays as one finite paired Mealy
controller.

The receive transition at an endpoint returns the *next ambiguity fork* for
that endpoint and the output of the current physical round.  The old fork is
resolved before this transition is called by `recvReforkMealy`. -/
noncomputable def pairedMealyController
    [Fintype Control₁] [Fintype Control₂]
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (recvOne :
      Control₁ → In₁ → Control₂ → In₂ →
        FiniteDelayedFork Control₁ × Out₁)
    (recvTwo :
      Control₂ → In₂ → Control₁ → In₁ →
        FiniteDelayedFork Control₂ × Out₂) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ where
  OneControl := FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁
  TwoControl := FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := ⟨.known initialOne, none⟩
  initialTwo := ⟨.known initialTwo, none⟩
  noRecvOne := FiniteAcknowledgedDelayedCarrier.noRecvMealy noRecvOne
  noRecvTwo := FiniteAcknowledgedDelayedCarrier.noRecvMealy noRecvTwo
  recvOne := fun own ownInput partner deliveredInput ↦
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne own ownInput
      partner deliveredInput
  recvTwo := fun own ownInput partner deliveredInput ↦
    FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo own ownInput
      partner deliveredInput

/-! ## Definitional endpoint equations -/

@[simp] theorem pairedMealyController_initialOne
    [Fintype Control₁] [Fintype Control₂]
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (recvOne :
      Control₁ → In₁ → Control₂ → In₂ →
        FiniteDelayedFork Control₁ × Out₁)
    (recvTwo :
      Control₂ → In₂ → Control₁ → In₁ →
        FiniteDelayedFork Control₂ × Out₂) :
    (pairedMealyController initialOne initialTwo noRecvOne noRecvTwo recvOne
      recvTwo).initialOne = ⟨.known initialOne, none⟩ :=
  rfl

@[simp] theorem pairedMealyController_initialTwo
    [Fintype Control₁] [Fintype Control₂]
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (recvOne :
      Control₁ → In₁ → Control₂ → In₂ →
        FiniteDelayedFork Control₁ × Out₁)
    (recvTwo :
      Control₂ → In₂ → Control₁ → In₁ →
        FiniteDelayedFork Control₂ × Out₂) :
    (pairedMealyController initialOne initialTwo noRecvOne noRecvTwo recvOne
      recvTwo).initialTwo = ⟨.known initialTwo, none⟩ :=
  rfl

@[simp] theorem pairedMealyController_noRecvOne
    [Fintype Control₁] [Fintype Control₂]
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (recvOne :
      Control₁ → In₁ → Control₂ → In₂ →
        FiniteDelayedFork Control₁ × Out₁)
    (recvTwo :
      Control₂ → In₂ → Control₁ → In₁ →
        FiniteDelayedFork Control₂ × Out₂)
    (state : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (input : In₁) :
    (pairedMealyController initialOne initialTwo noRecvOne noRecvTwo recvOne
      recvTwo).noRecvOne state input =
        FiniteAcknowledgedDelayedCarrier.noRecvMealy noRecvOne state input :=
  rfl

@[simp] theorem pairedMealyController_noRecvTwo
    [Fintype Control₁] [Fintype Control₂]
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (recvOne :
      Control₁ → In₁ → Control₂ → In₂ →
        FiniteDelayedFork Control₁ × Out₁)
    (recvTwo :
      Control₂ → In₂ → Control₁ → In₁ →
        FiniteDelayedFork Control₂ × Out₂)
    (state : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (input : In₂) :
    (pairedMealyController initialOne initialTwo noRecvOne noRecvTwo recvOne
      recvTwo).noRecvTwo state input =
        FiniteAcknowledgedDelayedCarrier.noRecvMealy noRecvTwo state input :=
  rfl

@[simp] theorem pairedMealyController_recvOne
    [Fintype Control₁] [Fintype Control₂]
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (recvOne :
      Control₁ → In₁ → Control₂ → In₂ →
        FiniteDelayedFork Control₁ × Out₁)
    (recvTwo :
      Control₂ → In₂ → Control₁ → In₁ →
        FiniteDelayedFork Control₂ × Out₂)
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (ownInput : In₁)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (deliveredInput : In₂) :
    (pairedMealyController initialOne initialTwo noRecvOne noRecvTwo recvOne
      recvTwo).recvOne own ownInput partner deliveredInput =
        FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvOne own ownInput
          partner deliveredInput :=
  rfl

@[simp] theorem pairedMealyController_recvTwo
    [Fintype Control₁] [Fintype Control₂]
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (recvOne :
      Control₁ → In₁ → Control₂ → In₂ →
        FiniteDelayedFork Control₁ × Out₁)
    (recvTwo :
      Control₂ → In₂ → Control₁ → In₁ →
        FiniteDelayedFork Control₂ × Out₂)
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (ownInput : In₂)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (deliveredInput : In₁) :
    (pairedMealyController initialOne initialTwo noRecvOne noRecvTwo recvOne
      recvTwo).recvTwo own ownInput partner deliveredInput =
        FiniteAcknowledgedDelayedCarrier.recvReforkMealy recvTwo own ownInput
          partner deliveredInput :=
  rfl

/-! ## Simultaneous refork synchronization -/

/-- On a simultaneous receive, the two local handlers install the same fresh
occurrence ID.  This is an algebraic consequence of the symmetric `Fin 5`
selector, not a leader or orientation test. -/
theorem pairedMealyController_both_currentIds_eq
    [Fintype Control₁] [Fintype Control₂]
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (recvOne :
      Control₁ → In₁ → Control₂ → In₂ →
        FiniteDelayedFork Control₁ × Out₁)
    (recvTwo :
      Control₂ → In₂ → Control₁ → In₁ →
        FiniteDelayedFork Control₂ × Out₂)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (oneInput : In₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (twoInput : In₂) :
    ((pairedMealyController initialOne initialTwo noRecvOne noRecvTwo recvOne
      recvTwo).recvOne one oneInput two twoInput).1.currentId? =
      ((pairedMealyController initialOne initialTwo noRecvOne noRecvTwo recvOne
        recvTwo).recvTwo two twoInput one oneInput).1.currentId? := by
  simp only [pairedMealyController_recvOne, pairedMealyController_recvTwo,
    recvReforkMealy, currentId?_refork]
  exact congrArg some (freshId_comm one two)

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
