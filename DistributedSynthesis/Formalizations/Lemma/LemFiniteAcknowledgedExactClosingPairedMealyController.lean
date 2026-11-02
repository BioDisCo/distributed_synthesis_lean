/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedDelayedPairedMealyController

/-!
# Acknowledged delayed forks with one exact joint close

The occurrence-sensitive relay needs two candidate continuations at every
receive.  Its open continuation is computed by the ordinary local transition;
its closed continuation is an exact jointly selected pair.  This file packages
that recurring pattern once.

Both endpoint receive maps call the same `close` function with the arguments
in the same process-one/process-two order.  Consequently their closed controls
are definitionally the two projections of one joint value.  The construction
does not expose a graph, orientation, hierarchy side, leader bit, history, or
view to either executable endpoint.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Control₁ : Type c₁} {Control₂ : Type c₂}

/-! ## The two local forks -/

/-- Process one's receive fork.  The current output and open control come
from `openRecvOne`; only the closed control is replaced by the first
projection of the exact joint close. -/
noncomputable def exactClosingRecvForkOne
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (one : Control₁) (own : In₁) (two : Control₂) (delivered : In₂) :
    FiniteDelayedFork Control₁ × Out₁ :=
  let openResult := openRecvOne one own two delivered
  let closed := close one own two delivered
  (⟨openResult.1, closed.1⟩, openResult.2)

/-- Process-two mirror.  Notice that `close` is called in canonical
process-one/process-two order. -/
noncomputable def exactClosingRecvForkTwo
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (two : Control₂) (own : In₂) (one : Control₁) (delivered : In₁) :
    FiniteDelayedFork Control₂ × Out₂ :=
  let openResult := openRecvTwo two own one delivered
  let closed := close one delivered two own
  (⟨openResult.1, closed.2⟩, openResult.2)

@[simp] theorem exactClosingRecvForkOne_open
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (one : Control₁) (own : In₁) (two : Control₂) (delivered : In₂) :
    (exactClosingRecvForkOne openRecvOne close one own two delivered).1.openControl =
      (openRecvOne one own two delivered).1 :=
  rfl

@[simp] theorem exactClosingRecvForkOne_closed
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (one : Control₁) (own : In₁) (two : Control₂) (delivered : In₂) :
    (exactClosingRecvForkOne openRecvOne close one own two delivered).1.closedControl =
      (close one own two delivered).1 :=
  rfl

@[simp] theorem exactClosingRecvForkOne_output
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (one : Control₁) (own : In₁) (two : Control₂) (delivered : In₂) :
    (exactClosingRecvForkOne openRecvOne close one own two delivered).2 =
      (openRecvOne one own two delivered).2 :=
  rfl

@[simp] theorem exactClosingRecvForkTwo_open
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (two : Control₂) (own : In₂) (one : Control₁) (delivered : In₁) :
    (exactClosingRecvForkTwo openRecvTwo close two own one delivered).1.openControl =
      (openRecvTwo two own one delivered).1 :=
  rfl

@[simp] theorem exactClosingRecvForkTwo_closed
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (two : Control₂) (own : In₂) (one : Control₁) (delivered : In₁) :
    (exactClosingRecvForkTwo openRecvTwo close two own one delivered).1.closedControl =
      (close one delivered two own).2 :=
  rfl

@[simp] theorem exactClosingRecvForkTwo_output
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (two : Control₂) (own : In₂) (one : Control₁) (delivered : In₁) :
    (exactClosingRecvForkTwo openRecvTwo close two own one delivered).2 =
      (openRecvTwo two own one delivered).2 :=
  rfl

/-- The two endpoint-local closed branches reconstruct the one exact joint
close, not two independently selected controls. -/
theorem exactClosingRecvFork_closed_pair
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (one : Control₁) (inputOne : In₁)
    (two : Control₂) (inputTwo : In₂) :
    ((exactClosingRecvForkOne openRecvOne close one inputOne two inputTwo).1
        |>.closedControl,
      (exactClosingRecvForkTwo openRecvTwo close two inputTwo one inputOne).1
        |>.closedControl) =
      close one inputOne two inputTwo :=
  rfl

/-! ## Complete acknowledged controller -/

/-- Assemble the exact-close forks into the finite acknowledged relay. -/
noncomputable def exactClosingPairedMealyController
    [Fintype Control₁] [Fintype Control₂]
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  pairedMealyController initialOne initialTwo noRecvOne noRecvTwo
    (exactClosingRecvForkOne openRecvOne close)
    (exactClosingRecvForkTwo openRecvTwo close)

/-- The acknowledged controller inherits simultaneous occurrence-ID
synchronization from the generic relay. -/
theorem exactClosingPairedMealyController_both_currentIds_eq
    [Fintype Control₁] [Fintype Control₂]
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (inputOne : In₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (inputTwo : In₂) :
    ((exactClosingPairedMealyController initialOne initialTwo noRecvOne
      noRecvTwo openRecvOne openRecvTwo close).recvOne one inputOne two
        inputTwo).1.currentId? =
      ((exactClosingPairedMealyController initialOne initialTwo noRecvOne
        noRecvTwo openRecvOne openRecvTwo close).recvTwo two inputTwo one
          inputOne).1.currentId? := by
  exact pairedMealyController_both_currentIds_eq initialOne initialTwo
    noRecvOne noRecvTwo (exactClosingRecvForkOne openRecvOne close)
      (exactClosingRecvForkTwo openRecvTwo close) one inputOne two inputTwo

/-! ## Exact mutual-selection preservation -/

/-- A strict-right proof step advances process one locally and selects the
open process-two receive continuation.  The closed exact seam remains only
the dormant alternative of the fresh fork. -/
theorem exactClosing_pairSelects_strictRight
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (actualOne : Control₁) (actualTwo : Control₂)
    (inputOne : In₁) (inputTwo : In₂)
    (hselects : PairSelects one two actualOne actualTwo) :
    PairSelects
      (noRecvMealy noRecvOne one inputOne).1
      (refork two one
        (exactClosingRecvForkTwo openRecvTwo close actualTwo inputTwo
          actualOne inputOne).1)
      (noRecvOne actualOne inputOne).1
      (openRecvTwo actualTwo inputTwo actualOne inputOne).1 := by
  simpa [exactClosingRecvForkTwo] using
    (pairSelects_strictRight noRecvOne one two actualOne actualTwo inputOne
      (exactClosingRecvForkTwo openRecvTwo close actualTwo inputTwo actualOne
        inputOne).1 hselects)

/-- Strict-left mirror of `exactClosing_pairSelects_strictRight`. -/
theorem exactClosing_pairSelects_strictLeft
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (actualOne : Control₁) (actualTwo : Control₂)
    (inputOne : In₁) (inputTwo : In₂)
    (hselects : PairSelects one two actualOne actualTwo) :
    PairSelects
      (refork one two
        (exactClosingRecvForkOne openRecvOne close actualOne inputOne
          actualTwo inputTwo).1)
      (noRecvMealy noRecvTwo two inputTwo).1
      (openRecvOne actualOne inputOne actualTwo inputTwo).1
      (noRecvTwo actualTwo inputTwo).1 := by
  simpa [exactClosingRecvForkOne] using
    (pairSelects_strictLeft noRecvTwo one two actualOne actualTwo inputTwo
      (exactClosingRecvForkOne openRecvOne close actualOne inputOne actualTwo
        inputTwo).1 hselects)

/-- On a simultaneous receive the two fresh forks select the two projections
of the one exact joint close.  This is the anti-mosaic invariant needed by
the tagged product controller. -/
theorem exactClosing_pairSelects_both
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (inputOne : In₁) (inputTwo : In₂) :
    let actualOne := resolvedControl one two
    let actualTwo := resolvedControl two one
    PairSelects
      (refork one two
        (exactClosingRecvForkOne openRecvOne close actualOne inputOne
          actualTwo inputTwo).1)
      (refork two one
        (exactClosingRecvForkTwo openRecvTwo close actualTwo inputTwo
          actualOne inputOne).1)
      (close actualOne inputOne actualTwo inputTwo).1
      (close actualOne inputOne actualTwo inputTwo).2 := by
  dsimp only
  simpa [exactClosingRecvForkOne, exactClosingRecvForkTwo] using
    (pairSelects_both one two
      (exactClosingRecvForkOne openRecvOne close (resolvedControl one two)
        inputOne (resolvedControl two one) inputTwo).1
      (exactClosingRecvForkTwo openRecvTwo close (resolvedControl two one)
        inputTwo (resolvedControl one two) inputOne).1)

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
