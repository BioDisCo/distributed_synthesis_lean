/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDependentDeferredSelectionProduct
import DistributedSynthesis.Formalizations.Lemma.LemFiniteDependentHeterogeneousPreselection
import DistributedSynthesis.Formalizations.Lemma.LemFiniteDependentHeterogeneousPinnedPreselection

/-!
# A preselected dependent table discharges blind-bank output coherence

`FiniteDependentDeferredSelectionFamily` deliberately leaves one output law
open: independently chosen candidate controllers need not emit the same blind
output.  A `FiniteDependentHeterogeneousTable` is the constructive way to
avoid that premise.  It rationalizes all receiver obligations at once, before
projecting a member, so every projection has definitionally the same sender
control, transition, and output function.

This file connects the two interfaces.  It packages the projected controllers
as a deferred-selection family and proves that a pointwise synchronized Pi
bank stays synchronized through every finite prefix.  Hence its physical
blind output is coherent at every reached state.  The remaining model-facing
relation is only the selected-member alignment between this one shared table
and the informed current carrier; no equality between independently
rationalized lambdas remains.

No operation below receives a graph, hierarchy orientation, leader bit,
strict-leader bit, history, or semantic view.
-/

namespace DistributedSynthesis

universe k u v x y w i xi yi

noncomputable section

variable {Key : Type k} {RIn : Type u} {SIn : Type v}
variable {ROut : Key → Type x} {SOut : Type y}
variable {InformedInput : Type xi} {InformedOutput : Type yi}
variable [Inhabited Key] [Fintype Key] [DecidableEq Key]
variable [Inhabited RIn] [Inhabited SIn] [Fintype RIn] [Fintype SIn]
variable [DecidableEq RIn] [DecidableEq SIn]
variable [(key : Key) → Inhabited (ROut key)]
variable [(key : Key) → Fintype (ROut key)] [Fintype SOut]

namespace FiniteDependentHeterogeneousTable

variable
  {base : (key : Key) →
    BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
  {start : (key : Key) → (base key).State}

variable (table : FiniteDependentHeterogeneousTable base start)

/-- Turn the shared sender table into the blind half of a dependent deferred
selection family.  The model supplies only its informed state and transition.
Although the blind control is written as key-indexed, every key projection
has the same underlying `family.Control × Bool` type and transition. -/
noncomputable def deferredSelectionFamily
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput) :
    FiniteAcknowledgedDelayedCarrier.FiniteDependentDeferredSelectionFamily
      Key SIn InformedInput SOut InformedOutput where
  Blind key := (table.memberController key).Control
  Informed := Informed
  blindFinite key := (table.memberController key).controlFinite
  informedFinite := informedFinite
  blindStep key control input :=
    ((table.memberController key).step control input,
      ((table.memberController key).labelOf control).1 input)
  informedStep := informedStep

/-- A Pi bank is synchronized when every candidate contains the one shared
sender control.  The equality is well typed because member controls differ
only in their receiver projection, not in their control type. -/
def BlindBankSynchronized
    (bank : ∀ key : Key, (table.memberController key).Control) : Prop :=
  ∀ left right : Key, bank left = bank right

/-- Canonical shared initial bank. -/
def initialBlindBank :
    ∀ key : Key, (table.memberController key).Control :=
  fun key ↦ (table.memberController key).initial

section
omit [Inhabited Key] [Inhabited RIn] [Inhabited SIn] [(key : Key) → Inhabited (ROut key)]

@[simp] theorem initialBlindBank_synchronized :
    table.BlindBankSynchronized table.initialBlindBank := by
  intro left right
  rfl

/-- Pointwise advancement of the projected sender controllers preserves the
single shared state. -/
theorem blindAdvance_synchronized
    (bank : ∀ key : Key, (table.memberController key).Control)
    (input : SIn) (hsync : table.BlindBankSynchronized bank) :
    table.BlindBankSynchronized (fun key ↦
      (table.memberController key).step (bank key) input) := by
  intro left right
  change
    (table.memberController left).step (bank left) input =
      (table.memberController right).step (bank right) input
  rw [hsync left right]
  exact table.memberController_step_eq left right (bank right) input

/-- Preselection turns state synchronization into the precise output premise
left open by the generic Pi-bank construction. -/
theorem blindOutputCoherentAt_of_synchronized
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput)
    (bank : ∀ key : Key, (table.memberController key).Control)
    (input : SIn) (hsync : table.BlindBankSynchronized bank) :
    (table.deferredSelectionFamily Informed informedFinite informedStep
      ).BlindOutputCoherentAt bank input := by
  intro left right
  change
    ((table.memberController left).labelOf (bank left)).1 input =
      ((table.memberController right).labelOf (bank right)).1 input
  rw [hsync left right]
  exact table.memberController_senderOutput_eq left right (bank right) input

/-- The blind-bank component of one full deferred-selection step stays
synchronized; the informed component and its hidden selected key are
irrelevant to this local fact. -/
theorem step_blind_synchronized
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput)
    (state :
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).DeferredSelectionState)
    (input : SIn × InformedInput)
    (hsync : table.BlindBankSynchronized state.1) :
    table.BlindBankSynchronized
      ((table.deferredSelectionFamily Informed informedFinite informedStep
        ).step state input).1 := by
  exact table.blindAdvance_synchronized state.1 input.1 hsync

/-- Synchronization, and therefore physical output coherence, survives an
arbitrary finite homogeneous prefix. -/
theorem run_blind_synchronized
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput)
    (state :
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).DeferredSelectionState)
    (inputs : List (SIn × InformedInput))
    (hsync : table.BlindBankSynchronized state.1) :
    table.BlindBankSynchronized
      ((table.deferredSelectionFamily Informed informedFinite informedStep
        ).run state inputs).1 := by
  induction inputs generalizing state with
  | nil => exact hsync
  | cons input inputs ih =>
      exact ih
        ((table.deferredSelectionFamily Informed informedFinite informedStep
          ).step state input)
        (table.step_blind_synchronized Informed informedFinite informedStep
          state input hsync)

theorem run_blindOutputCoherentAt
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput)
    (state :
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).DeferredSelectionState)
    (inputs : List (SIn × InformedInput))
    (nextInput : SIn)
    (hsync : table.BlindBankSynchronized state.1) :
    (table.deferredSelectionFamily Informed informedFinite informedStep
      ).BlindOutputCoherentAt
        ((table.deferredSelectionFamily Informed informedFinite informedStep
          ).run state inputs).1 nextInput := by
  apply table.blindOutputCoherentAt_of_synchronized Informed informedFinite
    informedStep
  exact table.run_blind_synchronized Informed informedFinite informedStep
    state inputs hsync

end

/-! ## Synchronization combined with the selected semantic relation -/

/-- The invariant consumed by an operational preselection carrier: all Pi
components share one sender state, while only the member named by the
informed Sigma has to satisfy the model-specific relation. -/
def SelectedSynchronizedRel
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput)
    (Rel : ∀ key,
      (table.memberController key).Control → Informed key → Prop)
    (state :
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).DeferredSelectionState) : Prop :=
  table.BlindBankSynchronized state.1 ∧
    (table.deferredSelectionFamily Informed informedFinite informedStep
      ).SelectedRel Rel state

section
omit [Inhabited Key] [Inhabited RIn] [Inhabited SIn] [(key : Key) → Inhabited (ROut key)]

/-- The combined invariant has no depth-dependent premise. -/
theorem selectedSynchronizedRel_step
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput)
    (Rel : ∀ key,
      (table.memberController key).Control → Informed key → Prop)
    (hstep : ∀ key blind informed blindInput informedInput,
      Rel key blind informed →
        Rel key
          ((table.deferredSelectionFamily Informed informedFinite informedStep
            ).blindStep key blind blindInput).1
          ((table.deferredSelectionFamily Informed informedFinite informedStep
            ).informedStep key informed informedInput blind blindInput).1)
    (state :
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).DeferredSelectionState)
    (input : SIn × InformedInput)
    (hinvariant : table.SelectedSynchronizedRel Informed informedFinite
      informedStep Rel state) :
    table.SelectedSynchronizedRel Informed informedFinite informedStep Rel
      ((table.deferredSelectionFamily Informed informedFinite informedStep
        ).step state input) := by
  constructor
  · exact table.step_blind_synchronized Informed informedFinite informedStep
      state input hinvariant.1
  · exact
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).selectedRel_step Rel hstep state input hinvariant.2

theorem selectedSynchronizedRel_run
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput)
    (Rel : ∀ key,
      (table.memberController key).Control → Informed key → Prop)
    (hstep : ∀ key blind informed blindInput informedInput,
      Rel key blind informed →
        Rel key
          ((table.deferredSelectionFamily Informed informedFinite informedStep
            ).blindStep key blind blindInput).1
          ((table.deferredSelectionFamily Informed informedFinite informedStep
            ).informedStep key informed informedInput blind blindInput).1)
    (state :
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).DeferredSelectionState)
    (inputs : List (SIn × InformedInput))
    (hinvariant : table.SelectedSynchronizedRel Informed informedFinite
      informedStep Rel state) :
    table.SelectedSynchronizedRel Informed informedFinite informedStep Rel
      ((table.deferredSelectionFamily Informed informedFinite informedStep
        ).run state inputs) := by
  induction inputs generalizing state with
  | nil => exact hinvariant
  | cons input inputs ih =>
      exact ih
        ((table.deferredSelectionFamily Informed informedFinite informedStep
          ).step state input)
        (table.selectedSynchronizedRel_step Informed informedFinite informedStep
          Rel hstep state input hinvariant)

/-- End-to-end local output theorem.  Any construction-time projection of
the executable blind table emits the selected informed candidate's output.
There is no `BlindOutputCoherentAt` hypothesis: simultaneous preselection and
the synchronized-state invariant have discharged it. -/
theorem blindNoRecv_output_eq_informed
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × SOut)
    (Rel : ∀ key,
      (table.memberController key).Control → Informed key → Prop)
    (outputKey : Key)
    (state :
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).DeferredSelectionState)
    (input : SIn × InformedInput)
    (hinvariant : table.SelectedSynchronizedRel Informed informedFinite
      informedStep Rel state)
    (houtput : ∀ key blind informed blindInput informedInput,
      Rel key blind informed →
        ((table.deferredSelectionFamily Informed informedFinite informedStep
          ).blindStep key blind blindInput).2 =
        ((table.deferredSelectionFamily Informed informedFinite informedStep
          ).informedStep key informed informedInput blind blindInput).2) :
    ((table.deferredSelectionFamily Informed informedFinite informedStep
      ).blindNoRecv outputKey state.1 input.1).2 =
      ((table.deferredSelectionFamily Informed informedFinite informedStep
        ).informedStep state.2.1 state.2.2 input.2
          (state.1 state.2.1) input.1).2 := by
  calc
    _ = ((table.deferredSelectionFamily Informed informedFinite informedStep
          ).blindStep state.2.1 (state.1 state.2.1) input.1).2 :=
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).blindNoRecv_output_eq_selected outputKey state.1 state.2 input.1
          (table.blindOutputCoherentAt_of_synchronized Informed informedFinite
            informedStep state.1 input.1 hinvariant.1)
    _ = _ := houtput state.2.1 (state.1 state.2.1) state.2.2 input.1 input.2
      hinvariant.2

end

end FiniteDependentHeterogeneousTable

/-! ## Root-pinned dependent preselection

The pinned construction has the same shared sender transition system, while
also preserving every member's complete semantic first record.  The small
adapter below makes the same no-post-hoc-coherence guarantee available to the
orientation-switch layer that consumes those root equations. -/

namespace FiniteDependentHeterogeneousPinnedTable

variable
  {base : (key : Key) →
    BlockRecordMonitor.{u, v, x, y, w} RIn SIn (ROut key) SOut}
  {start : (key : Key) → (base key).State}
  {receiver : (key : Key) → ReceiverBlockStrategy RIn SIn (ROut key)}
  {sender : SenderBlockStrategy SIn SOut}

variable
  (table : FiniteDependentHeterogeneousPinnedTable base start receiver sender)

noncomputable def deferredSelectionFamily
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput) :
    FiniteAcknowledgedDelayedCarrier.FiniteDependentDeferredSelectionFamily
      Key SIn InformedInput SOut InformedOutput where
  Blind key := (table.memberController key).Control
  Informed := Informed
  blindFinite key := (table.memberController key).controlFinite
  informedFinite := informedFinite
  blindStep key control input :=
    ((table.memberController key).step control input,
      ((table.memberController key).labelOf control).1 input)
  informedStep := informedStep

def BlindBankSynchronized
    (bank : ∀ key : Key, (table.memberController key).Control) : Prop :=
  ∀ left right : Key, bank left = bank right

def initialBlindBank :
    ∀ key : Key, (table.memberController key).Control :=
  fun key ↦ (table.memberController key).initial

section
omit [Inhabited Key] [Inhabited RIn] [Inhabited SIn]

@[simp] theorem initialBlindBank_synchronized :
    table.BlindBankSynchronized table.initialBlindBank := by
  intro left right
  rfl

theorem blindAdvance_synchronized
    (bank : ∀ key : Key, (table.memberController key).Control)
    (input : SIn) (hsync : table.BlindBankSynchronized bank) :
    table.BlindBankSynchronized (fun key ↦
      (table.memberController key).step (bank key) input) := by
  intro left right
  change
    (table.memberController left).step (bank left) input =
      (table.memberController right).step (bank right) input
  rw [hsync left right]
  rfl

theorem blindOutputCoherentAt_of_synchronized
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput)
    (bank : ∀ key : Key, (table.memberController key).Control)
    (input : SIn) (hsync : table.BlindBankSynchronized bank) :
    (table.deferredSelectionFamily Informed informedFinite informedStep
      ).BlindOutputCoherentAt bank input := by
  intro left right
  change
    ((table.memberController left).labelOf (bank left)).1 input =
      ((table.memberController right).labelOf (bank right)).1 input
  rw [hsync left right]
  rfl

end

section
omit [Inhabited Key] [Inhabited RIn] [Inhabited SIn]

theorem step_blind_synchronized
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput)
    (state :
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).DeferredSelectionState)
    (input : SIn × InformedInput)
    (hsync : table.BlindBankSynchronized state.1) :
    table.BlindBankSynchronized
      ((table.deferredSelectionFamily Informed informedFinite informedStep
        ).step state input).1 := by
  exact table.blindAdvance_synchronized state.1 input.1 hsync

theorem run_blind_synchronized
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × InformedOutput)
    (state :
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).DeferredSelectionState)
    (inputs : List (SIn × InformedInput))
    (hsync : table.BlindBankSynchronized state.1) :
    table.BlindBankSynchronized
      ((table.deferredSelectionFamily Informed informedFinite informedStep
        ).run state inputs).1 := by
  induction inputs generalizing state with
  | nil => exact hsync
  | cons input inputs ih =>
      exact ih
        ((table.deferredSelectionFamily Informed informedFinite informedStep
          ).step state input)
        (table.step_blind_synchronized Informed informedFinite informedStep
          state input hsync)

/-- Root pinning and arbitrary-prefix output coherence coexist in the same
finite table.  This is the interface used at a visible-anchor/hidden-input
switch: the pinned first-record theorem handles the boundary equation, and
this theorem handles every later blind output. -/
theorem blindNoRecv_output_eq_informed
    (Informed : Key → Type i)
    (informedFinite : ∀ key, Fintype (Informed key))
    (informedStep : ∀ key,
      Informed key → InformedInput →
        (table.memberController key).Control → SIn →
          Informed key × SOut)
    (Rel : ∀ key,
      (table.memberController key).Control → Informed key → Prop)
    (outputKey : Key)
    (state :
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).DeferredSelectionState)
    (input : SIn × InformedInput)
    (hsync : table.BlindBankSynchronized state.1)
    (hrel :
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).SelectedRel Rel state)
    (houtput : ∀ key blind informed blindInput informedInput,
      Rel key blind informed →
        ((table.deferredSelectionFamily Informed informedFinite informedStep
          ).blindStep key blind blindInput).2 =
        ((table.deferredSelectionFamily Informed informedFinite informedStep
          ).informedStep key informed informedInput blind blindInput).2) :
    ((table.deferredSelectionFamily Informed informedFinite informedStep
      ).blindNoRecv outputKey state.1 input.1).2 =
      ((table.deferredSelectionFamily Informed informedFinite informedStep
        ).informedStep state.2.1 state.2.2 input.2
          (state.1 state.2.1) input.1).2 := by
  calc
    _ = ((table.deferredSelectionFamily Informed informedFinite informedStep
          ).blindStep state.2.1 (state.1 state.2.1) input.1).2 :=
      (table.deferredSelectionFamily Informed informedFinite informedStep
        ).blindNoRecv_output_eq_selected outputKey state.1 state.2 input.1
          (table.blindOutputCoherentAt_of_synchronized Informed informedFinite
            informedStep state.1 input.1 hsync)
    _ = _ := houtput state.2.1 (state.1 state.2.1) state.2.2 input.1 input.2
      hrel

end

end FiniteDependentHeterogeneousPinnedTable

end

end DistributedSynthesis
