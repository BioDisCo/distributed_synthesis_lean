/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDependentPreselectedDeferredSelection

/-!
# Visible anchors outside, hidden candidates inside preselection

A dependent preselection table must not range over globally unrelated tags.
The executing blind process knows its current finite local anchor (for the
application: the common control and its own current input).  Only the hidden
partner input belongs in the simultaneous family quantified under that
anchor.

This file enforces that separation in the controller type.  It Sigma-packs
the visible anchor outside a root-pinned dependent table, retains a Pi bank
only over the hidden candidate type, and lifts the synchronization, arbitrary
prefix, selected-relation, and output theorems from
`LemFiniteDependentPreselectedDeferredSelection`.

Different anchors may use different sender tables and emit different outputs.
Within one anchor all hidden candidates are projections of one table.  No
transition receives the hidden key, a graph, orientation, hierarchy side,
leader bit, strict-leader bit, history, or semantic view.
-/

namespace DistributedSynthesis

universe a k u v x y w i xi

noncomputable section

variable {Anchor : Type a} {Key : Type k}
variable {RIn : Type u} {SIn : Type v}
variable {ROut : Anchor → Key → Type x} {SOut : Type y}
variable {InformedInput : Type xi}

variable [Fintype Anchor]
variable [Inhabited Key] [Fintype Key] [DecidableEq Key]
variable [Inhabited RIn] [Inhabited SIn] [Fintype RIn] [Fintype SIn]
variable [DecidableEq RIn] [DecidableEq SIn]
variable [(anchor : Anchor) → (key : Key) → Inhabited (ROut anchor key)]
variable [(anchor : Anchor) → (key : Key) → Fintype (ROut anchor key)]
variable [Fintype SOut]

namespace FiniteAnchorIndexedPinnedDeferredSelection

variable
  {base : (anchor : Anchor) → (key : Key) →
    BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn (ROut anchor key) SOut}
  {start : (anchor : Anchor) → (key : Key) →
    (base anchor key).State}
  {receiver : (anchor : Anchor) → (key : Key) →
    ReceiverBlockStrategy RIn SIn (ROut anchor key)}
  {sender : Anchor → SenderBlockStrategy SIn SOut}

variable
  (table : ∀ anchor : Anchor,
    DistributedSynthesis.FiniteDependentHeterogeneousPinnedTable (base anchor) (start anchor)
      (receiver anchor) (sender anchor))
  (Informed : Anchor → Key → Type i)
  (informedFinite : ∀ anchor key, Fintype (Informed anchor key))
  (informedStep : ∀ anchor key,
    Informed anchor key → InformedInput →
      ((table anchor).memberController key).Control → SIn →
        Informed anchor key × SOut)

/-- The per-visible-anchor Pi/Sigma family.  Its hidden key is never available
to the blind transition. -/
noncomputable abbrev localFamily (anchor : Anchor) :=
  (table anchor).deferredSelectionFamily (Informed anchor)
    (informedFinite anchor) (informedStep anchor)

/-- Executable state: a visible finite anchor and the corresponding local
preselection state.  There is no product over different anchors. -/
abbrev State := Σ anchor : Anchor, (localFamily table Informed informedFinite
  informedStep anchor).DeferredSelectionState

noncomputable instance :
    Fintype (State table Informed informedFinite informedStep) := by
  classical
  infer_instance

def step
    (state : State table Informed informedFinite informedStep)
    (input : SIn × InformedInput) :
    State table Informed informedFinite informedStep :=
  ⟨state.1,
    (localFamily table Informed informedFinite informedStep state.1).step
      state.2 input⟩

def run
    (state : State table Informed informedFinite informedStep) :
    List (SIn × InformedInput) →
      State table Informed informedFinite informedStep
  | [] => state
  | input :: tail =>
      run (step table Informed informedFinite informedStep state input) tail

omit [Fintype Anchor] [Inhabited Key] [Inhabited RIn] [Inhabited SIn] in
@[simp] theorem step_anchor
    (state : State table Informed informedFinite informedStep)
    (input : SIn × InformedInput) :
    (step table Informed informedFinite informedStep state input).1 =
      state.1 :=
  rfl

omit [Fintype Anchor] [Inhabited Key] [Inhabited RIn] [Inhabited SIn] in
@[simp] theorem run_anchor
    (state : State table Informed informedFinite informedStep)
    (inputs : List (SIn × InformedInput)) :
    (run table Informed informedFinite informedStep state inputs).1 =
      state.1 := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs ih =>
      exact ih (step table Informed informedFinite informedStep state input)

/-- Only candidates below the current visible anchor must share a control. -/
def Synchronized
    (state : State table Informed informedFinite informedStep) : Prop :=
  (table state.1).BlindBankSynchronized state.2.1

/-- Model relation only at the hidden candidate selected by the informed
Sigma, again within the same visible anchor. -/
def SelectedRel
    (Rel : ∀ anchor key,
      ((table anchor).memberController key).Control →
        Informed anchor key → Prop)
    (state : State table Informed informedFinite informedStep) : Prop :=
  (localFamily table Informed informedFinite informedStep state.1).SelectedRel
    (Rel state.1) state.2

def Invariant
    (Rel : ∀ anchor key,
      ((table anchor).memberController key).Control →
        Informed anchor key → Prop)
    (state : State table Informed informedFinite informedStep) : Prop :=
  Synchronized table Informed informedFinite informedStep state ∧
    SelectedRel table Informed informedFinite informedStep Rel state

section
omit [Fintype Anchor] [Inhabited Key] [Inhabited RIn] [Inhabited SIn]

theorem synchronized_step
    (state : State table Informed informedFinite informedStep)
    (input : SIn × InformedInput)
    (hsync : Synchronized table Informed informedFinite informedStep state) :
    Synchronized table Informed informedFinite informedStep
      (step table Informed informedFinite informedStep state input) := by
  exact (table state.1).step_blind_synchronized
    (Informed state.1) (informedFinite state.1) (informedStep state.1)
      state.2 input hsync

theorem synchronized_run
    (state : State table Informed informedFinite informedStep)
    (inputs : List (SIn × InformedInput))
    (hsync : Synchronized table Informed informedFinite informedStep state) :
    Synchronized table Informed informedFinite informedStep
      (run table Informed informedFinite informedStep state inputs) := by
  induction inputs generalizing state with
  | nil => exact hsync
  | cons input inputs ih =>
      exact ih (step table Informed informedFinite informedStep state input)
        (synchronized_step table Informed informedFinite informedStep state
          input hsync)

/-- Output coherence is local to the current visible anchor. -/
theorem blindOutputCoherentAt
    (state : State table Informed informedFinite informedStep)
    (input : SIn)
    (hsync : Synchronized table Informed informedFinite informedStep state) :
    (localFamily table Informed informedFinite informedStep state.1
      ).BlindOutputCoherentAt state.2.1 input := by
  exact (table state.1).blindOutputCoherentAt_of_synchronized
    (Informed state.1) (informedFinite state.1) (informedStep state.1)
      state.2.1 input hsync

theorem invariant_step
    (Rel : ∀ anchor key,
      ((table anchor).memberController key).Control →
        Informed anchor key → Prop)
    (hrelStep : ∀ anchor key blind informed blindInput informedInput,
      Rel anchor key blind informed →
        Rel anchor key
          ((localFamily table Informed informedFinite informedStep anchor
            ).blindStep key blind blindInput).1
          ((localFamily table Informed informedFinite informedStep anchor
            ).informedStep key informed informedInput blind blindInput).1)
    (state : State table Informed informedFinite informedStep)
    (input : SIn × InformedInput)
    (hinvariant :
      Invariant table Informed informedFinite informedStep Rel state) :
    Invariant table Informed informedFinite informedStep Rel
      (step table Informed informedFinite informedStep state input) := by
  constructor
  · exact synchronized_step table Informed informedFinite informedStep state
      input hinvariant.1
  · exact
      (localFamily table Informed informedFinite informedStep state.1
        ).selectedRel_step (Rel state.1) (hrelStep state.1) state.2 input
          hinvariant.2

theorem invariant_run
    (Rel : ∀ anchor key,
      ((table anchor).memberController key).Control →
        Informed anchor key → Prop)
    (hrelStep : ∀ anchor key blind informed blindInput informedInput,
      Rel anchor key blind informed →
        Rel anchor key
          ((localFamily table Informed informedFinite informedStep anchor
            ).blindStep key blind blindInput).1
          ((localFamily table Informed informedFinite informedStep anchor
            ).informedStep key informed informedInput blind blindInput).1)
    (state : State table Informed informedFinite informedStep)
    (inputs : List (SIn × InformedInput))
    (hinvariant :
      Invariant table Informed informedFinite informedStep Rel state) :
    Invariant table Informed informedFinite informedStep Rel
      (run table Informed informedFinite informedStep state inputs) := by
  induction inputs generalizing state with
  | nil => exact hinvariant
  | cons input inputs ih =>
      exact ih (step table Informed informedFinite informedStep state input)
        (invariant_step table Informed informedFinite informedStep Rel hrelStep
          state input hinvariant)

/-- Pick one construction-time output projection separately for each visible
anchor.  Under the invariant it equals the output of the hidden selected
candidate and hence the informed carrier's related candidate output. -/
theorem blindNoRecv_output_eq_informed
    (outputKey : Anchor → Key)
    (Rel : ∀ anchor key,
      ((table anchor).memberController key).Control →
        Informed anchor key → Prop)
    (houtput : ∀ anchor key blind informed blindInput informedInput,
      Rel anchor key blind informed →
        ((localFamily table Informed informedFinite informedStep anchor
          ).blindStep key blind blindInput).2 =
        ((localFamily table Informed informedFinite informedStep anchor
          ).informedStep key informed informedInput blind blindInput).2)
    (state : State table Informed informedFinite informedStep)
    (input : SIn × InformedInput)
    (hinvariant :
      Invariant table Informed informedFinite informedStep Rel state) :
    ((localFamily table Informed informedFinite informedStep state.1
      ).blindNoRecv (outputKey state.1) state.2.1 input.1).2 =
      ((localFamily table Informed informedFinite informedStep state.1
        ).informedStep state.2.2.1 state.2.2.2 input.2
          (state.2.1 state.2.2.1) input.1).2 := by
  exact (table state.1).blindNoRecv_output_eq_informed
    (Informed state.1) (informedFinite state.1) (informedStep state.1)
      (Rel state.1) (outputKey state.1) state.2 input hinvariant.1 hinvariant.2
        (houtput state.1)

end

end FiniteAnchorIndexedPinnedDeferredSelection

end

end DistributedSynthesis
