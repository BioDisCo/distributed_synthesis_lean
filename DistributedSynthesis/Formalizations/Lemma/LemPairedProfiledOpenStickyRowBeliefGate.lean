/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenStickyRowReceiptSplitTest

/-!
# Reachable-belief gate for sticky entry rows

The one-round pair test says exactly what a receiver needs: two represented
global states must carry rows produced by one and the same locally stored
receipt bit.  This file connects that pointwise statement to reachable local
beliefs.

The positive theorem is deliberately phrased through a local presentation.
If a proof-side sticky row factors through the receiver's actual finite local
control, then any two states in one reachable receiver belief have compatible
rows.  No leader, orientation, unique hidden state, or eventual recovery is
used.

The file also checks the tempting existing field `receivedOne/receivedTwo`.
Its value is indeed constant on the corresponding reachable belief, but it is
the receipt event of the *latest physical round*.  A strict continuation
overwrites it immediately.  Therefore it cannot be the sticky entry row.  The
remaining compiler invariant is precise: the active proof-side row must
factor through a separate receiver-local row bank which is retained on
continuations and reinstalled at reversals.
-/

namespace DistributedSynthesis

universe u v w x y a b k q p c₁ c₂

open DetParityAutomaton

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v}
variable [Fintype In₁] [Fintype In₂]
variable (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)

/-- The right-block row is homogeneous on every reachable process-two
belief, in the exact receipt-compatible sense used by the receiver pair
test. -/
def RightStickyRowBeliefCompatible
    (rightRow : G.State → PairedEntryRow) : Prop :=
  ∀ rounds left, left ∈ (G.beliefsAfter rounds).2 →
    ∀ right, right ∈ (G.beliefsAfter rounds).2 →
      DetParityAutomaton.PairedEntryRowsReceiverCompatible
        (rightRow left) (rightRow right)

/-- Left-block/process-one mirror. -/
def LeftStickyRowBeliefCompatible
    (leftRow : G.State → PairedEntryRow) : Prop :=
  ∀ rounds left, left ∈ (G.beliefsAfter rounds).1 →
    ∀ right, right ∈ (G.beliefsAfter rounds).1 →
      DetParityAutomaton.PairedEntryRowsReceiverCompatible
        (leftRow left) (leftRow right)

/-- Exact fail-fast witness against the right sticky-row belief law. -/
structure RightStickyRowBeliefCollision
    (rightRow : G.State → PairedEntryRow) where
  rounds : List (EnvironmentRound In₁ In₂)
  left : G.State
  right : G.State
  left_mem : left ∈ (G.beliefsAfter rounds).2
  right_mem : right ∈ (G.beliefsAfter rounds).2
  row_ne : rightRow left ≠ rightRow right

/-- Left mirror collision. -/
structure LeftStickyRowBeliefCollision
    (leftRow : G.State → PairedEntryRow) where
  rounds : List (EnvironmentRound In₁ In₂)
  left : G.State
  right : G.State
  left_mem : left ∈ (G.beliefsAfter rounds).1
  right_mem : right ∈ (G.beliefsAfter rounds).1
  row_ne : leftRow left ≠ leftRow right

/-- The right gate fails exactly when an unequal-row pair occurs in one
reachable process-two belief. -/
theorem rightStickyRowBeliefCompatible_iff_noCollision
    (rightRow : G.State → PairedEntryRow) :
    G.RightStickyRowBeliefCompatible rightRow ↔
      ¬ Nonempty (G.RightStickyRowBeliefCollision rightRow) := by
  constructor
  · intro hcompatible ⟨collision⟩
    exact collision.row_ne
      (DetParityAutomaton.pairedEntryRowsReceiverCompatible_eq
        (hcompatible collision.rounds collision.left collision.left_mem
          collision.right collision.right_mem))
  · intro hno rounds left hleft right hright
    rw [DetParityAutomaton.pairedEntryRowsReceiverCompatible_iff_eq]
    by_contra hne
    exact hno ⟨⟨rounds, left, right, hleft, hright, hne⟩⟩

/-- Left gate/collision equivalence. -/
theorem leftStickyRowBeliefCompatible_iff_noCollision
    (leftRow : G.State → PairedEntryRow) :
    G.LeftStickyRowBeliefCompatible leftRow ↔
      ¬ Nonempty (G.LeftStickyRowBeliefCollision leftRow) := by
  constructor
  · intro hcompatible ⟨collision⟩
    exact collision.row_ne
      (DetParityAutomaton.pairedEntryRowsReceiverCompatible_eq
        (hcompatible collision.rounds collision.left collision.left_mem
          collision.right collision.right_mem))
  · intro hno rounds left hleft right hright
    rw [DetParityAutomaton.pairedEntryRowsReceiverCompatible_iff_eq]
    by_contra hne
    exact hno ⟨⟨rounds, left, right, hleft, hright, hne⟩⟩

/-! ## The exact sufficient local recurrence invariant -/

variable {Out₁ : Type x} {Out₂ : Type y}
variable (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)

/-- If the right row is readable from the same genuinely local process-two
control that represents every state in the belief, the dangerous pair test
passes on every reachable belief. -/
theorem rightStickyRowBeliefCompatible_of_localControl
    (P : G.LocalPresentation outputOne outputTwo)
    (rightRow : G.State → PairedEntryRow)
    (storedRow : P.ControlTwo → PairedEntryRow)
    (hrow : ∀ {control state}, P.RepTwo control state →
      rightRow state = storedRow control) :
    G.RightStickyRowBeliefCompatible rightRow := by
  intro rounds left hleft right hright
  have hrep := LocalPresentation.controlsAfter_represent_beliefs
    G outputOne outputTwo P rounds
  have hleftRow := hrow (hrep.2 left hleft)
  have hrightRow := hrow (hrep.2 right hright)
  rw [DetParityAutomaton.pairedEntryRowsReceiverCompatible_iff_eq]
  exact hleftRow.trans hrightRow.symm

/-- Process-one/left-row mirror. -/
theorem leftStickyRowBeliefCompatible_of_localControl
    (P : G.LocalPresentation outputOne outputTwo)
    (leftRow : G.State → PairedEntryRow)
    (storedRow : P.ControlOne → PairedEntryRow)
    (hrow : ∀ {control state}, P.RepOne control state →
      leftRow state = storedRow control) :
    G.LeftStickyRowBeliefCompatible leftRow := by
  intro rounds left hleft right hright
  have hrep := LocalPresentation.controlsAfter_represent_beliefs
    G outputOne outputTwo P rounds
  have hleftRow := hrow (hrep.1 left hleft)
  have hrightRow := hrow (hrep.1 right hright)
  rw [DetParityAutomaton.pairedEntryRowsReceiverCompatible_iff_eq]
  exact hleftRow.trans hrightRow.symm

end FiniteGlobalRoundMachine

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Branch : Type b} {Bank : Type k} {Query : Type q} {Phase : Type p}
variable
  (controller : FinitePairedPhysicalController.{u, v, x, y, c₁, c₂}
    In₁ In₂ Out₁ Out₂)
variable
  (adapter : FiniteEpochQueryAdapter In₁ In₂ Branch Bank Query Phase
    controller)
variable (initialBranch : Branch)
variable (label : Branch → Option Bank)
variable (branchStep : Branch → Query → Branch)

noncomputable section

variable [Fintype In₁] [Fintype In₂]
variable [Fintype Branch] [Fintype Bank] [Fintype Query] [Fintype Phase]

private noncomputable abbrev PhysicalMachine :=
  finiteEpochPhysicalGlobalMachine controller adapter initialBranch label
    branchStep

/-! ## The latest receipt bit passes, but it is not sticky -/

/-- The process-two belief always agrees on the latest process-two receipt
event.  This follows from the honest graph ambiguity: `right` and `both` both
mean receive, while a no-receive event fixes `left`. -/
theorem finiteEpochPhysical_belief_receivedTwo_constant
    (rounds : List (EnvironmentRound In₁ In₂)) :
    ∃ received : Bool, ∀ state,
      state ∈ ((PhysicalMachine controller adapter initialBranch label
        branchStep).beliefsAfter rounds).2 →
        state.receivedTwo = received := by
  classical
  induction rounds using List.reverseRecOn with
  | nil =>
      refine ⟨false, ?_⟩
      intro state hstate
      simp [PhysicalMachine, finiteEpochPhysicalGlobalMachine,
        FiniteGlobalRoundMachine.beliefsAfter] at hstate
      have hstate' := Finset.mem_singleton.mp hstate
      subst state
      rfl
  | append_singleton rounds round ih =>
      rcases round with ⟨inputOne, inputTwo, graph⟩
      cases graph with
      | left =>
          refine ⟨false, ?_⟩
          intro state hstate
          simp only [FiniteGlobalRoundMachine.beliefsAfter,
            List.foldl_append, List.foldl_cons, List.foldl_nil,
            FiniteGlobalRoundMachine.beliefAdvance,
            FiniteGlobalRoundMachine.beliefNoRecvTwo,
            Finset.mem_filter, Finset.mem_univ, true_and] at hstate
          rcases hstate with ⟨source, _hsource, hidden, rfl⟩
          rfl
      | right =>
          refine ⟨true, ?_⟩
          intro state hstate
          simp only [FiniteGlobalRoundMachine.beliefsAfter,
            List.foldl_append, List.foldl_cons, List.foldl_nil,
            FiniteGlobalRoundMachine.beliefAdvance,
            FiniteGlobalRoundMachine.beliefRecvTwo,
            Finset.mem_filter, Finset.mem_univ, true_and] at hstate
          rcases hstate with ⟨source, _hself, _hother, hstep | hstep⟩
          · subst state
            rfl
          · subst state
            rfl
      | both =>
          refine ⟨true, ?_⟩
          intro state hstate
          simp only [FiniteGlobalRoundMachine.beliefsAfter,
            List.foldl_append, List.foldl_cons, List.foldl_nil,
            FiniteGlobalRoundMachine.beliefAdvance,
            FiniteGlobalRoundMachine.beliefRecvTwo,
            Finset.mem_filter, Finset.mem_univ, true_and] at hstate
          rcases hstate with ⟨source, _hself, _hother, hstep | hstep⟩
          · subst state
            rfl
          · subst state
            rfl

/-- Process-one latest-receipt mirror. -/
theorem finiteEpochPhysical_belief_receivedOne_constant
    (rounds : List (EnvironmentRound In₁ In₂)) :
    ∃ received : Bool, ∀ state,
      state ∈ ((PhysicalMachine controller adapter initialBranch label
        branchStep).beliefsAfter rounds).1 →
        state.receivedOne = received := by
  classical
  induction rounds using List.reverseRecOn with
  | nil =>
      refine ⟨false, ?_⟩
      intro state hstate
      simp [PhysicalMachine, finiteEpochPhysicalGlobalMachine,
        FiniteGlobalRoundMachine.beliefsAfter] at hstate
      have hstate' := Finset.mem_singleton.mp hstate
      subst state
      rfl
  | append_singleton rounds round ih =>
      rcases round with ⟨inputOne, inputTwo, graph⟩
      cases graph with
      | left =>
          refine ⟨true, ?_⟩
          intro state hstate
          simp only [FiniteGlobalRoundMachine.beliefsAfter,
            List.foldl_append, List.foldl_cons, List.foldl_nil,
            FiniteGlobalRoundMachine.beliefAdvance,
            FiniteGlobalRoundMachine.beliefRecvOne,
            Finset.mem_filter, Finset.mem_univ, true_and] at hstate
          rcases hstate with ⟨source, _hself, _hother, hstep | hstep⟩
          · subst state
            rfl
          · subst state
            rfl
      | right =>
          refine ⟨false, ?_⟩
          intro state hstate
          simp only [FiniteGlobalRoundMachine.beliefsAfter,
            List.foldl_append, List.foldl_cons, List.foldl_nil,
            FiniteGlobalRoundMachine.beliefAdvance,
            FiniteGlobalRoundMachine.beliefNoRecvOne,
            Finset.mem_filter, Finset.mem_univ, true_and] at hstate
          rcases hstate with ⟨source, _hsource, hidden, rfl⟩
          rfl
      | both =>
          refine ⟨true, ?_⟩
          intro state hstate
          simp only [FiniteGlobalRoundMachine.beliefsAfter,
            List.foldl_append, List.foldl_cons, List.foldl_nil,
            FiniteGlobalRoundMachine.beliefAdvance,
            FiniteGlobalRoundMachine.beliefRecvOne,
            Finset.mem_filter, Finset.mem_univ, true_and] at hstate
          rcases hstate with ⟨source, _hself, _hother, hstep | hstep⟩
          · subst state
            rfl
          · subst state
            rfl

/-- Thus the non-sticky latest receipt does pass the right pair test. -/
theorem finiteEpochPhysical_latestRightRow_beliefCompatible :
    (PhysicalMachine controller adapter initialBranch label branchStep
      ).RightStickyRowBeliefCompatible
        (fun state ↦ FirstEntryFinitePolicyFamilies.entryRowOfReceived
          state.receivedTwo) := by
  intro rounds left hleft right hright
  rcases finiteEpochPhysical_belief_receivedTwo_constant controller adapter
      initialBranch label branchStep rounds with ⟨received, hreceived⟩
  exact ⟨received, congrArg FirstEntryFinitePolicyFamilies.entryRowOfReceived
      (hreceived left hleft),
    congrArg FirstEntryFinitePolicyFamilies.entryRowOfReceived
      (hreceived right hright)⟩

/-- Left latest-receipt pair test. -/
theorem finiteEpochPhysical_latestLeftRow_beliefCompatible :
    (PhysicalMachine controller adapter initialBranch label branchStep
      ).LeftStickyRowBeliefCompatible
        (fun state ↦ FirstEntryFinitePolicyFamilies.entryRowOfReceived
          state.receivedOne) := by
  intro rounds left hleft right hright
  rcases finiteEpochPhysical_belief_receivedOne_constant controller adapter
      initialBranch label branchStep rounds with ⟨received, hreceived⟩
  exact ⟨received, congrArg FirstEntryFinitePolicyFamilies.entryRowOfReceived
      (hreceived left hleft),
    congrArg FirstEntryFinitePolicyFamilies.entryRowOfReceived
      (hreceived right hright)⟩

/-- But one strict-right continuation overwrites the process-two bit with
`true`, independently of the sticky entry row. -/
@[simp] theorem finiteEpochPhysical_step_right_latestRightRow
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (inputOne : In₁) (inputTwo : In₂) :
    FirstEntryFinitePolicyFamilies.entryRowOfReceived
        (state.step controller adapter label branchStep
          { inputOne := inputOne, inputTwo := inputTwo,
            graph := .right }).receivedTwo =
      .both :=
  rfl

/-- Hence the latest-receipt field cannot retain a `.first` entry row through
even one strict-right continuation. -/
theorem finiteEpochPhysical_step_right_latestRightRow_ne_first
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (inputOne : In₁) (inputTwo : In₂) :
    FirstEntryFinitePolicyFamilies.entryRowOfReceived
        (state.step controller adapter label branchStep
          { inputOne := inputOne, inputTwo := inputTwo,
            graph := .right }).receivedTwo ≠
      .first := by
  simp

/-- Strict-left mirror. -/
@[simp] theorem finiteEpochPhysical_step_left_latestLeftRow
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (inputOne : In₁) (inputTwo : In₂) :
    FirstEntryFinitePolicyFamilies.entryRowOfReceived
        (state.step controller adapter label branchStep
          { inputOne := inputOne, inputTwo := inputTwo,
            graph := .left }).receivedOne =
      .both :=
  rfl

theorem finiteEpochPhysical_step_left_latestLeftRow_ne_first
    (state : FiniteEpochPhysicalState Branch Bank Query Phase controller)
    (inputOne : In₁) (inputTwo : In₂) :
    FirstEntryFinitePolicyFamilies.entryRowOfReceived
        (state.step controller adapter label branchStep
          { inputOne := inputOne, inputTwo := inputTwo,
            graph := .left }).receivedOne ≠
      .first := by
  simp

end


end DetParityAutomaton

end DistributedSynthesis
