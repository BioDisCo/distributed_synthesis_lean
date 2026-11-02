/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmGlobalJournalAutomaton
import DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization

/-!
# Instantiating the universal-thread checkers

This file discharges the checker interfaces of the global journal
tree automaton from the narrowed-thread determinization.  The checked
determinization provides, per boundary state, a deterministic block
monitor over sender branching whose branchwise parity decides whether
every receiver thread of the block wins the block monitor
(`threadBlockMonitor_winningTree_iff`).  The per-boundary instances
are glued fiberwise into one monitor whose state space is the
dependent sum over boundary states, so no identification of the
per-boundary state types is ever needed: the checker starts in the
fiber of the block's boundary and stays there.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Threading ignores the initial state. -/
theorem _root_.DistributedSynthesis.DeterministicBlockMonitor.controlIn_update_initial
    {Branch : Type u} {Alphabet : Type v}
    (M : DeterministicBlockMonitor.{u, v, s} Branch Alphabet)
    (q₀ : M.State) :
    ∀ (node : TreeNode Branch) (tree : LabeledTree Branch Alphabet)
      (q : M.State),
      ({ M with initial := q₀ } :
          DeterministicBlockMonitor Branch Alphabet).controlIn tree q
          node =
        M.controlIn tree q node := by
  intro node
  induction node with
  | nil =>
      intro tree q
      rfl
  | cons dir rest ih =>
      intro tree q
      show
        ({ M with initial := q₀ } :
            DeterministicBlockMonitor Branch Alphabet).controlIn
            (fun node => tree (dir :: node)) (M.step q (tree []) dir)
            rest =
          _
      rw [ih]
      rfl

/-- The left checker monitor: the disjoint union of the per-boundary
narrowed-thread determinizations, threaded fiberwise. -/
noncomputable def leftCheckerMonitor :
    DeterministicBlockMonitor.{v, max u v x y s, s}
      In₂ (NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) where
  branchFinite := inferInstance
  alphabetFinite := by
    classical
    infer_instance
  State :=
    Σ boundary : A.State,
      ((A.leftBlockMonitor boundary).threadBlockMonitor).State
  stateFinite := by
    letI :
        ∀ boundary : A.State,
          Fintype ((A.leftBlockMonitor boundary).threadBlockMonitor).State :=
      fun boundary =>
        ((A.leftBlockMonitor boundary).threadBlockMonitor).stateFinite
    infer_instance
  initial :=
    ⟨A.initial, ((A.leftBlockMonitor A.initial).threadBlockMonitor).initial⟩
  step := fun state label branch =>
    ⟨state.1,
      ((A.leftBlockMonitor state.1).threadBlockMonitor).step state.2 label
        branch⟩
  priority := fun state =>
    ((A.leftBlockMonitor state.1).threadBlockMonitor).priority state.2

/-- The right checker monitor: the mirror. -/
noncomputable def rightCheckerMonitor :
    DeterministicBlockMonitor.{u, max u v x y s, s}
      In₁ (NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)) where
  branchFinite := inferInstance
  alphabetFinite := by
    classical
    infer_instance
  State :=
    Σ boundary : A.State,
      ((A.rightBlockMonitor boundary).threadBlockMonitor).State
  stateFinite := by
    letI :
        ∀ boundary : A.State,
          Fintype ((A.rightBlockMonitor boundary).threadBlockMonitor).State :=
      fun boundary =>
        ((A.rightBlockMonitor boundary).threadBlockMonitor).stateFinite
    infer_instance
  initial :=
    ⟨A.initial, ((A.rightBlockMonitor A.initial).threadBlockMonitor).initial⟩
  step := fun state label branch =>
    ⟨state.1,
      ((A.rightBlockMonitor state.1).threadBlockMonitor).step state.2 label
        branch⟩
  priority := fun state =>
    ((A.rightBlockMonitor state.1).threadBlockMonitor).priority state.2

/-- Fiberwise threading of the left checker monitor. -/
theorem leftCheckerMonitor_controlIn (boundary : A.State) :
    ∀ node : TreeNode In₂,
      ∀ tree' :
        LabeledTree In₂
          (NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)),
      ∀ state' :
        ((A.leftBlockMonitor boundary).threadBlockMonitor).State,
        (leftCheckerMonitor A).controlIn tree' ⟨boundary, state'⟩ node =
          ⟨boundary,
            ((A.leftBlockMonitor boundary).threadBlockMonitor).controlIn
              tree' state' node⟩ := by
  intro node
  induction node with
  | nil =>
      intro tree' state'
      rfl
  | cons dir rest ih =>
      intro tree' state'
      show
        (leftCheckerMonitor A).controlIn (fun node => tree' (dir :: node))
            ⟨boundary,
              ((A.leftBlockMonitor boundary).threadBlockMonitor).step state'
                (tree' []) dir⟩ rest =
          _
      rw [ih]
      rfl

/-- Fiberwise threading of the right checker monitor. -/
theorem rightCheckerMonitor_controlIn (boundary : A.State) :
    ∀ node : TreeNode In₁,
      ∀ tree' :
        LabeledTree In₁
          (NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)),
      ∀ state' :
        ((A.rightBlockMonitor boundary).threadBlockMonitor).State,
        (rightCheckerMonitor A).controlIn tree' ⟨boundary, state'⟩ node =
          ⟨boundary,
            ((A.rightBlockMonitor boundary).threadBlockMonitor).controlIn
              tree' state' node⟩ := by
  intro node
  induction node with
  | nil =>
      intro tree' state'
      rfl
  | cons dir rest ih =>
      intro tree' state'
      show
        (rightCheckerMonitor A).controlIn (fun node => tree' (dir :: node))
            ⟨boundary,
              ((A.rightBlockMonitor boundary).threadBlockMonitor).step state'
                (tree' []) dir⟩ rest =
          _
      rw [ih]
      rfl

/-- The left thread checker of the global journal automaton. -/
noncomputable def leftThreadCheckerInstance :
    LeftThreadChecker (In₁ := In₁) A where
  monitor := leftCheckerMonitor A
  start := fun boundary =>
    ⟨boundary, ((A.leftBlockMonitor boundary).threadBlockMonitor).initial⟩
  winning_iff := by
    intro boundary narrowed
    rw [← BlockRecordMonitor.threadBlockMonitor_winningTree_iff
      (A.leftBlockMonitor boundary) narrowed]
    have hcontrol :
        ∀ node : TreeNode In₂,
          ({ leftCheckerMonitor A with
              initial :=
                ⟨boundary,
                  ((A.leftBlockMonitor boundary).threadBlockMonitor).initial⟩ } :
            DeterministicBlockMonitor In₂
              (NarrowedBlockLabel In₁ In₂ Out₁ Out₂
                (A.State × A.State))).control narrowed node =
            ⟨boundary,
              ((A.leftBlockMonitor boundary).threadBlockMonitor).control
                narrowed node⟩ := by
      intro node
      show
        ({ leftCheckerMonitor A with
            initial :=
              ⟨boundary,
                ((A.leftBlockMonitor boundary).threadBlockMonitor).initial⟩ } :
          DeterministicBlockMonitor In₂
            (NarrowedBlockLabel In₁ In₂ Out₁ Out₂
              (A.State × A.State))).controlIn narrowed
            ⟨boundary,
              ((A.leftBlockMonitor boundary).threadBlockMonitor).initial⟩
            node =
          _
      rw [DeterministicBlockMonitor.controlIn_update_initial]
      exact
        leftCheckerMonitor_controlIn A boundary node narrowed
          ((A.leftBlockMonitor boundary).threadBlockMonitor).initial
    have heq :
        ∀ branch : Nat -> In₂,
          (fun n =>
            ({ leftCheckerMonitor A with
                initial :=
                  ⟨boundary,
                    ((A.leftBlockMonitor
                        boundary).threadBlockMonitor).initial⟩ } :
              DeterministicBlockMonitor In₂
                (NarrowedBlockLabel In₁ In₂ Out₁ Out₂
                  (A.State × A.State))).priority
              (DeterministicBlockMonitor.control _ narrowed
                (branchNode branch n))) =
            fun n =>
              ((A.leftBlockMonitor boundary).threadBlockMonitor).priority
                (((A.leftBlockMonitor boundary).threadBlockMonitor).control
                  narrowed (branchNode branch n)) := by
      intro branch
      funext n
      rw [hcontrol (branchNode branch n)]
      rfl
    constructor
    · intro hwin branch
      have hb := hwin branch
      rwa [heq branch] at hb
    · intro hwin branch
      have hb := hwin branch
      rw [heq branch]
      exact hb

/-- The right thread checker of the global journal automaton. -/
noncomputable def rightThreadCheckerInstance :
    RightThreadChecker (In₁ := In₁) A where
  monitor := rightCheckerMonitor A
  start := fun boundary =>
    ⟨boundary, ((A.rightBlockMonitor boundary).threadBlockMonitor).initial⟩
  winning_iff := by
    intro boundary narrowed
    rw [← BlockRecordMonitor.threadBlockMonitor_winningTree_iff
      (A.rightBlockMonitor boundary) narrowed]
    have hcontrol :
        ∀ node : TreeNode In₁,
          ({ rightCheckerMonitor A with
              initial :=
                ⟨boundary,
                  ((A.rightBlockMonitor boundary).threadBlockMonitor).initial⟩ } :
            DeterministicBlockMonitor In₁
              (NarrowedBlockLabel In₂ In₁ Out₂ Out₁
                (A.State × A.State))).control narrowed node =
            ⟨boundary,
              ((A.rightBlockMonitor boundary).threadBlockMonitor).control
                narrowed node⟩ := by
      intro node
      show
        ({ rightCheckerMonitor A with
            initial :=
              ⟨boundary,
                ((A.rightBlockMonitor boundary).threadBlockMonitor).initial⟩ } :
          DeterministicBlockMonitor In₁
            (NarrowedBlockLabel In₂ In₁ Out₂ Out₁
              (A.State × A.State))).controlIn narrowed
            ⟨boundary,
              ((A.rightBlockMonitor boundary).threadBlockMonitor).initial⟩
            node =
          _
      rw [DeterministicBlockMonitor.controlIn_update_initial]
      exact
        rightCheckerMonitor_controlIn A boundary node narrowed
          ((A.rightBlockMonitor boundary).threadBlockMonitor).initial
    have heq :
        ∀ branch : Nat -> In₁,
          (fun n =>
            ({ rightCheckerMonitor A with
                initial :=
                  ⟨boundary,
                    ((A.rightBlockMonitor
                        boundary).threadBlockMonitor).initial⟩ } :
              DeterministicBlockMonitor In₁
                (NarrowedBlockLabel In₂ In₁ Out₂ Out₁
                  (A.State × A.State))).priority
              (DeterministicBlockMonitor.control _ narrowed
                (branchNode branch n))) =
            fun n =>
              ((A.rightBlockMonitor boundary).threadBlockMonitor).priority
                (((A.rightBlockMonitor boundary).threadBlockMonitor).control
                  narrowed (branchNode branch n)) := by
      intro branch
      funext n
      rw [hcontrol (branchNode branch n)]
      rfl
    constructor
    · intro hwin branch
      have hb := hwin branch
      rwa [heq branch] at hb
    · intro hwin branch
      have hb := hwin branch
      rw [heq branch]
      exact hb

end DetParityAutomaton

end DistributedSynthesis
