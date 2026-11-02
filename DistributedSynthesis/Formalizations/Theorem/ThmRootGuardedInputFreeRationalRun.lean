/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmInputFreeRationalRun

/-!
# One-shot root guards for input-free rational runs

An entry handoff may have to preserve one finite overlap condition on its
first transition.  Constraining the original initial state globally is too
strong when that state can recur.  This construction adds one fresh Boolean
root bit: the guarded transition is used exactly once, and every child enters
the ordinary automaton permanently.

The construction is independent of the shape of directions and of the root
guard.  In particular, the guard may assert the existence of a model-specific
lambda whose finite entry profile has prescribed values.
-/

namespace DistributedSynthesis

universe u w

namespace InputFreeRunParityTreeAutomaton

variable {Branch : Type u}

/-- The fresh-root state paired with the underlying run state.  Reachable
children always have `fresh = false`. -/
abbrev RootGuardedState
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch) :=
  Bool × A.State

/-- Add a one-shot constraint on the complete first successor assignment. -/
def rootGuarded
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch -> A.State) -> Prop) :
    InputFreeRunParityTreeAutomaton.{u, w} Branch where
  State := RootGuardedState A
  stateFinite := inferInstance
  initial := (true, A.initial)
  delta state _ children :=
    if state.1 then
      ∃ next : Branch -> A.State,
        RootAllowed next ∧ children = fun branch => (false, next branch)
    else
      ∃ next : Branch -> A.State,
        A.delta state.2 PUnit.unit next ∧
          children = fun branch => (false, next branch)
  priority state := A.priority state.2

/-- Lift a concrete run, marking only its root as fresh. -/
def rootGuardedRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch -> A.State) -> Prop)
    (run : TreeNode Branch -> A.State) :
    TreeNode Branch -> (A.rootGuarded RootAllowed).State
  | [] => (true, run [])
  | branch :: node => (false, run (branch :: node))

@[simp] theorem rootGuardedRun_nil
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch -> A.State) -> Prop)
    (run : TreeNode Branch -> A.State) :
    rootGuardedRun A (RootAllowed := RootAllowed) run [] = (true, run []) := rfl

@[simp] theorem rootGuardedRun_cons
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch -> A.State) -> Prop)
    (run : TreeNode Branch -> A.State)
    (branch : Branch) (node : TreeNode Branch) :
    rootGuardedRun A (RootAllowed := RootAllowed) run (branch :: node) =
      (false, run (branch :: node)) := rfl

theorem rootGuardedRun_child
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch -> A.State) -> Prop)
    (run : TreeNode Branch -> A.State)
    (node : TreeNode Branch) (branch : Branch) :
    rootGuardedRun A (RootAllowed := RootAllowed) run (node ++ [branch]) =
      (false, run (node ++ [branch])) := by
  cases node <;> rfl

@[simp] theorem rootGuardedRun_snd
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch -> A.State) -> Prop)
    (run : TreeNode Branch -> A.State) (node : TreeNode Branch) :
    (rootGuardedRun A RootAllowed run node).2 = run node := by
  cases node <;> rfl

/-- An ordinary accepting run whose first successor assignment satisfies the
guard lifts to an accepting run of the one-shot automaton. -/
theorem rootGuarded_isAcceptingRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch -> A.State) -> Prop)
    (run : TreeNode Branch -> A.State)
    (hrun : A.IsAcceptingRun uniqueTree run)
    (hroot : RootAllowed (fun branch => run [branch])) :
    (A.rootGuarded RootAllowed).IsAcceptingRun uniqueTree
      (rootGuardedRun A RootAllowed run) := by
  have hisRun : (A.rootGuarded RootAllowed).IsRun uniqueTree
      (rootGuardedRun A RootAllowed run) := by
    refine ⟨?_, ?_⟩
    · rw [rootGuardedRun_nil, hrun.1.1]
      rfl
    · intro node
      cases node with
      | nil =>
          change ∃ next, RootAllowed next ∧
            (fun branch => rootGuardedRun A RootAllowed run [branch]) =
              fun branch => (false, next branch)
          exact ⟨fun branch => run [branch], hroot, by
            funext branch
            rfl⟩
      | cons first rest =>
          change ∃ next,
            A.delta (run (first :: rest)) PUnit.unit next ∧
              (fun branch => rootGuardedRun A RootAllowed run
                ((first :: rest) ++ [branch])) =
                fun branch => (false, next branch)
          have hdelta := hrun.1.2 (first :: rest)
          refine ⟨fun branch => run ((first :: rest) ++ [branch]), hdelta, ?_⟩
          funext branch
          exact rootGuardedRun_child A RootAllowed run (first :: rest) branch
  refine ⟨hisRun, ?_⟩
  intro branch
  have heq :
      (fun n => (A.rootGuarded RootAllowed).priority
        (rootGuardedRun A RootAllowed run (branchNode branch n))) =
        fun n => A.priority (run (branchNode branch n)) := by
    funext n
    change A.priority
      (rootGuardedRun A RootAllowed run (branchNode branch n)).2 = _
    rw [rootGuardedRun_snd]
  rw [heq]
  exact hrun.2 branch

/-- Guarded nonemptiness follows from one accepting run satisfying the root
condition. -/
theorem rootGuarded_nonemptyLanguage
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch -> A.State) -> Prop)
    (run : TreeNode Branch -> A.State)
    (hrun : A.IsAcceptingRun uniqueTree run)
    (hroot : RootAllowed (fun branch => run [branch])) :
    (A.rootGuarded RootAllowed).NonemptyLanguage :=
  ⟨rootGuardedRun A RootAllowed run,
    rootGuarded_isAcceptingRun A RootAllowed run hrun hroot⟩

/-- Applying the ordinary rational-run basis to the finite one-shot extension
preserves the guarded-entry obligation. -/
theorem rootGuarded_hasRationalRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch -> A.State) -> Prop)
    (run : TreeNode Branch -> A.State)
    (hrun : A.IsAcceptingRun uniqueTree run)
    (hroot : RootAllowed (fun branch => run [branch]))
    (basis : (A.rootGuarded RootAllowed).RationalRunBasis) :
    (A.rootGuarded RootAllowed).HasRationalRun :=
  basis (rootGuarded_nonemptyLanguage A RootAllowed run hrun hroot)

/-- Every run of the guarded automaton exposes an allowed complete first
successor assignment. -/
theorem rootAllowed_of_rootGuarded_isRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch -> A.State) -> Prop)
    (run : TreeNode Branch -> (A.rootGuarded RootAllowed).State)
    (hrun : (A.rootGuarded RootAllowed).IsRun uniqueTree run) :
    ∃ next : Branch -> A.State,
      RootAllowed next ∧ run [] = (true, A.initial) ∧
        (fun branch => run [branch]) = fun branch => (false, next branch) := by
  have hstep := hrun.2 []
  rw [hrun.1] at hstep
  change ∃ next, RootAllowed next ∧
    (fun branch => run [branch]) = fun branch => (false, next branch) at hstep
  rcases hstep with ⟨next, hallowed, hchildren⟩
  exact ⟨next, hallowed, hrun.1, hchildren⟩

/-- In particular, a rational guarded run retains a guarded root transition. -/
theorem exists_rootAllowed_of_rootGuarded_hasRationalRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch -> A.State) -> Prop)
    (h : (A.rootGuarded RootAllowed).HasRationalRun) :
    ∃ next : Branch -> A.State, RootAllowed next := by
  rcases h with ⟨run, haccepts, _⟩
  rcases rootAllowed_of_rootGuarded_isRun A RootAllowed run haccepts.1 with
    ⟨next, hallowed, _, _⟩
  exact ⟨next, hallowed⟩

end InputFreeRunParityTreeAutomaton

end DistributedSynthesis
