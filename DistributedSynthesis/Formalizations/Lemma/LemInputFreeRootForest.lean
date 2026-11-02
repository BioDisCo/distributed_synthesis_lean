/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmRootGuardedPolicyActivation

/-!
# Gluing a forest below one input-free root

`rootGuarded_isAcceptingRun` lifts one run of the underlying automaton.  An
initial homogeneous block instead has one possible recurrent entry state for
every finite closing direction.  This file supplies the missing forest form:
each root direction may start a different accepting underlying run, while one
application of the rational-run basis is performed only after the complete
forest has been glued below the common root.

This is the ordering needed by the end-to-end Bérard route.  In particular,
no recurrent policy is selected independently at an initial close.
-/

namespace DistributedSynthesis

universe u w

namespace InputFreeRunParityTreeAutomaton

variable {Branch : Type u}

/-- Glue a branch-indexed forest below the fresh root of `rootGuarded`. -/
def rootGuardedForestRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch → A.State) → Prop)
    (forest : Branch → TreeNode Branch → A.State) :
    TreeNode Branch → (A.rootGuarded RootAllowed).State
  | [] => (true, A.initial)
  | first :: rest => (false, forest first rest)

@[simp] theorem rootGuardedForestRun_nil
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch → A.State) → Prop)
    (forest : Branch → TreeNode Branch → A.State) :
    rootGuardedForestRun A RootAllowed forest [] = (true, A.initial) :=
  rfl

@[simp] theorem rootGuardedForestRun_cons
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch → A.State) → Prop)
    (forest : Branch → TreeNode Branch → A.State)
    (first : Branch) (rest : TreeNode Branch) :
    rootGuardedForestRun A RootAllowed forest (first :: rest) =
      (false, forest first rest) :=
  rfl

/-- Split an infinite branch into its first direction and tail. -/
def branchTail (branch : Nat → Branch) : Nat → Branch :=
  fun n => branch (n + 1)

theorem branchNode_succ_eq_cons_tail
    (branch : Nat → Branch) : ∀ n,
    branchNode branch (n + 1) =
      branch 0 :: branchNode (branchTail branch) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 2) =
          branchNode branch (n + 1) ++ [branch (n + 1)] from rfl,
        ih]
      change branch 0 ::
          (branchNode (branchTail branch) n ++ [branchTail branch n]) = _
      rfl

/-- A branch-indexed family of accepting runs glues to an accepting run of
the one-shot root extension. -/
theorem rootGuardedForest_isAcceptingRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch → A.State) → Prop)
    (initial : Branch → A.State)
    (forest : Branch → TreeNode Branch → A.State)
    (hinitial : ∀ branch, forest branch [] = initial branch)
    (hforest : ∀ branch,
      (A.withInitial (initial branch)).IsAcceptingRun uniqueTree
        (forest branch))
    (hroot : RootAllowed initial) :
    (A.rootGuarded RootAllowed).IsAcceptingRun uniqueTree
      (rootGuardedForestRun A RootAllowed forest) := by
  have hisRun : (A.rootGuarded RootAllowed).IsRun uniqueTree
      (rootGuardedForestRun A RootAllowed forest) := by
    refine ⟨rfl, ?_⟩
    intro node
    cases node with
    | nil =>
        change ∃ next, RootAllowed next ∧
          (fun branch =>
            rootGuardedForestRun A RootAllowed forest [branch]) =
              fun branch => (false, next branch)
        refine ⟨initial, hroot, ?_⟩
        funext branch
        simp [hinitial]
    | cons first rest =>
        change ∃ next,
          A.delta (forest first rest) PUnit.unit next ∧
            (fun branch =>
              rootGuardedForestRun A RootAllowed forest
                ((first :: rest) ++ [branch])) =
              fun branch => (false, next branch)
        let next : Branch → A.State :=
          fun branch => forest first (rest ++ [branch])
        refine ⟨next, ?_, ?_⟩
        · simpa only [withInitial, uniqueTree] using
            (hforest first).1.2 rest
        · funext branch
          rfl
  refine ⟨hisRun, ?_⟩
  intro branch
  let priorities : Nat → Nat := fun n =>
    (A.rootGuarded RootAllowed).priority
      (rootGuardedForestRun A RootAllowed forest (branchNode branch n))
  have htail : NatSeqMinEvenParity (fun n =>
      A.priority
        (forest (branch 0) (branchNode (branchTail branch) n))) :=
    (hforest (branch 0)).2 (branchTail branch)
  have hshift : NatSeqMinEvenParity (fun n => priorities (1 + n)) := by
    have heq : (fun n => priorities (1 + n)) = (fun n =>
        A.priority
          (forest (branch 0) (branchNode (branchTail branch) n))) := by
      funext n
      change (A.rootGuarded RootAllowed).priority
        (rootGuardedForestRun A RootAllowed forest
          (branchNode branch (1 + n))) = _
      rw [show 1 + n = n + 1 by omega,
        branchNode_succ_eq_cons_tail]
      rfl
    rw [heq]
    exact htail
  exact (natSeqMinEvenParity_shift priorities 1).mp hshift

/-- The complete initial forest is rationalized in one application of the
classical input-free basis. -/
theorem rootGuardedForest_hasRationalRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (RootAllowed : (Branch → A.State) → Prop)
    (initial : Branch → A.State)
    (forest : Branch → TreeNode Branch → A.State)
    (hinitial : ∀ branch, forest branch [] = initial branch)
    (hforest : ∀ branch,
      (A.withInitial (initial branch)).IsAcceptingRun uniqueTree
        (forest branch))
    (hroot : RootAllowed initial)
    (basis : (A.rootGuarded RootAllowed).RationalRunBasis) :
    (A.rootGuarded RootAllowed).HasRationalRun := by
  apply basis
  exact ⟨rootGuardedForestRun A RootAllowed forest,
    rootGuardedForest_isAcceptingRun A RootAllowed initial forest hinitial
      hforest hroot⟩

end InputFreeRunParityTreeAutomaton

end DistributedSynthesis
