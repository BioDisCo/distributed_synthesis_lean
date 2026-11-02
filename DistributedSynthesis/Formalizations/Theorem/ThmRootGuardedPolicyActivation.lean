/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmRootGuardedInputFreeRationalRun
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting

/-!
# Activating an ordinary policy below a one-shot root guard

A rational policy of `rootGuarded` uses the fresh bit only at its root.  Below
any first child all states have `fresh = false`, so the corresponding subtree
projects to an ordinary rational transition policy rooted at that child's
underlying state.  This is the exact interface needed for a guarded first
handoff followed by an ordinary recurrent policy bank.
-/

namespace DistributedSynthesis

universe u w

namespace InputFreeRunParityTreeAutomaton

variable {Branch : Type u}

/-- Change only the initial state of an input-free run automaton. -/
def withInitial
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch) (state : A.State) :
    InputFreeRunParityTreeAutomaton.{u, w} Branch where
  State := A.State
  stateFinite := A.stateFinite
  initial := state
  delta := A.delta
  priority := A.priority

@[simp] theorem withInitial_initial
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch) (state : A.State) :
    (A.withInitial state).initial = state := rfl

/-- A finite transition policy is itself a witness of rational-run
nonemptiness. -/
theorem hasRationalRun_of_policy
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (policy : A.RationalTransitionPolicy) : A.HasRationalRun := by
  refine ⟨policy.run, policy.accepts, ?_⟩
  intro left right heq
  constructor
  · exact Subsingleton.elim _ _
  · funext branch
    rw [← policy.successor_at left branch,
      ← policy.successor_at right branch, heq]

section RootGuarded

variable
  (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
  (RootAllowed : (Branch -> A.State) -> Prop)
  (policy : (A.rootGuarded RootAllowed).RationalTransitionPolicy)

/-- Every node strictly below the guarded root has its fresh bit cleared. -/
theorem rootGuardedPolicy_fresh_false
    (first : Branch) (node : TreeNode Branch) :
    (policy.run ([first] ++ node)).1 = false := by
  induction node using List.reverseRecOn with
  | nil =>
      have hlegal := policy.legal_at []
      rw [policy.accepts.1.1] at hlegal
      change ∃ next : Branch -> A.State,
        RootAllowed next ∧ policy.successor (true, A.initial) =
          fun branch => (false, next branch) at hlegal
      rcases hlegal with ⟨next, _, hchildren⟩
      have hchild := policy.successor_at [] first
      rw [policy.accepts.1.1] at hchild
      simp only [rootGuarded, List.nil_append] at hchild
      change policy.successor (true, A.initial) first = policy.run [first] at hchild
      rw [hchildren] at hchild
      simpa using congrArg Prod.fst hchild.symm
  | @append_singleton node branch ih =>
      have hlegal := policy.legal_at ([first] ++ node)
      have hstate : policy.run ([first] ++ node) =
          (false, (policy.run ([first] ++ node)).2) := by
        apply Prod.ext
        · simpa using ih
        · rfl
      rw [hstate] at hlegal
      change ∃ next : Branch -> A.State,
        A.delta (policy.run ([first] ++ node)).2 PUnit.unit next ∧
          policy.successor (false, (policy.run ([first] ++ node)).2) =
            fun branch => (false, next branch) at hlegal
      rcases hlegal with ⟨next, _, hchildren⟩
      have hchild := policy.successor_at ([first] ++ node) branch
      rw [hstate, hchildren] at hchild
      simpa [List.append_assoc] using congrArg Prod.fst hchild.symm

/-- The branch obtained by prefixing one fixed direction. -/
def prefixedBranch (first : Branch) (tail : Nat -> Branch) : Nat -> Branch
  | 0 => first
  | n + 1 => tail n

theorem branchNode_prefixedBranch
    (first : Branch) (tail : Nat -> Branch) (n : Nat) :
    branchNode (prefixedBranch first tail) (n + 1) =
      [first] ++ branchNode tail n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [branchNode, ih, branchNode]
      simp [prefixedBranch, List.append_assoc]

/-- Project the rational guarded subtree below a first child to an ordinary
rational policy.  The finite fresh bit is consumed once and is absent from
the resulting policy state. -/
noncomputable def ordinaryPolicyBelowRootGuard
    (first : Branch) :
    (A.withInitial (policy.run [first]).2).RationalTransitionPolicy where
  run := fun node => (policy.run ([first] ++ node)).2
  accepts := by
    constructor
    · constructor
      · rfl
      · intro node
        have hfalse := rootGuardedPolicy_fresh_false A RootAllowed policy first node
        have hstate : policy.run ([first] ++ node) =
            (false, (policy.run ([first] ++ node)).2) := by
          apply Prod.ext
          · simpa using hfalse
          · rfl
        have hlegal := policy.legal_at ([first] ++ node)
        rw [hstate] at hlegal
        change ∃ next : Branch -> A.State,
          A.delta (policy.run ([first] ++ node)).2 PUnit.unit next ∧
            policy.successor (false, (policy.run ([first] ++ node)).2) =
              fun branch => (false, next branch) at hlegal
        rcases hlegal with ⟨next, hdelta, hchildren⟩
        have hrunChildren :
            (fun branch => (policy.run ([first] ++ (node ++ [branch]))).2) =
              next := by
          funext branch
          have hchild := policy.successor_at ([first] ++ node) branch
          rw [hstate, hchildren] at hchild
          simpa [List.append_assoc] using congrArg Prod.snd hchild.symm
        rw [← hrunChildren] at hdelta
        simpa only [withInitial, uniqueTree] using hdelta
    · intro tail
      have hparity := policy.accepts.2 (prefixedBranch first tail)
      have hshift := (natSeqMinEvenParity_shift
        (fun n => (A.rootGuarded RootAllowed).priority
          (policy.run (branchNode (prefixedBranch first tail) n))) 1).mpr hparity
      simpa [withInitial, branchNode_prefixedBranch, Nat.add_comm] using hshift
  successor := fun state branch =>
    (policy.successor (false, state) branch).2
  successor_at := by
    intro node branch
    have hfalse := rootGuardedPolicy_fresh_false A RootAllowed policy first node
    have hstate : policy.run ([first] ++ node) =
        (false, (policy.run ([first] ++ node)).2) := by
      apply Prod.ext
      · simpa using hfalse
      · rfl
    have hchild := congrArg Prod.snd
      (policy.successor_at ([first] ++ node) branch)
    rw [hstate] at hchild
    simpa [List.append_assoc] using hchild
  legal_at := by
    intro node
    have hfalse := rootGuardedPolicy_fresh_false A RootAllowed policy first node
    have hstate : policy.run ([first] ++ node) =
        (false, (policy.run ([first] ++ node)).2) := by
      apply Prod.ext
      · simpa using hfalse
      · rfl
    have hlegal := policy.legal_at ([first] ++ node)
    rw [hstate] at hlegal
    change ∃ next : Branch -> A.State,
      A.delta (policy.run ([first] ++ node)).2 PUnit.unit next ∧
        policy.successor (false, (policy.run ([first] ++ node)).2) =
          fun branch => (false, next branch) at hlegal
    rcases hlegal with ⟨next, hdelta, hchildren⟩
    have hnext :
        (fun branch =>
          (policy.successor (false, (policy.run ([first] ++ node)).2) branch).2) =
        next := by
      funext branch
      simpa using congrArg (fun children => (children branch).2) hchildren
    rw [hnext]
    exact hdelta

end RootGuarded

end InputFreeRunParityTreeAutomaton

end DistributedSynthesis
