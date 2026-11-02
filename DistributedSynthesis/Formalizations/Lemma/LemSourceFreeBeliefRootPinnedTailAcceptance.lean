/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefFiniteCodePolicyImage
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefRootPinnedRationalPolicy

/-!
# Acceptance below one child of a root-pinned finite-code policy

The Boolean root guard is proof memory used exactly once.  Below any literal
first child, its accepting subtree is an ordinary source-free finite-code
policy.  This file re-roots the objective DPA at the *actual* control stored
in that child and exposes the usual allowed-target path acceptance theorem.

The successor table is projected from the original guarded policy; no new
rational policy is selected.  Consequently this adapter cannot create an
accepted-run mosaic or reset the objective automaton.
-/

namespace DistributedSynthesis

universe u v w z

section

variable {RawDirection : Type u} {Move : Type v} {BeliefCode : Type z}
variable [Fintype BeliefCode] [Nonempty RawDirection]

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (rawNext : BeliefCode → Move → RawDirection → BeliefCode)

namespace SourceFreeBeliefCodeParityRootPinnedPolicy

variable {RootPred : Move → Prop}

/-- The ordinary accepting tail below `first`, viewed as a finite-code policy
whose objective DPA starts at the exact control stored in that child.  Its
successor function is definitionally the false-state successor table of the
original guarded policy. -/
noncomputable def tailCodePolicy
    (package : SourceFreeBeliefFiniteCodeRootPinnedPolicy D initialCode Valid
      rawNext RootPred)
    (first : BeliefCode) :
    SourceFreeBeliefCodeParityRationalPolicy
      (D.withInitial (package.policy.run [first]).2.2)
      (package.policy.run [first]).2.1 Valid
      (sourceFreeBeliefFiniteCodeNext rawNext) := by
  let tail := package.ordinaryBelow first
  exact tail

@[simp] theorem tailCodePolicy_run
    (package : SourceFreeBeliefFiniteCodeRootPinnedPolicy D initialCode Valid
      rawNext RootPred)
    (first : BeliefCode) (node : TreeNode BeliefCode) :
    (package.tailCodePolicy D initialCode Valid rawNext first).run node =
      (package.policy.run ([first] ++ node)).2 :=
  rfl

@[simp] theorem tailCodePolicy_successor
    (package : SourceFreeBeliefFiniteCodeRootPinnedPolicy D initialCode Valid
      rawNext RootPred)
    (first : BeliefCode) :
    (package.tailCodePolicy D initialCode Valid rawNext first).successor =
      fun state childCode ↦
        (package.policy.successor (false, state) childCode).2 :=
  rfl

/-- Allowed edges of the re-rooted tail remain literal edges of the one
root-pinned guarded policy. -/
def TailAllowedTarget
    (package : SourceFreeBeliefFiniteCodeRootPinnedPolicy D initialCode Valid
      rawNext RootPred)
    (first : BeliefCode)
    (source target :
      (sourceFreeBeliefCodeParityRunAutomaton
        (D.withInitial (package.policy.run [first]).2.2)
        (package.policy.run [first]).2.1 Valid
        (sourceFreeBeliefFiniteCodeNext rawNext)).State) : Prop :=
  SourceFreeBeliefFiniteCodePolicyImage.AllowedTarget
    (D.withInitial (package.policy.run [first]).2.2)
    (package.policy.run [first]).2.1 Valid rawNext
    (package.tailCodePolicy D initialCode Valid rawNext first) source target

/-- Any infinite path through allowed targets of this one tail is accepted
from the exact objective-DPA control stored at the guarded child. -/
theorem acceptsFrom_of_tailAllowedTarget_path
    (package : SourceFreeBeliefFiniteCodeRootPinnedPolicy D initialCode Valid
      rawNext RootPred)
    (first : BeliefCode)
    (states : Nat →
      (sourceFreeBeliefCodeParityRunAutomaton
        (D.withInitial (package.policy.run [first]).2.2)
        (package.policy.run [first]).2.1 Valid
        (sourceFreeBeliefFiniteCodeNext rawNext)).State)
    (hzero : states 0 =
      (package.tailCodePolicy D initialCode Valid rawNext first).run [])
    (hstep : ∀ n,
      package.TailAllowedTarget D initialCode Valid rawNext first
        (states n) (states (n + 1))) :
    D.AcceptsFrom (package.policy.run [first]).2.2
      (fun n ↦ (states (n + 1)).1) := by
  have haccepts :=
    SourceFreeBeliefFiniteCodePolicyImage.accepts_of_allowedTarget_path
      (D.withInitial (package.policy.run [first]).2.2)
      (package.policy.run [first]).2.1 Valid rawNext
      (package.tailCodePolicy D initialCode Valid rawNext first)
      states hzero hstep
  exact (D.withInitial_accepts_iff (package.policy.run [first]).2.2
    (fun n ↦ (states (n + 1)).1)).mp haccepts

end SourceFreeBeliefCodeParityRootPinnedPolicy

end

end DistributedSynthesis
