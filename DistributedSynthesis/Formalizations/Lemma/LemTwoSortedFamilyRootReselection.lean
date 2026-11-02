/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemTwoSortedFamilyRun

/-!
# The two-sorted family run does not retain its selected root

This small kernel example isolates the quantifier issue in the old outer
run.  A branch letter contains a claimed source root and an emitted root.
After one `chosen` state the automaton returns to the whole family, so the
next family letter may claim a different source.  The transition remains
legal: source persistence is simply not part of `historyRun`.

The example does not say that the generic automaton accepts a bad parity
stream.  It says that parity of its `historySelectedDescriptor` stream cannot
be proved by chaining semantic one-step witnesses unless an additional
hidden-thread guard retains the emitted root.
-/

namespace DistributedSynthesis

namespace TwoSortedFamilyRootReselection

/-- First coordinate: claimed current root.  Second coordinate: emitted
root. -/
abbrev Branch := Bool × Bool

noncomputable def roots : Finset Bool := {false, true}

/-- The old family successor ignores the claimed source coordinate, because
the generic two-sorted interface has no place to check it against the root
emitted at the preceding family transition. -/
noncomputable def nextAt
    (_node : TreeNode Branch) (_current : Finset Bool) :
    TwoSortedFamilySuccessor Bool Branch :=
  fun direction => (direction.2, roots)

/-- At the second family transition the branch changes its claimed source
from `false` to `true`. -/
def crossedBranch : Nat → Branch
  | 0 => (false, false)
  | 1 => (false, false)
  | _ => (true, true)

@[simp] theorem selected_zero :
    TwoSortedFamilyPolicy.historySelectedDescriptor roots nextAt
      crossedBranch 0 = false := by
  rfl

@[simp] theorem selected_one :
    TwoSortedFamilyPolicy.historySelectedDescriptor roots nextAt
      crossedBranch 1 = true := by
  rfl

/-- The selected root emitted by the first family transition is not the
source claimed by the next family transition. -/
theorem next_source_ne_previous_selected :
    (crossedBranch 2).1 ≠
      TwoSortedFamilyPolicy.historySelectedDescriptor roots nextAt
        crossedBranch 0 := by
  simp [crossedBranch]

/-- Nevertheless the intervening `chosen → family` transition reaches the
whole root family normally. -/
theorem family_after_chosen :
    TwoSortedFamilyPolicy.historyRun roots nextAt
        (branchNode crossedBranch 2) =
      .family roots := by
  rfl

/-- With a trivial transition law and parity objective the very same
root-reselecting history tree is a legal accepting run.  Thus legality of the
two-sorted interface cannot imply a persistent pointed semantic history. -/
theorem rootReselecting_historyRun_isAccepting :
    (twoSortedFamilyRunAutomaton (fun _ : Bool => 0) roots
      (fun _ _ => True)).IsAcceptingRun
        InputFreeRunParityTreeAutomaton.uniqueTree
        (TwoSortedFamilyPolicy.historyRun roots nextAt) := by
  apply TwoSortedFamilyPolicy.historyRun_isAccepting
    (fun _ : Bool => 0) roots (fun _ _ => True) nextAt
  · intro _ _ _
    trivial
  · intro branch
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro n
      exact ⟨n, le_rfl, rfl⟩
    · intro q _
      exact Nat.zero_le q

end TwoSortedFamilyRootReselection

end DistributedSynthesis
