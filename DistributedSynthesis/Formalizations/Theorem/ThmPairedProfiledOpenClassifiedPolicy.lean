/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenClassifiedAutomaton
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRationalPolicy

/-!
# Rational outer policies from history-indexed classified moves

This is the parity/rationalization half of the final classified integration.
A raw realizing strategy may choose a different finite classified table at
two proof histories carrying the same canonical family.  The history is kept
while legality and epoch parity are proved and is removed only by the
input-free rational-run basis theorem.

The actual hidden root occurs only in the environment direction.  The move
chosen at a family node depends on the complete family, never on a selected
root, strict-leader flag, or orientation signal available to a process.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Forget the view-class wrapper and recover the profiled objective state
carried by a classified anchor.  The sink is the existing neutral initial
state of the paired-entry automaton. -/
def ProfiledOpenClassifiedAnchor.toProfiledState :
    ProfiledOpenClassifiedAnchor A → PairedProfiledTreeState A
  | .sink => .inl PUnit.unit
  | .right root => .inr (.inl root.1)
  | .left root => .inr (.inr root.1)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledOpenClassifiedAnchorPriority_eq
    (anchor : ProfiledOpenClassifiedAnchor A) :
    profiledOpenClassifiedAnchorPriority A anchor =
      pairedProfiledEntryPriority A anchor.toProfiledState := by
  cases anchor <;> rfl

/-- A classified move selected at a raw proof history.  Its successor
assignment is the one consumed by the generic two-sorted history run. -/
noncomputable def profiledOpenClassifiedNextAt
    (moveAt : TreeNode (ProfiledOpenClassifiedDirection A) →
      Finset (ProfiledOpenClassifiedAnchor A) →
        ProfiledOpenClassifiedMove A) :
    TreeNode (ProfiledOpenClassifiedDirection A) →
      Finset (ProfiledOpenClassifiedAnchor A) →
        TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
          (ProfiledOpenClassifiedDirection A) :=
  fun node roots => (moveAt node roots).successor A

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- If every reachable raw family is represented by the selected move, and
that move carries both checked local certificates, the history run is legal
for the concrete classified outer automaton. -/
theorem profiledOpenClassifiedHistory_allowed
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (moveAt : TreeNode (ProfiledOpenClassifiedDirection A) →
      Finset (ProfiledOpenClassifiedAnchor A) →
        ProfiledOpenClassifiedMove A)
    (hvalid : ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots
          (profiledOpenClassifiedNextAt A moveAt) node = .family roots →
        (moveAt node roots).Valid A)
    (hroots : ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots
          (profiledOpenClassifiedNextAt A moveAt) node = .family roots →
        (moveAt node roots).roots A = roots) :
    ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots
          (profiledOpenClassifiedNextAt A moveAt) node = .family roots →
        ProfiledOpenClassifiedFamilyAllowed A roots
          (profiledOpenClassifiedNextAt A moveAt node roots) := by
  intro node roots hrun
  exact ⟨moveAt node roots, hvalid node roots hrun,
    hroots node roots hrun, rfl⟩

/-- Epoch parity for a classified history run is inherited verbatim from an
already checked rational paired-profiled policy.  Only the proof-side anchor
is mapped; the classified family and table selected by the processes remain
shared. -/
theorem profiledOpenClassifiedHistory_selectedParity
    {initialState : PairedProfiledTreeState A}
    (inner :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (moveAt : TreeNode (ProfiledOpenClassifiedDirection A) →
      Finset (ProfiledOpenClassifiedAnchor A) →
        ProfiledOpenClassifiedMove A)
    (hzero : ∀ branch,
      (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
        (profiledOpenClassifiedNextAt A moveAt) branch 0).toProfiledState =
          inner.run [])
    (hstep : ∀ branch n,
      PairedProfiledRationalPolicy.Allowed A inner
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenClassifiedNextAt A moveAt) branch n).toProfiledState
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenClassifiedNextAt A moveAt) branch (n + 1)).toProfiledState) :
    ∀ branch,
      NatSeqMinEvenParity (fun n =>
        profiledOpenClassifiedAnchorPriority A
          (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
            (profiledOpenClassifiedNextAt A moveAt) branch n)) := by
  intro branch
  rw [show (fun n =>
      profiledOpenClassifiedAnchorPriority A
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenClassifiedNextAt A moveAt) branch n)) =
      (fun n => pairedProfiledEntryPriority A
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenClassifiedNextAt A moveAt) branch n).toProfiledState) by
    funext n
    exact profiledOpenClassifiedAnchorPriority_eq A _]
  exact PairedProfiledRationalPolicy.accepts_of_allowed_path A inner
    (fun n =>
      (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
        (profiledOpenClassifiedNextAt A moveAt) branch n).toProfiledState)
    (hzero branch) (hstep branch)

/-- End-to-end history-sensitive extraction for the concrete classified
outer automaton.  The remaining model work is exactly `moveAt`, its two
reachable-family certificates, and the ordinary paired-profiled edge facts.
Rationalization adds no model-specific construction. -/
theorem nonempty_profiledOpenClassifiedHistoryRationalPolicy
    {initialState : PairedProfiledTreeState A}
    (inner :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (moveAt : TreeNode (ProfiledOpenClassifiedDirection A) →
      Finset (ProfiledOpenClassifiedAnchor A) →
        ProfiledOpenClassifiedMove A)
    (hvalid : ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots
          (profiledOpenClassifiedNextAt A moveAt) node = .family roots →
        (moveAt node roots).Valid A)
    (hroots : ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots
          (profiledOpenClassifiedNextAt A moveAt) node = .family roots →
        (moveAt node roots).roots A = roots)
    (hzero : ∀ branch,
      (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
        (profiledOpenClassifiedNextAt A moveAt) branch 0).toProfiledState =
          inner.run [])
    (hstep : ∀ branch n,
      PairedProfiledRationalPolicy.Allowed A inner
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenClassifiedNextAt A moveAt) branch n).toProfiledState
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenClassifiedNextAt A moveAt) branch (n + 1)).toProfiledState)
    (basis : InputFreeRunParityTreeAutomaton.RationalRunBasis
      (profiledOpenClassifiedFamilyRunAutomaton A initialRoots)) :
    Nonempty (InputFreeRunParityTreeAutomaton.RationalTransitionPolicy
      (profiledOpenClassifiedFamilyRunAutomaton A initialRoots)) := by
  apply TwoSortedFamilyPolicy.nonempty_rationalPolicy_of_historyAssignment
    (profiledOpenClassifiedAnchorPriority A) initialRoots
    (ProfiledOpenClassifiedFamilyAllowed A)
    (profiledOpenClassifiedNextAt A moveAt)
  · exact profiledOpenClassifiedHistory_allowed A initialRoots moveAt
      hvalid hroots
  · exact profiledOpenClassifiedHistory_selectedParity A inner initialRoots
      moveAt hzero hstep
  · exact basis

end

end

end


end DetParityAutomaton

end DistributedSynthesis
