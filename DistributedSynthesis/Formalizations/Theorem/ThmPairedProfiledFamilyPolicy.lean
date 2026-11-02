/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemTwoSortedFamilyRun
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRationalPolicy

/-!
# Family-valued profiled paired policy

This is the parity handoff for the recursive hidden-root construction.  The
inner profiled policy is used only as a finite objective graph: its arbitrary
allowed paths already satisfy epoch parity.  The outer policy chooses one
simultaneous family controller before any hidden anchor is selected.

Consequently this file does not reuse the independently selected inner block
lambda.  A concrete family transition only has to prove that its selected
descriptor starts at the inner initial state and follows the inner finite
`Allowed` relation.  The two-sorted construction then supplies the finite
shared outer policy without exposing an orientation or leader bit.
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

variable [Inhabited In₁] [Inhabited In₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

local instance : Inhabited (PairedProfiledTreeState A) :=
  ⟨.inl PUnit.unit⟩

variable {initialState : PairedProfiledTreeState A}
variable
  (inner :
    (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

/-- The family-valued paired automaton.  Its descriptors are precisely the
finite profiled paired states and its objective is the existing epoch
priority. -/
noncomputable abbrev pairedProfiledFamilyAutomaton
    (initialRoots : Finset (PairedProfiledTreeState A))
    (FamilyAllowed : Finset (PairedProfiledTreeState A) →
      TwoSortedFamilySuccessor (PairedProfiledTreeState A)
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) → Prop) :=
  twoSortedFamilyRunAutomaton (pairedProfiledEntryPriority A) initialRoots
    FamilyAllowed

section
omit [Inhabited In₁] [Inhabited In₂]

/-- Once selected descriptors follow the already checked inner finite graph,
the outer family recursion has accepting parity on every branch.  This is the
formal connection to epoch-priority pasting; no separate mosaic argument is
left open. -/
theorem pairedProfiledFamily_selectedParity
    (initialRoots : Finset (PairedProfiledTreeState A))
    (FamilyAllowed : Finset (PairedProfiledTreeState A) →
      TwoSortedFamilySuccessor (PairedProfiledTreeState A)
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) → Prop)
    (next : Finset (PairedProfiledTreeState A) →
      TwoSortedFamilySuccessor (PairedProfiledTreeState A)
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (hzero : ∀ branch,
      TwoSortedFamilyPolicy.selectedDescriptor initialRoots next branch 0 =
        inner.run [])
    (hstep : ∀ branch n,
      PairedProfiledRationalPolicy.Allowed A inner
        (TwoSortedFamilyPolicy.selectedDescriptor initialRoots next branch n)
        (TwoSortedFamilyPolicy.selectedDescriptor initialRoots next branch
          (n + 1))) :
    ∀ branch,
      NatSeqMinEvenParity (fun n =>
        pairedProfiledEntryPriority A
          (TwoSortedFamilyPolicy.selectedDescriptor initialRoots next branch
            n)) := by
  intro branch
  exact PairedProfiledRationalPolicy.accepts_of_allowed_path A inner
    (fun n => TwoSortedFamilyPolicy.selectedDescriptor initialRoots next
      branch n)
    (hzero branch) (hstep branch)

/-- End-to-end recursive extraction at the profiled paired interface.  The
only model-specific premises are legality of the simultaneous family tables
and their successor-edge compatibility.  Rationalization itself introduces
no additional fixed point and cannot distinguish a hidden family member. -/
theorem nonempty_pairedProfiledFamilyRationalPolicy
    (initialRoots : Finset (PairedProfiledTreeState A))
    (FamilyAllowed : Finset (PairedProfiledTreeState A) →
      TwoSortedFamilySuccessor (PairedProfiledTreeState A)
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) → Prop)
    (next : Finset (PairedProfiledTreeState A) →
      TwoSortedFamilySuccessor (PairedProfiledTreeState A)
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (hallowed : ∀ roots, FamilyAllowed roots (next roots))
    (hzero : ∀ branch,
      TwoSortedFamilyPolicy.selectedDescriptor initialRoots next branch 0 =
        inner.run [])
    (hstep : ∀ branch n,
      PairedProfiledRationalPolicy.Allowed A inner
        (TwoSortedFamilyPolicy.selectedDescriptor initialRoots next branch n)
        (TwoSortedFamilyPolicy.selectedDescriptor initialRoots next branch
          (n + 1)))
    (basis : InputFreeRunParityTreeAutomaton.RationalRunBasis
      (pairedProfiledFamilyAutomaton A initialRoots FamilyAllowed)) :
    Nonempty (InputFreeRunParityTreeAutomaton.RationalTransitionPolicy
      (pairedProfiledFamilyAutomaton A initialRoots FamilyAllowed)) := by
  apply TwoSortedFamilyPolicy.nonempty_rationalPolicy_of_assignment
    (pairedProfiledEntryPriority A) initialRoots FamilyAllowed next hallowed
  · exact pairedProfiledFamily_selectedParity A inner initialRoots
      FamilyAllowed next hzero hstep
  · exact basis

/-- History-dependent parity handoff.  This is the version used by a raw
distributed strategy before rationalization: two occurrences of the same
finite family may still carry different semantic representatives. -/
theorem pairedProfiledHistoryFamily_selectedParity
    (initialRoots : Finset (PairedProfiledTreeState A))
    (FamilyAllowed : Finset (PairedProfiledTreeState A) →
      TwoSortedFamilySuccessor (PairedProfiledTreeState A)
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) → Prop)
    (nextAt : TreeNode
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) →
      Finset (PairedProfiledTreeState A) →
      TwoSortedFamilySuccessor (PairedProfiledTreeState A)
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (hzero : ∀ branch,
      TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots nextAt
          branch 0 = inner.run [])
    (hstep : ∀ branch n,
      PairedProfiledRationalPolicy.Allowed A inner
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots nextAt
          branch n)
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots nextAt
          branch (n + 1))) :
    ∀ branch,
      NatSeqMinEvenParity (fun n =>
        pairedProfiledEntryPriority A
          (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots nextAt
            branch n)) := by
  intro branch
  exact PairedProfiledRationalPolicy.accepts_of_allowed_path A inner
    (fun n => TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
      nextAt branch n)
    (hzero branch) (hstep branch)

/-- Correct history-sensitive recursive extraction at the profiled paired
interface.  The outer finite policy is obtained only after accepting legality
has been proved for the raw, history-dependent family tree. -/
theorem nonempty_pairedProfiledHistoryFamilyRationalPolicy
    (initialRoots : Finset (PairedProfiledTreeState A))
    (FamilyAllowed : Finset (PairedProfiledTreeState A) →
      TwoSortedFamilySuccessor (PairedProfiledTreeState A)
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) → Prop)
    (nextAt : TreeNode
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) →
      Finset (PairedProfiledTreeState A) →
      TwoSortedFamilySuccessor (PairedProfiledTreeState A)
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (hallowed : ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots nextAt node =
          .family roots →
        FamilyAllowed roots (nextAt node roots))
    (hzero : ∀ branch,
      TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots nextAt
          branch 0 = inner.run [])
    (hstep : ∀ branch n,
      PairedProfiledRationalPolicy.Allowed A inner
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots nextAt
          branch n)
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots nextAt
          branch (n + 1)))
    (basis : InputFreeRunParityTreeAutomaton.RationalRunBasis
      (pairedProfiledFamilyAutomaton A initialRoots FamilyAllowed)) :
    Nonempty (InputFreeRunParityTreeAutomaton.RationalTransitionPolicy
      (pairedProfiledFamilyAutomaton A initialRoots FamilyAllowed)) := by
  apply TwoSortedFamilyPolicy.nonempty_rationalPolicy_of_historyAssignment
    (pairedProfiledEntryPriority A) initialRoots FamilyAllowed nextAt hallowed
  · exact pairedProfiledHistoryFamily_selectedParity A inner initialRoots
      FamilyAllowed nextAt hzero hstep
  · exact basis

end

end

end


end DetParityAutomaton

end DistributedSynthesis
