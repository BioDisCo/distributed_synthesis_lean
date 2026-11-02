/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenRepresentableAutomaton

/-! # History rationalization for productive classified moves -/

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

noncomputable def profiledOpenRepresentableNextAt
    (moveAt : TreeNode (ProfiledOpenClassifiedDirection A) →
      Finset (ProfiledOpenClassifiedAnchor A) →
        ProfiledOpenRepresentableMove A) :
    TreeNode (ProfiledOpenClassifiedDirection A) →
      Finset (ProfiledOpenClassifiedAnchor A) →
        TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
          (ProfiledOpenClassifiedDirection A) :=
  fun node roots => (moveAt node roots).successor A

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenRepresentableHistory_allowed
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (moveAt : TreeNode (ProfiledOpenClassifiedDirection A) →
      Finset (ProfiledOpenClassifiedAnchor A) →
        ProfiledOpenRepresentableMove A)
    (hvalid : ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots
          (profiledOpenRepresentableNextAt A moveAt) node = .family roots →
        (moveAt node roots).Valid A)
    (hroots : ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots
          (profiledOpenRepresentableNextAt A moveAt) node = .family roots →
        (moveAt node roots).roots A = roots) :
    ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots
          (profiledOpenRepresentableNextAt A moveAt) node = .family roots →
        ProfiledOpenRepresentableFamilyAllowed A roots
          (profiledOpenRepresentableNextAt A moveAt node roots) := by
  intro node roots hrun
  exact ⟨moveAt node roots, hvalid node roots hrun,
    hroots node roots hrun, rfl⟩

theorem profiledOpenRepresentableHistory_selectedParity
    {initialState : PairedProfiledTreeState A}
    (inner :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (moveAt : TreeNode (ProfiledOpenClassifiedDirection A) →
      Finset (ProfiledOpenClassifiedAnchor A) →
        ProfiledOpenRepresentableMove A)
    (hzero : ∀ branch,
      (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
        (profiledOpenRepresentableNextAt A moveAt) branch 0).toProfiledState =
          inner.run [])
    (hstep : ∀ branch n,
      PairedProfiledRationalPolicy.Allowed A inner
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenRepresentableNextAt A moveAt) branch n).toProfiledState
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenRepresentableNextAt A moveAt) branch (n + 1)).toProfiledState) :
    ∀ branch,
      NatSeqMinEvenParity (fun n =>
        profiledOpenClassifiedAnchorPriority A
          (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
            (profiledOpenRepresentableNextAt A moveAt) branch n)) := by
  intro branch
  rw [show (fun n =>
      profiledOpenClassifiedAnchorPriority A
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenRepresentableNextAt A moveAt) branch n)) =
      (fun n => pairedProfiledEntryPriority A
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenRepresentableNextAt A moveAt) branch n).toProfiledState) by
    funext n
    exact profiledOpenClassifiedAnchorPriority_eq A _]
  exact PairedProfiledRationalPolicy.accepts_of_allowed_path A inner
    (fun n =>
      (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
        (profiledOpenRepresentableNextAt A moveAt) branch n).toProfiledState)
    (hzero branch) (hstep branch)

theorem nonempty_profiledOpenRepresentableHistoryRationalPolicy
    {initialState : PairedProfiledTreeState A}
    (inner :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (moveAt : TreeNode (ProfiledOpenClassifiedDirection A) →
      Finset (ProfiledOpenClassifiedAnchor A) →
        ProfiledOpenRepresentableMove A)
    (hvalid : ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots
          (profiledOpenRepresentableNextAt A moveAt) node = .family roots →
        (moveAt node roots).Valid A)
    (hroots : ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots
          (profiledOpenRepresentableNextAt A moveAt) node = .family roots →
        (moveAt node roots).roots A = roots)
    (hzero : ∀ branch,
      (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
        (profiledOpenRepresentableNextAt A moveAt) branch 0).toProfiledState =
          inner.run [])
    (hstep : ∀ branch n,
      PairedProfiledRationalPolicy.Allowed A inner
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenRepresentableNextAt A moveAt) branch n).toProfiledState
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenRepresentableNextAt A moveAt) branch (n + 1)).toProfiledState)
    (basis : InputFreeRunParityTreeAutomaton.RationalRunBasis
      (profiledOpenRepresentableFamilyRunAutomaton A initialRoots)) :
    Nonempty (InputFreeRunParityTreeAutomaton.RationalTransitionPolicy
      (profiledOpenRepresentableFamilyRunAutomaton A initialRoots)) := by
  apply TwoSortedFamilyPolicy.nonempty_rationalPolicy_of_historyAssignment
    (profiledOpenClassifiedAnchorPriority A) initialRoots
    (ProfiledOpenRepresentableFamilyAllowed A)
    (profiledOpenRepresentableNextAt A moveAt)
  · exact profiledOpenRepresentableHistory_allowed A initialRoots moveAt
      hvalid hroots
  · exact profiledOpenRepresentableHistory_selectedParity A inner
      initialRoots moveAt hzero hstep
  · exact basis

end

/-! ## Single remaining global parity certificate -/

noncomputable def profiledOpenRepresentableCanonicalNextAt
    (_node : TreeNode (ProfiledOpenClassifiedDirection A))
    (roots : Finset (ProfiledOpenClassifiedAnchor A)) :
    TwoSortedFamilySuccessor (ProfiledOpenClassifiedAnchor A)
      (ProfiledOpenClassifiedDirection A) :=
  profiledOpenRepresentableSuccessorFor A roots

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenRepresentableHistoryRun_eq_deterministicRun
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A)) :
    ∀ node,
      TwoSortedFamilyPolicy.historyRun initialRoots
          (profiledOpenRepresentableCanonicalNextAt A) node =
        TwoSortedFamilyPolicy.deterministicRun initialRoots
          (profiledOpenRepresentableSuccessorFor A) node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node direction ih =>
      rw [TwoSortedFamilyPolicy.historyRun_append,
        TwoSortedFamilyPolicy.deterministicRun_append, ih]
      rfl

/-- Exact global obligation left after local reversal and recursive
productivity have been discharged.  It deliberately states epoch parity on
the one canonical productive unfolding; it is not inferred from separate
block acceptance. -/
def ProfiledOpenRepresentableGlobalParity
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A)) : Prop :=
  ∀ branch : Nat → ProfiledOpenClassifiedDirection A,
    NatSeqMinEvenParity (fun n =>
      profiledOpenClassifiedAnchorPriority A
        (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
          (profiledOpenRepresentableCanonicalNextAt A) branch n))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Productive recursion plus the one honest global parity certificate yields
the finite rational outer policy. -/
theorem nonempty_profiledOpenRepresentableRationalPolicy_of_globalParity
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (hinitial : ProfiledOpenRepresentableFamily A initialRoots)
    (hparity : ProfiledOpenRepresentableGlobalParity A initialRoots)
    (basis : InputFreeRunParityTreeAutomaton.RationalRunBasis
      (profiledOpenRepresentableFamilyRunAutomaton A initialRoots)) :
    Nonempty (InputFreeRunParityTreeAutomaton.RationalTransitionPolicy
      (profiledOpenRepresentableFamilyRunAutomaton A initialRoots)) := by
  apply TwoSortedFamilyPolicy.nonempty_rationalPolicy_of_historyAssignment
    (profiledOpenClassifiedAnchorPriority A) initialRoots
    (ProfiledOpenRepresentableFamilyAllowed A)
    (profiledOpenRepresentableCanonicalNextAt A)
  · intro node roots hrun
    have hdet : TwoSortedFamilyPolicy.deterministicRun initialRoots
        (profiledOpenRepresentableSuccessorFor A) node = .family roots := by
      rw [← profiledOpenRepresentableHistoryRun_eq_deterministicRun A
        initialRoots node]
      exact hrun
    have hfamily := profiledOpenRepresentableDeterministicRun_productive A
      initialRoots hinitial node
    rw [hdet] at hfamily
    exact profiledOpenRepresentableSuccessorFor_allowed A roots hfamily
  · exact hparity
  · exact basis

end

end


end DetParityAutomaton

end DistributedSynthesis
