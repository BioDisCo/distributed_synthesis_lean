/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndGuardedFirstSoundness
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledControllerFamily

/-!
# Recurrent controller banks below common-policy first-block children

An allowed child is a finite runtime key.  Its recurrent rational policy is
obtained by restricting the supplied guarded policy below a proof-side root
direction.  The coherent recurrent controller family therefore continues the
same policy instead of selecting an unrelated feasible-state policy.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Children below a process-one guarded root -/

/-- Finite child keys admitted by one supplied process-one guarded policy. -/
abbrev EndToEndGuardedRightChild
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy) :=
  {child : PairedProfiledTreeState A //
    ProfiledGuardedRightPolicyAllows A target overlap policy child}

noncomputable instance
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (policy : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy) :
    Fintype (EndToEndGuardedRightChild A target overlap policy) := by
  classical
  infer_instance

/-- The recurrent policy below a process-one guarded child. -/
noncomputable def EndToEndGuardedRightChild.policy
    {target : PairedProfiledTreeState A}
    {overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)}
    {guarded : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedRightChild A target overlap guarded) :
    (pairedProfiledEntryRunAutomaton A child.1).RationalTransitionPolicy :=
  profiledGuardedRightPolicyBelowAllowedChild A target overlap guarded child.1
    child.2

noncomputable def EndToEndGuardedRightChild.family
    {target : PairedProfiledTreeState A}
    {overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)}
    {guarded : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedRightChild A target overlap guarded) :
    FiniteProfiledPairedPolicyFamily A (child.policy A) :=
  finiteProfiledPairedPolicyFamily A (child.policy A)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
theorem EndToEndGuardedRightChild.reachable
    {target : PairedProfiledTreeState A}
    {overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)}
    {guarded : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedRightChild A target overlap guarded) :
    PairedProfiledRationalPolicy.Reachable A (child.policy A) child.1 := by
  refine ⟨[], ?_⟩
  exact (child.policy A).accepts.1.1

/-- After a first-right block, a live process-two child has an unconditional
finite first ordinary left-block controller from the restricted policy. -/
theorem EndToEndGuardedRightChild.exists_leftController
    {target : PairedProfiledTreeState A}
    {overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)}
    {guarded : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedRightChild A target overlap guarded)
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hshape : child.1 = .inr (.inr ((code, minimum), profile))) :
    ∃ controller : TransitionRationalTree.{v, max 1 u v x y s, max 1 s u v y}
      In₂ (ProfiledLeftNarrowedControllerLabel A (child.policy A) code minimum
        profile),
      NarrowedAllThreadsWin
        (profiledLeftBlockMonitor.{u, v, x, y, s, 1}
          A (child.policy A) code minimum profile) controller.labeledTree := by
  have hreachable : PairedProfiledRationalPolicy.Reachable A (child.policy A)
      (.inr (.inr ((code, minimum), profile))) := by
    rw [← hshape]
    exact child.reachable A
  exact exists_finite_profiledProcessTwoBlockController A (child.policy A)
    code minimum profile hreachable

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- The checked erasure of a first-right close forces the admitted child to
have process-two/live shape. -/
theorem EndToEndGuardedRightChild.exists_leftShape_of_close
    {target : PairedProfiledTreeState A}
    {overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)}
    {guarded : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedRightChild A target overlap guarded)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedRightCloseTarget A scan row letter) :
    ∃ (code : A.State × A.State) (minimum : A.State)
        (profile : LeftInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)),
      child.1 = .inr (.inr ((code, minimum), profile)) := by
  cases hchild : child.1 with
  | inl trivial =>
      rw [hchild] at herase
      cases row <;>
        simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          rw [hchild] at herase
          cases row <;>
            simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
      | inr leftLive =>
          rcases leftLive with ⟨⟨code, minimum⟩, profile⟩
          exact ⟨code, minimum, profile, rfl⟩

/-- A certified first-right close therefore hands off immediately to an
ordinary finite left-block controller of the restricted common policy. -/
theorem EndToEndGuardedRightChild.exists_leftController_of_close
    {target : PairedProfiledTreeState A}
    {overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)}
    {guarded : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedRightChild A target overlap guarded)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedRightCloseTarget A scan row letter) :
    ∃ (code : A.State × A.State) (minimum : A.State)
        (profile : LeftInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
        (hshape : child.1 = .inr (.inr ((code, minimum), profile))),
      ∃ controller : TransitionRationalTree.{v, max 1 u v x y s, max 1 s u v y}
        In₂ (ProfiledLeftNarrowedControllerLabel A (child.policy A) code
          minimum profile),
        NarrowedAllThreadsWin
          (profiledLeftBlockMonitor.{u, v, x, y, s, 1}
            A (child.policy A) code minimum profile) controller.labeledTree := by
  obtain ⟨code, minimum, profile, hshape⟩ :=
    child.exists_leftShape_of_close A scan row letter herase
  exact ⟨code, minimum, profile, hshape,
    child.exists_leftController A code minimum profile hshape⟩

/-! ## Children below a process-two guarded root -/

abbrev EndToEndGuardedLeftChild
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy) :=
  {child : PairedProfiledTreeState A //
    ProfiledGuardedLeftPolicyAllows A target overlap policy child}

noncomputable instance
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (policy : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy) :
    Fintype (EndToEndGuardedLeftChild A target overlap policy) := by
  classical
  infer_instance

noncomputable def EndToEndGuardedLeftChild.policy
    {target : PairedProfiledTreeState A}
    {overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)}
    {guarded : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedLeftChild A target overlap guarded) :
    (pairedProfiledEntryRunAutomaton A child.1).RationalTransitionPolicy :=
  profiledGuardedLeftPolicyBelowAllowedChild A target overlap guarded child.1
    child.2

noncomputable def EndToEndGuardedLeftChild.family
    {target : PairedProfiledTreeState A}
    {overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)}
    {guarded : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedLeftChild A target overlap guarded) :
    FiniteProfiledPairedPolicyFamily A (child.policy A) :=
  finiteProfiledPairedPolicyFamily A (child.policy A)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
theorem EndToEndGuardedLeftChild.reachable
    {target : PairedProfiledTreeState A}
    {overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)}
    {guarded : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedLeftChild A target overlap guarded) :
    PairedProfiledRationalPolicy.Reachable A (child.policy A) child.1 := by
  refine ⟨[], ?_⟩
  exact (child.policy A).accepts.1.1

/-- After a first-left block, a live process-one child has the symmetric
ordinary right-block controller. -/
theorem EndToEndGuardedLeftChild.exists_rightController
    {target : PairedProfiledTreeState A}
    {overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)}
    {guarded : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedLeftChild A target overlap guarded)
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hshape : child.1 = .inr (.inl ((code, minimum), profile))) :
    ∃ controller : TransitionRationalTree.{u, max 1 u v x y s, max 1 s u v x}
      In₁ (ProfiledRightNarrowedControllerLabel A (child.policy A) code minimum
        profile),
      NarrowedAllThreadsWin
        (profiledRightBlockMonitor.{u, v, x, y, s, 1}
          A (child.policy A) code minimum profile) controller.labeledTree := by
  have hreachable : PairedProfiledRationalPolicy.Reachable A (child.policy A)
      (.inr (.inl ((code, minimum), profile))) := by
    rw [← hshape]
    exact child.reachable A
  exact exists_finite_profiledProcessOneBlockController A (child.policy A)
    code minimum profile hreachable

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
theorem EndToEndGuardedLeftChild.exists_rightShape_of_close
    {target : PairedProfiledTreeState A}
    {overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)}
    {guarded : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedLeftChild A target overlap guarded)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedLeftCloseTarget A scan row letter) :
    ∃ (code : A.State × A.State) (minimum : A.State)
        (profile : RightInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)),
      child.1 = .inr (.inl ((code, minimum), profile)) := by
  cases hchild : child.1 with
  | inl trivial =>
      rw [hchild] at herase
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          rcases rightLive with ⟨⟨code, minimum⟩, profile⟩
          exact ⟨code, minimum, profile, rfl⟩
      | inr leftLive =>
          rw [hchild] at herase
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase

theorem EndToEndGuardedLeftChild.exists_rightController_of_close
    {target : PairedProfiledTreeState A}
    {overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)}
    {guarded : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy}
    (child : EndToEndGuardedLeftChild A target overlap guarded)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedLeftCloseTarget A scan row letter) :
    ∃ (code : A.State × A.State) (minimum : A.State)
        (profile : RightInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
        (hshape : child.1 = .inr (.inl ((code, minimum), profile))),
      ∃ controller : TransitionRationalTree.{u, max 1 u v x y s, max 1 s u v x}
        In₁ (ProfiledRightNarrowedControllerLabel A (child.policy A) code
          minimum profile),
        NarrowedAllThreadsWin
          (profiledRightBlockMonitor.{u, v, x, y, s, 1}
            A (child.policy A) code minimum profile) controller.labeledTree := by
  obtain ⟨code, minimum, profile, hshape⟩ :=
    child.exists_rightShape_of_close A scan row letter herase
  exact ⟨code, minimum, profile, hshape,
    child.exists_rightController A code minimum profile hshape⟩

/-! ## Direct readback from arbitrary winning narrowed first-block plays -/

/-- The exact target emitted on a winning first-right play, packaged as a
finite admitted child of the supplied guarded policy. -/
noncomputable def endToEndGuardedRightChild_of_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (guarded : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A target overlap guarded code minimum profile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    EndToEndGuardedRightChild A target overlap guarded :=
  ⟨(play n).2.1.target row,
    (endToEndGuardedFirstRight_targetsSafe_of_wins A target overlap guarded
      code minimum profile play hwin n row).2⟩

/-- Pointwise first-right to ordinary-left controller handoff, valid for an
arbitrary winning narrowed first-block play. -/
theorem exists_recurrentLeftController_of_endToEndGuardedFirstRight_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (guarded : (rightProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A target overlap guarded code minimum profile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    let child := endToEndGuardedRightChild_of_wins A target overlap guarded
      code minimum profile play hwin n row
    ∃ (nextCode : A.State × A.State) (nextMinimum : A.State)
        (nextProfile : LeftInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
        (hshape : child.1 =
          .inr (.inr ((nextCode, nextMinimum), nextProfile))),
      ∃ controller : TransitionRationalTree.{v, max 1 u v x y s, max 1 s u v y}
        In₂ (ProfiledLeftNarrowedControllerLabel A (child.policy A)
          nextCode nextMinimum nextProfile),
        NarrowedAllThreadsWin
          (profiledLeftBlockMonitor.{u, v, x, y, s, 1}
            A (child.policy A) nextCode nextMinimum nextProfile)
          controller.labeledTree := by
  let child := endToEndGuardedRightChild_of_wins A target overlap guarded
    code minimum profile play hwin n row
  have hsafe := endToEndGuardedFirstRight_targetsSafe_of_wins A target overlap
    guarded code minimum profile play hwin n row
  exact child.exists_leftController_of_close A
    ((endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
      A target overlap guarded code minimum profile).run play n).2.1
    row (profiledRightPhysicalLetter A (play n)) hsafe.1

noncomputable def endToEndGuardedLeftChild_of_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (guarded : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A target overlap guarded code minimum profile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    EndToEndGuardedLeftChild A target overlap guarded :=
  ⟨(play n).2.1.target row,
    (endToEndGuardedFirstLeft_targetsSafe_of_wins A target overlap guarded
      code minimum profile play hwin n row).2⟩

theorem exists_recurrentRightController_of_endToEndGuardedFirstLeft_wins
    (target : PairedProfiledTreeState A)
    (overlap : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (guarded : (leftProfiledGuardedAutomaton A target overlap).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A target overlap guarded code minimum profile).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) :
    let child := endToEndGuardedLeftChild_of_wins A target overlap guarded
      code minimum profile play hwin n row
    ∃ (nextCode : A.State × A.State) (nextMinimum : A.State)
        (nextProfile : RightInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
        (hshape : child.1 =
          .inr (.inl ((nextCode, nextMinimum), nextProfile))),
      ∃ controller : TransitionRationalTree.{u, max 1 u v x y s, max 1 s u v x}
        In₁ (ProfiledRightNarrowedControllerLabel A (child.policy A)
          nextCode nextMinimum nextProfile),
        NarrowedAllThreadsWin
          (profiledRightBlockMonitor.{u, v, x, y, s, 1}
            A (child.policy A) nextCode nextMinimum nextProfile)
          controller.labeledTree := by
  let child := endToEndGuardedLeftChild_of_wins A target overlap guarded
    code minimum profile play hwin n row
  have hsafe := endToEndGuardedFirstLeft_targetsSafe_of_wins A target overlap
    guarded code minimum profile play hwin n row
  exact child.exists_rightController_of_close A
    ((endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
      A target overlap guarded code minimum profile).run play n).2.1
    row (profiledLeftPhysicalLetter A (play n)) hsafe.1

end


end DetParityAutomaton

end DistributedSynthesis
