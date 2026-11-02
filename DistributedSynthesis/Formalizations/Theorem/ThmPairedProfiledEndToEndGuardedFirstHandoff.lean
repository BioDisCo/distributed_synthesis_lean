/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndGuardedFirstRegularization

/-!
# Handoff from initial controllers to one-policy guarded-first controllers

The staged profiled state emitted by an arbitrary winning initial controller
has the live orientation forced by its checked erased delayed target.  Hence
the guarded policy inherited from the one global policy can be regularized by
the strengthened first-block monitor.

All controller keys below are finite.  The outer direction witnessing that a
staged source belongs to the global policy image remains proof-only.
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

open PairedStrategyMemory

/-! ## The erased delayed target forces the profiled orientation -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem exists_right_profiled_shape_of_initialLeftDelayedTarget
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (target : PairedProfiledTreeState A)
    (herase : erasePairedProfiledState A target =
      initialLeftDelayedTarget A scan letter) :
    ∃ (code : A.State × A.State) (minimum : A.State)
        (profile : RightInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)),
      target = .inr (.inl ((code, minimum), profile)) := by
  rcases target with sink | live
  · simp [erasePairedProfiledState, initialLeftDelayedTarget] at herase
  · rcases live with right | left
    · rcases right with ⟨⟨code, minimum⟩, profile⟩
      exact ⟨code, minimum, profile, rfl⟩
    · simp [erasePairedProfiledState, initialLeftDelayedTarget] at herase

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem exists_left_profiled_shape_of_initialRightDelayedTarget
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (target : PairedProfiledTreeState A)
    (herase : erasePairedProfiledState A target =
      initialRightDelayedTarget A scan letter) :
    ∃ (code : A.State × A.State) (minimum : A.State)
        (profile : LeftInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)),
      target = .inr (.inr ((code, minimum), profile)) := by
  rcases target with sink | live
  · simp [erasePairedProfiledState, initialRightDelayedTarget] at herase
  · rcases live with right | left
    · simp [erasePairedProfiledState, initialRightDelayedTarget] at herase
    · rcases left with ⟨⟨code, minimum⟩, profile⟩
      exact ⟨code, minimum, profile, rfl⟩

namespace PairedStrategyMemory.PairedInitialProfiledRationalPackage

/-! ## Boundary-level controller existence -/

/-- Every activated initial-left boundary admits a finite first-right
controller whose targets stay inside the same common policy. -/
theorem exists_finite_guardedFirstRightController_of_initialLeftActivation
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A)
    (activation : EndToEndInitialLeftActivation A package scan letter source) :
    ∃ (code : A.State × A.State) (minimum : A.State)
        (profile : RightInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
        (hshape : source.2 = .inr (.inl ((code, minimum), profile))),
      ∃ controller : TransitionRationalTree.{u, max 1 u v x y s, max 1 s u v x}
        In₁ (NarrowedBlockLabel In₂ In₁ (ProfiledRightReceiverOutput A) Out₁
          (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
            A source.2 activation.profile activation.policy code minimum
              profile).State),
        NarrowedAllThreadsWin
          (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
            A source.2 activation.profile activation.policy code minimum
              profile)
          controller.labeledTree := by
  obtain ⟨code, minimum, profile, hshape⟩ :=
    exists_right_profiled_shape_of_initialLeftDelayedTarget A scan letter
      source.2 activation.target
  refine ⟨code, minimum, profile, hshape, ?_⟩
  exact exists_finite_endToEndGuardedFirstRightController A source.2
    activation.profile activation.policy code minimum profile hshape

/-- Every activated initial-right boundary admits the symmetric finite
first-left controller. -/
theorem exists_finite_guardedFirstLeftController_of_initialRightActivation
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A)
    (activation : EndToEndInitialRightActivation A package scan letter source) :
    ∃ (code : A.State × A.State) (minimum : A.State)
        (profile : LeftInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
        (hshape : source.2 = .inr (.inr ((code, minimum), profile))),
      ∃ controller : TransitionRationalTree.{v, max 1 u v x y s, max 1 s u v y}
        In₂ (NarrowedBlockLabel In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂
          (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
            A source.2 activation.profile activation.policy code minimum
              profile).State),
        NarrowedAllThreadsWin
          (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
            A source.2 activation.profile activation.policy code minimum
              profile)
          controller.labeledTree := by
  obtain ⟨code, minimum, profile, hshape⟩ :=
    exists_left_profiled_shape_of_initialRightDelayedTarget A scan letter
      source.2 activation.target
  refine ⟨code, minimum, profile, hshape, ?_⟩
  exact exists_finite_endToEndGuardedFirstLeftController A source.2
    activation.profile activation.policy code minimum profile hshape

/-- Source-checking alone suffices: an image witness activates a supplied
guarded policy and then the strengthened regularization theorem applies. -/
theorem exists_finite_guardedFirstRightController_of_initialLeftSourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A)
    (hsource : endToEndInitialLeftSourceOK A package scan letter source) :
    ∃ activation : EndToEndInitialLeftActivation A package scan letter source,
      ∃ (code : A.State × A.State) (minimum : A.State)
          (profile : RightInitialActionProfile
            (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
          (hshape : source.2 = .inr (.inl ((code, minimum), profile))),
        ∃ controller : TransitionRationalTree.{u, max 1 u v x y s, max 1 s u v x}
          In₁ (NarrowedBlockLabel In₂ In₁ (ProfiledRightReceiverOutput A) Out₁
            (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
              A source.2 activation.profile activation.policy code minimum
                profile).State),
          NarrowedAllThreadsWin
            (endToEndGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
              A source.2 activation.profile activation.policy code minimum
                profile)
            controller.labeledTree := by
  let activation := Classical.choice
    (nonempty_endToEndInitialLeftActivation_of_sourceOK A package scan letter
      source hsource)
  exact ⟨activation,
    exists_finite_guardedFirstRightController_of_initialLeftActivation A
      package scan letter source activation⟩

/-- Initial-right mirror. -/
theorem exists_finite_guardedFirstLeftController_of_initialRightSourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A)
    (hsource : endToEndInitialRightSourceOK A package scan letter source) :
    ∃ activation : EndToEndInitialRightActivation A package scan letter source,
      ∃ (code : A.State × A.State) (minimum : A.State)
          (profile : LeftInitialActionProfile
            (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
          (hshape : source.2 = .inr (.inr ((code, minimum), profile))),
        ∃ controller : TransitionRationalTree.{v, max 1 u v x y s, max 1 s u v y}
          In₂ (NarrowedBlockLabel In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂
            (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
              A source.2 activation.profile activation.policy code minimum
                profile).State),
          NarrowedAllThreadsWin
            (endToEndGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
              A source.2 activation.profile activation.policy code minimum
                profile)
            controller.labeledTree := by
  let activation := Classical.choice
    (nonempty_endToEndInitialRightActivation_of_sourceOK A package scan letter
      source hsource)
  exact ⟨activation,
    exists_finite_guardedFirstLeftController_of_initialRightActivation A
      package scan letter source activation⟩

end PairedStrategyMemory.PairedInitialProfiledRationalPackage

end


end DetParityAutomaton

end DistributedSynthesis
