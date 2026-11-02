/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledBlockMonitor

/-!
# A coherent finite family of profiled recurrent controllers

The profiled rational policy is one finite global witness used only in the
existence proof.  At every reachable live policy state this module selects
the corresponding unconditional finite block controller.  The controller's
receiver output carries the exact finite successor certificate checked by
the profiled block monitor.

Reachability proofs are subsingleton data: they cannot be inspected by a
process and do not provide a leader oracle.
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
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

/-- The right-controller alphabet at one profiled process-one state. -/
abbrev ProfiledRightNarrowedControllerLabel
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) :=
  NarrowedBlockLabel In₂ In₁ (ProfiledRightReceiverOutput A) Out₁
    (profiledRightBlockMonitor.{u, v, x, y, s, 1}
      A policy code minimum profile).State

/-- The left-controller alphabet at one profiled process-two state. -/
abbrev ProfiledLeftNarrowedControllerLabel
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) :=
  NarrowedBlockLabel In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂
    (profiledLeftBlockMonitor.{u, v, x, y, s, 1}
      A policy code minimum profile).State

/-- One selected finite certificate-preserving controller at every reachable
live state of the profiled rational policy. -/
structure FiniteProfiledPairedPolicyFamily where
  rightController : ∀ (code : A.State × A.State) (minimum : A.State)
      (profile : RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)),
    PairedProfiledRationalPolicy.Reachable A policy
      (.inr (.inl ((code, minimum), profile))) →
      TransitionRationalTree.{u, max 1 u v x y s, max 1 s u v x} In₁
        (ProfiledRightNarrowedControllerLabel A policy code minimum profile)
  rightWins : ∀ (code : A.State × A.State) (minimum : A.State)
      (profile : RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
      (hreachable : PairedProfiledRationalPolicy.Reachable A policy
        (.inr (.inl ((code, minimum), profile)))),
    NarrowedAllThreadsWin
      (profiledRightBlockMonitor.{u, v, x, y, s, 1}
        A policy code minimum profile)
      (rightController code minimum profile hreachable).labeledTree
  leftController : ∀ (code : A.State × A.State) (minimum : A.State)
      (profile : LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)),
    PairedProfiledRationalPolicy.Reachable A policy
      (.inr (.inr ((code, minimum), profile))) →
      TransitionRationalTree.{v, max 1 u v x y s, max 1 s u v y} In₂
        (ProfiledLeftNarrowedControllerLabel A policy code minimum profile)
  leftWins : ∀ (code : A.State × A.State) (minimum : A.State)
      (profile : LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
      (hreachable : PairedProfiledRationalPolicy.Reachable A policy
        (.inr (.inr ((code, minimum), profile)))),
    NarrowedAllThreadsWin
      (profiledLeftBlockMonitor.{u, v, x, y, s, 1}
        A policy code minimum profile)
      (leftController code minimum profile hreachable).labeledTree

/-- Select the entire profiled controller family simultaneously. -/
noncomputable def finiteProfiledPairedPolicyFamily :
    FiniteProfiledPairedPolicyFamily A policy := by
  classical
  let chooseRight := fun (code : A.State × A.State) (minimum : A.State)
      (profile : RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
      (hreachable : PairedProfiledRationalPolicy.Reachable A policy
        (.inr (.inl ((code, minimum), profile)))) =>
    Classical.choose (exists_finite_profiledProcessOneBlockController
      A policy code minimum profile hreachable)
  let chooseLeft := fun (code : A.State × A.State) (minimum : A.State)
      (profile : LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
      (hreachable : PairedProfiledRationalPolicy.Reachable A policy
        (.inr (.inr ((code, minimum), profile)))) =>
    Classical.choose (exists_finite_profiledProcessTwoBlockController
      A policy code minimum profile hreachable)
  exact {
    rightController := chooseRight
    rightWins := fun code minimum profile hreachable =>
      Classical.choose_spec (exists_finite_profiledProcessOneBlockController
        A policy code minimum profile hreachable)
    leftController := chooseLeft
    leftWins := fun code minimum profile hreachable =>
      Classical.choose_spec (exists_finite_profiledProcessTwoBlockController
        A policy code minimum profile hreachable)
  }

end

end


end DetParityAutomaton

end DistributedSynthesis
