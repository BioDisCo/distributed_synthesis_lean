/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedFirstBlockSoundness

/-!
# Finite bank of profiled guarded first-block controllers

The exceptional first-block key retains the recurrent boundary profile as
part of its live state.  We select one finite certificate-producing controller
at every such finite key.  Proof fields are subsingleton data and are never
available as a run-time leader test.
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

/-- Finite key for the profiled exceptional right block. -/
abbrev ProfiledGuardedFirstRightMacro :=
  Σ source : ProfiledGuardedRightEntrySource A,
    {live : (((A.State × A.State) × A.State) ×
        RightInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) //
      source.1.1 = .inr (.inl live)}

/-- Process-two mirror. -/
abbrev ProfiledGuardedFirstLeftMacro :=
  Σ source : ProfiledGuardedLeftEntrySource A,
    {live : (((A.State × A.State) × A.State) ×
        LeftInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) //
      source.1.1 = .inr (.inr live)}

noncomputable instance : Fintype (ProfiledGuardedFirstRightMacro A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledGuardedFirstLeftMacro A) := by
  classical
  infer_instance

def profiledGuardedFirstRightMacroOfShape
    (source : ProfiledGuardedRightEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hshape : source.1.1 = .inr (.inl ((code, minimum), profile))) :
    ProfiledGuardedFirstRightMacro A :=
  ⟨source, ⟨((code, minimum), profile), hshape⟩⟩

def profiledGuardedFirstLeftMacroOfShape
    (source : ProfiledGuardedLeftEntrySource A)
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hshape : source.1.1 = .inr (.inr ((code, minimum), profile))) :
    ProfiledGuardedFirstLeftMacro A :=
  ⟨source, ⟨((code, minimum), profile), hshape⟩⟩

/-- Simultaneous finite selection in both first-block orientations. -/
structure FiniteProfiledGuardedFirstControllerBank where
  rightController : ∀ key : ProfiledGuardedFirstRightMacro A,
    TransitionRationalTree.{u, max 1 u v x y s, max 1 s u v x} In₁
      (NarrowedBlockLabel In₂ In₁ (ProfiledRightReceiverOutput A) Out₁
        (profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
          A key.1 key.2.1.1.1 key.2.1.1.2 key.2.1.2).State)
  rightWins : ∀ key : ProfiledGuardedFirstRightMacro A,
    NarrowedAllThreadsWin
      (profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
        A key.1 key.2.1.1.1 key.2.1.1.2 key.2.1.2)
      (rightController key).labeledTree
  leftController : ∀ key : ProfiledGuardedFirstLeftMacro A,
    TransitionRationalTree.{v, max 1 u v x y s, max 1 s u v y} In₂
      (NarrowedBlockLabel In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂
        (profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
          A key.1 key.2.1.1.1 key.2.1.1.2 key.2.1.2).State)
  leftWins : ∀ key : ProfiledGuardedFirstLeftMacro A,
    NarrowedAllThreadsWin
      (profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
        A key.1 key.2.1.1.1 key.2.1.1.2 key.2.1.2)
      (leftController key).labeledTree

/-- The complete profiled exceptional-controller bank exists unconditionally. -/
noncomputable def finiteProfiledGuardedFirstControllerBank :
    FiniteProfiledGuardedFirstControllerBank A := by
  classical
  let chooseRight := fun key : ProfiledGuardedFirstRightMacro A =>
    Classical.choose (exists_finite_profiledGuardedFirstRightController
      A key.1 key.2.1.1.1 key.2.1.1.2 key.2.1.2 key.2.2)
  let chooseLeft := fun key : ProfiledGuardedFirstLeftMacro A =>
    Classical.choose (exists_finite_profiledGuardedFirstLeftController
      A key.1 key.2.1.1.1 key.2.1.1.2 key.2.1.2 key.2.2)
  exact {
    rightController := chooseRight
    rightWins := fun key => Classical.choose_spec
      (exists_finite_profiledGuardedFirstRightController
        A key.1 key.2.1.1.1 key.2.1.1.2 key.2.1.2 key.2.2)
    leftController := chooseLeft
    leftWins := fun key => Classical.choose_spec
      (exists_finite_profiledGuardedFirstLeftController
        A key.1 key.2.1.1.1 key.2.1.1.2 key.2.1.2 key.2.2)
  }

/-- Convenient monitor name at a selected right key. -/
noncomputable abbrev profiledGuardedFirstRightMonitorAt
    (key : ProfiledGuardedFirstRightMacro A) :=
  profiledGuardedFirstRightBlockMonitor.{u, v, x, y, s, 1}
    A key.1 key.2.1.1.1 key.2.1.1.2 key.2.1.2

/-- Convenient monitor name at a selected left key. -/
noncomputable abbrev profiledGuardedFirstLeftMonitorAt
    (key : ProfiledGuardedFirstLeftMacro A) :=
  profiledGuardedFirstLeftBlockMonitor.{u, v, x, y, s, 1}
    A key.1 key.2.1.1.1 key.2.1.1.2 key.2.1.2

/-- Every selected right controller exposes the direct feasible-child
readback theorem. -/
noncomputable def FiniteProfiledGuardedFirstControllerBank.rightChild
    (bank : FiniteProfiledGuardedFirstControllerBank A)
    (key : ProfiledGuardedFirstRightMacro A)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    FeasibleProfiledPairedState A := by
  let monitor := profiledGuardedFirstRightMonitorAt A key
  let tree := narrowedInducedTree monitor
    (bank.rightController key).labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (bank.rightWins key)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  exact profiledGuardedFirstRight_childFeasible_of_wins A key.1
    key.2.1.1.1 key.2.1.1.2 key.2.1.2
    (treePlay tree env) hwin n row

/-- Left mirror. -/
noncomputable def FiniteProfiledGuardedFirstControllerBank.leftChild
    (bank : FiniteProfiledGuardedFirstControllerBank A)
    (key : ProfiledGuardedFirstLeftMacro A)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    FeasibleProfiledPairedState A := by
  let monitor := profiledGuardedFirstLeftMonitorAt A key
  let tree := narrowedInducedTree monitor
    (bank.leftController key).labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (bank.leftWins key)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  exact profiledGuardedFirstLeft_childFeasible_of_wins A key.1
    key.2.1.1.1 key.2.1.1.2 key.2.1.2
    (treePlay tree env) hwin n row

end

end


end DetParityAutomaton

end DistributedSynthesis
