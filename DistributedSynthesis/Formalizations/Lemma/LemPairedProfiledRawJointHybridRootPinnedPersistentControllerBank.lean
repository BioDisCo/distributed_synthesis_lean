/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentRightBlock
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentLeftBlock

/-!
# One finite controller bank below an exact guarded hybrid root

For one first-input index, all recurrent controls use false/one-sided keys of
the same root-pinned hybrid policy.  This file selects the installed move and
the target-parametric right/left controllers once at every live key.

The exact close maps return complete guarded-policy states.  Their targets
are definitionally the strict successor keys of the selected installed move,
so they are allowed edges of the same table and keep the fresh bit false.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (first : In₁ × In₂)

/-! ## Finite live macros -/

structure ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro where
  key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
    hwin first
  slot : ProfiledRawRightSlot A
  active_slot : key.incidenceCode.family.right () = some slot

structure ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro where
  key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
    hwin first
  slot : ProfiledRawLeftSlot A
  active_slot : key.incidenceCode.family.left () = some slot

noncomputable instance
    profiledRawJointHybridInitialRootPinnedPersistentRightMacroFintype :
    Fintype
      (ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) := by
  classical
  let encode := fun entry :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first ↦ (entry.key, entry.slot)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftKey, leftSlot, leftActive⟩
    rcases right with ⟨rightKey, rightSlot, rightActive⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

noncomputable instance
    profiledRawJointHybridInitialRootPinnedPersistentLeftMacroFintype :
    Fintype
      (ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) := by
  classical
  let encode := fun entry :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first ↦ (entry.key, entry.slot)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftKey, leftSlot, leftActive⟩
    rcases right with ⟨rightKey, rightSlot, rightActive⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

/-! ## Once-selected installed moves and exact close maps -/

noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentInstalledMove
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first) :
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
      strategy hwin first key :=
  Classical.choice
    (nonempty_profiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove
      A strategy hwin first key)

/-- Exact complete-state close map for a right block. -/
noncomputable def
    ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro.closeKey
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy hwin
      first :=
  (profiledRawJointHybridInitialRootPinnedPersistentInstalledMove A strategy
    hwin first source.key).strictSuccessorKey A
      (profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)

/-- Left-block mirror. -/
noncomputable def
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro.closeKey
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy hwin
      first :=
  (profiledRawJointHybridInitialRootPinnedPersistentInstalledMove A strategy
    hwin first source.key).strictSuccessorKey A
      (profiledRawJointUnitLeftActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)

section
omit [DecidableEq In₁] [DecidableEq In₂]

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem
    ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro.close_allowed
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin first
      source.key.state (source.closeKey A strategy hwin first row past input
        ).state :=
  (profiledRawJointHybridInitialRootPinnedPersistentInstalledMove A strategy
    hwin first source.key).strict_allowedTarget A
      (profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)

theorem
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro.close_allowed
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin first
      source.key.state (source.closeKey A strategy hwin first row past input
        ).state :=
  (profiledRawJointHybridInitialRootPinnedPersistentInstalledMove A strategy
    hwin first source.key).strict_allowedTarget A
      (profiledRawJointUnitLeftActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input)

/-- The right close map carries the exact literal opposite-lane slot. -/
theorem
    ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro.close_slot
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ∃ lambda : ProcOnePairedRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      (profiledRawJointHybridInitialRootPinnedPersistentInstalledMove A
          strategy hwin first source.key).rawMove.rightLambda () =
          some lambda ∧
        rightInitialFirstProfile lambda = source.slot.2 ∧
        PairedRightForeverAccepts A source.slot.1.1 lambda ∧
        (source.closeKey A strategy hwin first row past input
          ).incidenceCode.family.left () =
          some (profiledRawRightChildSlot A source.slot lambda row past input) := by
  rcases
      (profiledRawJointHybridInitialRootPinnedPersistentInstalledMove A
        strategy hwin first source.key).unitRight_physicalClose A source.slot
          source.active_slot row past input with
    ⟨lambda, hlambda, hprofile, hforever, hslot, _⟩
  exact ⟨lambda, hlambda, hprofile, hforever, hslot⟩

/-- Left close-map mirror. -/
theorem
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro.close_slot
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ∃ lambda : ProcTwoPairedLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      (profiledRawJointHybridInitialRootPinnedPersistentInstalledMove A
          strategy hwin first source.key).rawMove.leftLambda () =
          some lambda ∧
        leftInitialFirstProfile lambda = source.slot.2 ∧
        PairedLeftForeverAccepts A source.slot.1.1 lambda ∧
        (source.closeKey A strategy hwin first row past input
          ).incidenceCode.family.right () =
          some (profiledRawLeftChildSlot A source.slot lambda row past input) := by
  rcases
      (profiledRawJointHybridInitialRootPinnedPersistentInstalledMove A
        strategy hwin first source.key).unitLeft_physicalClose A source.slot
          source.active_slot row past input with
    ⟨lambda, hlambda, hprofile, hforever, hslot, _⟩
  exact ⟨lambda, hlambda, hprofile, hforever, hslot⟩

end

end

/-! ## Once-selected target-parametric controllers -/

abbrev ProfiledRawJointHybridInitialRootPinnedPersistentTarget :=
  ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first

abbrev ProfiledRawJointHybridInitialRootPinnedPersistentRightControllerAt
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :=
  { controller :
      TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
        (NarrowedBlockLabel In₂ In₁
          (ProfiledRawJointTargetRightReceiverOutput
            (Out₁ := Out₁) (Out₂ := Out₂)
            (ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy
              first))
          Out₁
          (profiledRawJointTargetRightBlockMonitor A
            (ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy
              first)
            (profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A)
            (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy
              hwin first source.key.state)
            source.slot).State) //
    NarrowedAllThreadsWin
      (profiledRawJointTargetRightBlockMonitor A
        (ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy
          first)
        (profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A)
        (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
          first source.key.state)
        source.slot) controller.labeledTree }

abbrev ProfiledRawJointHybridInitialRootPinnedPersistentLeftControllerAt
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :=
  { controller :
      TransitionRationalTree.{v, max u v x y s, max u v y s} In₂
        (NarrowedBlockLabel In₁ In₂
          (ProfiledRawJointTargetLeftReceiverOutput
            (Out₁ := Out₁) (Out₂ := Out₂)
            (ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy
              first))
          Out₂
          (profiledRawJointTargetLeftBlockMonitor A
            (ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy
              first)
            (profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState A)
            (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy
              hwin first source.key.state)
            source.slot).State) //
    NarrowedAllThreadsWin
      (profiledRawJointTargetLeftBlockMonitor A
        (ProfiledRawJointHybridInitialRootPinnedPersistentTarget A strategy
          first)
        (profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState A)
        (ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
          first source.key.state)
        source.slot) controller.labeledTree }

noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentRightControllerAt
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :
    ProfiledRawJointHybridInitialRootPinnedPersistentRightControllerAt A
      strategy hwin first source := by
  let installed :=
    profiledRawJointHybridInitialRootPinnedPersistentInstalledMove A strategy
      hwin first source.key
  exact ⟨Classical.choose
      (exists_profiledRawJointHybridInitialRootPinnedPersistentRightController
        A installed source.slot source.active_slot),
    Classical.choose_spec
      (exists_profiledRawJointHybridInitialRootPinnedPersistentRightController
        A installed source.slot source.active_slot)⟩

noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentLeftControllerAt
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftControllerAt A
      strategy hwin first source := by
  let installed :=
    profiledRawJointHybridInitialRootPinnedPersistentInstalledMove A strategy
      hwin first source.key
  exact ⟨Classical.choose
      (exists_profiledRawJointHybridInitialRootPinnedPersistentLeftController
        A installed source.slot source.active_slot),
    Classical.choose_spec
      (exists_profiledRawJointHybridInitialRootPinnedPersistentLeftController
        A installed source.slot source.active_slot)⟩

/-- The finite bank over all live macros of this one first-input policy. -/
structure ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank where
  right : ∀ source,
    ProfiledRawJointHybridInitialRootPinnedPersistentRightControllerAt A
      strategy hwin first source
  left : ∀ source,
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftControllerAt A
      strategy hwin first source

noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentControllerBank :
    ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A strategy
      hwin first where
  right := fun source ↦
    profiledRawJointHybridInitialRootPinnedPersistentRightControllerAt A
      strategy hwin first source
  left := fun source ↦
    profiledRawJointHybridInitialRootPinnedPersistentLeftControllerAt A
      strategy hwin first source

end


end DetParityAutomaton

end DistributedSynthesis
