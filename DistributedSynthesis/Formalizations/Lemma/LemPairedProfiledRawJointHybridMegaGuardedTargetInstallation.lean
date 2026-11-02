/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridGuardedSiblingLocalInstallation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaRootStaging

/-!
# Recurrent installation after a guarded sibling close

A guarded sibling front can be the special table below the initial common
root or a table below an arbitrary root-pinned recurrent common control.  In
both cases its emitted target is checked against the exact finite sibling
relation and embedded in the corresponding summand of the mega child family.

The lookup functions are executable finite tests.  Their sum tags record only
which finite table supplied the target; no graph, orientation, or leader bit
is inspected.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev Installation :=
  ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin

/-! ## Deterministic checked-child lookup -/

/-- Check a guarded right-table target and embed it in the initial or
recurrent sibling-target summand of the mega family. -/
noncomputable def profiledRawJointHybridMegaGuardedRightTargetChild?
    (installation : Installation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A) :
    Option (ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) := by
  classical
  cases installation with
  | inl initial =>
      exact if htarget : ProfiledRawJointRightSiblingSharedAllowedTarget A
          (profiledRawJointHybridInitialSiblingParentFamily A strategy
            initial.first)
          (profiledRawJointHybridInitialSiblingDirection initial.current)
          target then
        some (profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy
          hwin initialBank
          ⟨initial,
            profiledRawJointSiblingTargetChildOfRight A strategy
              (profiledRawJointHybridInitialSiblingParentFamily A strategy
                initial.first)
              (profiledRawJointHybridInitialSiblingDirection initial.current)
              ⟨target, htarget⟩⟩)
      else none
  | inr recurrent =>
      exact if htarget : ProfiledRawJointRightSiblingSharedAllowedTarget A
          (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
            recurrent.1)
          (profiledRawJointBothRestartDirection recurrent.2) target then
        some (profiledRawJointHybridMegaChildOfCommonSiblingTarget A strategy
          hwin initialBank
          ⟨recurrent.1, recurrent.2,
            profiledRawJointSiblingTargetChildOfRight A strategy
              (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
                recurrent.1)
              (profiledRawJointBothRestartDirection recurrent.2)
              ⟨target, htarget⟩⟩)
      else none

/-- Left-table mirror. -/
noncomputable def profiledRawJointHybridMegaGuardedLeftTargetChild?
    (installation : Installation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A) :
    Option (ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) := by
  classical
  cases installation with
  | inl initial =>
      exact if htarget : ProfiledRawJointLeftSiblingSharedAllowedTarget A
          (profiledRawJointHybridInitialSiblingParentFamily A strategy
            initial.first)
          (profiledRawJointHybridInitialSiblingDirection initial.current)
          target then
        some (profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy
          hwin initialBank
          ⟨initial,
            profiledRawJointSiblingTargetChildOfLeft A strategy
              (profiledRawJointHybridInitialSiblingParentFamily A strategy
                initial.first)
              (profiledRawJointHybridInitialSiblingDirection initial.current)
              ⟨target, htarget⟩⟩)
      else none
  | inr recurrent =>
      exact if htarget : ProfiledRawJointLeftSiblingSharedAllowedTarget A
          (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
            recurrent.1)
          (profiledRawJointBothRestartDirection recurrent.2) target then
        some (profiledRawJointHybridMegaChildOfCommonSiblingTarget A strategy
          hwin initialBank
          ⟨recurrent.1, recurrent.2,
            profiledRawJointSiblingTargetChildOfLeft A strategy
              (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
                recurrent.1)
              (profiledRawJointBothRestartDirection recurrent.2)
              ⟨target, htarget⟩⟩)
      else none

/-! ## Staged literal roots -/

/-- A checked guarded right close and its literal left recurrent root. -/
abbrev ProfiledRawJointHybridMegaGuardedRightTargetRoot :=
  Σ child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank,
    ProfiledRawJointHybridMegaLeftMacro A strategy hwin initialBank child

/-- Checked guarded left-close mirror. -/
abbrev ProfiledRawJointHybridMegaGuardedLeftTargetRoot :=
  Σ child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank,
    ProfiledRawJointHybridMegaRightMacro A strategy hwin initialBank child

/-- Total right-target/root lookup. -/
noncomputable def profiledRawJointHybridMegaGuardedRightTargetRoot?
    (installation : Installation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A) :
    Option (ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank) :=
  match profiledRawJointHybridMegaGuardedRightTargetChild? A strategy hwin
      initialBank installation target with
  | none => none
  | some child =>
      match profiledRawJointHybridMegaLeftRoot? A strategy hwin initialBank
          child with
      | none => none
      | some root => some ⟨child, root⟩

/-- Total left-target/root lookup. -/
noncomputable def profiledRawJointHybridMegaGuardedLeftTargetRoot?
    (installation : Installation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A) :
    Option (ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank) :=
  match profiledRawJointHybridMegaGuardedLeftTargetChild? A strategy hwin
      initialBank installation target with
  | none => none
  | some child =>
      match profiledRawJointHybridMegaRightRoot? A strategy hwin initialBank
          child with
      | none => none
      | some root => some ⟨child, root⟩

/-! ## Literal slot carried by a successful root lookup -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

private theorem profiledRawJointHybridMegaGuardedRightTargetChild?_code
    (installation : Installation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A)
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (hchild : profiledRawJointHybridMegaGuardedRightTargetChild? A strategy
      hwin initialBank installation target = some child) :
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
      ).code A = target := by
  classical
  cases installation with
  | inl initial =>
      by_cases hallowed : ProfiledRawJointRightSiblingSharedAllowedTarget A
          (profiledRawJointHybridInitialSiblingParentFamily A strategy
            initial.first)
          (profiledRawJointHybridInitialSiblingDirection initial.current)
          target
      · simp [profiledRawJointHybridMegaGuardedRightTargetChild?, hallowed]
          at hchild
        subst child
        simp [profiledRawJointHybridInitialSiblingTargetChildSource]
      · simp [profiledRawJointHybridMegaGuardedRightTargetChild?, hallowed]
          at hchild
  | inr recurrent =>
      by_cases hallowed : ProfiledRawJointRightSiblingSharedAllowedTarget A
          (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
            recurrent.1)
          (profiledRawJointBothRestartDirection recurrent.2) target
      · simp [profiledRawJointHybridMegaGuardedRightTargetChild?, hallowed]
          at hchild
        subst child
        simp [profiledRawJointHybridCommonSiblingTargetSource]
      · simp [profiledRawJointHybridMegaGuardedRightTargetChild?, hallowed]
          at hchild

private theorem profiledRawJointHybridMegaGuardedLeftTargetChild?_code
    (installation : Installation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A)
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (hchild : profiledRawJointHybridMegaGuardedLeftTargetChild? A strategy
      hwin initialBank installation target = some child) :
    (profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
      ).code A = target := by
  classical
  cases installation with
  | inl initial =>
      by_cases hallowed : ProfiledRawJointLeftSiblingSharedAllowedTarget A
          (profiledRawJointHybridInitialSiblingParentFamily A strategy
            initial.first)
          (profiledRawJointHybridInitialSiblingDirection initial.current)
          target
      · simp [profiledRawJointHybridMegaGuardedLeftTargetChild?, hallowed]
          at hchild
        subst child
        simp [profiledRawJointHybridInitialSiblingTargetChildSource]
      · simp [profiledRawJointHybridMegaGuardedLeftTargetChild?, hallowed]
          at hchild
  | inr recurrent =>
      by_cases hallowed : ProfiledRawJointLeftSiblingSharedAllowedTarget A
          (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
            recurrent.1)
          (profiledRawJointBothRestartDirection recurrent.2) target
      · simp [profiledRawJointHybridMegaGuardedLeftTargetChild?, hallowed]
          at hchild
        subst child
        simp [profiledRawJointHybridCommonSiblingTargetSource]
      · simp [profiledRawJointHybridMegaGuardedLeftTargetChild?, hallowed]
          at hchild

private theorem profiledRawJointHybridMegaLeftRoot?_slot
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (root : ProfiledRawJointHybridMegaLeftMacro A strategy hwin initialBank
      child)
    (hroot : profiledRawJointHybridMegaLeftRoot? A strategy hwin initialBank
      child = some root) :
    ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
      ).code A).family.left () = some root.slot := by
  classical
  unfold profiledRawJointHybridMegaLeftRoot? at hroot
  split at hroot
  · cases hroot
  · simp only [Option.some.injEq] at hroot
    subst root
    assumption

private theorem profiledRawJointHybridMegaRightRoot?_slot
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (root : ProfiledRawJointHybridMegaRightMacro A strategy hwin initialBank
      child)
    (hroot : profiledRawJointHybridMegaRightRoot? A strategy hwin initialBank
      child = some root) :
    ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
      ).code A).family.right () = some root.slot := by
  classical
  unfold profiledRawJointHybridMegaRightRoot? at hroot
  split at hroot
  · cases hroot
  · simp only [Option.some.injEq] at hroot
    subst root
    assumption

/-- A successful guarded-right lookup stages the very left slot stored by
the checked target code. -/
theorem profiledRawJointHybridMegaGuardedRightTargetRoot?_slot
    (installation : Installation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A)
    (root : ProfiledRawJointHybridMegaGuardedRightTargetRoot A strategy hwin
      initialBank)
    (hroot : profiledRawJointHybridMegaGuardedRightTargetRoot? A strategy hwin
      initialBank installation target = some root) :
    target.family.left () = some root.2.slot := by
  classical
  unfold profiledRawJointHybridMegaGuardedRightTargetRoot? at hroot
  cases hchild : profiledRawJointHybridMegaGuardedRightTargetChild? A strategy
      hwin initialBank installation target with
  | none => simp [hchild] at hroot
  | some child =>
      rw [hchild] at hroot
      cases hstage : profiledRawJointHybridMegaLeftRoot? A strategy hwin
          initialBank child with
      | none => simp [hstage] at hroot
      | some stage =>
          simp only [hstage, Option.some.injEq] at hroot
          subst root
          have hcode :=
            profiledRawJointHybridMegaGuardedRightTargetChild?_code A strategy
              hwin initialBank installation target child hchild
          have hslot := profiledRawJointHybridMegaLeftRoot?_slot A strategy
            hwin initialBank child stage hstage
          exact hcode ▸ hslot

/-- Successful guarded-left lookup mirror. -/
theorem profiledRawJointHybridMegaGuardedLeftTargetRoot?_slot
    (installation : Installation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A)
    (root : ProfiledRawJointHybridMegaGuardedLeftTargetRoot A strategy hwin
      initialBank)
    (hroot : profiledRawJointHybridMegaGuardedLeftTargetRoot? A strategy hwin
      initialBank installation target = some root) :
    target.family.right () = some root.2.slot := by
  classical
  unfold profiledRawJointHybridMegaGuardedLeftTargetRoot? at hroot
  cases hchild : profiledRawJointHybridMegaGuardedLeftTargetChild? A strategy
      hwin initialBank installation target with
  | none => simp [hchild] at hroot
  | some child =>
      rw [hchild] at hroot
      cases hstage : profiledRawJointHybridMegaRightRoot? A strategy hwin
          initialBank child with
      | none => simp [hstage] at hroot
      | some stage =>
          simp only [hstage, Option.some.injEq] at hroot
          subst root
          have hcode :=
            profiledRawJointHybridMegaGuardedLeftTargetChild?_code A strategy
              hwin initialBank installation target child hchild
          have hslot := profiledRawJointHybridMegaRightRoot?_slot A strategy
            hwin initialBank child stage hstage
          exact hcode ▸ hslot

end

end

end DetParityAutomaton

end DistributedSynthesis
