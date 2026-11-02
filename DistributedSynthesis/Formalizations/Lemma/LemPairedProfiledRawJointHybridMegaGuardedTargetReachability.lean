/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedTargetInstallation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridGuardedSiblingCommonPair
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLocalStrictReachability

/-!
# Reachable guarded targets enter the hybrid mega family

Every hybrid guarded installation is represented by one literal guarded
common pair.  The generic strict-prefix safety theorem therefore applies to
its two finite tables.  This file transports the resulting target certificate
back through the initial/recurrent installation tag and proves that the
executable mega-child lookup succeeds on every real prefix.
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

/-! ## Installation-indexed target safety -/

/-- The finite target relation stored in a guarded-right installation is the
shared semantic sibling relation named by that installation. -/
private theorem profiledRawJointHybridGuardedRightMoveAt_allowed_iff
    (installation : Installation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A) :
    profiledRawJointRightPhysicalSiblingAllowed A
        (profiledRawJointHybridGuardedRightMoveAt A strategy hwin
          installation).1.base target ↔
      match installation with
      | .inl initial =>
          ProfiledRawJointRightSiblingSharedAllowedTarget A
            (profiledRawJointHybridInitialSiblingParentFamily A strategy
              initial.first)
            (profiledRawJointHybridInitialSiblingDirection initial.current)
            target
      | .inr recurrent =>
          ProfiledRawJointRightSiblingSharedAllowedTarget A
            (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
              recurrent.1)
            (profiledRawJointBothRestartDirection recurrent.2) target := by
  cases installation with
  | inl initial =>
      change profiledRawJointRightPhysicalSiblingAllowed A
          (profiledRawJointRightPhysicalSiblingDescriptorOf A
            (profiledRawJointHybridInitialSiblingParentFamily A strategy
              initial.first)
            (profiledRawJointHybridInitialSiblingDirection initial.current)
            ((profiledRawJointHybridInitialSiblingWorld A strategy
              initial.first initial.current).procOneMember A)) target ↔ _
      exact profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff A _
        _ _ target
  | inr recurrent =>
      change profiledRawJointRightPhysicalSiblingAllowed A
          (profiledRawJointRightPhysicalSiblingDescriptorOf A
            (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
              recurrent.1)
            (profiledRawJointBothRestartDirection recurrent.2)
            ((profiledRawJointHybridCommonSiblingWorld A strategy hwin
              recurrent.1 recurrent.2).procOneMember A)) target ↔ _
      exact profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff A _
        _ _ target

/-- Left-installation mirror. -/
private theorem profiledRawJointHybridGuardedLeftMoveAt_allowed_iff
    (installation : Installation A strategy hwin)
    (target : ProfiledRawJointUnitTarget A) :
    profiledRawJointLeftPhysicalSiblingAllowed A
        (profiledRawJointHybridGuardedLeftMoveAt A strategy hwin
          installation).1.base target ↔
      match installation with
      | .inl initial =>
          ProfiledRawJointLeftSiblingSharedAllowedTarget A
            (profiledRawJointHybridInitialSiblingParentFamily A strategy
              initial.first)
            (profiledRawJointHybridInitialSiblingDirection initial.current)
            target
      | .inr recurrent =>
          ProfiledRawJointLeftSiblingSharedAllowedTarget A
            (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
              recurrent.1)
            (profiledRawJointBothRestartDirection recurrent.2) target := by
  cases installation with
  | inl initial =>
      change profiledRawJointLeftPhysicalSiblingAllowed A
          (profiledRawJointLeftPhysicalSiblingDescriptorOf A
            (profiledRawJointHybridInitialSiblingParentFamily A strategy
              initial.first)
            (profiledRawJointHybridInitialSiblingDirection initial.current)
            ((profiledRawJointHybridInitialSiblingWorld A strategy
              initial.first initial.current).procTwoMember A)) target ↔ _
      exact profiledRawJointLeftPhysicalSiblingDescriptorOf_allowed_iff A _ _
        _ target
  | inr recurrent =>
      change profiledRawJointLeftPhysicalSiblingAllowed A
          (profiledRawJointLeftPhysicalSiblingDescriptorOf A
            (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
              recurrent.1)
            (profiledRawJointBothRestartDirection recurrent.2)
            ((profiledRawJointHybridCommonSiblingWorld A strategy hwin
              recurrent.1 recurrent.2).procTwoMember A)) target ↔ _
      exact profiledRawJointLeftPhysicalSiblingDescriptorOf_allowed_iff A _ _
        _ target

/-- A target emitted at a real guarded-right prefix belongs to the exact
initial or recurrent sibling relation named by its installation. -/
theorem profiledRawJointHybridGuardedRightPrefixTargetAllowed
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (row : PairedEntryRow) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let target :=
      (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin pair
        past input).target row
    match installation with
    | .inl initial =>
        ProfiledRawJointRightSiblingSharedAllowedTarget A
          (profiledRawJointHybridInitialSiblingParentFamily A strategy
            initial.first)
          (profiledRawJointHybridInitialSiblingDirection initial.current)
          target
    | .inr recurrent =>
        ProfiledRawJointRightSiblingSharedAllowedTarget A
          (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
            recurrent.1)
          (profiledRawJointBothRestartDirection recurrent.2) target := by
  classical
  dsimp only
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let target :=
    (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin pair past
      input).target row
  have hsafe := profiledRawJointGuardedCommonRightPrefixTargetSafe A strategy
    hwin pair past input row
  have hpair := profiledRawJointHybridGuardedCommonPairAt_right A strategy hwin
    installation
  change pair.1.1 =
    profiledRawJointHybridGuardedRightMoveAt A strategy hwin installation at hpair
  have hallowed := hsafe.2
  change profiledRawJointRightPhysicalSiblingAllowed A pair.1.1.1.base target at hallowed
  rw [hpair] at hallowed
  exact
    (profiledRawJointHybridGuardedRightMoveAt_allowed_iff A strategy hwin
      installation target).mp hallowed

/-- Left-prefix mirror. -/
theorem profiledRawJointHybridGuardedLeftPrefixTargetAllowed
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (row : PairedEntryRow) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let target :=
      (profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin pair past
        input).target row
    match installation with
    | .inl initial =>
        ProfiledRawJointLeftSiblingSharedAllowedTarget A
          (profiledRawJointHybridInitialSiblingParentFamily A strategy
            initial.first)
          (profiledRawJointHybridInitialSiblingDirection initial.current)
          target
    | .inr recurrent =>
        ProfiledRawJointLeftSiblingSharedAllowedTarget A
          (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
            recurrent.1)
          (profiledRawJointBothRestartDirection recurrent.2) target := by
  classical
  dsimp only
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let target :=
    (profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin pair past
      input).target row
  have hsafe := profiledRawJointGuardedCommonLeftPrefixTargetSafe A strategy
    hwin pair past input row
  have hpair := profiledRawJointHybridGuardedCommonPairAt_left A strategy hwin
    installation
  change pair.1.2 =
    profiledRawJointHybridGuardedLeftMoveAt A strategy hwin installation at hpair
  have hallowed := hsafe.2
  change profiledRawJointLeftPhysicalSiblingAllowed A pair.1.2.1.base target at hallowed
  rw [hpair] at hallowed
  exact
    (profiledRawJointHybridGuardedLeftMoveAt_allowed_iff A strategy hwin
      installation target).mp hallowed

/-! ## Exact physical closes -/

/-- The same guarded-right target is the exact physical close recorded by the
finite monitor. -/
theorem profiledRawJointHybridGuardedRightPrefixTargetCloses
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (row : PairedEntryRow) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
      pair.1.1.1 false
    let controller := (pair.1.1).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    let target :=
      (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin pair
        past input).target row
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) =
      pairedRightCloseTarget A state.2.base.2.1 row
        (profiledRawJointTargetRightPhysicalLetter A record) := by
  dsimp only
  exact (profiledRawJointGuardedCommonRightPrefixTargetSafe A strategy hwin
    (profiledRawJointHybridGuardedCommonPairAt A strategy hwin installation)
    past input row).1

/-- Left physical-close mirror. -/
theorem profiledRawJointHybridGuardedLeftPrefixTargetCloses
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (row : PairedEntryRow) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair past
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
      pair.1.2.1 false
    let controller := (pair.1.2).memberController A false
    let record := narrowedRecord monitor (controller.labelOf state.1) state.2
      input
    let target :=
      (profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin pair past
        input).target row
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) =
      pairedLeftCloseTarget A state.2.base.2.1 row
        (profiledRawJointTargetLeftPhysicalLetter A record) := by
  dsimp only
  exact (profiledRawJointGuardedCommonLeftPrefixTargetSafe A strategy hwin
    (profiledRawJointHybridGuardedCommonPairAt A strategy hwin installation)
    past input row).1

/-! ## Success of the executable child lookup -/

/-- Every real guarded-right prefix installs a concrete mega child. -/
theorem exists_profiledRawJointHybridMegaGuardedRightTargetChild_at_prefix
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (row : PairedEntryRow) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let target :=
      (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin pair
        past input).target row
    ∃ child,
      profiledRawJointHybridMegaGuardedRightTargetChild? A strategy hwin
        initialBank installation target = some child := by
  classical
  dsimp only
  have hallowed := profiledRawJointHybridGuardedRightPrefixTargetAllowed A
    strategy hwin installation past input row
  cases installation with
  | inl initial =>
      simp only [profiledRawJointHybridMegaGuardedRightTargetChild?, hallowed,
        dite_true]
      exact ⟨_, rfl⟩
  | inr recurrent =>
      simp only [profiledRawJointHybridMegaGuardedRightTargetChild?, hallowed,
        dite_true]
      exact ⟨_, rfl⟩

/-- Left-prefix mirror. -/
theorem exists_profiledRawJointHybridMegaGuardedLeftTargetChild_at_prefix
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (row : PairedEntryRow) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let target :=
      (profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin pair past
        input).target row
    ∃ child,
      profiledRawJointHybridMegaGuardedLeftTargetChild? A strategy hwin
        initialBank installation target = some child := by
  classical
  dsimp only
  have hallowed := profiledRawJointHybridGuardedLeftPrefixTargetAllowed A
    strategy hwin installation past input row
  cases installation with
  | inl initial =>
      simp only [profiledRawJointHybridMegaGuardedLeftTargetChild?, hallowed,
        dite_true]
      exact ⟨_, rfl⟩
  | inr recurrent =>
      simp only [profiledRawJointHybridMegaGuardedLeftTargetChild?, hallowed,
        dite_true]
      exact ⟨_, rfl⟩

/-! ## Success of literal-root staging -/

/-- Every reachable guarded-right target also stages the literal left root
needed to enter its fixed mega-child policy. -/
theorem exists_profiledRawJointHybridMegaGuardedRightTargetRoot_at_prefix
    (installation : Installation A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (row : PairedEntryRow) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let target :=
      (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin pair
        past input).target row
    ∃ root,
      profiledRawJointHybridMegaGuardedRightTargetRoot? A strategy hwin
        initialBank installation target = some root := by
  classical
  dsimp only
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let target :=
    (profiledRawJointGuardedCommonRightPrefixOutput A strategy hwin pair past
      input).target row
  have hallowed := profiledRawJointHybridGuardedRightPrefixTargetAllowed A
    strategy hwin installation past input row
  have hclose := profiledRawJointHybridGuardedRightPrefixTargetCloses A
    strategy hwin installation past input row
  cases hslot : target.family.left () with
  | none =>
      change erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A target) = _ at hclose
      simp [profiledRawJointUnitRightTargetProjection, hslot,
        erasePairedProfiledState, pairedRightCloseTarget] at hclose
  | some slot =>
      cases installation with
      | inl initial =>
          have hallowed' :
              ProfiledRawJointRightSiblingSharedAllowedTarget A
                (profiledRawJointHybridInitialSiblingParentFamily A strategy
                  initial.first)
                (profiledRawJointHybridInitialSiblingDirection
                  initial.current) target := by
            simpa only using hallowed
          let child : ProfiledRawJointHybridMegaChildCode A strategy hwin
              initialBank :=
            profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy
              hwin initialBank
              ⟨initial,
                profiledRawJointSiblingTargetChildOfRight A strategy
                  (profiledRawJointHybridInitialSiblingParentFamily A strategy
                    initial.first)
                  (profiledRawJointHybridInitialSiblingDirection
                    initial.current) ⟨target, hallowed'⟩⟩
          have hchild :
              profiledRawJointHybridMegaGuardedRightTargetChild? A strategy
                  hwin initialBank (.inl initial) target = some child := by
            simp [profiledRawJointHybridMegaGuardedRightTargetChild?,
              hallowed', child]
          have hsource :
              ((profiledRawJointHybridMegaChildSource A strategy hwin
                initialBank child).code A).family.left () = some slot := by
            simpa [child,
              profiledRawJointHybridInitialSiblingTargetChildSource] using
              hslot
          obtain ⟨rootMacro, hmacro⟩ :=
            exists_profiledRawJointHybridMegaLeftRoot A strategy hwin
              initialBank child slot hsource
          exact ⟨⟨child, rootMacro⟩, by
            change profiledRawJointHybridMegaGuardedRightTargetRoot? A
              strategy hwin initialBank (.inl initial) target = _
            unfold profiledRawJointHybridMegaGuardedRightTargetRoot?
            rw [hchild]
            simp only
            rw [hmacro]⟩
      | inr recurrent =>
          have hallowed' :
              ProfiledRawJointRightSiblingSharedAllowedTarget A
                (profiledRawJointHybridCommonSiblingParentFamily A strategy
                  hwin recurrent.1)
                (profiledRawJointBothRestartDirection recurrent.2) target := by
            simpa only using hallowed
          let child : ProfiledRawJointHybridMegaChildCode A strategy hwin
              initialBank :=
            profiledRawJointHybridMegaChildOfCommonSiblingTarget A strategy
              hwin initialBank
              ⟨recurrent.1, recurrent.2,
                profiledRawJointSiblingTargetChildOfRight A strategy
                  (profiledRawJointHybridCommonSiblingParentFamily A strategy
                    hwin recurrent.1)
                  (profiledRawJointBothRestartDirection recurrent.2)
                  ⟨target, hallowed'⟩⟩
          have hchild :
              profiledRawJointHybridMegaGuardedRightTargetChild? A strategy
                  hwin initialBank (.inr recurrent) target = some child := by
            simp [profiledRawJointHybridMegaGuardedRightTargetChild?,
              hallowed', child]
          have hsource :
              ((profiledRawJointHybridMegaChildSource A strategy hwin
                initialBank child).code A).family.left () = some slot := by
            simpa [child,
              profiledRawJointHybridCommonSiblingTargetSource] using hslot
          obtain ⟨rootMacro, hmacro⟩ :=
            exists_profiledRawJointHybridMegaLeftRoot A strategy hwin
              initialBank child slot hsource
          exact ⟨⟨child, rootMacro⟩, by
            change profiledRawJointHybridMegaGuardedRightTargetRoot? A
              strategy hwin initialBank (.inr recurrent) target = _
            unfold profiledRawJointHybridMegaGuardedRightTargetRoot?
            rw [hchild]
            simp only
            rw [hmacro]⟩

/-- Every reachable guarded-left target stages the literal right root needed
to enter its fixed mega-child policy. -/
theorem exists_profiledRawJointHybridMegaGuardedLeftTargetRoot_at_prefix
    (installation : Installation A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (row : PairedEntryRow) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let target :=
      (profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin pair past
        input).target row
    ∃ root,
      profiledRawJointHybridMegaGuardedLeftTargetRoot? A strategy hwin
        initialBank installation target = some root := by
  classical
  dsimp only
  let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
    installation
  let target :=
    (profiledRawJointGuardedCommonLeftPrefixOutput A strategy hwin pair past
      input).target row
  have hallowed := profiledRawJointHybridGuardedLeftPrefixTargetAllowed A
    strategy hwin installation past input row
  have hclose := profiledRawJointHybridGuardedLeftPrefixTargetCloses A
    strategy hwin installation past input row
  cases hslot : target.family.right () with
  | none =>
      change erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A target) = _ at hclose
      simp [profiledRawJointUnitLeftTargetProjection, hslot,
        erasePairedProfiledState, pairedLeftCloseTarget] at hclose
  | some slot =>
      cases installation with
      | inl initial =>
          have hallowed' :
              ProfiledRawJointLeftSiblingSharedAllowedTarget A
                (profiledRawJointHybridInitialSiblingParentFamily A strategy
                  initial.first)
                (profiledRawJointHybridInitialSiblingDirection
                  initial.current) target := by
            simpa only using hallowed
          let child : ProfiledRawJointHybridMegaChildCode A strategy hwin
              initialBank :=
            profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy
              hwin initialBank
              ⟨initial,
                profiledRawJointSiblingTargetChildOfLeft A strategy
                  (profiledRawJointHybridInitialSiblingParentFamily A strategy
                    initial.first)
                  (profiledRawJointHybridInitialSiblingDirection
                    initial.current) ⟨target, hallowed'⟩⟩
          have hchild :
              profiledRawJointHybridMegaGuardedLeftTargetChild? A strategy
                  hwin initialBank (.inl initial) target = some child := by
            simp [profiledRawJointHybridMegaGuardedLeftTargetChild?,
              hallowed', child]
          have hsource :
              ((profiledRawJointHybridMegaChildSource A strategy hwin
                initialBank child).code A).family.right () = some slot := by
            simpa [child,
              profiledRawJointHybridInitialSiblingTargetChildSource] using
              hslot
          obtain ⟨rootMacro, hmacro⟩ :=
            exists_profiledRawJointHybridMegaRightRoot A strategy hwin
              initialBank child slot hsource
          exact ⟨⟨child, rootMacro⟩, by
            change profiledRawJointHybridMegaGuardedLeftTargetRoot? A strategy
              hwin initialBank (.inl initial) target = _
            unfold profiledRawJointHybridMegaGuardedLeftTargetRoot?
            rw [hchild]
            simp only
            rw [hmacro]⟩
      | inr recurrent =>
          have hallowed' :
              ProfiledRawJointLeftSiblingSharedAllowedTarget A
                (profiledRawJointHybridCommonSiblingParentFamily A strategy
                  hwin recurrent.1)
                (profiledRawJointBothRestartDirection recurrent.2) target := by
            simpa only using hallowed
          let child : ProfiledRawJointHybridMegaChildCode A strategy hwin
              initialBank :=
            profiledRawJointHybridMegaChildOfCommonSiblingTarget A strategy
              hwin initialBank
              ⟨recurrent.1, recurrent.2,
                profiledRawJointSiblingTargetChildOfLeft A strategy
                  (profiledRawJointHybridCommonSiblingParentFamily A strategy
                    hwin recurrent.1)
                  (profiledRawJointBothRestartDirection recurrent.2)
                  ⟨target, hallowed'⟩⟩
          have hchild :
              profiledRawJointHybridMegaGuardedLeftTargetChild? A strategy
                  hwin initialBank (.inr recurrent) target = some child := by
            simp [profiledRawJointHybridMegaGuardedLeftTargetChild?,
              hallowed', child]
          have hsource :
              ((profiledRawJointHybridMegaChildSource A strategy hwin
                initialBank child).code A).family.right () = some slot := by
            simpa [child,
              profiledRawJointHybridCommonSiblingTargetSource] using hslot
          obtain ⟨rootMacro, hmacro⟩ :=
            exists_profiledRawJointHybridMegaRightRoot A strategy hwin
              initialBank child slot hsource
          exact ⟨⟨child, rootMacro⟩, by
            change profiledRawJointHybridMegaGuardedLeftTargetRoot? A strategy
              hwin initialBank (.inr recurrent) target = _
            unfold profiledRawJointHybridMegaGuardedLeftTargetRoot?
            rw [hchild]
            simp only
            rw [hmacro]⟩

end

end DetParityAutomaton

end DistributedSynthesis
