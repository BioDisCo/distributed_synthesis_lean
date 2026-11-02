/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedInitialCommonLocalBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSiblingTargetIndexedKernel

/-!
# Local installation of the first strict block below a guarded common state

After a first strict-right round, process one has entered the right owner
while process two still carries the ambiguity shadow produced by its receive.
The `RightPending` state below relates those two independently executable
local states.  A delivered owner on the next strict-right round resolves the
receiver.  The strict-left construction is the literal mirror.

The final section turns an allowed target of a represented guarded pair into
the dependent finite child key used by the existing sibling target-indexed
kernel.  Runtime data are only the represented finite pair and target.  The
semantic family and direction are recovered proof-side from the pair's fixed
representative.

No executable definition accepts a graph, orientation, hierarchy side,
leader bit, semantic world, or history.
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

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

/-! ## Pending states after the first strict round -/

/-- Actual global relation after a first strict-right round.  Process one is
the blind right owner; process two has received but still locally retains the
common/strict ambiguity. -/
structure ProfiledRawJointGuardedCommonRightPending where
  owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin
  receiver : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin
  source_eq : owner.1 = receiver.shadow.source

/-- Strict-left mirror. -/
structure ProfiledRawJointGuardedCommonLeftPending where
  receiver : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin
  owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin
  source_eq : owner.1 = receiver.shadow.source

noncomputable instance profiledRawJointGuardedCommonRightPendingFintype :
    Fintype (ProfiledRawJointGuardedCommonRightPending A strategy hwin) := by
  classical
  let Rep := Σ owner :
      ProfiledRawJointGuardedCommonRightOwner A strategy hwin,
    { receiver :
        ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin //
      owner.1 = receiver.shadow.source }
  let equiv : ProfiledRawJointGuardedCommonRightPending A strategy hwin ≃
      Rep :=
    { toFun := fun state ↦ ⟨state.owner, state.receiver, state.source_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; rcases state with ⟨owner, receiver, h⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointGuardedCommonLeftPendingFintype :
    Fintype (ProfiledRawJointGuardedCommonLeftPending A strategy hwin) := by
  classical
  let Rep := Σ receiver :
      ProfiledRawJointGuardedInitialCommonOneState A strategy hwin,
    { owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin //
      owner.1 = receiver.shadow.source }
  let equiv : ProfiledRawJointGuardedCommonLeftPending A strategy hwin ≃
      Rep :=
    { toFun := fun state ↦ ⟨state.receiver, state.owner, state.source_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; rcases state with ⟨receiver, owner, h⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- First strict-right local step. -/
noncomputable def profiledRawJointGuardedCommonFirstStrictRight
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonRightPending A strategy hwin :=
  let owner := profiledRawJointGuardedInitialCommonOneNoRecv A strategy hwin
    one input.1
  let receiver := profiledRawJointGuardedInitialCommonTwoRecv A strategy hwin
    two one input.2 input.1
  ((owner.1, receiver.1), ⟨owner.2, receiver.2,
    profiledRawJointGuardedInitialCommon_strictRight_sources A strategy hwin
      one two hagrees input⟩)

/-- First strict-left mirror. -/
noncomputable def profiledRawJointGuardedCommonFirstStrictLeft
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonLeftPending A strategy hwin :=
  let receiver := profiledRawJointGuardedInitialCommonOneRecv A strategy hwin
    one two input.1 input.2
  let owner := profiledRawJointGuardedInitialCommonTwoNoRecv A strategy hwin
    two input.2
  ((receiver.1, owner.1), ⟨receiver.2, owner.2,
    profiledRawJointGuardedInitialCommon_strictLeft_sources A strategy hwin
      one two hagrees input⟩)

theorem profiledRawJointGuardedCommonFirstStrictRight_outputs
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonFirstStrictRight A strategy hwin one two
      hagrees input).1 =
      ((one.shadow.common.rightRootRecord A strategy hwin input).2.2,
        pairedRightInformedForRow .both
          (one.shadow.common.rightRootRecord A strategy hwin input
            ).2.1.physical) :=
  profiledRawJointGuardedInitialCommon_strictRight_outputs A strategy hwin one
    two hagrees input

theorem profiledRawJointGuardedCommonFirstStrictLeft_outputs
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonFirstStrictLeft A strategy hwin one two
      hagrees input).1 =
      (pairedLeftInformedForRow .both
          (one.shadow.common.leftRootRecord A strategy hwin input
            ).2.1.physical,
        (one.shadow.common.leftRootRecord A strategy hwin input).2.2) :=
  profiledRawJointGuardedInitialCommon_strictLeft_outputs A strategy hwin one
    two hagrees input

/-! ## Resolution on the next delivered owner -/

/-- Resolved strict-right owner/receiver pair. -/
structure ProfiledRawJointGuardedCommonRightStrictState where
  owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin
  receiver : ProfiledRawJointGuardedCommonRightStrictReceiver A strategy hwin
  source_eq : owner.1 = receiver.1

/-- Resolved strict-left mirror. -/
structure ProfiledRawJointGuardedCommonLeftStrictState where
  receiver : ProfiledRawJointGuardedCommonLeftStrictReceiver A strategy hwin
  owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin
  source_eq : owner.1 = receiver.1

noncomputable instance profiledRawJointGuardedCommonRightStrictStateFintype :
    Fintype (ProfiledRawJointGuardedCommonRightStrictState A strategy hwin) := by
  classical
  let Rep := Σ owner :
      ProfiledRawJointGuardedCommonRightOwner A strategy hwin,
    { receiver :
        ProfiledRawJointGuardedCommonRightStrictReceiver A strategy hwin //
      owner.1 = receiver.1 }
  let equiv : ProfiledRawJointGuardedCommonRightStrictState A strategy hwin ≃
      Rep :=
    { toFun := fun state ↦ ⟨state.owner, state.receiver, state.source_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; rcases state with ⟨owner, receiver, h⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointGuardedCommonLeftStrictStateFintype :
    Fintype (ProfiledRawJointGuardedCommonLeftStrictState A strategy hwin) := by
  classical
  let Rep := Σ receiver :
      ProfiledRawJointGuardedCommonLeftStrictReceiver A strategy hwin,
    { owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin //
      owner.1 = receiver.1 }
  let equiv : ProfiledRawJointGuardedCommonLeftStrictState A strategy hwin ≃
      Rep :=
    { toFun := fun state ↦ ⟨state.receiver, state.owner, state.source_eq⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; rcases state with ⟨receiver, owner, h⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- A second strict-right round delivers the owner tag and resolves process
two's ambiguity. -/
noncomputable def profiledRawJointGuardedCommonResolveStrictRight
    (state : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonRightStrictState A strategy hwin :=
  let owner := profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin
    state.owner input.1
  let receiver := profiledRawJointGuardedCommonTwoShadowRecvRightOwner A
    strategy hwin state.receiver.shadow state.owner input.2 input.1
  ((owner.1, receiver.1), ⟨owner.2, receiver.2, by
    rw [profiledRawJointGuardedCommonRightOwnerNoRecv_source,
      profiledRawJointGuardedCommonTwoShadowRecvRightOwner_source]
    exact state.source_eq⟩)

/-- Strict-left resolution. -/
noncomputable def profiledRawJointGuardedCommonResolveStrictLeft
    (state : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonLeftStrictState A strategy hwin :=
  let receiver := profiledRawJointGuardedCommonOneShadowRecvLeftOwner A
    strategy hwin state.receiver.shadow state.owner input.1 input.2
  let owner := profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin
    state.owner input.2
  ((receiver.1, owner.1), ⟨receiver.2, owner.2, by
    rw [profiledRawJointGuardedCommonLeftOwnerNoRecv_source,
      profiledRawJointGuardedCommonOneShadowRecvLeftOwner_source]
    exact state.source_eq⟩)

/-- Continue one resolved strict-right round. -/
noncomputable def profiledRawJointGuardedCommonStrictRightStep
    (state : ProfiledRawJointGuardedCommonRightStrictState A strategy hwin)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonRightStrictState A strategy hwin :=
  let owner := profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin
    state.owner input.1
  let receiver :=
    profiledRawJointGuardedCommonRightStrictReceiverRecvOwner A strategy hwin
      state.receiver state.owner input.2 input.1
  ((owner.1, receiver.1), ⟨owner.2, receiver.2, by
    rw [profiledRawJointGuardedCommonRightOwnerNoRecv_source,
      profiledRawJointGuardedCommonRightStrictReceiverRecvOwner_source]
    exact state.source_eq⟩)

/-- Continue one resolved strict-left round. -/
noncomputable def profiledRawJointGuardedCommonStrictLeftStep
    (state : ProfiledRawJointGuardedCommonLeftStrictState A strategy hwin)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonLeftStrictState A strategy hwin :=
  let receiver :=
    profiledRawJointGuardedCommonLeftStrictReceiverRecvOwner A strategy hwin
      state.receiver state.owner input.1 input.2
  let owner := profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin
    state.owner input.2
  ((receiver.1, owner.1), ⟨receiver.2, owner.2, by
    rw [profiledRawJointGuardedCommonLeftOwnerNoRecv_source,
      profiledRawJointGuardedCommonLeftStrictReceiverRecvOwner_source]
    exact state.source_eq⟩)

@[simp] theorem profiledRawJointGuardedCommonResolveStrictRight_source
    (state : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonResolveStrictRight A strategy hwin state
      input).2.owner.1 = state.owner.1 :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonResolveStrictLeft_source
    (state : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonResolveStrictLeft A strategy hwin state
      input).2.owner.1 = state.owner.1 :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonStrictRightStep_source
    (state : ProfiledRawJointGuardedCommonRightStrictState A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonStrictRightStep A strategy hwin state
      input).2.owner.1 = state.owner.1 :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonStrictLeftStep_source
    (state : ProfiledRawJointGuardedCommonLeftStrictState A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonStrictLeftStep A strategy hwin state
      input).2.owner.1 = state.owner.1 :=
  rfl

/-! ## Finite handoff keys for the target-indexed kernel -/

noncomputable def profiledRawJointGuardedCommonPairFamily
    (pair : CommonPair A strategy hwin) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  profiledRawJointCommonWorldFamily A
    (pair.representativeWorld A strategy hwin)

noncomputable def profiledRawJointGuardedCommonPairDirection
    (pair : CommonPair A strategy hwin) :
    ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) :=
  profiledRawJointBothRestartDirection
    (pair.representativeCurrent A strategy hwin)

/-- Finite right target key below one represented guarded pair. -/
abbrev ProfiledRawJointGuardedCommonRightHandoff :=
  Σ pair : CommonPair A strategy hwin,
    ProfiledRawJointRightSiblingChildCode A
      (profiledRawJointGuardedCommonPairFamily A strategy hwin pair)
      (profiledRawJointGuardedCommonPairDirection A strategy hwin pair)

/-- Left target key. -/
abbrev ProfiledRawJointGuardedCommonLeftHandoff :=
  Σ pair : CommonPair A strategy hwin,
    ProfiledRawJointLeftSiblingChildCode A
      (profiledRawJointGuardedCommonPairFamily A strategy hwin pair)
      (profiledRawJointGuardedCommonPairDirection A strategy hwin pair)

noncomputable instance profiledRawJointGuardedCommonRightHandoffFintype :
    Fintype (ProfiledRawJointGuardedCommonRightHandoff A strategy hwin) := by
  classical
  infer_instance

noncomputable instance profiledRawJointGuardedCommonLeftHandoffFintype :
    Fintype (ProfiledRawJointGuardedCommonLeftHandoff A strategy hwin) := by
  classical
  infer_instance

/-- Materialize an allowed right target as the exact finite kernel child key
below the fixed representative of the guarded pair. -/
noncomputable def profiledRawJointGuardedCommonRightHandoffOfSafe
    (pair : CommonPair A strategy hwin) (target : ProfiledRawJointUnitTarget A)
    (hsafe : profiledRawJointRightPhysicalSiblingAllowed A pair.1.1.1.base
      target) :
    ProfiledRawJointGuardedCommonRightHandoff A strategy hwin := by
  let family := profiledRawJointGuardedCommonPairFamily A strategy hwin pair
  let direction := profiledRawJointGuardedCommonPairDirection A strategy hwin
    pair
  let world := profiledRawJointCommonWorldAfterBoth A
    (pair.representativeWorld A strategy hwin)
    (pair.representativeCurrent A strategy hwin)
  have hdescriptor : pair.1.1.1.base =
      profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
        (world.procOneMember A) := by
    rw [pair.right_eq_representative A strategy hwin]
    rfl
  have hallowed : ProfiledRawJointRightSiblingSharedAllowedTarget A family
      direction target := by
    apply (profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff A
      family direction (world.procOneMember A) target).mp
    rw [← hdescriptor]
    exact hsafe
  exact ⟨pair, target, hallowed⟩

/-- Left mirror. -/
noncomputable def profiledRawJointGuardedCommonLeftHandoffOfSafe
    (pair : CommonPair A strategy hwin) (target : ProfiledRawJointUnitTarget A)
    (hsafe : profiledRawJointLeftPhysicalSiblingAllowed A pair.1.2.1.base
      target) :
    ProfiledRawJointGuardedCommonLeftHandoff A strategy hwin := by
  let family := profiledRawJointGuardedCommonPairFamily A strategy hwin pair
  let direction := profiledRawJointGuardedCommonPairDirection A strategy hwin
    pair
  let world := profiledRawJointCommonWorldAfterBoth A
    (pair.representativeWorld A strategy hwin)
    (pair.representativeCurrent A strategy hwin)
  have hdescriptor : pair.1.2.1.base =
      profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
        (world.procTwoMember A) := by
    rw [pair.left_eq_representative A strategy hwin]
    rfl
  have hallowed : ProfiledRawJointLeftSiblingSharedAllowedTarget A family
      direction target := by
    apply (profiledRawJointLeftPhysicalSiblingDescriptorOf_allowed_iff A
      family direction (world.procTwoMember A) target).mp
    rw [← hdescriptor]
    exact hsafe
  exact ⟨pair, target, hallowed⟩

@[simp] theorem profiledRawJointGuardedCommonRightHandoffOfSafe_target
    (pair : CommonPair A strategy hwin) (target : ProfiledRawJointUnitTarget A)
    (hsafe : profiledRawJointRightPhysicalSiblingAllowed A pair.1.1.1.base
      target) :
    (profiledRawJointGuardedCommonRightHandoffOfSafe A strategy hwin pair
      target hsafe).2.1 = target :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonLeftHandoffOfSafe_target
    (pair : CommonPair A strategy hwin) (target : ProfiledRawJointUnitTarget A)
    (hsafe : profiledRawJointLeftPhysicalSiblingAllowed A pair.1.2.1.base
      target) :
    (profiledRawJointGuardedCommonLeftHandoffOfSafe A strategy hwin pair
      target hsafe).2.1 = target :=
  rfl

/-- A checked right close below the handoff key initializes exactly the
existing target-indexed recurrent package. -/
theorem
    nonempty_profiledRawJointGuardedCommonRightHandoffRootPackage_of_close
    (handoff : ProfiledRawJointGuardedCommonRightHandoff A strategy hwin)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A handoff.2.1) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointSiblingTargetChildRootPackage A strategy hwin
        (profiledRawJointGuardedCommonPairFamily A strategy hwin handoff.1)
        (profiledRawJointGuardedCommonPairDirection A strategy hwin handoff.1)
        (profiledRawJointSiblingTargetChildOfRight A strategy
          (profiledRawJointGuardedCommonPairFamily A strategy hwin handoff.1)
          (profiledRawJointGuardedCommonPairDirection A strategy hwin
            handoff.1) handoff.2)) :=
  nonempty_profiledRawJointSiblingTargetChildRootPackage_of_rightClose A
    strategy hwin
    (profiledRawJointGuardedCommonPairFamily A strategy hwin handoff.1)
    (profiledRawJointGuardedCommonPairDirection A strategy hwin handoff.1)
    handoff.2 scan row physical hclose

/-- Left close mirror. -/
theorem
    nonempty_profiledRawJointGuardedCommonLeftHandoffRootPackage_of_close
    (handoff : ProfiledRawJointGuardedCommonLeftHandoff A strategy hwin)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A handoff.2.1) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointSiblingTargetChildRootPackage A strategy hwin
        (profiledRawJointGuardedCommonPairFamily A strategy hwin handoff.1)
        (profiledRawJointGuardedCommonPairDirection A strategy hwin handoff.1)
        (profiledRawJointSiblingTargetChildOfLeft A strategy
          (profiledRawJointGuardedCommonPairFamily A strategy hwin handoff.1)
          (profiledRawJointGuardedCommonPairDirection A strategy hwin
            handoff.1) handoff.2)) :=
  nonempty_profiledRawJointSiblingTargetChildRootPackage_of_leftClose A
    strategy hwin
    (profiledRawJointGuardedCommonPairFamily A strategy hwin handoff.1)
    (profiledRawJointGuardedCommonPairDirection A strategy hwin handoff.1)
    handoff.2 scan row physical hclose

end

end DetParityAutomaton

end DistributedSynthesis
