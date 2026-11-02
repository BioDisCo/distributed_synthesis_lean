/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointLeaderFreeReadback

/-!
# Fixed strict tails of the guarded-common core adapter

This file identifies the concrete tail-core kernel on a forever strict-right
or forever strict-left environment with the guarded finite sibling controller
selected by its represented common pair.  The first round opens a blind owner
and an ambiguity shadow, the second delivered owner resolves that shadow, and
all later rounds advance the matched finite controller/monitor state.

All orientation words below describe proof-side traces of a fixed physical
environment.  They are not observations or leader bits supplied to a local
transition.
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

private abbrev CommonControl :=
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

private abbrev TailKernel (root : CommonControl A strategy hwin) :=
  profiledRawJointGuardedCommonTailCoreKernel A strategy hwin initialBank root

/-! ## Physical environments and finite controller records -/

/-- A right-controller input word viewed as an all-strict-right physical
environment. -/
def profiledRawJointGuardedCommonTailStrictRightEnvironment
    (env : Nat → In₂ × In₁) : EnvironmentSequence In₁ In₂ :=
  fun n ↦
    { inputOne := (env n).2
      inputTwo := (env n).1
      graph := .right }

/-- Left mirror. -/
def profiledRawJointGuardedCommonTailStrictLeftEnvironment
    (env : Nat → In₁ × In₂) : EnvironmentSequence In₁ In₂ :=
  fun n ↦
    { inputOne := (env n).1
      inputTwo := (env n).2
      graph := .left }

/-- The literal guarded-right controller/monitor record at a finite prefix. -/
noncomputable def profiledRawJointGuardedCommonTailRightControllerRecordAt
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :=
  let state := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair past
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
    pair.1.1.1 false
  let controller := (pair.1.1).memberController A false
  narrowedRecord monitor (controller.labelOf state.1) state.2 input

/-- Left controller/monitor record. -/
noncomputable def profiledRawJointGuardedCommonTailLeftControllerRecordAt
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :=
  let state := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair past
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
    pair.1.2.1 false
  let controller := (pair.1.2).memberController A false
  narrowedRecord monitor (controller.labelOf state.1) state.2 input

/-- Physical right round read from the same guarded finite record. -/
noncomputable def profiledRawJointGuardedCommonTailRightPhysicalRecordAt
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) : RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  pairedRightRecordForRow .both
    (profiledRawJointTargetRightPhysicalLetter A
      (profiledRawJointGuardedCommonTailRightControllerRecordAt A strategy
        hwin pair past input))

/-- Left physical round. -/
noncomputable def profiledRawJointGuardedCommonTailLeftPhysicalRecordAt
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) : RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  pairedLeftRecordForRow .both
    (profiledRawJointTargetLeftPhysicalLetter A
      (profiledRawJointGuardedCommonTailLeftControllerRecordAt A strategy hwin
        pair past input))

/-! ## First open strict round -/

/-- After one strict-right round, the concrete kernel is exactly in the
blind-owner/common-shadow pair produced by the two local front maps, with the
outputs of that same guarded root record. -/
theorem profiledRawJointGuardedCommonTailCore_firstStrictRight
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    let kernel := TailKernel A strategy hwin initialBank root
    let one := profiledRawJointGuardedCommonTailInitialNoRecvOne A strategy
      hwin initialBank root (env 0).2
    let two := profiledRawJointGuardedCommonTailInitialRecvTwo A strategy hwin
      initialBank root (env 0).1 (env 0).2
    kernel.globalMachine.globalStateTrace
        (profiledRawJointGuardedCommonTailStrictRightEnvironment env) 1 =
      ((one.2, one.1), (two.2, two.1)) := by
  simp [TailKernel, profiledRawJointGuardedCommonTailCoreKernel,
    profiledRawJointGuardedHybridCombinedLeaderFreeKernel,
    profiledRawJointIndexedPolicyLeaderFreeKernel,
    ProfiledRawJointLeaderFreeKernel.globalMachine,
    ProfiledRawJointLeaderFreeKernel.physicalController,
    FiniteGlobalRoundMachine.globalStateTrace_succ,
    profiledRawJointGuardedCommonTailStrictRightEnvironment,
    profiledRawJointGuardedCommonTailCoreAdapter,
    profiledRawJointGuardedCommonTailCoreRecvTwo,
    ProfiledRawJointLeaderFreeKernel.noRecvOne,
    ProfiledRawJointLeaderFreeKernel.recvTwo]

/-- First strict-left mirror. -/
theorem profiledRawJointGuardedCommonTailCore_firstStrictLeft
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    let kernel := TailKernel A strategy hwin initialBank root
    let one := profiledRawJointGuardedCommonTailInitialRecvOne A strategy hwin
      initialBank root (env 0).1 (env 0).2
    let two := profiledRawJointGuardedCommonTailInitialNoRecvTwo A strategy
      hwin initialBank root (env 0).2
    kernel.globalMachine.globalStateTrace
        (profiledRawJointGuardedCommonTailStrictLeftEnvironment env) 1 =
      ((one.2, one.1), (two.2, two.1)) := by
  simp [TailKernel, profiledRawJointGuardedCommonTailCoreKernel,
    profiledRawJointGuardedHybridCombinedLeaderFreeKernel,
    profiledRawJointIndexedPolicyLeaderFreeKernel,
    ProfiledRawJointLeaderFreeKernel.globalMachine,
    ProfiledRawJointLeaderFreeKernel.physicalController,
    FiniteGlobalRoundMachine.globalStateTrace_succ,
    profiledRawJointGuardedCommonTailStrictLeftEnvironment,
    profiledRawJointGuardedCommonTailCoreAdapter,
    profiledRawJointGuardedCommonTailCoreRecvOne,
    ProfiledRawJointLeaderFreeKernel.recvOne,
    ProfiledRawJointLeaderFreeKernel.noRecvTwo]

/-! ## Resolved states retained after the second strict round -/

/-- Exact resolved local payload obtained by advancing the represented right
controller through `past` and the current `input`. -/
noncomputable def profiledRawJointGuardedCommonTailRightResolvedAt
    (pair : CommonPair A strategy hwin) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin :=
  let before := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair past
  let after := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
    hwin pair (past ++ [input])
  let record := profiledRawJointGuardedCommonTailRightControllerRecordAt A
    strategy hwin pair past input
  let owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin :=
    ⟨pair, after.1⟩
  let receiver : ProfiledRawJointGuardedCommonRightStrictReceiver A strategy
      hwin := ⟨pair, after.2, some (record.2.1.target .both)⟩
  let strict : ProfiledRawJointGuardedCommonRightStrictState A strategy hwin :=
    ⟨owner, receiver, rfl⟩
  let close := profiledRawJointGuardedCommonRightStageClose A strategy hwin
    pair before input .both
  ⟨strict, close⟩

/-- Left resolved payload. -/
noncomputable def profiledRawJointGuardedCommonTailLeftResolvedAt
    (pair : CommonPair A strategy hwin) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin :=
  let before := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair past
  let after := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
    hwin pair (past ++ [input])
  let record := profiledRawJointGuardedCommonTailLeftControllerRecordAt A
    strategy hwin pair past input
  let receiver : ProfiledRawJointGuardedCommonLeftStrictReceiver A strategy
      hwin := ⟨pair, after.2, some (record.2.1.target .both)⟩
  let owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin :=
    ⟨pair, after.1⟩
  let strict : ProfiledRawJointGuardedCommonLeftStrictState A strategy hwin :=
    ⟨receiver, owner, rfl⟩
  let close := profiledRawJointGuardedCommonLeftStageClose A strategy hwin pair
    before input .both
  ⟨strict, close⟩

/-- The second strict-right round resolves the common/right ambiguity and
uses the literal local owner and receiver transitions of the tail front. -/
theorem profiledRawJointGuardedCommonTailCore_secondStrictRight
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    let kernel := TailKernel A strategy hwin initialBank root
    let firstOwner := profiledRawJointGuardedCommonTailInitialNoRecvOne A
      strategy hwin initialBank root (env 0).2
    let firstCommon := profiledRawJointGuardedCommonTailInitialRecvTwo A
      strategy hwin initialBank root (env 0).1 (env 0).2
    let owner := (profiledRawJointGuardedCommonNoRecvOne A strategy hwin
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin root)
      (env 0).2).2
    let common := (profiledRawJointGuardedInitialCommonStartTwo A strategy hwin
      root ((env 0).2, (env 0).1)).2
    let one := profiledRawJointGuardedCommonTailRightOwnerNoRecvOne A strategy
      hwin initialBank owner (env 1).2
    let two := profiledRawJointGuardedCommonTailResolveRightTwo A strategy hwin
      initialBank common owner (env 1).1 (env 1).2
    kernel.globalMachine.globalStateTrace
        (profiledRawJointGuardedCommonTailStrictRightEnvironment env) 2 =
      ((one.2, one.1), (two.2, two.1)) := by
  dsimp only
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
    profiledRawJointGuardedCommonTailCore_firstStrictRight A strategy hwin
      initialBank root env]
  simp [TailKernel, profiledRawJointGuardedCommonTailCoreKernel,
    profiledRawJointGuardedHybridCombinedLeaderFreeKernel,
    profiledRawJointIndexedPolicyLeaderFreeKernel,
    ProfiledRawJointLeaderFreeKernel.globalMachine,
    ProfiledRawJointLeaderFreeKernel.physicalController,
    profiledRawJointGuardedCommonTailStrictRightEnvironment,
    profiledRawJointGuardedCommonTailCoreAdapter,
    profiledRawJointGuardedCommonTailCoreNoRecvOne,
    profiledRawJointGuardedCommonTailCoreRecvTwo,
    profiledRawJointGuardedCommonTailInitialNoRecvOne,
    profiledRawJointGuardedCommonTailInitialRecvTwo,
    profiledRawJointGuardedInitialCommonStartTwo,
    profiledRawJointGuardedCommonTailOneOfRightOwner,
    profiledRawJointGuardedCommonTailTwoOfCommon,
    ProfiledRawJointLeaderFreeKernel.noRecvOne,
    ProfiledRawJointLeaderFreeKernel.recvTwo]

/-- Second strict-left mirror. -/
theorem profiledRawJointGuardedCommonTailCore_secondStrictLeft
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    let kernel := TailKernel A strategy hwin initialBank root
    let firstCommon := profiledRawJointGuardedCommonTailInitialRecvOne A
      strategy hwin initialBank root (env 0).1 (env 0).2
    let firstOwner := profiledRawJointGuardedCommonTailInitialNoRecvTwo A
      strategy hwin initialBank root (env 0).2
    let common := (profiledRawJointGuardedInitialCommonStartOne A strategy hwin
      root (env 0)).2
    let owner := (profiledRawJointGuardedCommonNoRecvTwo A strategy hwin
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin root)
      (env 0).2).2
    let one := profiledRawJointGuardedCommonTailResolveLeftOne A strategy hwin
      initialBank common owner (env 1).1 (env 1).2
    let two := profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo A strategy
      hwin initialBank owner (env 1).2
    kernel.globalMachine.globalStateTrace
        (profiledRawJointGuardedCommonTailStrictLeftEnvironment env) 2 =
      ((one.2, one.1), (two.2, two.1)) := by
  dsimp only
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
    profiledRawJointGuardedCommonTailCore_firstStrictLeft A strategy hwin
      initialBank root env]
  simp [TailKernel, profiledRawJointGuardedCommonTailCoreKernel,
    profiledRawJointGuardedHybridCombinedLeaderFreeKernel,
    profiledRawJointIndexedPolicyLeaderFreeKernel,
    ProfiledRawJointLeaderFreeKernel.globalMachine,
    ProfiledRawJointLeaderFreeKernel.physicalController,
    profiledRawJointGuardedCommonTailStrictLeftEnvironment,
    profiledRawJointGuardedCommonTailCoreAdapter,
    profiledRawJointGuardedCommonTailCoreRecvOne,
    profiledRawJointGuardedCommonTailCoreNoRecvTwo,
    profiledRawJointGuardedCommonTailInitialRecvOne,
    profiledRawJointGuardedCommonTailInitialNoRecvTwo,
    profiledRawJointGuardedInitialCommonStartOne,
    profiledRawJointGuardedCommonTailOneOfCommon,
    profiledRawJointGuardedCommonTailTwoOfLeftOwner,
    ProfiledRawJointLeaderFreeKernel.recvOne,
    ProfiledRawJointLeaderFreeKernel.noRecvTwo]

/-! ## Canonical resolved-tail steps -/

/-- Resolve one synchronized pending right state and stage the close computed
by the same finite pre-step controller/monitor state. -/
noncomputable def profiledRawJointGuardedCommonTailResolveRightStep
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₂ × In₁) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin :=
  let ownerControl := profiledRawJointGuardedCommonRightOwnerFor A strategy
    hwin pending.receiver.shadow pending.owner
  let close := profiledRawJointGuardedCommonRightStageClose A strategy hwin
    pending.receiver.shadow.source
      (ownerControl, pending.receiver.shadow.strictReceiver) input .both
  let next := profiledRawJointGuardedCommonResolveStrictRight A strategy hwin
    pending (input.2, input.1)
  (next.1, ⟨next.2, close⟩)

/-- Continue one synchronized resolved right state. -/
noncomputable def profiledRawJointGuardedCommonTailStrictRightStep
    (state : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (input : In₂ × In₁) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin :=
  let ownerControl := profiledRawJointGuardedCommonRightStrictOwnerFor A
    strategy hwin state.strict.receiver state.strict.owner
  let close := profiledRawJointGuardedCommonRightStageClose A strategy hwin
    state.strict.receiver.1 (ownerControl, state.strict.receiver.2.1) input
      .both
  let next := profiledRawJointGuardedCommonStrictRightStep A strategy hwin
    state.strict (input.2, input.1)
  (next.1, ⟨next.2, close⟩)

/-- Pending left resolution. -/
noncomputable def profiledRawJointGuardedCommonTailResolveLeftStep
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin :=
  let ownerControl := profiledRawJointGuardedCommonLeftOwnerFor A strategy hwin
    pending.receiver.shadow pending.owner
  let close := profiledRawJointGuardedCommonLeftStageClose A strategy hwin
    pending.receiver.shadow.source
      (ownerControl, pending.receiver.shadow.strictReceiver) input .both
  let next := profiledRawJointGuardedCommonResolveStrictLeft A strategy hwin
    pending input
  (next.1, ⟨next.2, close⟩)

/-- Resolved left continuation. -/
noncomputable def profiledRawJointGuardedCommonTailStrictLeftStep
    (state : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin :=
  let ownerControl := profiledRawJointGuardedCommonLeftStrictOwnerFor A
    strategy hwin state.strict.receiver state.strict.owner
  let close := profiledRawJointGuardedCommonLeftStageClose A strategy hwin
    state.strict.receiver.1 (ownerControl, state.strict.receiver.2.1) input
      .both
  let next := profiledRawJointGuardedCommonStrictLeftStep A strategy hwin
    state.strict input
  (next.1, ⟨next.2, close⟩)

/-- On the synchronized resolved-right invariant, the two concrete tail-front
maps are exactly the canonical finite strict step. -/
theorem profiledRawJointGuardedCommonTailStrictRightStep_local
    (state : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (input : In₂ × In₁) :
    let next := profiledRawJointGuardedCommonTailStrictRightStep A strategy
      hwin state input
    ((profiledRawJointGuardedCommonTailRightOwnerNoRecvOne A strategy hwin
        initialBank state.strict.owner input.2).1,
      (profiledRawJointGuardedCommonTailContinueRightTwo A strategy hwin
        initialBank state state.strict.owner input.1 input.2).1) = next.1 ∧
    (profiledRawJointGuardedCommonTailRightOwnerNoRecvOne A strategy hwin
        initialBank state.strict.owner input.2).2 =
      .exceptional
        (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin
          next.2.strict.owner) ∧
    (profiledRawJointGuardedCommonTailContinueRightTwo A strategy hwin
        initialBank state state.strict.owner input.1 input.2).2 =
      .exceptional
        (profiledRawJointGuardedCommonTailTwoOfRightReceiver A strategy hwin
          next.2) := by
  rcases state with ⟨⟨owner, receiver, hsource⟩, close⟩
  rcases owner with ⟨source, ownerControl⟩
  rcases receiver with ⟨receiverSource, receiverState, target⟩
  cases hsource
  simp [profiledRawJointGuardedCommonTailStrictRightStep,
    profiledRawJointGuardedCommonTailRightOwnerNoRecvOne,
    profiledRawJointGuardedCommonTailContinueRightTwo,
    profiledRawJointGuardedCommonStrictRightStep,
    profiledRawJointGuardedCommonRightStrictOwnerFor,
    profiledRawJointGuardedCommonRightOwnerNoRecv,
    profiledRawJointGuardedCommonRightStrictReceiverRecvOwner,
    profiledRawJointGuardedCommonTailOneOfRightOwner,
    profiledRawJointGuardedCommonTailTwoOfRightReceiver]

/-- Resolved-left mirror. -/
theorem profiledRawJointGuardedCommonTailStrictLeftStep_local
    (state : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (input : In₁ × In₂) :
    let next := profiledRawJointGuardedCommonTailStrictLeftStep A strategy hwin
      state input
    ((profiledRawJointGuardedCommonTailContinueLeftOne A strategy hwin
        initialBank state state.strict.owner input.1 input.2).1,
      (profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo A strategy hwin
        initialBank state.strict.owner input.2).1) = next.1 ∧
    (profiledRawJointGuardedCommonTailContinueLeftOne A strategy hwin
        initialBank state state.strict.owner input.1 input.2).2 =
      .exceptional
        (profiledRawJointGuardedCommonTailOneOfLeftReceiver A strategy hwin
          next.2) ∧
    (profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo A strategy hwin
        initialBank state.strict.owner input.2).2 =
      .exceptional
        (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin
          next.2.strict.owner) := by
  rcases state with ⟨⟨receiver, owner, hsource⟩, close⟩
  rcases receiver with ⟨receiverSource, receiverState, target⟩
  rcases owner with ⟨ownerSource, ownerControl⟩
  cases hsource
  simp [profiledRawJointGuardedCommonTailStrictLeftStep,
    profiledRawJointGuardedCommonTailContinueLeftOne,
    profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo,
    profiledRawJointGuardedCommonStrictLeftStep,
    profiledRawJointGuardedCommonLeftStrictOwnerFor,
    profiledRawJointGuardedCommonLeftOwnerNoRecv,
    profiledRawJointGuardedCommonLeftStrictReceiverRecvOwner,
    profiledRawJointGuardedCommonTailOneOfLeftReceiver,
    profiledRawJointGuardedCommonTailTwoOfLeftOwner]

/-- The synchronized pending state produced by the first strict-right round.
The hypothetical receiver-side common transition is exactly the one executed
by process two in the concrete tail front. -/
noncomputable def profiledRawJointGuardedCommonTailInitialRightPending
    (root : CommonControl A strategy hwin) (input : In₂ × In₁) :
    ProfiledRawJointGuardedCommonRightPending A strategy hwin :=
  let pair := profiledRawJointGuardedInitialCommonControlPair A strategy hwin
    root
  let owner := profiledRawJointGuardedCommonNoRecvOne A strategy hwin pair
    input.2
  let receiver := profiledRawJointGuardedInitialCommonStartTwo A strategy hwin
    root (input.2, input.1)
  ⟨owner.2, receiver.2, rfl⟩

/-- First strict-left pending state. -/
noncomputable def profiledRawJointGuardedCommonTailInitialLeftPending
    (root : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLeftPending A strategy hwin :=
  let pair := profiledRawJointGuardedInitialCommonControlPair A strategy hwin
    root
  let receiver := profiledRawJointGuardedInitialCommonStartOne A strategy hwin
    root input
  let owner := profiledRawJointGuardedCommonNoRecvTwo A strategy hwin pair
    input.2
  ⟨receiver.2, owner.2, rfl⟩

/-- The concrete second-round local maps are exactly pending resolution. -/
theorem profiledRawJointGuardedCommonTailResolveRightStep_local
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₂ × In₁) :
    let next := profiledRawJointGuardedCommonTailResolveRightStep A strategy
      hwin pending input
    ((profiledRawJointGuardedCommonTailRightOwnerNoRecvOne A strategy hwin
        initialBank pending.owner input.2).1,
      (profiledRawJointGuardedCommonTailResolveRightTwo A strategy hwin
        initialBank pending.receiver pending.owner input.1 input.2).1) =
        next.1 ∧
    (profiledRawJointGuardedCommonTailRightOwnerNoRecvOne A strategy hwin
        initialBank pending.owner input.2).2 =
      .exceptional
        (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin
          next.2.strict.owner) ∧
    (profiledRawJointGuardedCommonTailResolveRightTwo A strategy hwin
        initialBank pending.receiver pending.owner input.1 input.2).2 =
      .exceptional
        (profiledRawJointGuardedCommonTailTwoOfRightReceiver A strategy hwin
          next.2) := by
  rcases pending with ⟨owner, receiver, hsource⟩
  rcases owner with ⟨ownerSource, ownerControl⟩
  rcases receiver.shadow.source with receiverSource
  cases hsource
  simp [profiledRawJointGuardedCommonTailResolveRightStep,
    profiledRawJointGuardedCommonResolveStrictRight,
    profiledRawJointGuardedCommonTailResolveRightTwo,
    profiledRawJointGuardedCommonTailRightOwnerNoRecvOne,
    profiledRawJointGuardedCommonRightOwnerFor,
    profiledRawJointGuardedCommonRightOwnerNoRecv,
    profiledRawJointGuardedCommonTwoShadowRecvRightOwner,
    profiledRawJointGuardedCommonTailOneOfRightOwner,
    profiledRawJointGuardedCommonTailTwoOfRightReceiver]

/-- Left pending resolution mirror. -/
theorem profiledRawJointGuardedCommonTailResolveLeftStep_local
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    let next := profiledRawJointGuardedCommonTailResolveLeftStep A strategy hwin
      pending input
    ((profiledRawJointGuardedCommonTailResolveLeftOne A strategy hwin
        initialBank pending.receiver pending.owner input.1 input.2).1,
      (profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo A strategy hwin
        initialBank pending.owner input.2).1) = next.1 ∧
    (profiledRawJointGuardedCommonTailResolveLeftOne A strategy hwin
        initialBank pending.receiver pending.owner input.1 input.2).2 =
      .exceptional
        (profiledRawJointGuardedCommonTailOneOfLeftReceiver A strategy hwin
          next.2) ∧
    (profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo A strategy hwin
        initialBank pending.owner input.2).2 =
      .exceptional
        (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin
          next.2.strict.owner) := by
  rcases pending with ⟨receiver, owner, hsource⟩
  rcases owner with ⟨ownerSource, ownerControl⟩
  rcases receiver.shadow.source with receiverSource
  cases hsource
  simp [profiledRawJointGuardedCommonTailResolveLeftStep,
    profiledRawJointGuardedCommonResolveStrictLeft,
    profiledRawJointGuardedCommonTailResolveLeftOne,
    profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo,
    profiledRawJointGuardedCommonLeftOwnerFor,
    profiledRawJointGuardedCommonLeftOwnerNoRecv,
    profiledRawJointGuardedCommonOneShadowRecvLeftOwner,
    profiledRawJointGuardedCommonTailOneOfLeftReceiver,
    profiledRawJointGuardedCommonTailTwoOfLeftOwner]

/-! ## Embedded resolved states and exact strict-tail traces -/

/-- Embed a synchronized resolved strict-right state, together with the
freshly emitted pair of outputs, in the concrete global Moore state. -/
noncomputable def profiledRawJointGuardedCommonTailStrictRightGlobalState
    (root : CommonControl A strategy hwin)
    (state : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (output : Out₁ × Out₂) :
    ((TailKernel A strategy hwin initialBank root).globalMachine).State :=
  ((.exceptional
      (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin
        state.strict.owner), output.1),
    (.exceptional
      (profiledRawJointGuardedCommonTailTwoOfRightReceiver A strategy hwin
        state), output.2))

/-- Strict-left mirror. -/
noncomputable def profiledRawJointGuardedCommonTailStrictLeftGlobalState
    (root : CommonControl A strategy hwin)
    (state : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (output : Out₁ × Out₂) :
    ((TailKernel A strategy hwin initialBank root).globalMachine).State :=
  ((.exceptional
      (profiledRawJointGuardedCommonTailOneOfLeftReceiver A strategy hwin
        state), output.1),
    (.exceptional
      (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin
        state.strict.owner), output.2))

/-- One concrete strict-right global step agrees exactly with the canonical
finite sibling-controller step.  The orientation is selected by the fixed
physical environment; it is not supplied to either local process. -/
theorem profiledRawJointGuardedCommonTailCore_advanceStrictRight
    (root : CommonControl A strategy hwin)
    (state : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (oldOutput : Out₁ × Out₂) (input : In₂ × In₁) :
    let kernel := TailKernel A strategy hwin initialBank root
    let next := profiledRawJointGuardedCommonTailStrictRightStep A strategy
      hwin state input
    kernel.globalMachine.step
        (profiledRawJointGuardedCommonTailStrictRightGlobalState A strategy
          hwin initialBank root state oldOutput)
        { inputOne := input.2, inputTwo := input.1, graph := .right } =
      profiledRawJointGuardedCommonTailStrictRightGlobalState A strategy hwin
        initialBank root next.2 next.1 := by
  dsimp only
  let one := profiledRawJointGuardedCommonTailRightOwnerNoRecvOne A strategy
    hwin initialBank state.strict.owner input.2
  let two := profiledRawJointGuardedCommonTailContinueRightTwo A strategy hwin
    initialBank state state.strict.owner input.1 input.2
  have hlocal :=
    profiledRawJointGuardedCommonTailStrictRightStep_local A strategy hwin
      initialBank state input
  rcases hlocal with ⟨hout, hone, htwo⟩
  change ((one.2, one.1), (two.2, two.1)) = _
  rw [hone, htwo]
  unfold profiledRawJointGuardedCommonTailStrictRightGlobalState
  rw [← hout]
  rfl

/-- One concrete strict-left step agrees with its canonical finite mirror. -/
theorem profiledRawJointGuardedCommonTailCore_advanceStrictLeft
    (root : CommonControl A strategy hwin)
    (state : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (oldOutput : Out₁ × Out₂) (input : In₁ × In₂) :
    let kernel := TailKernel A strategy hwin initialBank root
    let next := profiledRawJointGuardedCommonTailStrictLeftStep A strategy
      hwin state input
    kernel.globalMachine.step
        (profiledRawJointGuardedCommonTailStrictLeftGlobalState A strategy hwin
          initialBank root state oldOutput)
        { inputOne := input.1, inputTwo := input.2, graph := .left } =
      profiledRawJointGuardedCommonTailStrictLeftGlobalState A strategy hwin
        initialBank root next.2 next.1 := by
  dsimp only
  let one := profiledRawJointGuardedCommonTailContinueLeftOne A strategy hwin
    initialBank state state.strict.owner input.1 input.2
  let two := profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo A strategy hwin
    initialBank state.strict.owner input.2
  have hlocal :=
    profiledRawJointGuardedCommonTailStrictLeftStep_local A strategy hwin
      initialBank state input
  rcases hlocal with ⟨hout, hone, htwo⟩
  change ((one.2, one.1), (two.2, two.1)) = _
  rw [hone, htwo]
  unfold profiledRawJointGuardedCommonTailStrictLeftGlobalState
  rw [← hout]
  rfl

/-- The finite resolved state after the resolving round and `n` subsequent
strict-right rounds. -/
noncomputable def profiledRawJointGuardedCommonTailStrictRightStateTrace
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    Nat → ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin
  | 0 =>
      (profiledRawJointGuardedCommonTailResolveRightStep A strategy hwin
        (profiledRawJointGuardedCommonTailInitialRightPending A strategy hwin
          root (env 0)) (env 1)).2
  | n + 1 =>
      (profiledRawJointGuardedCommonTailStrictRightStep A strategy hwin
        (profiledRawJointGuardedCommonTailStrictRightStateTrace root env n)
        (env (n + 2))).2

/-- Outputs stored with the corresponding resolved strict-right state. -/
noncomputable def profiledRawJointGuardedCommonTailStrictRightOutputTrace
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    Nat → Out₁ × Out₂
  | 0 =>
      (profiledRawJointGuardedCommonTailResolveRightStep A strategy hwin
        (profiledRawJointGuardedCommonTailInitialRightPending A strategy hwin
          root (env 0)) (env 1)).1
  | n + 1 =>
      (profiledRawJointGuardedCommonTailStrictRightStep A strategy hwin
        (profiledRawJointGuardedCommonTailStrictRightStateTrace A strategy hwin
          root env n) (env (n + 2))).1

/-- Left resolved-state trace. -/
noncomputable def profiledRawJointGuardedCommonTailStrictLeftStateTrace
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    Nat → ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin
  | 0 =>
      (profiledRawJointGuardedCommonTailResolveLeftStep A strategy hwin
        (profiledRawJointGuardedCommonTailInitialLeftPending A strategy hwin
          root (env 0)) (env 1)).2
  | n + 1 =>
      (profiledRawJointGuardedCommonTailStrictLeftStep A strategy hwin
        (profiledRawJointGuardedCommonTailStrictLeftStateTrace root env n)
        (env (n + 2))).2

/-- Left stored-output trace. -/
noncomputable def profiledRawJointGuardedCommonTailStrictLeftOutputTrace
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    Nat → Out₁ × Out₂
  | 0 =>
      (profiledRawJointGuardedCommonTailResolveLeftStep A strategy hwin
        (profiledRawJointGuardedCommonTailInitialLeftPending A strategy hwin
          root (env 0)) (env 1)).1
  | n + 1 =>
      (profiledRawJointGuardedCommonTailStrictLeftStep A strategy hwin
        (profiledRawJointGuardedCommonTailStrictLeftStateTrace A strategy hwin
          root env n) (env (n + 2))).1

/-- The resolving round enters exactly the canonical resolved right state. -/
theorem profiledRawJointGuardedCommonTailCore_globalStateTrace_two_right
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    ((TailKernel A strategy hwin initialBank root).globalMachine
        ).globalStateTrace
        (profiledRawJointGuardedCommonTailStrictRightEnvironment env) 2 =
      profiledRawJointGuardedCommonTailStrictRightGlobalState A strategy hwin
        initialBank root
        (profiledRawJointGuardedCommonTailStrictRightStateTrace A strategy hwin
          root env 0)
        (profiledRawJointGuardedCommonTailStrictRightOutputTrace A strategy hwin
          root env 0) := by
  let pending :=
    profiledRawJointGuardedCommonTailInitialRightPending A strategy hwin root
      (env 0)
  let one := profiledRawJointGuardedCommonTailRightOwnerNoRecvOne A strategy
    hwin initialBank pending.owner (env 1).2
  let two := profiledRawJointGuardedCommonTailResolveRightTwo A strategy hwin
    initialBank pending.receiver pending.owner (env 1).1 (env 1).2
  have hlocal :=
    profiledRawJointGuardedCommonTailResolveRightStep_local A strategy hwin
      initialBank pending (env 1)
  rcases hlocal with ⟨hout, hone, htwo⟩
  rw [profiledRawJointGuardedCommonTailCore_secondStrictRight A strategy hwin
    initialBank root env]
  change ((one.2, one.1), (two.2, two.1)) = _
  rw [hone, htwo]
  unfold profiledRawJointGuardedCommonTailStrictRightGlobalState
  rw [profiledRawJointGuardedCommonTailStrictRightStateTrace,
    profiledRawJointGuardedCommonTailStrictRightOutputTrace]
  rw [← hout]
  rfl

/-- Resolving-round left mirror. -/
theorem profiledRawJointGuardedCommonTailCore_globalStateTrace_two_left
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    ((TailKernel A strategy hwin initialBank root).globalMachine
        ).globalStateTrace
        (profiledRawJointGuardedCommonTailStrictLeftEnvironment env) 2 =
      profiledRawJointGuardedCommonTailStrictLeftGlobalState A strategy hwin
        initialBank root
        (profiledRawJointGuardedCommonTailStrictLeftStateTrace A strategy hwin
          root env 0)
        (profiledRawJointGuardedCommonTailStrictLeftOutputTrace A strategy hwin
          root env 0) := by
  let pending :=
    profiledRawJointGuardedCommonTailInitialLeftPending A strategy hwin root
      (env 0)
  let one := profiledRawJointGuardedCommonTailResolveLeftOne A strategy hwin
    initialBank pending.receiver pending.owner (env 1).1 (env 1).2
  let two := profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo A strategy
    hwin initialBank pending.owner (env 1).2
  have hlocal :=
    profiledRawJointGuardedCommonTailResolveLeftStep_local A strategy hwin
      initialBank pending (env 1)
  rcases hlocal with ⟨hout, hone, htwo⟩
  rw [profiledRawJointGuardedCommonTailCore_secondStrictLeft A strategy hwin
    initialBank root env]
  change ((one.2, one.1), (two.2, two.1)) = _
  rw [hone, htwo]
  unfold profiledRawJointGuardedCommonTailStrictLeftGlobalState
  rw [profiledRawJointGuardedCommonTailStrictLeftStateTrace,
    profiledRawJointGuardedCommonTailStrictLeftOutputTrace]
  rw [← hout]
  rfl

/-- Every state after the resolving round is the exact embedded finite
strict-right controller/monitor state. -/
theorem profiledRawJointGuardedCommonTailCore_globalStateTrace_add_two_right
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    ∀ n,
      ((TailKernel A strategy hwin initialBank root).globalMachine
          ).globalStateTrace
          (profiledRawJointGuardedCommonTailStrictRightEnvironment env)
          (n + 2) =
        profiledRawJointGuardedCommonTailStrictRightGlobalState A strategy hwin
          initialBank root
          (profiledRawJointGuardedCommonTailStrictRightStateTrace A strategy
            hwin root env n)
          (profiledRawJointGuardedCommonTailStrictRightOutputTrace A strategy
            hwin root env n) := by
  intro n
  induction n with
  | zero =>
      exact
        profiledRawJointGuardedCommonTailCore_globalStateTrace_two_right A
          strategy hwin initialBank root env
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, ih]
      change
        (TailKernel A strategy hwin initialBank root).globalMachine.step
            (profiledRawJointGuardedCommonTailStrictRightGlobalState A
              strategy hwin initialBank root
              (profiledRawJointGuardedCommonTailStrictRightStateTrace A
                strategy hwin root env n)
              (profiledRawJointGuardedCommonTailStrictRightOutputTrace A
                strategy hwin root env n))
            { inputOne := (env (n + 2)).2,
              inputTwo := (env (n + 2)).1,
              graph := .right } = _
      rw [profiledRawJointGuardedCommonTailCore_advanceStrictRight A strategy
        hwin initialBank]
      rfl

/-- Infinite strict-left trace mirror. -/
theorem profiledRawJointGuardedCommonTailCore_globalStateTrace_add_two_left
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    ∀ n,
      ((TailKernel A strategy hwin initialBank root).globalMachine
          ).globalStateTrace
          (profiledRawJointGuardedCommonTailStrictLeftEnvironment env)
          (n + 2) =
        profiledRawJointGuardedCommonTailStrictLeftGlobalState A strategy hwin
          initialBank root
          (profiledRawJointGuardedCommonTailStrictLeftStateTrace A strategy
            hwin root env n)
          (profiledRawJointGuardedCommonTailStrictLeftOutputTrace A strategy
            hwin root env n) := by
  intro n
  induction n with
  | zero =>
      exact
        profiledRawJointGuardedCommonTailCore_globalStateTrace_two_left A
          strategy hwin initialBank root env
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, ih]
      change
        (TailKernel A strategy hwin initialBank root).globalMachine.step
            (profiledRawJointGuardedCommonTailStrictLeftGlobalState A strategy
              hwin initialBank root
              (profiledRawJointGuardedCommonTailStrictLeftStateTrace A strategy
                hwin root env n)
              (profiledRawJointGuardedCommonTailStrictLeftOutputTrace A strategy
                hwin root env n))
            { inputOne := (env (n + 2)).1,
              inputTwo := (env (n + 2)).2,
              graph := .left } = _
      rw [profiledRawJointGuardedCommonTailCore_advanceStrictLeft A strategy
        hwin initialBank]
      rfl

/-! ## Literal guarded controller/monitor letters -/

/-- The one narrowed guarded-right record read from an arbitrary synchronized
resolved state. -/
noncomputable def profiledRawJointGuardedCommonTailStrictRightRecord
    (state : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (input : In₂ × In₁) :=
  let receiver := state.strict.receiver
  let move := receiver.1.1.1
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  let ownerControl := profiledRawJointGuardedCommonRightStrictOwnerFor A
    strategy hwin receiver state.strict.owner
  narrowedRecord monitor (controller.labelOf ownerControl) receiver.2.1 input

/-- Left narrowed guarded record. -/
noncomputable def profiledRawJointGuardedCommonTailStrictLeftRecord
    (state : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (input : In₁ × In₂) :=
  let receiver := state.strict.receiver
  let move := receiver.1.1.2
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  let ownerControl := profiledRawJointGuardedCommonLeftStrictOwnerFor A
    strategy hwin receiver state.strict.owner
  narrowedRecord monitor (controller.labelOf ownerControl) receiver.2.1 input

/-- Pending-resolution right record, before its monitor state is advanced. -/
noncomputable def profiledRawJointGuardedCommonTailResolveRightRecord
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₂ × In₁) :=
  let shadow := pending.receiver.shadow
  let move := shadow.source.1.1
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  let ownerControl := profiledRawJointGuardedCommonRightOwnerFor A strategy hwin
    shadow pending.owner
  narrowedRecord monitor (controller.labelOf ownerControl)
    shadow.strictReceiver input

/-- Pending left record. -/
noncomputable def profiledRawJointGuardedCommonTailResolveLeftRecord
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :=
  let shadow := pending.receiver.shadow
  let move := shadow.source.1.2
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  let ownerControl := profiledRawJointGuardedCommonLeftOwnerFor A strategy hwin
    shadow pending.owner
  narrowedRecord monitor (controller.labelOf ownerControl)
    shadow.strictReceiver input

/-- A resolved strict-right step emits exactly the two physical projections
of its single guarded controller/monitor record. -/
theorem profiledRawJointGuardedCommonTailStrictRightStep_output_record
    (state : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (input : In₂ × In₁) :
    (profiledRawJointGuardedCommonTailStrictRightStep A strategy hwin state
      input).1 =
      let record := profiledRawJointGuardedCommonTailStrictRightRecord A
        strategy hwin state input
      (record.2.2,
        pairedRightInformedForRow .both
          (profiledRawJointTargetRightPhysicalLetter A record).2.1) := by
  rcases state with ⟨⟨owner, receiver, hsource⟩, close⟩
  rcases owner with ⟨source, ownerControl⟩
  rcases receiver with ⟨receiverSource, receiverState, target⟩
  cases hsource
  simp [profiledRawJointGuardedCommonTailStrictRightStep,
    profiledRawJointGuardedCommonTailStrictRightRecord,
    profiledRawJointGuardedCommonStrictRightStep,
    profiledRawJointGuardedCommonRightStrictOwnerFor,
    profiledRawJointGuardedCommonRightOwnerNoRecv,
    profiledRawJointGuardedCommonRightStrictReceiverRecvOwner,
    narrowedRecord, profiledRawJointTargetRightPhysicalLetter,
    indexedTargetPhysicalLetter]

/-- Resolved strict-left output record. -/
theorem profiledRawJointGuardedCommonTailStrictLeftStep_output_record
    (state : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonTailStrictLeftStep A strategy hwin state
      input).1 =
      let record := profiledRawJointGuardedCommonTailStrictLeftRecord A
        strategy hwin state input
      (pairedLeftInformedForRow .both
          (profiledRawJointTargetLeftPhysicalLetter A record).2.1,
        record.2.2) := by
  rcases state with ⟨⟨receiver, owner, hsource⟩, close⟩
  rcases receiver with ⟨receiverSource, receiverState, target⟩
  rcases owner with ⟨ownerSource, ownerControl⟩
  cases hsource
  simp [profiledRawJointGuardedCommonTailStrictLeftStep,
    profiledRawJointGuardedCommonTailStrictLeftRecord,
    profiledRawJointGuardedCommonStrictLeftStep,
    profiledRawJointGuardedCommonLeftStrictOwnerFor,
    profiledRawJointGuardedCommonLeftOwnerNoRecv,
    profiledRawJointGuardedCommonLeftStrictReceiverRecvOwner,
    narrowedRecord, profiledRawJointTargetLeftPhysicalLetter,
    indexedTargetPhysicalLetter]

/-- Pending right resolution emits the same projections before advancing the
finite state. -/
theorem profiledRawJointGuardedCommonTailResolveRightStep_output_record
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₂ × In₁) :
    (profiledRawJointGuardedCommonTailResolveRightStep A strategy hwin pending
      input).1 =
      let record := profiledRawJointGuardedCommonTailResolveRightRecord A
        strategy hwin pending input
      (record.2.2,
        pairedRightInformedForRow .both
          (profiledRawJointTargetRightPhysicalLetter A record).2.1) := by
  rcases pending with ⟨owner, receiver, hsource⟩
  rcases owner with ⟨ownerSource, ownerControl⟩
  rcases receiver.shadow.source with receiverSource
  cases hsource
  simp [profiledRawJointGuardedCommonTailResolveRightStep,
    profiledRawJointGuardedCommonTailResolveRightRecord,
    profiledRawJointGuardedCommonResolveStrictRight,
    profiledRawJointGuardedCommonRightOwnerFor,
    profiledRawJointGuardedCommonRightOwnerNoRecv,
    profiledRawJointGuardedCommonTwoShadowRecvRightOwner,
    narrowedRecord, profiledRawJointTargetRightPhysicalLetter,
    indexedTargetPhysicalLetter]

/-- Pending left output record. -/
theorem profiledRawJointGuardedCommonTailResolveLeftStep_output_record
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonTailResolveLeftStep A strategy hwin pending
      input).1 =
      let record := profiledRawJointGuardedCommonTailResolveLeftRecord A
        strategy hwin pending input
      (pairedLeftInformedForRow .both
          (profiledRawJointTargetLeftPhysicalLetter A record).2.1,
        record.2.2) := by
  rcases pending with ⟨receiver, owner, hsource⟩
  rcases owner with ⟨ownerSource, ownerControl⟩
  rcases receiver.shadow.source with receiverSource
  cases hsource
  simp [profiledRawJointGuardedCommonTailResolveLeftStep,
    profiledRawJointGuardedCommonTailResolveLeftRecord,
    profiledRawJointGuardedCommonResolveStrictLeft,
    profiledRawJointGuardedCommonLeftOwnerFor,
    profiledRawJointGuardedCommonLeftOwnerNoRecv,
    profiledRawJointGuardedCommonOneShadowRecvLeftOwner,
    narrowedRecord, profiledRawJointTargetLeftPhysicalLetter,
    indexedTargetPhysicalLetter]

/-! ## Physical words and controller-play identification -/

/-- The physical all-right word written directly from the exact finite output
trace.  Round zero is the open root record; round `n+1` reads the output
stored with resolved state `n`. -/
noncomputable def profiledRawJointGuardedCommonTailStrictRightTraceWord
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)
  | 0 =>
      let one := profiledRawJointGuardedCommonTailInitialNoRecvOne A strategy
        hwin initialBank root (env 0).2
      let two := profiledRawJointGuardedCommonTailInitialRecvTwo A strategy hwin
        initialBank root (env 0).1 (env 0).2
      rightRoundRecord (env 0) one.1 two.1
  | n + 1 =>
      let output :=
        profiledRawJointGuardedCommonTailStrictRightOutputTrace A strategy hwin
          root env n
      rightRoundRecord (env (n + 1)) output.1 output.2

/-- Left physical trace word. -/
noncomputable def profiledRawJointGuardedCommonTailStrictLeftTraceWord
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)
  | 0 =>
      let one := profiledRawJointGuardedCommonTailInitialRecvOne A strategy hwin
        initialBank root (env 0).1 (env 0).2
      let two := profiledRawJointGuardedCommonTailInitialNoRecvTwo A strategy
        hwin initialBank root (env 0).2
      leftRoundRecord (env 0) one.1 two.1
  | n + 1 =>
      let output :=
        profiledRawJointGuardedCommonTailStrictLeftOutputTrace A strategy hwin
          root env n
      leftRoundRecord (env (n + 1)) output.1 output.2

/-- The concrete kernel's global all-right word is pointwise the exact finite
strict trace word. -/
theorem
    profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_right_apply
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁)
    (n : Nat) :
    let kernel := TailKernel A strategy hwin initialBank root
    kernel.globalMachine.globalMachineTraceWord kernel.globalOutputOne
        kernel.globalOutputTwo
        (profiledRawJointGuardedCommonTailStrictRightEnvironment env) n =
      profiledRawJointGuardedCommonTailStrictRightTraceWord A strategy hwin
        initialBank root env n := by
  dsimp only
  rw [FiniteGlobalRoundMachine.globalMachineTraceWord]
  cases n with
  | zero =>
      rw [profiledRawJointGuardedCommonTailCore_firstStrictRight A strategy
        hwin initialBank root env]
      rfl
  | succ n =>
      rw [profiledRawJointGuardedCommonTailCore_globalStateTrace_add_two_right
        A strategy hwin initialBank root env n]
      rfl

/-- Whole-word all-right equality. -/
theorem profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_right_eq
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    let kernel := TailKernel A strategy hwin initialBank root
    kernel.globalMachine.globalMachineTraceWord kernel.globalOutputOne
        kernel.globalOutputTwo
        (profiledRawJointGuardedCommonTailStrictRightEnvironment env) =
      profiledRawJointGuardedCommonTailStrictRightTraceWord A strategy hwin
        initialBank root env := by
  funext n
  exact
    profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_right_apply A
      strategy hwin initialBank root env n

/-- Pointwise all-left global trace word. -/
theorem
    profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_left_apply
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂)
    (n : Nat) :
    let kernel := TailKernel A strategy hwin initialBank root
    kernel.globalMachine.globalMachineTraceWord kernel.globalOutputOne
        kernel.globalOutputTwo
        (profiledRawJointGuardedCommonTailStrictLeftEnvironment env) n =
      profiledRawJointGuardedCommonTailStrictLeftTraceWord A strategy hwin
        initialBank root env n := by
  dsimp only
  rw [FiniteGlobalRoundMachine.globalMachineTraceWord]
  cases n with
  | zero =>
      rw [profiledRawJointGuardedCommonTailCore_firstStrictLeft A strategy hwin
        initialBank root env]
      rfl
  | succ n =>
      rw [profiledRawJointGuardedCommonTailCore_globalStateTrace_add_two_left A
        strategy hwin initialBank root env n]
      rfl

/-- Whole-word all-left equality. -/
theorem profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_left_eq
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    let kernel := TailKernel A strategy hwin initialBank root
    kernel.globalMachine.globalMachineTraceWord kernel.globalOutputOne
        kernel.globalOutputTwo
        (profiledRawJointGuardedCommonTailStrictLeftEnvironment env) =
      profiledRawJointGuardedCommonTailStrictLeftTraceWord A strategy hwin
        initialBank root env := by
  funext n
  exact
    profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_left_apply A
      strategy hwin initialBank root env n

/-- The same all-right word, now written solely as the row-`both` physical
projection of the guarded finite sibling controller/monitor play. -/
noncomputable def profiledRawJointGuardedCommonTailStrictRightControllerWord
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)
  | 0 =>
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin root
      pairedRightRecordForRow .both
        (profiledRawJointTargetRightPhysicalLetter A
          (pair.rightRootRecord A strategy hwin ((env 0).2, (env 0).1)))
  | 1 =>
      let pending :=
        profiledRawJointGuardedCommonTailInitialRightPending A strategy hwin
          root (env 0)
      pairedRightRecordForRow .both
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointGuardedCommonTailResolveRightRecord A strategy hwin
            pending (env 1)))
  | n + 2 =>
      pairedRightRecordForRow .both
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointGuardedCommonTailStrictRightRecord A strategy hwin
            (profiledRawJointGuardedCommonTailStrictRightStateTrace A strategy
              hwin root env n) (env (n + 2))))

/-- Guarded finite left controller/monitor play. -/
noncomputable def profiledRawJointGuardedCommonTailStrictLeftControllerWord
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)
  | 0 =>
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin root
      pairedLeftRecordForRow .both
        (profiledRawJointTargetLeftPhysicalLetter A
          (pair.leftRootRecord A strategy hwin (env 0)))
  | 1 =>
      let pending :=
        profiledRawJointGuardedCommonTailInitialLeftPending A strategy hwin root
          (env 0)
      pairedLeftRecordForRow .both
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointGuardedCommonTailResolveLeftRecord A strategy hwin
            pending (env 1)))
  | n + 2 =>
      pairedLeftRecordForRow .both
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointGuardedCommonTailStrictLeftRecord A strategy hwin
            (profiledRawJointGuardedCommonTailStrictLeftStateTrace A strategy
              hwin root env n) (env (n + 2))))

/-- Output-trace and guarded-controller descriptions coincide at every
all-right round. -/
theorem profiledRawJointGuardedCommonTailStrictRightTraceWord_eq_controller
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    profiledRawJointGuardedCommonTailStrictRightTraceWord A strategy hwin
        initialBank root env =
      profiledRawJointGuardedCommonTailStrictRightControllerWord A strategy
        hwin root env := by
  funext n
  cases n with
  | zero =>
      have hout :=
        profiledRawJointGuardedCommonTailInitialStrictRight_outputs A strategy
          hwin initialBank root ((env 0).2, (env 0).1)
      simpa [profiledRawJointGuardedCommonTailStrictRightTraceWord,
        profiledRawJointGuardedCommonTailStrictRightControllerWord,
        pairedRightRecordForRow, profiledRawJointTargetRightPhysicalLetter,
        indexedTargetPhysicalLetter] using
          congrArg (fun output ↦ rightRoundRecord (env 0) output.1 output.2)
            hout
  | succ n =>
      cases n with
      | zero =>
          have hout :=
            profiledRawJointGuardedCommonTailResolveRightStep_output_record A
              strategy hwin
              (profiledRawJointGuardedCommonTailInitialRightPending A strategy
                hwin root (env 0)) (env 1)
          simpa [profiledRawJointGuardedCommonTailStrictRightTraceWord,
            profiledRawJointGuardedCommonTailStrictRightControllerWord,
            profiledRawJointGuardedCommonTailStrictRightOutputTrace,
            pairedRightRecordForRow] using
              congrArg
                (fun output ↦ rightRoundRecord (env 1) output.1 output.2)
                hout
      | succ n =>
          have hout :=
            profiledRawJointGuardedCommonTailStrictRightStep_output_record A
              strategy hwin
              (profiledRawJointGuardedCommonTailStrictRightStateTrace A
                strategy hwin root env n) (env (n + 2))
          simpa [profiledRawJointGuardedCommonTailStrictRightTraceWord,
            profiledRawJointGuardedCommonTailStrictRightControllerWord,
            profiledRawJointGuardedCommonTailStrictRightOutputTrace,
            pairedRightRecordForRow] using
              congrArg
                (fun output ↦
                  rightRoundRecord (env (n + 2)) output.1 output.2) hout

/-- Left trace/controller equality. -/
theorem profiledRawJointGuardedCommonTailStrictLeftTraceWord_eq_controller
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    profiledRawJointGuardedCommonTailStrictLeftTraceWord A strategy hwin
        initialBank root env =
      profiledRawJointGuardedCommonTailStrictLeftControllerWord A strategy hwin
        root env := by
  funext n
  cases n with
  | zero =>
      have hout :=
        profiledRawJointGuardedCommonTailInitialStrictLeft_outputs A strategy
          hwin initialBank root (env 0)
      simpa [profiledRawJointGuardedCommonTailStrictLeftTraceWord,
        profiledRawJointGuardedCommonTailStrictLeftControllerWord,
        pairedLeftRecordForRow, profiledRawJointTargetLeftPhysicalLetter,
        indexedTargetPhysicalLetter] using
          congrArg (fun output ↦ leftRoundRecord (env 0) output.1 output.2)
            hout
  | succ n =>
      cases n with
      | zero =>
          have hout :=
            profiledRawJointGuardedCommonTailResolveLeftStep_output_record A
              strategy hwin
              (profiledRawJointGuardedCommonTailInitialLeftPending A strategy
                hwin root (env 0)) (env 1)
          simpa [profiledRawJointGuardedCommonTailStrictLeftTraceWord,
            profiledRawJointGuardedCommonTailStrictLeftControllerWord,
            profiledRawJointGuardedCommonTailStrictLeftOutputTrace,
            pairedLeftRecordForRow] using
              congrArg
                (fun output ↦ leftRoundRecord (env 1) output.1 output.2)
                hout
      | succ n =>
          have hout :=
            profiledRawJointGuardedCommonTailStrictLeftStep_output_record A
              strategy hwin
              (profiledRawJointGuardedCommonTailStrictLeftStateTrace A strategy
                hwin root env n) (env (n + 2))
          simpa [profiledRawJointGuardedCommonTailStrictLeftTraceWord,
            profiledRawJointGuardedCommonTailStrictLeftControllerWord,
            profiledRawJointGuardedCommonTailStrictLeftOutputTrace,
            pairedLeftRecordForRow] using
              congrArg
                (fun output ↦
                  leftRoundRecord (env (n + 2)) output.1 output.2) hout

/-- End-to-end operational identification: the concrete all-right kernel word
is exactly the physical row of one guarded finite sibling-controller play. -/
theorem
    profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_right_controller
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    let kernel := TailKernel A strategy hwin initialBank root
    kernel.globalMachine.globalMachineTraceWord kernel.globalOutputOne
        kernel.globalOutputTwo
        (profiledRawJointGuardedCommonTailStrictRightEnvironment env) =
      profiledRawJointGuardedCommonTailStrictRightControllerWord A strategy
        hwin root env := by
  dsimp only
  rw [profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_right_eq A
    strategy hwin initialBank root env,
    profiledRawJointGuardedCommonTailStrictRightTraceWord_eq_controller A
      strategy hwin initialBank root env]

/-- All-left operational identification. -/
theorem
    profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_left_controller
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    let kernel := TailKernel A strategy hwin initialBank root
    kernel.globalMachine.globalMachineTraceWord kernel.globalOutputOne
        kernel.globalOutputTwo
        (profiledRawJointGuardedCommonTailStrictLeftEnvironment env) =
      profiledRawJointGuardedCommonTailStrictLeftControllerWord A strategy hwin
        root env := by
  dsimp only
  rw [profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_left_eq A
    strategy hwin initialBank root env,
    profiledRawJointGuardedCommonTailStrictLeftTraceWord_eq_controller A
      strategy hwin initialBank root env]

/-! ## Exact acceptance residual -/

/-- What remains after the operational trace identification on the right:
extract the `.both` DPA thread from `memberController_wins` for the guarded
target monitor.  The start state is the represented entry state, not
`A.initial`; an outer finite prefix must separately identify its reached DPA
state with this entry state before ordinary `A.Accepts` can be concluded. -/
def ProfiledRawJointGuardedCommonTailStrictRightControllerAcceptsFromEntry
    (root : CommonControl A strategy hwin) : Prop :=
  let pair := profiledRawJointGuardedInitialCommonControlPair A strategy hwin
    root
  ∀ env : Nat → In₂ × In₁,
    A.AcceptsFrom pair.1.1.1.base.source.1.1.2
      (profiledRawJointGuardedCommonTailStrictRightControllerWord A strategy
        hwin root env)

/-- Left `.both`-entry acceptance residual. -/
def ProfiledRawJointGuardedCommonTailStrictLeftControllerAcceptsFromEntry
    (root : CommonControl A strategy hwin) : Prop :=
  let pair := profiledRawJointGuardedInitialCommonControlPair A strategy hwin
    root
  ∀ env : Nat → In₁ × In₂,
    A.AcceptsFrom pair.1.2.1.base.source.1.1.2
      (profiledRawJointGuardedCommonTailStrictLeftControllerWord A strategy
        hwin root env)

end


end DetParityAutomaton

end DistributedSynthesis
