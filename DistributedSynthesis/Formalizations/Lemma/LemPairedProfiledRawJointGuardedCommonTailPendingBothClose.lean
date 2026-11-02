/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCrossAnchorJointMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailHandoff

/-!
# Closing a one-round strict block on the first simultaneous receive

Suppose a common phase is followed by one strict-right round and then by a
simultaneous round.  The latter round is charged to the old right epoch: the
two processes execute the next record of the already installed right sibling
controller and immediately enter its checked `.both` target.  The left case
is symmetric.

This is the finite alternative to rationalizing the common and strict
histories independently.  At the simultaneous receive both processes exchange
the complete finite pending controls, so each can reconstruct the same old
controller record, staged close, recurrent key, and root controls.  No local
map is given the graph, an orientation, a leader bit, or a semantic history.
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

private abbrev OneControl :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin)

private abbrev TwoControl :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin)

/-! ## The checked close computed from the shared pending key -/

/-- Close a right sibling controller at the current simultaneous record. -/
noncomputable def profiledRawJointGuardedRightPendingBothClose
    (key : ProfiledRawJointGuardedRightCrossAnchorKey A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin :=
  let ownerControl := profiledRawJointGuardedCommonRightOwnerFor A strategy
    hwin key.receiver.shadow key.owner
  profiledRawJointGuardedCommonRightStageClose A strategy hwin
    key.receiver.shadow.source
    (ownerControl, key.receiver.shadow.strictReceiver) (input.2, input.1) .both

/-- Strict-left mirror. -/
noncomputable def profiledRawJointGuardedLeftPendingBothClose
    (key : ProfiledRawJointGuardedLeftCrossAnchorKey A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin :=
  let ownerControl := profiledRawJointGuardedCommonLeftOwnerFor A strategy
    hwin key.receiver.shadow key.owner
  profiledRawJointGuardedCommonLeftStageClose A strategy hwin
    key.receiver.shadow.source
    (ownerControl, key.receiver.shadow.strictReceiver) input .both

/-! ## Direct responses: old-epoch output, fresh recurrent root -/

/-- The response to a right-pending simultaneous receive.  The current output
is the old right controller's next record; the continuation is the checked
left-oriented recurrent root selected by that same record. -/
noncomputable def profiledRawJointGuardedRightPendingBothResponse
    (key : ProfiledRawJointGuardedRightCrossAnchorKey A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCrossAnchorResponse A strategy hwin initialBank :=
  let owner := profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin
    key.owner input.1
  let receiver := profiledRawJointGuardedCommonTwoShadowRecvRightOwner A
    strategy hwin key.receiver.shadow key.owner input.2 input.1
  let output := (owner.1, receiver.1)
  let close := profiledRawJointGuardedRightPendingBothClose A strategy hwin
    key input
  let recurrentKey :=
    profiledRawJointGuardedCommonRightStagedCombinedKey A strategy hwin
      initialBank close
  let receiver :=
    profiledRawJointGuardedCommonRightStagedInitialLeftReceiver A strategy
      hwin initialBank close
  let owner :=
    profiledRawJointGuardedCommonRightStagedInitialLeftOwner A strategy hwin
      initialBank close
  ⟨output.1, output.2,
    ⟨.leftReceiver recurrentKey receiver, .leftOwner recurrentKey owner⟩⟩

/-- Left-pending mirror. -/
noncomputable def profiledRawJointGuardedLeftPendingBothResponse
    (key : ProfiledRawJointGuardedLeftCrossAnchorKey A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCrossAnchorResponse A strategy hwin initialBank :=
  let receiver := profiledRawJointGuardedCommonOneShadowRecvLeftOwner A
    strategy hwin key.receiver.shadow key.owner input.1 input.2
  let owner := profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin
    key.owner input.2
  let output := (receiver.1, owner.1)
  let close := profiledRawJointGuardedLeftPendingBothClose A strategy hwin key
    input
  let recurrentKey :=
    profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy hwin
      initialBank close
  let owner :=
    profiledRawJointGuardedCommonLeftStagedInitialRightOwner A strategy hwin
      initialBank close
  let receiver :=
    profiledRawJointGuardedCommonLeftStagedInitialRightReceiver A strategy
      hwin initialBank close
  ⟨output.1, output.2,
    ⟨.rightOwner recurrentKey owner, .rightReceiver recurrentKey receiver⟩⟩

/-! ## Total finite banks and exact local projections -/

/-- The direct right-pending bank needs no outer rational policy. -/
noncomputable def profiledRawJointGuardedRightPendingBothBank :
    ProfiledRawJointGuardedRightCrossAnchorBank A strategy hwin initialBank :=
  fun key ↦ ⟨profiledRawJointGuardedRightPendingBothResponse A strategy hwin
    initialBank key⟩

/-- Left mirror. -/
noncomputable def profiledRawJointGuardedLeftPendingBothBank :
    ProfiledRawJointGuardedLeftCrossAnchorBank A strategy hwin initialBank :=
  fun key ↦ ⟨profiledRawJointGuardedLeftPendingBothResponse A strategy hwin
    initialBank key⟩

/-- The direct right bank emits exactly the old strict controller output. -/
theorem profiledRawJointGuardedRightPendingBothBank_output
    (pending : ProfiledRawJointGuardedCommonRightPending A strategy hwin)
    (input : In₁ × In₂) :
    let bank := profiledRawJointGuardedRightPendingBothBank A strategy hwin
      initialBank
    ((profiledRawJointGuardedRightCrossAnchorRecvOne A strategy hwin
        initialBank bank pending.owner pending.receiver input.1 input.2).1,
      (profiledRawJointGuardedRightCrossAnchorRecvTwo A strategy hwin
        initialBank bank pending.receiver pending.owner input.2 input.1).1) =
      (profiledRawJointGuardedCommonResolveStrictRight A strategy hwin pending
        input).1 := by
  rfl

/-- Left output mirror. -/
theorem profiledRawJointGuardedLeftPendingBothBank_output
    (pending : ProfiledRawJointGuardedCommonLeftPending A strategy hwin)
    (input : In₁ × In₂) :
    let bank := profiledRawJointGuardedLeftPendingBothBank A strategy hwin
      initialBank
    ((profiledRawJointGuardedLeftCrossAnchorRecvOne A strategy hwin
        initialBank bank pending.receiver pending.owner input.1 input.2).1,
      (profiledRawJointGuardedLeftCrossAnchorRecvTwo A strategy hwin
        initialBank bank pending.owner pending.receiver input.2 input.1).1) =
      (profiledRawJointGuardedCommonResolveStrictLeft A strategy hwin pending
        input).1 := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
