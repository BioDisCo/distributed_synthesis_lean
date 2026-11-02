/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedHybridCombinedFamily
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLocalStagedClose
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedForeverCommonAcceptance

/-!
# The local guarded-common tail front

After two simultaneous seed rounds, both processes carry the same finite
occurrence-sensitive common-policy control.  This file installs that control
in the genuinely local indexed-kernel front.  It covers:

* a first simultaneous receive from the bare common root;
* repeated simultaneous receives in the common shadow;
* the blind half of a first strict round;
* resolution of the receiver's common/strict ambiguity when the owner is
  delivered on the following strict round; and
* blind-owner continuation inside the resolved strict block.

The eventual checked close is deliberately left to the staged-close module:
at that point the two local maps must install the same dependent recurrent
key.  No definition below accepts a graph, orientation, hierarchy side,
strict-leader bit, semantic world, or history.
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

/-! ## Finite local front alphabets -/

/-- At the tail root, process one stores only the common-policy control
selected from the two physical seed rounds. -/
abbrev ProfiledRawJointGuardedCommonTailInitialOne :=
  CommonControl A strategy hwin

/-- Process-two mirror. -/
abbrev ProfiledRawJointGuardedCommonTailInitialTwo :=
  CommonControl A strategy hwin

/-- Process-one states before a checked recurrent handoff: a common shadow,
a strict-right blind owner, or a resolved strict-left receiver. -/
structure ProfiledRawJointGuardedCommonTailLeftReceiver where
  strict : ProfiledRawJointGuardedCommonLeftStrictState A strategy hwin
  close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin

/-- Process-two resolved strict-right receiver together with the checked
recurrent close staged by its latest actual receive. -/
structure ProfiledRawJointGuardedCommonTailRightReceiver where
  strict : ProfiledRawJointGuardedCommonRightStrictState A strategy hwin
  close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin

noncomputable instance profiledRawJointGuardedCommonTailLeftReceiverFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin) := by
  classical
  let equiv :
      ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin ≃
        ProfiledRawJointGuardedCommonLeftStrictState A strategy hwin ×
          ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin :=
    { toFun := fun state ↦ (state.strict, state.close)
      invFun := fun state ↦ ⟨state.1, state.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; cases state; rfl }
  exact Fintype.ofEquiv _ equiv.symm

noncomputable instance profiledRawJointGuardedCommonTailRightReceiverFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin) := by
  classical
  let equiv :
      ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin ≃
        ProfiledRawJointGuardedCommonRightStrictState A strategy hwin ×
          ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin :=
    { toFun := fun state ↦ (state.strict, state.close)
      invFun := fun state ↦ ⟨state.1, state.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; cases state; rfl }
  exact Fintype.ofEquiv _ equiv.symm

/-- Process-one states before a checked recurrent handoff: a common shadow,
a strict-right blind owner, or a resolved strict-left receiver. -/
abbrev ProfiledRawJointGuardedCommonTailExceptionalOne :=
  ProfiledRawJointGuardedInitialCommonOneState A strategy hwin ⊕
    (ProfiledRawJointGuardedCommonRightOwner A strategy hwin ⊕
      ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)

/-- Process-two mirror. -/
abbrev ProfiledRawJointGuardedCommonTailExceptionalTwo :=
  ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin ⊕
    (ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin ⊕
      ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)

noncomputable instance profiledRawJointGuardedCommonTailInitialOneFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin) := by
  classical
  infer_instance

noncomputable instance profiledRawJointGuardedCommonTailInitialTwoFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin) := by
  classical
  infer_instance

noncomputable instance profiledRawJointGuardedCommonTailExceptionalOneFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin) := by
  classical
  infer_instance

noncomputable instance profiledRawJointGuardedCommonTailExceptionalTwoFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin) := by
  classical
  infer_instance

private abbrev OneControl :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin)

private abbrev TwoControl :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
    (ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin)

/-! ## Named local injections -/

def profiledRawJointGuardedCommonTailOneOfCommon
    (state : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin) :
    ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin :=
  .inl state

def profiledRawJointGuardedCommonTailOneOfRightOwner
    (state : ProfiledRawJointGuardedCommonRightOwner A strategy hwin) :
    ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin :=
  .inr (.inl state)

def profiledRawJointGuardedCommonTailOneOfLeftReceiver
    (state : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin) :
    ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin :=
  .inr (.inr state)

def profiledRawJointGuardedCommonTailTwoOfCommon
    (state : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin) :
    ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin :=
  .inl state

def profiledRawJointGuardedCommonTailTwoOfRightReceiver
    (state : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin) :
    ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin :=
  .inr (.inl state)

def profiledRawJointGuardedCommonTailTwoOfLeftOwner
    (state : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin) :
    ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin :=
  .inr (.inr state)

/-! ## The bare common root -/

/-- A local non-receive at the common root starts the strict-right owner. -/
noncomputable def profiledRawJointGuardedCommonTailInitialNoRecvOne
    (control : ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
    (input : In₁) : Out₁ × OneControl A strategy hwin initialBank :=
  let next := profiledRawJointGuardedCommonNoRecvOne A strategy hwin
    (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control)
    input
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin next.2))

/-- Strict-left mirror. -/
noncomputable def profiledRawJointGuardedCommonTailInitialNoRecvTwo
    (control : ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
    (input : In₂) : Out₂ × TwoControl A strategy hwin initialBank :=
  let next := profiledRawJointGuardedCommonNoRecvTwo A strategy hwin
    (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control)
    input
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin next.2))

/-- Process one's receive from a bare common root.  Its arguments are exactly
its stored local control, its own input, and the delivered partner input. -/
noncomputable def profiledRawJointGuardedCommonTailInitialRecvOne
    (control : ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × OneControl A strategy hwin initialBank :=
  let next := profiledRawJointGuardedInitialCommonStartOne A strategy hwin
    control (own, delivered)
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailOneOfCommon A strategy hwin next.2))

/-- Process-two receive mirror. -/
noncomputable def profiledRawJointGuardedCommonTailInitialRecvTwo
    (control : ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank :=
  let next := profiledRawJointGuardedInitialCommonStartTwo A strategy hwin
    control (delivered, own)
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailTwoOfCommon A strategy hwin next.2))

/-! ## Common and open strict steps -/

/-- A common-state non-receive starts or continues the strict-right owner. -/
noncomputable def profiledRawJointGuardedCommonTailCommonNoRecvOne
    (state : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (input : In₁) : Out₁ × OneControl A strategy hwin initialBank :=
  let next := profiledRawJointGuardedInitialCommonOneNoRecv A strategy hwin
    state input
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin next.2))

/-- Process-two mirror. -/
noncomputable def profiledRawJointGuardedCommonTailCommonNoRecvTwo
    (state : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (input : In₂) : Out₂ × TwoControl A strategy hwin initialBank :=
  let next := profiledRawJointGuardedInitialCommonTwoNoRecv A strategy hwin
    state input
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin next.2))

/-- Repeated common receive at process one. -/
noncomputable def profiledRawJointGuardedCommonTailCommonRecvOne
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × OneControl A strategy hwin initialBank :=
  let next := profiledRawJointGuardedInitialCommonOneRecv A strategy hwin one
    two own delivered
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailOneOfCommon A strategy hwin next.2))

/-- Repeated common receive at process two. -/
noncomputable def profiledRawJointGuardedCommonTailCommonRecvTwo
    (two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank :=
  let next := profiledRawJointGuardedInitialCommonTwoRecv A strategy hwin two
    one own delivered
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailTwoOfCommon A strategy hwin next.2))

/-- A delivered right owner resolves process two's ambiguity. -/
noncomputable def profiledRawJointGuardedCommonTailResolveRightTwo
    (receiver : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank :=
  let ownerControl := profiledRawJointGuardedCommonRightOwnerFor A strategy
    hwin receiver.shadow owner
  let close := profiledRawJointGuardedCommonRightStageClose A strategy hwin
    receiver.shadow.source (ownerControl, receiver.shadow.strictReceiver)
      (own, delivered) .both
  let controller :=
    (receiver.shadow.source.1.1).memberController A false
  let next := profiledRawJointGuardedCommonTwoShadowRecvRightOwner A strategy
    hwin receiver.shadow owner own delivered
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailTwoOfRightReceiver A strategy hwin
      ⟨⟨⟨next.2.1, controller.step ownerControl delivered⟩,
        next.2, rfl⟩, close⟩))

/-- Left mirror. -/
noncomputable def profiledRawJointGuardedCommonTailResolveLeftOne
    (receiver : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × OneControl A strategy hwin initialBank :=
  let ownerControl := profiledRawJointGuardedCommonLeftOwnerFor A strategy
    hwin receiver.shadow owner
  let close := profiledRawJointGuardedCommonLeftStageClose A strategy hwin
    receiver.shadow.source (ownerControl, receiver.shadow.strictReceiver)
      (own, delivered) .both
  let controller :=
    (receiver.shadow.source.1.2).memberController A false
  let next := profiledRawJointGuardedCommonOneShadowRecvLeftOwner A strategy
    hwin receiver.shadow owner own delivered
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailOneOfLeftReceiver A strategy hwin
      ⟨⟨next.2, ⟨next.2.1, controller.step ownerControl delivered⟩,
        rfl⟩, close⟩))

/-- Continue a resolved strict-right receiver and replace, rather than
accumulate, the staged close by the one computed at this actual receive. -/
noncomputable def profiledRawJointGuardedCommonTailContinueRightTwo
    (receiver : ProfiledRawJointGuardedCommonTailRightReceiver A strategy
      hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank :=
  let ownerControl := profiledRawJointGuardedCommonRightStrictOwnerFor A
    strategy hwin receiver.strict.receiver owner
  let close := profiledRawJointGuardedCommonRightStageClose A strategy hwin
    receiver.strict.receiver.1 (ownerControl, receiver.strict.receiver.2.1)
      (own, delivered) .both
  let controller :=
    (receiver.strict.receiver.1.1.1).memberController A false
  let next := profiledRawJointGuardedCommonRightStrictReceiverRecvOwner A
    strategy hwin receiver.strict.receiver owner own delivered
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailTwoOfRightReceiver A strategy hwin
      ⟨⟨⟨next.2.1, controller.step ownerControl delivered⟩,
        next.2, rfl⟩, close⟩))

/-- Resolved strict-left mirror. -/
noncomputable def profiledRawJointGuardedCommonTailContinueLeftOne
    (receiver : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × OneControl A strategy hwin initialBank :=
  let ownerControl := profiledRawJointGuardedCommonLeftStrictOwnerFor A
    strategy hwin receiver.strict.receiver owner
  let close := profiledRawJointGuardedCommonLeftStageClose A strategy hwin
    receiver.strict.receiver.1 (ownerControl, receiver.strict.receiver.2.1)
      (own, delivered) .both
  let controller :=
    (receiver.strict.receiver.1.1.2).memberController A false
  let next := profiledRawJointGuardedCommonLeftStrictReceiverRecvOwner A
    strategy hwin receiver.strict.receiver owner own delivered
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailOneOfLeftReceiver A strategy hwin
      ⟨⟨next.2, ⟨next.2.1, controller.step ownerControl delivered⟩,
        rfl⟩, close⟩))

/-- Advance a resolved guarded strict-right receiver from its retained owner
when the delivered partner is itself only an ambiguity receiver. -/
noncomputable def profiledRawJointGuardedCommonTailSelfContinueRightTwo
    (receiver : ProfiledRawJointGuardedCommonTailRightReceiver A strategy
      hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank :=
  profiledRawJointGuardedCommonTailContinueRightTwo A strategy hwin initialBank
    receiver receiver.strict.owner own delivered

/-- Self-powered strict-left mirror. -/
noncomputable def profiledRawJointGuardedCommonTailSelfContinueLeftOne
    (receiver : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × OneControl A strategy hwin initialBank :=
  profiledRawJointGuardedCommonTailContinueLeftOne A strategy hwin initialBank
    receiver receiver.strict.owner own delivered

/-- Blind strict-right owner continuation. -/
noncomputable def profiledRawJointGuardedCommonTailRightOwnerNoRecvOne
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (input : In₁) : Out₁ × OneControl A strategy hwin initialBank :=
  let next := profiledRawJointGuardedCommonRightOwnerNoRecv A strategy hwin
    owner input
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin next.2))

/-- Blind strict-left owner continuation. -/
noncomputable def profiledRawJointGuardedCommonTailLeftOwnerNoRecvTwo
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (input : In₂) : Out₂ × TwoControl A strategy hwin initialBank :=
  let next := profiledRawJointGuardedCommonLeftOwnerNoRecv A strategy hwin
    owner input
  (next.1, .exceptional
    (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin next.2))

/-! ## Proof-side synchronization equations -/

/-- Two local receives from equal bare controls execute the exact common
start pair. -/
theorem profiledRawJointGuardedCommonTailInitialRecv_outputs
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonTailInitialRecvOne A strategy hwin
        initialBank control input.1 input.2).1,
      (profiledRawJointGuardedCommonTailInitialRecvTwo A strategy hwin
        initialBank control input.2 input.1).1) =
      profiledRawJointGuardedCommonPairBothOutput A strategy hwin
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          control) input := by
  exact profiledRawJointGuardedInitialCommonStart_outputs A strategy hwin
    control input

/-- At a strict-right root the two independently chosen local maps are the
two projections of one guarded right record. -/
theorem profiledRawJointGuardedCommonTailInitialStrictRight_outputs
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonTailInitialNoRecvOne A strategy hwin
        initialBank control input.1).1,
      (profiledRawJointGuardedCommonTailInitialRecvTwo A strategy hwin
        initialBank control input.2 input.1).1) =
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin control
      ((pair.rightRootRecord A strategy hwin input).2.2,
        pairedRightInformedForRow .both
          (pair.rightRootRecord A strategy hwin input).2.1.physical) := by
  exact profiledRawJointGuardedCommon_strictRight_root_pair A strategy hwin
    (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control)
    (profiledRawJointGuardedInitialCommonControlSuccessor A strategy hwin
      control input).1 input

/-- Strict-left mirror. -/
theorem profiledRawJointGuardedCommonTailInitialStrictLeft_outputs
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonTailInitialRecvOne A strategy hwin
        initialBank control input.1 input.2).1,
      (profiledRawJointGuardedCommonTailInitialNoRecvTwo A strategy hwin
        initialBank control input.2).1) =
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin control
      (pairedLeftInformedForRow .both
          (pair.leftRootRecord A strategy hwin input).2.1.physical,
        (pair.leftRootRecord A strategy hwin input).2.2) := by
  exact profiledRawJointGuardedCommon_strictLeft_root_pair A strategy hwin
    (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control)
    (profiledRawJointGuardedInitialCommonControlSuccessor A strategy hwin
      control input).1 input

end

end DetParityAutomaton

end DistributedSynthesis
