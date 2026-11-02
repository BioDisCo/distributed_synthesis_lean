/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailHandoff

/-!
# Self-powered recurrent receivers below a guarded-common handoff

A checked guarded close installs an ordinary recurrent owner and receiver at
one combined child key.  On a simultaneous round the receiving process cannot
assume that the matching owner is delivered again: the delivered local control
may itself be a receiver.  The finite wrappers in this file therefore retain
the matching owner control beside the receiver.

The owner field is dependent on the receiver's literal macro, not merely on
its combined key.  Repeated receives consequently execute the genuine
owner/receiver branch without a source-mismatch fallback.  A later non-receive
switches to the opposite owner, while delivery of an ordinary equal-key owner
drops the wrapper back into the ordinary recurrent receiver alphabet.

Every operation is local.  Its arguments are stored finite controls and the
current own/delivered inputs; no graph, orientation, hierarchy side, leader
bit, semantic world, or history is supplied at runtime.
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

private abbrev CombinedKey :=
  ProfiledRawJointGuardedHybridCombinedChildCode A strategy hwin initialBank

private abbrev CombinedSource (key : CombinedKey A strategy hwin initialBank) :=
  profiledRawJointGuardedHybridCombinedChildSource A strategy hwin initialBank
    key

private abbrev CombinedPolicy (key : CombinedKey A strategy hwin initialBank) :=
  profiledRawJointGuardedHybridCombinedChildPolicy A strategy hwin initialBank
    key

private abbrev CombinedBank (key : CombinedKey A strategy hwin initialBank) :=
  profiledRawJointGuardedHybridCombinedControllerBank A strategy hwin
    initialBank key

private abbrev LeftReceiver (key : CombinedKey A strategy hwin initialBank) :=
  ProfiledRawJointGuardedHybridCombinedLeftReceiver A strategy hwin initialBank
    key

private abbrev RightReceiver (key : CombinedKey A strategy hwin initialBank) :=
  ProfiledRawJointGuardedHybridCombinedRightReceiver A strategy hwin
    initialBank key

private abbrev LeftOwner (key : CombinedKey A strategy hwin initialBank) :=
  ProfiledRawJointGuardedHybridCombinedLeftOwner A strategy hwin initialBank
    key

private abbrev RightOwner (key : CombinedKey A strategy hwin initialBank) :=
  ProfiledRawJointGuardedHybridCombinedRightOwner A strategy hwin initialBank
    key

private abbrev InitialOne :=
  ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin

private abbrev InitialTwo :=
  ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin

private abbrev ExceptionalOne :=
  ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin

private abbrev ExceptionalTwo :=
  ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin

private abbrev OneControl :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (InitialOne A strategy hwin) (ExceptionalOne A strategy hwin)

private abbrev TwoControl :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (InitialTwo A strategy hwin) (ExceptionalTwo A strategy hwin)

/-! ## Finite dependent wrappers -/

/-- A combined-key left receiver retaining the owner control for its exact
left macro.  The dependent field rules out both key and macro mismatch. -/
structure ProfiledRawJointGuardedCommonTailPoweredLeftReceiver where
  key : CombinedKey A strategy hwin initialBank
  receiver : LeftReceiver A strategy hwin initialBank key
  owner : (((CombinedBank A strategy hwin initialBank key).left
    receiver.1).1).Control

/-- Right-oriented mirror. -/
structure ProfiledRawJointGuardedCommonTailPoweredRightReceiver where
  key : CombinedKey A strategy hwin initialBank
  receiver : RightReceiver A strategy hwin initialBank key
  owner : (((CombinedBank A strategy hwin initialBank key).right
    receiver.1).1).Control

noncomputable instance
    profiledRawJointGuardedCommonTailPoweredLeftReceiverFintype :
    Fintype (ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank) := by
  classical
  let Rep := Σ key : CombinedKey A strategy hwin initialBank,
    Σ receiver : LeftReceiver A strategy hwin initialBank key,
      (((CombinedBank A strategy hwin initialBank key).left receiver.1).1).Control
  let equiv :
      ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy hwin
          initialBank ≃ Rep := {
    toFun := fun state ↦ ⟨state.key, state.receiver, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by
      intro state
      rcases state with ⟨key, receiver, owner⟩
      rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointGuardedCommonTailPoweredRightReceiverFintype :
    Fintype (ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank) := by
  classical
  let Rep := Σ key : CombinedKey A strategy hwin initialBank,
    Σ receiver : RightReceiver A strategy hwin initialBank key,
      (((CombinedBank A strategy hwin initialBank key).right receiver.1).1).Control
  let equiv :
      ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy hwin
          initialBank ≃ Rep := {
    toFun := fun state ↦ ⟨state.key, state.receiver, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by
      intro state
      rcases state with ⟨key, receiver, owner⟩
      rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-! ## Entry from a checked guarded close -/

/-- Execute the receive following a staged guarded right close and retain the
matching left owner after its simultaneous local advance. -/
noncomputable def
    profiledRawJointGuardedCommonRightStagedStartPoweredLeftReceiver
    (close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank :=
  let key := profiledRawJointGuardedCommonRightStagedCombinedKey A strategy
    hwin initialBank close
  let source := CombinedSource A strategy hwin initialBank key
  let policy := CombinedPolicy A strategy hwin initialBank key
  let bank := CombinedBank A strategy hwin initialBank key
  let receiver :=
    profiledRawJointGuardedCommonRightStagedInitialLeftReceiver A strategy hwin
      initialBank close
  let owner :=
    profiledRawJointGuardedCommonRightStagedInitialLeftOwner A strategy hwin
      initialBank close
  let receiverNext := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
    source policy bank receiver owner (own, delivered)
  let ownerNext := stepProfiledRawJointUnitLeftPolicyOwner A strategy source
    policy bank owner delivered
  (receiverNext.1, ⟨key, receiverNext.2, ownerNext.2.2⟩)

/-- Staged left-close mirror. -/
noncomputable def
    profiledRawJointGuardedCommonLeftStagedStartPoweredRightReceiver
    (close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank :=
  let key := profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy hwin
    initialBank close
  let source := CombinedSource A strategy hwin initialBank key
  let policy := CombinedPolicy A strategy hwin initialBank key
  let bank := CombinedBank A strategy hwin initialBank key
  let receiver :=
    profiledRawJointGuardedCommonLeftStagedInitialRightReceiver A strategy hwin
      initialBank close
  let owner :=
    profiledRawJointGuardedCommonLeftStagedInitialRightOwner A strategy hwin
      initialBank close
  let receiverNext := continueProfiledRawJointUnitRightPolicyReceiver A
    strategy source policy bank receiver owner (own, delivered)
  let ownerNext := stepProfiledRawJointUnitRightPolicyOwner A strategy source
    policy bank owner delivered
  (receiverNext.1, ⟨key, receiverNext.2, ownerNext.2.2⟩)

@[simp] theorem
    profiledRawJointGuardedCommonRightStagedStartPoweredLeftReceiver_key
    (close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin)
    (own : In₁) (delivered : In₂) :
    (profiledRawJointGuardedCommonRightStagedStartPoweredLeftReceiver A
      strategy hwin initialBank close own delivered).2.key =
      profiledRawJointGuardedCommonRightStagedCombinedKey A strategy hwin
        initialBank close :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonLeftStagedStartPoweredRightReceiver_key
    (close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin)
    (own : In₂) (delivered : In₁) :
    (profiledRawJointGuardedCommonLeftStagedStartPoweredRightReceiver A
      strategy hwin initialBank close own delivered).2.key =
      profiledRawJointGuardedCommonLeftStagedCombinedKey A strategy hwin
        initialBank close :=
  rfl

/-- The powered constructor emits exactly the already verified staged receive
output; retaining the matching owner does not alter the physical action. -/
@[simp] theorem
    profiledRawJointGuardedCommonRightStagedStartPoweredLeftReceiver_output
    (close : ProfiledRawJointGuardedCommonRightStagedClose A strategy hwin)
    (own : In₁) (delivered : In₂) :
    (profiledRawJointGuardedCommonRightStagedStartPoweredLeftReceiver A
      strategy hwin initialBank close own delivered).1 =
      (profiledRawJointGuardedCommonRightStagedStartLeftReceiver A strategy
        hwin initialBank close own delivered).1 :=
  rfl

/-- Staged-left output mirror. -/
@[simp] theorem
    profiledRawJointGuardedCommonLeftStagedStartPoweredRightReceiver_output
    (close : ProfiledRawJointGuardedCommonLeftStagedClose A strategy hwin)
    (own : In₂) (delivered : In₁) :
    (profiledRawJointGuardedCommonLeftStagedStartPoweredRightReceiver A
      strategy hwin initialBank close own delivered).1 =
      (profiledRawJointGuardedCommonLeftStagedStartRightReceiver A strategy
        hwin initialBank close own delivered).1 :=
  rfl

/-! ## Self-powered simultaneous receives -/

/-- Advance a left receiver and its structurally matching retained owner.
Only the receiver's own input and the delivered partner input are needed. -/
noncomputable def
    advanceProfiledRawJointGuardedCommonTailPoweredLeftReceiver
    (state : ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank :=
  let source := CombinedSource A strategy hwin initialBank state.key
  let policy := CombinedPolicy A strategy hwin initialBank state.key
  let bank := CombinedBank A strategy hwin initialBank state.key
  let owner : LeftOwner A strategy hwin initialBank state.key :=
    ⟨state.receiver.1, state.owner⟩
  let receiverNext := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
    source policy bank state.receiver owner (own, delivered)
  let ownerNext := stepProfiledRawJointUnitLeftPolicyOwner A strategy source
    policy bank owner delivered
  (receiverNext.1, ⟨state.key, receiverNext.2, ownerNext.2.2⟩)

/-- Right mirror. -/
noncomputable def
    advanceProfiledRawJointGuardedCommonTailPoweredRightReceiver
    (state : ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank :=
  let source := CombinedSource A strategy hwin initialBank state.key
  let policy := CombinedPolicy A strategy hwin initialBank state.key
  let bank := CombinedBank A strategy hwin initialBank state.key
  let owner : RightOwner A strategy hwin initialBank state.key :=
    ⟨state.receiver.1, state.owner⟩
  let receiverNext := continueProfiledRawJointUnitRightPolicyReceiver A
    strategy source policy bank state.receiver owner (own, delivered)
  let ownerNext := stepProfiledRawJointUnitRightPolicyOwner A strategy source
    policy bank owner delivered
  (receiverNext.1, ⟨state.key, receiverNext.2, ownerNext.2.2⟩)

@[simp] theorem
    advanceProfiledRawJointGuardedCommonTailPoweredLeftReceiver_key
    (state : ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank)
    (own : In₁) (delivered : In₂) :
    (advanceProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank state own delivered).2.key = state.key :=
  rfl

@[simp] theorem
    advanceProfiledRawJointGuardedCommonTailPoweredRightReceiver_key
    (state : ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank)
    (own : In₂) (delivered : In₁) :
    (advanceProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank state own delivered).2.key = state.key :=
  rfl

/-- Exact receiver coordinate of a self-powered left receive. -/
@[simp] theorem
    advanceProfiledRawJointGuardedCommonTailPoweredLeftReceiver_receiver
    (state : ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank)
    (own : In₁) (delivered : In₂) :
    (advanceProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank state own delivered).2.receiver =
      (continueProfiledRawJointUnitLeftPolicyReceiver A strategy
        (CombinedSource A strategy hwin initialBank state.key)
        (CombinedPolicy A strategy hwin initialBank state.key)
        (CombinedBank A strategy hwin initialBank state.key) state.receiver
        ⟨state.receiver.1, state.owner⟩ (own, delivered)).2 :=
  rfl

/-- The retained left owner is advanced on the same delivered input. -/
@[simp] theorem
    advanceProfiledRawJointGuardedCommonTailPoweredLeftReceiver_owner
    (state : ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank)
    (own : In₁) (delivered : In₂) :
    (advanceProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank state own delivered).2.owner =
      (stepProfiledRawJointUnitLeftPolicyOwner A strategy
        (CombinedSource A strategy hwin initialBank state.key)
        (CombinedPolicy A strategy hwin initialBank state.key)
        (CombinedBank A strategy hwin initialBank state.key)
        ⟨state.receiver.1, state.owner⟩ delivered).2.2 :=
  rfl

/-- Exact receiver coordinate of the right mirror. -/
@[simp] theorem
    advanceProfiledRawJointGuardedCommonTailPoweredRightReceiver_receiver
    (state : ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank)
    (own : In₂) (delivered : In₁) :
    (advanceProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank state own delivered).2.receiver =
      (continueProfiledRawJointUnitRightPolicyReceiver A strategy
        (CombinedSource A strategy hwin initialBank state.key)
        (CombinedPolicy A strategy hwin initialBank state.key)
        (CombinedBank A strategy hwin initialBank state.key) state.receiver
        ⟨state.receiver.1, state.owner⟩ (own, delivered)).2 :=
  rfl

/-- Right retained-owner coordinate. -/
@[simp] theorem
    advanceProfiledRawJointGuardedCommonTailPoweredRightReceiver_owner
    (state : ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank)
    (own : In₂) (delivered : In₁) :
    (advanceProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank state own delivered).2.owner =
      (stepProfiledRawJointUnitRightPolicyOwner A strategy
        (CombinedSource A strategy hwin initialBank state.key)
        (CombinedPolicy A strategy hwin initialBank state.key)
        (CombinedBank A strategy hwin initialBank state.key)
        ⟨state.receiver.1, state.owner⟩ delivered).2.2 :=
  rfl

/-! ## Local exits -/

/-- A left receiver that observes no receive installs the opposite right
owner at the same combined key. -/
noncomputable def
    profiledRawJointGuardedCommonTailPoweredLeftReceiverNoRecv
    (state : ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank)
    (input : In₁) : Out₁ × OneControl A strategy hwin initialBank :=
  let next := profiledRawJointUnitPolicyStartRightOwner A strategy
    (CombinedSource A strategy hwin initialBank state.key)
    (CombinedPolicy A strategy hwin initialBank state.key)
    (CombinedBank A strategy hwin initialBank state.key) state.receiver input
  (next.1, .rightOwner state.key next.2)

/-- Right receiver no-receive mirror. -/
noncomputable def
    profiledRawJointGuardedCommonTailPoweredRightReceiverNoRecv
    (state : ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank)
    (input : In₂) : Out₂ × TwoControl A strategy hwin initialBank :=
  let next := profiledRawJointUnitPolicyStartLeftOwner A strategy
    (CombinedSource A strategy hwin initialBank state.key)
    (CombinedPolicy A strategy hwin initialBank state.key)
    (CombinedBank A strategy hwin initialBank state.key) state.receiver input
  (next.1, .leftOwner state.key next.2)

@[simp] theorem
    profiledRawJointGuardedCommonTailPoweredLeftReceiverNoRecv_eq
    (state : ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank)
    (input : In₁) :
    profiledRawJointGuardedCommonTailPoweredLeftReceiverNoRecv A strategy hwin
        initialBank state input =
      let next := profiledRawJointUnitPolicyStartRightOwner A strategy
        (CombinedSource A strategy hwin initialBank state.key)
        (CombinedPolicy A strategy hwin initialBank state.key)
        (CombinedBank A strategy hwin initialBank state.key) state.receiver
          input
      (next.1, .rightOwner state.key next.2) :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonTailPoweredRightReceiverNoRecv_eq
    (state : ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank)
    (input : In₂) :
    profiledRawJointGuardedCommonTailPoweredRightReceiverNoRecv A strategy hwin
        initialBank state input =
      let next := profiledRawJointUnitPolicyStartLeftOwner A strategy
        (CombinedSource A strategy hwin initialBank state.key)
        (CombinedPolicy A strategy hwin initialBank state.key)
        (CombinedBank A strategy hwin initialBank state.key) state.receiver
          input
      (next.1, .leftOwner state.key next.2) :=
  rfl

/-! ## Drop to an ordinary equal-key recurrent receiver -/

/-- If an ordinary left owner with the same combined key is delivered, use it
for the current receive and drop the powered wrapper.  The equality is the
only key transport performed by this function. -/
noncomputable def
    profiledRawJointGuardedCommonTailPoweredLeftReceiverRecvOwner
    (state : ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank)
    (ownerKey : CombinedKey A strategy hwin initialBank)
    (owner : LeftOwner A strategy hwin initialBank ownerKey)
    (key_eq : ownerKey = state.key)
    (own : In₁) (delivered : In₂) :
    Out₁ × OneControl A strategy hwin initialBank :=
  let ownerAtKey : LeftOwner A strategy hwin initialBank state.key :=
    key_eq ▸ owner
  let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
    (CombinedSource A strategy hwin initialBank state.key)
    (CombinedPolicy A strategy hwin initialBank state.key)
    (CombinedBank A strategy hwin initialBank state.key) state.receiver
      ownerAtKey (own, delivered)
  (next.1, .leftReceiver state.key next.2)

/-- Right equal-key owner mirror. -/
noncomputable def
    profiledRawJointGuardedCommonTailPoweredRightReceiverRecvOwner
    (state : ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank)
    (ownerKey : CombinedKey A strategy hwin initialBank)
    (owner : RightOwner A strategy hwin initialBank ownerKey)
    (key_eq : ownerKey = state.key)
    (own : In₂) (delivered : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank :=
  let ownerAtKey : RightOwner A strategy hwin initialBank state.key :=
    key_eq ▸ owner
  let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
    (CombinedSource A strategy hwin initialBank state.key)
    (CombinedPolicy A strategy hwin initialBank state.key)
    (CombinedBank A strategy hwin initialBank state.key) state.receiver
      ownerAtKey (own, delivered)
  (next.1, .rightReceiver state.key next.2)

@[simp] theorem
    profiledRawJointGuardedCommonTailPoweredLeftReceiverRecvOwner_sameKey
    (state : ProfiledRawJointGuardedCommonTailPoweredLeftReceiver A strategy
      hwin initialBank)
    (owner : LeftOwner A strategy hwin initialBank state.key)
    (own : In₁) (delivered : In₂) :
    profiledRawJointGuardedCommonTailPoweredLeftReceiverRecvOwner A strategy
        hwin initialBank state state.key owner rfl own delivered =
      let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
        (CombinedSource A strategy hwin initialBank state.key)
        (CombinedPolicy A strategy hwin initialBank state.key)
        (CombinedBank A strategy hwin initialBank state.key) state.receiver
          owner (own, delivered)
      (next.1, .leftReceiver state.key next.2) :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonTailPoweredRightReceiverRecvOwner_sameKey
    (state : ProfiledRawJointGuardedCommonTailPoweredRightReceiver A strategy
      hwin initialBank)
    (owner : RightOwner A strategy hwin initialBank state.key)
    (own : In₂) (delivered : In₁) :
    profiledRawJointGuardedCommonTailPoweredRightReceiverRecvOwner A strategy
        hwin initialBank state state.key owner rfl own delivered =
      let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
        (CombinedSource A strategy hwin initialBank state.key)
        (CombinedPolicy A strategy hwin initialBank state.key)
        (CombinedBank A strategy hwin initialBank state.key) state.receiver
          owner (own, delivered)
      (next.1, .rightReceiver state.key next.2) :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
