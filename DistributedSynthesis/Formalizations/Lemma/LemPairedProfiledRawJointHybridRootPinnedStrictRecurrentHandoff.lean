/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedStrictSwitchMaps

/-!
# Dependent recurrent handoff on complete guarded children

This lifts the fixed-first executable handoff to the complete guarded child
index expected by the leader-free carrier.  Every output of a strict switch
is indexed by the exact false/one-sided key stored in the newly staged macro.
The outer first-input pair is preserved.

The generic carrier is total and can syntactically pair controls from
different first-input indices.  Only the two continuing-receiver cases need
to inspect that equality.  When the indices agree, the genuinely delivered
owner is used.  The mismatch branch restarts the receiver's own source and is
outside the synchronized invariant.  No branch inspects a graph or leader.
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

/-! ## Owner steps preserve the complete child -/

noncomputable def profiledRawJointHybridRootPinnedStrictStepRightOwner
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (owner : ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin
      child)
    (input : In₁) :
    Out₁ ×
      ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin child := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch owner
  · let bank :=
      profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first
    let next :=
      stepProfiledRawJointHybridInitialRootPinnedPersistentRightOwner A
        strategy hwin first bank owner.1 input
    refine (next.1, ⟨next.2, ?_⟩)
    simpa [next] using owner.2

noncomputable def profiledRawJointHybridRootPinnedStrictStepLeftOwner
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (owner : ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin
      child)
    (input : In₂) :
    Out₂ ×
      ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin child := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch owner
  · let bank :=
      profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first
    let next :=
      stepProfiledRawJointHybridInitialRootPinnedPersistentLeftOwner A strategy
        hwin first bank owner.1 input
    refine (next.1, ⟨next.2, ?_⟩)
    simpa [next] using owner.2

/-! ## Strict receiver-to-owner switches -/

noncomputable def profiledRawJointHybridRootPinnedStrictStartRightOwner
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin child)
    (input : In₁) :
    Out₁ × (Σ next : ProfiledRawJointHybridRootPinnedChildCode A
      strategy hwin,
      ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin next) := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch receiver
  · let bank :=
      profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first
    let next :=
      profiledRawJointHybridInitialRootPinnedPersistentStartRightOwner A
        strategy hwin first bank receiver.1 input
    let nextChild := next.2.1.child A strategy hwin first
    refine (next.1, ⟨nextChild, ?_⟩)
    exact ⟨next.2, rfl⟩

noncomputable def profiledRawJointHybridRootPinnedStrictStartLeftOwner
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin child)
    (input : In₂) :
    Out₂ × (Σ next : ProfiledRawJointHybridRootPinnedChildCode A
      strategy hwin,
      ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin next) := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch receiver
  · let bank :=
      profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first
    let next :=
      profiledRawJointHybridInitialRootPinnedPersistentStartLeftOwner A
        strategy hwin first bank receiver.1 input
    let nextChild := next.2.1.child A strategy hwin first
    refine (next.1, ⟨nextChild, ?_⟩)
    exact ⟨next.2, rfl⟩

/-! ## Strict receiver-to-receiver switches -/

noncomputable def profiledRawJointHybridRootPinnedStrictStartLeftReceiver
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin child)
    (move : In₁ × In₂) :
    Out₁ × (Σ next : ProfiledRawJointHybridRootPinnedChildCode A
      strategy hwin,
      ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin
        next) := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch receiver
  · let bank :=
      profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first
    let next :=
      profiledRawJointHybridInitialRootPinnedPersistentStartLeftReceiver A
        strategy hwin first bank receiver.1 move
    let nextChild := next.2.1.child A strategy hwin first
    refine (next.1, ⟨nextChild, ?_⟩)
    exact ⟨next.2, rfl⟩

noncomputable def profiledRawJointHybridRootPinnedStrictStartRightReceiver
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin child)
    (move : In₂ × In₁) :
    Out₂ × (Σ next : ProfiledRawJointHybridRootPinnedChildCode A
      strategy hwin,
      ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin
        next) := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch receiver
  · let bank :=
      profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
        strategy hwin first
    let next :=
      profiledRawJointHybridInitialRootPinnedPersistentStartRightReceiver A
        strategy hwin first bank receiver.1 move
    let nextChild := next.2.1.child A strategy hwin first
    refine (next.1, ⟨nextChild, ?_⟩)
    exact ⟨next.2, rfl⟩

/-! ## Equality-sensitive matched continuations -/

noncomputable def profiledRawJointHybridRootPinnedStrictContinueRightReceiver
    (receiverChild rightChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver : ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy
      hwin receiverChild)
    (owner : ProfiledRawJointHybridRootPinnedStrictRightOwner A strategy hwin
      rightChild)
    (move : In₂ × In₁) :
    Out₂ × (Σ next : ProfiledRawJointHybridRootPinnedChildCode A
      strategy hwin,
      ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin
        next) := by
  classical
  rcases receiverChild with ⟨receiverFirst, receiverCommon | receiverKey⟩
  · exact nomatch receiver
  · rcases rightChild with ⟨rightFirst, rightCommon | rightKey⟩
    · exact nomatch owner
    · by_cases hfirst : receiverFirst = rightFirst
      · subst rightFirst
        let bank :=
          profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
            strategy hwin receiverFirst
        let next :=
          continueProfiledRawJointHybridInitialRootPinnedPersistentRightReceiver
            A strategy hwin receiverFirst bank receiver.1 owner.1 move
        refine (next.1, ⟨⟨receiverFirst, .inr receiverKey⟩, ?_⟩)
        refine ⟨next.2, ?_⟩
        simpa [next] using receiver.2
      · let bank :=
          profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
            strategy hwin receiverFirst
        let fallback :=
          initialProfiledRawJointHybridInitialRootPinnedPersistentRightOwner A
            strategy hwin receiverFirst bank receiver.1.1
        let next :=
          continueProfiledRawJointHybridInitialRootPinnedPersistentRightReceiver
            A strategy hwin receiverFirst bank receiver.1 fallback move
        refine (next.1, ⟨⟨receiverFirst, .inr receiverKey⟩, ?_⟩)
        refine ⟨next.2, ?_⟩
        simpa [next] using receiver.2

noncomputable def profiledRawJointHybridRootPinnedStrictContinueLeftReceiver
    (receiverChild leftChild :
      ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver : ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy
      hwin receiverChild)
    (owner : ProfiledRawJointHybridRootPinnedStrictLeftOwner A strategy hwin
      leftChild)
    (move : In₁ × In₂) :
    Out₁ × (Σ next : ProfiledRawJointHybridRootPinnedChildCode A
      strategy hwin,
      ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin
        next) := by
  classical
  rcases receiverChild with ⟨receiverFirst, receiverCommon | receiverKey⟩
  · exact nomatch receiver
  · rcases leftChild with ⟨leftFirst, leftCommon | leftKey⟩
    · exact nomatch owner
    · by_cases hfirst : receiverFirst = leftFirst
      · subst leftFirst
        let bank :=
          profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
            strategy hwin receiverFirst
        let next :=
          continueProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiver
            A strategy hwin receiverFirst bank receiver.1 owner.1 move
        refine (next.1, ⟨⟨receiverFirst, .inr receiverKey⟩, ?_⟩)
        refine ⟨next.2, ?_⟩
        simpa [next] using receiver.2
      · let bank :=
          profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
            strategy hwin receiverFirst
        let fallback :=
          initialProfiledRawJointHybridInitialRootPinnedPersistentLeftOwner A
            strategy hwin receiverFirst bank receiver.1.1
        let next :=
          continueProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiver
            A strategy hwin receiverFirst bank receiver.1 fallback move
        refine (next.1, ⟨⟨receiverFirst, .inr receiverKey⟩, ?_⟩)
        refine ⟨next.2, ?_⟩
        simpa [next] using receiver.2

/-! ## The strict pair test: both local restarts choose one complete child -/

/-- At a right-to-left switch, process one's new left receiver and process
two's new left owner are indexed by literally the same complete guarded child. -/
theorem profiledRawJointHybridRootPinnedStrictStartLeft_commonChild
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin child)
    (move : In₁ × In₂) :
    (profiledRawJointHybridRootPinnedStrictStartLeftReceiver A strategy hwin
      child receiver move).2.1 =
      (profiledRawJointHybridRootPinnedStrictStartLeftOwner A strategy hwin
        child receiver move.2).2.1 := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch receiver
  · change
      ((profiledRawJointHybridInitialRootPinnedPersistentStartLeftReceiver A
        strategy hwin first
          (profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
            strategy hwin first)
          receiver.1 move).2.1.child A strategy hwin first) =
      ((profiledRawJointHybridInitialRootPinnedPersistentStartLeftOwner A
        strategy hwin first
          (profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
            strategy hwin first)
          receiver.1 move.2).2.1.child A strategy hwin first)
    exact congrArg
      (fun source ↦ source.child A strategy hwin first)
      (profiledRawJointHybridInitialRootPinnedPersistentStartLeft_commonSource
        A strategy hwin first
        (profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
          strategy hwin first)
        receiver.1 move)

/-- Left-to-right mirror of the complete-child pair test. -/
theorem profiledRawJointHybridRootPinnedStrictStartRight_commonChild
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin child)
    (move : In₂ × In₁) :
    (profiledRawJointHybridRootPinnedStrictStartRightOwner A strategy hwin
      child receiver move.2).2.1 =
      (profiledRawJointHybridRootPinnedStrictStartRightReceiver A strategy hwin
        child receiver move).2.1 := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch receiver
  · change
      ((profiledRawJointHybridInitialRootPinnedPersistentStartRightOwner A
        strategy hwin first
          (profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
            strategy hwin first)
          receiver.1 move.2).2.1.child A strategy hwin first) =
      ((profiledRawJointHybridInitialRootPinnedPersistentStartRightReceiver A
        strategy hwin first
          (profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
            strategy hwin first)
          receiver.1 move).2.1.child A strategy hwin first)
    exact congrArg
      (fun source ↦ source.child A strategy hwin first)
      (profiledRawJointHybridInitialRootPinnedPersistentStartRight_commonSource
        A strategy hwin first
        (profiledRawJointHybridInitialRootPinnedPersistentControllerBank A
          strategy hwin first)
        receiver.1 move)

/-! ## Outer policy index preservation -/

@[simp] theorem
    profiledRawJointHybridRootPinnedStrictStartRightOwner_first
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin child)
    (input : In₁) :
    ((profiledRawJointHybridRootPinnedStrictStartRightOwner A strategy hwin
      child receiver input).2.1).1 = child.1 := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch receiver
  · rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedStrictStartLeftOwner_first
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin child)
    (input : In₂) :
    ((profiledRawJointHybridRootPinnedStrictStartLeftOwner A strategy hwin
      child receiver input).2.1).1 = child.1 := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch receiver
  · rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedStrictStartLeftReceiver_first
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictRightReceiver A strategy hwin child)
    (move : In₁ × In₂) :
    ((profiledRawJointHybridRootPinnedStrictStartLeftReceiver A strategy hwin
      child receiver move).2.1).1 = child.1 := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch receiver
  · rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedStrictStartRightReceiver_first
    (child : ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (receiver :
      ProfiledRawJointHybridRootPinnedStrictLeftReceiver A strategy hwin child)
    (move : In₂ × In₁) :
    ((profiledRawJointHybridRootPinnedStrictStartRightReceiver A strategy hwin
      child receiver move).2.1).1 = child.1 := by
  classical
  rcases child with ⟨first, common | key⟩
  · exact nomatch receiver
  · rfl

end

end DetParityAutomaton

end DistributedSynthesis
