/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLiveCanonicalPhysicalCutPriority

/-!
# Anchor-free physical target-cut priorities

This file factors the physical half out of the canonical-cut adapter.  A cut
is indexed by the *actual live target root* supplied by its table witness.
The cuts themselves are arbitrary proof-side natural-number coordinates.
There is no fixed policy, canonical query, anchor, row choice, or equality
between roots belonging to independently chosen policies.

Consequently the conclusion is exactly the local fact needed by every later
lineage construction: the minimum priority of the actual physical block is
the priority stored in the target live slot.  Any later coupling to a parent
annotation can be performed by a separate, explicit root equality.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev RightReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev RightSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
    hwin package

private abbrev LeftReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

private abbrev LeftSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedSenderState A strategy
    hwin package

/-! ## One arbitrary physical target cut -/

/-- Exact phase-live data at one arbitrary physical block, indexed by the
live target root produced by that block.

The index makes the orientation and selected slot available to clients
without adding a choice function.  In particular, this statement contains
no fixed-policy or canonical-query lineage premise. -/
inductive LiteralCombinedFreshPhaseLivePhysicalTargetCutAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (base : Nat)
    (cuts : Nat → Nat) (k : Nat) :
    ProfiledRawJointThreadRoot A → Prop where
  | right
      (receiver : RightReceiver A strategy hwin package)
      (sender : RightSender A strategy hwin package)
      (past : List (In₁ × In₂))
      (slot : ProfiledRawRightSlot A)
      (past_length :
        past.length = cuts (k + 1) - cuts k - 1)
      (segment :
        package.LiteralRightSeamTableRootPhysicalSegmentFrom A strategy hwin
          env (base + cuts (k + 1) - 1) (base + cuts k)
            past receiver sender)
      (entryState_eq :
        A.run (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
            env) (base + cuts k) =
          literalRightSeamSelectedTableEntryState A strategy hwin
            (package.literalRightSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1 .both)
      (target_live :
        (literalRightSeamSelectedTableTargetCode A strategy hwin
          (package.literalRightSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1
          (fun j ↦
            ((env (base + cuts k + j)).inputOne,
              (env (base + cuts k + j)).inputTwo))
          past.length .both).family.right () = some slot) :
      LiteralCombinedFreshPhaseLivePhysicalTargetCutAt package env base cuts k
        (.inl slot)
  | left
      (receiver : LeftReceiver A strategy hwin package)
      (sender : LeftSender A strategy hwin package)
      (past : List (In₂ × In₁))
      (slot : ProfiledRawLeftSlot A)
      (past_length :
        past.length = cuts (k + 1) - cuts k - 1)
      (segment :
        package.LiteralLeftSeamTableRootPhysicalSegmentFrom A strategy hwin
          env (base + cuts (k + 1) - 1) (base + cuts k)
            past receiver sender)
      (entryState_eq :
        A.run (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
            env) (base + cuts k) =
          literalLeftSeamSelectedTableEntryState A strategy hwin
            (package.literalLeftSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1 .both)
      (target_live :
        (literalLeftSeamSelectedTableTargetCode A strategy hwin
          (package.literalLeftSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1
          (fun j ↦
            ((env (base + cuts k + j)).inputTwo,
              (env (base + cuts k + j)).inputOne))
          past.length .both).family.left () = some slot) :
      LiteralCombinedFreshPhaseLivePhysicalTargetCutAt package env base cuts k
        (.inr slot)

namespace LiteralCombinedFreshPhaseLivePhysicalTargetCutAt

/-- The actual physical block minimum is exactly the priority of its live
target slot.  This is the anchor-free first half of the old canonical-cut
proof. -/
theorem blockMin_eq_targetPriority
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂} {base : Nat}
    {cuts : Nat → Nat} {k : Nat} {root : ProfiledRawJointThreadRoot A}
    (cut : LiteralCombinedFreshPhaseLivePhysicalTargetCutAt A strategy hwin
      package env base cuts k root) :
    cutBlockMin
        (fun n ↦ A.priority
          (A.run
            (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
              env) (base + n)))
        cuts k = profiledRawJointThreadRootPriority A root := by
  let word := literalCombinedFreshPhaseLiveActualWord A strategy hwin package
    env
  let semanticWord :=
    package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin env
  have hword : semanticWord = word := by
    exact package.literalCombinedFreshPhaseLiveRootSemanticWord_eq_actualTraceWord
      A strategy hwin env
  cases cut with
  | right receiver sender past slot hpast hsegment hentry hlive =>
      let state := literalRightSeamSelectedTableEntryState A strategy hwin
        (package.literalRightSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1 .both
      let block := phaseLiveOmegaSegment word (base + cuts k) past.length
      have hlength : block.length = cuts (k + 1) - cuts k - 1 := by
        simpa [block, phaseLiveOmegaSegment] using hpast
      have hslice :
          omegaPrefix (OmegaWord.drop word (base + cuts k)) block.length =
            block := by
        simpa [block, phaseLiveOmegaSegment] using
          (phaseLiveOmegaSegment_eq_omegaPrefix_drop word (base + cuts k)
            past.length).symm
      have hphysical :
          cutBlockMin
              (fun n ↦ A.priority (A.run word (base + n))) cuts k =
            A.priority (blockMinState A state block) := by
        exact cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word
          base cuts k state block (by simpa [word, state] using hentry)
            hlength hslice
      have htarget :=
        hsegment.targetPriority_eq A strategy hwin package env
          (base + cuts (k + 1) - 1) (base + cuts k) past slot hlive
      rw [package.literalCombinedFreshPhaseLiveRootSemanticWord_eq_actualTraceWord
        A strategy hwin env] at htarget
      calc
        _ = A.priority (blockMinState A state block) := hphysical
        _ = profiledRawJointThreadRootPriority A (.inl slot) := by
          simpa [state, block, semanticWord, word] using htarget.symm
  | left receiver sender past slot hpast hsegment hentry hlive =>
      let state := literalLeftSeamSelectedTableEntryState A strategy hwin
        (package.literalLeftSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1 .both
      let block := phaseLiveOmegaSegment word (base + cuts k) past.length
      have hlength : block.length = cuts (k + 1) - cuts k - 1 := by
        simpa [block, phaseLiveOmegaSegment] using hpast
      have hslice :
          omegaPrefix (OmegaWord.drop word (base + cuts k)) block.length =
            block := by
        simpa [block, phaseLiveOmegaSegment] using
          (phaseLiveOmegaSegment_eq_omegaPrefix_drop word (base + cuts k)
            past.length).symm
      have hphysical :
          cutBlockMin
              (fun n ↦ A.priority (A.run word (base + n))) cuts k =
            A.priority (blockMinState A state block) := by
        exact cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word
          base cuts k state block (by simpa [word, state] using hentry)
            hlength hslice
      have htarget :=
        hsegment.targetPriority_eq A strategy hwin package env
          (base + cuts (k + 1) - 1) (base + cuts k) past slot hlive
      rw [package.literalCombinedFreshPhaseLiveRootSemanticWord_eq_actualTraceWord
        A strategy hwin env] at htarget
      calc
        _ = A.priority (blockMinState A state block) := hphysical
        _ = profiledRawJointThreadRootPriority A (.inr slot) := by
          simpa [state, block, semanticWord, word] using htarget.symm

end LiteralCombinedFreshPhaseLivePhysicalTargetCutAt

/-! ## A family over one arbitrary cut sequence -/

/-- A target-root-indexed physical witness at every cut. -/
structure LiteralCombinedFreshPhaseLivePhysicalTargetCutFamily
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (base : Nat)
    (cuts : Nat → Nat) where
  rootAt : Nat → ProfiledRawJointThreadRoot A
  cutAt : ∀ k : Nat,
    LiteralCombinedFreshPhaseLivePhysicalTargetCutAt A strategy hwin package
      env base cuts k (rootAt k)

namespace LiteralCombinedFreshPhaseLivePhysicalTargetCutFamily

/-- Pointwise physical priority equality for an arbitrary target-cut
family. -/
theorem blockMin_eq_targetPriority
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂} {base : Nat}
    {cuts : Nat → Nat}
    (family : LiteralCombinedFreshPhaseLivePhysicalTargetCutFamily A strategy
      hwin package env base cuts) (k : Nat) :
    cutBlockMin
        (fun n ↦ A.priority
          (A.run
            (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
              env) (base + n)))
        cuts k =
      profiledRawJointThreadRootPriority A (family.rootAt k) :=
  (family.cutAt k).blockMin_eq_targetPriority A strategy hwin

end LiteralCombinedFreshPhaseLivePhysicalTargetCutFamily

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
