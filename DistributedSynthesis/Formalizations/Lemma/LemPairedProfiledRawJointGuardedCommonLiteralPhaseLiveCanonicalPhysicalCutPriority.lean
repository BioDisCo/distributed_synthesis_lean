/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLiveTablePhysicalSegment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossPriorityAcceptance

/-!
# Canonical physical-cut priorities of the phase-live table

The phase-live table invariant gives an exact physical segment ending at
every trace position.  The canonical acceptance layer, on the other hand,
indexes blocks by proof-side root-oriented close cuts.  This file is the
lossless adapter between those two descriptions.

For one canonical cut the model-specific construction owes only:

* the table segment starts at that cut and has the canonical open length;
* the actual DPA state at the cut is the selected table entry state; and
* the selected table's live target slot is the next root of the one fixed
  canonical policy thread.

The last item is deliberately a slot equality.  It neither equates an
emitting seam key with the freshly installed key nor identifies two
independently rationalized policies.  It is the weakest lineage fact needed
by parity.  From these data, equality of the actual block minimum with the
canonical query priority is unconditional.

All cuts, orientations, rows, receivers, and lineage witnesses below are
proof-side.  They are not inputs of either local transition.
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

/-! ## Fixed witnesses behind the existential segment invariant -/

/-- The fixed-start/fixed-prefix body of a represented right-table segment.
This is exactly the body hidden by the two existentials in
`LiteralRightSeamTableRootPhysicalSegmentAt`. -/
def LiteralRightSeamTableRootPhysicalSegmentFrom
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n start : Nat)
    (past : List (In₁ × In₂))
    (receiver : RightReceiver A strategy hwin package)
    (sender : RightSender A strategy hwin package) : Prop :=
  start + past.length = n ∧
    (∀ (j : Nat) (hj : j < past.length),
      past[j] = ((env (start + j)).inputOne,
        (env (start + j)).inputTwo)) ∧
    sender =
      ⟨receiver.1,
        finiteCrossAnchorSenderAtPrefix
          (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A
            strategy hwin
            (package.literalRightSeamInstalled A strategy hwin receiver.1))
          past⟩ ∧
    receiver.2.2.1 =
      finiteCrossAnchorReceiverAtPrefix
        (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A
          strategy hwin
          (package.literalRightSeamInstalled A strategy hwin receiver.1))
        receiver.2.2.1.1 past ∧
    ∀ (j : Nat) (hj : j < past.length),
      package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin
          env (start + j) =
        pairedLeftRecordForRow .both
          (literalRightSeamSelectedTablePhysicalPlay A strategy hwin
            (package.literalRightSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1
            (fun k ↦ ((env (start + k)).inputOne,
              (env (start + k)).inputTwo)) j)

/-- Fixed witness for the mirror table. -/
def LiteralLeftSeamTableRootPhysicalSegmentFrom
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n start : Nat)
    (past : List (In₂ × In₁))
    (receiver : LeftReceiver A strategy hwin package)
    (sender : LeftSender A strategy hwin package) : Prop :=
  start + past.length = n ∧
    (∀ (j : Nat) (hj : j < past.length),
      past[j] = ((env (start + j)).inputTwo,
        (env (start + j)).inputOne)) ∧
    sender =
      ⟨receiver.1,
        finiteCrossAnchorSenderAtPrefix
          (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A
            strategy hwin
            (package.literalLeftSeamInstalled A strategy hwin receiver.1))
          past⟩ ∧
    receiver.2.2.1 =
      finiteCrossAnchorReceiverAtPrefix
        (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A
          strategy hwin
          (package.literalLeftSeamInstalled A strategy hwin receiver.1))
        receiver.2.2.1.1 past ∧
    ∀ (j : Nat) (hj : j < past.length),
      package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin
          env (start + j) =
        pairedRightRecordForRow .both
          (literalLeftSeamSelectedTablePhysicalPlay A strategy hwin
            (package.literalLeftSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1
            (fun k ↦ ((env (start + k)).inputTwo,
              (env (start + k)).inputOne)) j)

theorem literalRightSeamTableRootPhysicalSegmentAt_iff_exists_from
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (receiver : RightReceiver A strategy hwin package)
    (sender : RightSender A strategy hwin package) :
    package.LiteralRightSeamTableRootPhysicalSegmentAt A strategy hwin env n
        receiver sender ↔
      ∃ start past,
        package.LiteralRightSeamTableRootPhysicalSegmentFrom A strategy hwin
          env n start past receiver sender := by
  rfl

theorem literalLeftSeamTableRootPhysicalSegmentAt_iff_exists_from
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (receiver : LeftReceiver A strategy hwin package)
    (sender : LeftSender A strategy hwin package) :
    package.LiteralLeftSeamTableRootPhysicalSegmentAt A strategy hwin env n
        receiver sender ↔
      ∃ start past,
        package.LiteralLeftSeamTableRootPhysicalSegmentFrom A strategy hwin
          env n start past receiver sender := by
  rfl

/-- `phaseLiveOmegaSegment` is the ordinary finite prefix of the dropped
word, stated once for use at every canonical cut. -/
theorem phaseLiveOmegaSegment_eq_omegaPrefix_drop
    {Letter : Type*} (word : Nat → Letter) (start length : Nat) :
    phaseLiveOmegaSegment word start length =
      omegaPrefix (OmegaWord.drop word start) length := by
  rfl

/-! ## Exact target priority for a fixed segment witness -/

/-- Any live right slot of the selected target has exactly the physical
minimum of this fixed actual segment. -/
theorem LiteralRightSeamTableRootPhysicalSegmentFrom.targetPriority_eq
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n start : Nat)
    (past : List (In₁ × In₂))
    {receiver : RightReceiver A strategy hwin package}
    {sender : RightSender A strategy hwin package}
    (hsegment :
      package.LiteralRightSeamTableRootPhysicalSegmentFrom A strategy hwin
        env n start past receiver sender)
    (slot : ProfiledRawRightSlot A)
    (hlive :
      (literalRightSeamSelectedTableTargetCode A strategy hwin
        (package.literalRightSeamInstalled A strategy hwin receiver.1)
        receiver.2.2.1.1
        (fun k ↦ ((env (start + k)).inputOne,
          (env (start + k)).inputTwo)) past.length .both).family.right () =
          some slot) :
    profiledRawJointThreadRootPriority A (.inl slot) =
      A.priority
        (blockMinState A
          (literalRightSeamSelectedTableEntryState A strategy hwin
            (package.literalRightSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1 .both)
          (phaseLiveOmegaSegment
            (package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy
              hwin env) start past.length)) := by
  rcases hsegment with
    ⟨_hend, _hinputs, _hsender, _hreceiver, hrecords⟩
  have hword :
      phaseLiveOmegaSegment
          (package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy
            hwin env) start past.length =
        omegaPrefix
          (fun j ↦ pairedLeftRecordForRow .both
            (literalRightSeamSelectedTablePhysicalPlay A strategy hwin
              (package.literalRightSeamInstalled A strategy hwin receiver.1)
              receiver.2.2.1.1
              (fun k ↦ ((env (start + k)).inputOne,
                (env (start + k)).inputTwo)) j))
          past.length := by
    apply List.ext_get
    · simp [phaseLiveOmegaSegment, omegaPrefix]
    · intro j hjLeft hjRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [phaseLiveOmegaSegment, omegaPrefix, List.getElem_ofFn]
      exact hrecords j (by simpa [phaseLiveOmegaSegment] using hjLeft)
  have hminimum :
      A.priority
          (blockMinState A
            (literalRightSeamSelectedTableEntryState A strategy hwin
              (package.literalRightSeamInstalled A strategy hwin receiver.1)
              receiver.2.2.1.1 .both)
            (phaseLiveOmegaSegment
              (package.literalCombinedFreshPhaseLiveRootSemanticWord A
                strategy hwin env) start past.length)) =
        literalRightSeamSelectedTableBlockPriority A strategy hwin
          (package.literalRightSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1
          (fun k ↦ ((env (start + k)).inputOne,
            (env (start + k)).inputTwo)) past.length .both := by
    rw [hword]
    cases hanchor : receiver.2.2.1.1
    · simp [literalRightSeamSelectedTableEntryState,
        literalRightSeamSelectedTableBlockPriority, hanchor,
        literalRightSeamSelectedTablePhysicalPlay_false,
        profiledRawJointTargetLeftPhysicalPrefixRecords, omegaPrefix]
      rfl
    · simp [literalRightSeamSelectedTableEntryState,
        literalRightSeamSelectedTableBlockPriority, hanchor,
        literalRightSeamSelectedTablePhysicalPlay_true,
        profiledRawJointGuardedFirstLeftPhysicalPrefixRecords, omegaPrefix]
      rfl
  obtain ⟨slot', hlive', hpriority⟩ :=
    exists_literalRightSeamSelectedTable_bothTargetPriority_eq_blockMin A
      strategy hwin
      (package.literalRightSeamInstalled A strategy hwin receiver.1)
      receiver.2.2.1.1
      (fun k ↦ ((env (start + k)).inputOne,
        (env (start + k)).inputTwo)) past.length
  have hslot : slot' = slot := by
    exact Option.some.inj (hlive'.symm.trans hlive)
  subst slot'
  exact hpriority.trans hminimum.symm

/-- Mirror fixed-segment target-priority law. -/
theorem LiteralLeftSeamTableRootPhysicalSegmentFrom.targetPriority_eq
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n start : Nat)
    (past : List (In₂ × In₁))
    {receiver : LeftReceiver A strategy hwin package}
    {sender : LeftSender A strategy hwin package}
    (hsegment :
      package.LiteralLeftSeamTableRootPhysicalSegmentFrom A strategy hwin env
        n start past receiver sender)
    (slot : ProfiledRawLeftSlot A)
    (hlive :
      (literalLeftSeamSelectedTableTargetCode A strategy hwin
        (package.literalLeftSeamInstalled A strategy hwin receiver.1)
        receiver.2.2.1.1
        (fun k ↦ ((env (start + k)).inputTwo,
          (env (start + k)).inputOne)) past.length .both).family.left () =
          some slot) :
    profiledRawJointThreadRootPriority A (.inr slot) =
      A.priority
        (blockMinState A
          (literalLeftSeamSelectedTableEntryState A strategy hwin
            (package.literalLeftSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1 .both)
          (phaseLiveOmegaSegment
            (package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy
              hwin env) start past.length)) := by
  rcases hsegment with
    ⟨_hend, _hinputs, _hsender, _hreceiver, hrecords⟩
  have hword :
      phaseLiveOmegaSegment
          (package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy
            hwin env) start past.length =
        omegaPrefix
          (fun j ↦ pairedRightRecordForRow .both
            (literalLeftSeamSelectedTablePhysicalPlay A strategy hwin
              (package.literalLeftSeamInstalled A strategy hwin receiver.1)
              receiver.2.2.1.1
              (fun k ↦ ((env (start + k)).inputTwo,
                (env (start + k)).inputOne)) j))
          past.length := by
    apply List.ext_get
    · simp [phaseLiveOmegaSegment, omegaPrefix]
    · intro j hjLeft hjRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [phaseLiveOmegaSegment, omegaPrefix, List.getElem_ofFn]
      exact hrecords j (by simpa [phaseLiveOmegaSegment] using hjLeft)
  have hminimum :
      A.priority
          (blockMinState A
            (literalLeftSeamSelectedTableEntryState A strategy hwin
              (package.literalLeftSeamInstalled A strategy hwin receiver.1)
              receiver.2.2.1.1 .both)
            (phaseLiveOmegaSegment
              (package.literalCombinedFreshPhaseLiveRootSemanticWord A
                strategy hwin env) start past.length)) =
        literalLeftSeamSelectedTableBlockPriority A strategy hwin
          (package.literalLeftSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1
          (fun k ↦ ((env (start + k)).inputTwo,
            (env (start + k)).inputOne)) past.length .both := by
    rw [hword]
    cases hanchor : receiver.2.2.1.1
    · simp [literalLeftSeamSelectedTableEntryState,
        literalLeftSeamSelectedTableBlockPriority, hanchor,
        literalLeftSeamSelectedTablePhysicalPlay_false,
        profiledRawJointTargetRightPhysicalPrefixRecords, omegaPrefix]
      rfl
    · simp [literalLeftSeamSelectedTableEntryState,
        literalLeftSeamSelectedTableBlockPriority, hanchor,
        literalLeftSeamSelectedTablePhysicalPlay_true,
        profiledRawJointGuardedFirstRightPhysicalPrefixRecords, omegaPrefix]
      rfl
  obtain ⟨slot', hlive', hpriority⟩ :=
    exists_literalLeftSeamSelectedTable_bothTargetPriority_eq_blockMin A
      strategy hwin
      (package.literalLeftSeamInstalled A strategy hwin receiver.1)
      receiver.2.2.1.1
      (fun k ↦ ((env (start + k)).inputTwo,
        (env (start + k)).inputOne)) past.length
  have hslot : slot' = slot := by
    exact Option.some.inj (hlive'.symm.trans hlive)
  subst slot'
  exact hpriority.trans hminimum.symm

/-! ## Canonical proof-side coordinates -/

/-- The actual executable word of the phase-live controller. -/
noncomputable def literalCombinedFreshPhaseLiveActualWord
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  let controller :=
    package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
      hwin
  controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
    controller.globalOutputTwo env

/-- Canonical close schedule of an independently supplied fixed-policy
anchor.  It remains proof-side. -/
noncomputable def literalCombinedFreshPhaseLiveCanonicalSchedule
    (env : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail env base))
    (anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy)
    (rowAt : Nat → PairedEntryRow) :
    ProfiledRawJointUnitPolicyCloseSchedule A strategy anchor.initial
      anchor.policy :=
  profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy anchor.initial
    anchor.policy anchor.bank env base hterm anchor.seed rowAt

/-- Root-oriented cuts generated by the canonical schedule. -/
noncomputable def literalCombinedFreshPhaseLiveCanonicalCuts
    (env : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail env base))
    (anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy)
    (rowAt : Nat → PairedEntryRow) : Nat → Nat :=
  profiledRawJointUnitPolicyRootOrientedCuts A strategy anchor.initial
    anchor.policy anchor.bank env base hterm anchor.seed
      (literalCombinedFreshPhaseLiveCanonicalSchedule A strategy env base
        hterm anchor rowAt)

/-- The fixed-policy query at canonical cut `k`. -/
noncomputable def literalCombinedFreshPhaseLiveCanonicalQuery
    (env : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail env base))
    (anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy)
    (rowAt : Nat → PairedEntryRow) (k : Nat) :
    ProfiledRawJointUnitPolicyCloseQuery A strategy anchor.initial
      anchor.policy
        (profiledRawJointUnitPolicyScheduledRoot A strategy anchor.initial
          anchor.policy anchor.bank anchor.seed
            (literalCombinedFreshPhaseLiveCanonicalSchedule A strategy env
              base hterm anchor rowAt) k) :=
  let schedule := literalCombinedFreshPhaseLiveCanonicalSchedule A strategy
    env base hterm anchor rowAt
  schedule k
    (profiledRawJointUnitPolicyScheduledRoot A strategy anchor.initial
      anchor.policy anchor.bank anchor.seed schedule k)

/-! ## One canonical physical cut -/

/-- Exact phase-live data at one canonical open block.

The `target_threadRoot_eq` field is the entire acceptance-lineage premise.
It equates only the active finite slot, never keys or policies. -/
inductive LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutAt
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail env base))
    (anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy)
    (rowAt : Nat → PairedEntryRow) (k : Nat) : Prop where
  | right
      (receiver : RightReceiver A strategy hwin package)
      (sender : RightSender A strategy hwin package)
      (past : List (In₁ × In₂))
      (slot : ProfiledRawRightSlot A)
      (past_length :
        past.length =
          literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base
              hterm anchor rowAt (k + 1) -
            literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base
              hterm anchor rowAt k - 1)
      (segment :
        package.LiteralRightSeamTableRootPhysicalSegmentFrom A strategy hwin
          env
          (base +
            literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base
              hterm anchor rowAt (k + 1) - 1)
          (base +
            literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base
              hterm anchor rowAt k)
          past receiver sender)
      (entryState_eq :
        A.run (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
            env)
            (base +
              literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base
                hterm anchor rowAt k) =
          literalRightSeamSelectedTableEntryState A strategy hwin
            (package.literalRightSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1 .both)
      (target_live :
        (literalRightSeamSelectedTableTargetCode A strategy hwin
          (package.literalRightSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1
          (fun j ↦
            ((env
              (base +
                literalCombinedFreshPhaseLiveCanonicalCuts A strategy env
                  base hterm anchor rowAt k + j)).inputOne,
              (env
                (base +
                  literalCombinedFreshPhaseLiveCanonicalCuts A strategy env
                    base hterm anchor rowAt k + j)).inputTwo))
          past.length .both).family.right () = some slot)
      (target_threadRoot_eq :
        ProfiledRawJointUnitFixedPolicyRoot.threadRoot A anchor.policy
            ((literalCombinedFreshPhaseLiveCanonicalQuery A strategy env base
              hterm anchor rowAt k).target A strategy anchor.initial
                anchor.policy anchor.bank) =
          .inl slot) :
      LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutAt package env base
        hterm anchor rowAt k
  | left
      (receiver : LeftReceiver A strategy hwin package)
      (sender : LeftSender A strategy hwin package)
      (past : List (In₂ × In₁))
      (slot : ProfiledRawLeftSlot A)
      (past_length :
        past.length =
          literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base
              hterm anchor rowAt (k + 1) -
            literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base
              hterm anchor rowAt k - 1)
      (segment :
        package.LiteralLeftSeamTableRootPhysicalSegmentFrom A strategy hwin
          env
          (base +
            literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base
              hterm anchor rowAt (k + 1) - 1)
          (base +
            literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base
              hterm anchor rowAt k)
          past receiver sender)
      (entryState_eq :
        A.run (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
            env)
            (base +
              literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base
                hterm anchor rowAt k) =
          literalLeftSeamSelectedTableEntryState A strategy hwin
            (package.literalLeftSeamInstalled A strategy hwin receiver.1)
            receiver.2.2.1.1 .both)
      (target_live :
        (literalLeftSeamSelectedTableTargetCode A strategy hwin
          (package.literalLeftSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1
          (fun j ↦
            ((env
              (base +
                literalCombinedFreshPhaseLiveCanonicalCuts A strategy env
                  base hterm anchor rowAt k + j)).inputTwo,
              (env
                (base +
                  literalCombinedFreshPhaseLiveCanonicalCuts A strategy env
                    base hterm anchor rowAt k + j)).inputOne))
          past.length .both).family.left () = some slot)
      (target_threadRoot_eq :
        ProfiledRawJointUnitFixedPolicyRoot.threadRoot A anchor.policy
            ((literalCombinedFreshPhaseLiveCanonicalQuery A strategy env base
              hterm anchor rowAt k).target A strategy anchor.initial
                anchor.policy anchor.bank) =
          .inr slot) :
      LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutAt package env base
        hterm anchor rowAt k

namespace LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutAt

/-- One exact canonical cut gives the priority equality consumed by the
fixed-policy alternating-thread theorem.  The proof uses only literal list
alignment, DPA run algebra, and equality of the active target slot. -/
theorem blockMin_eq
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail env base)}
    {anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy}
    {rowAt : Nat → PairedEntryRow} {k : Nat}
    (cut : LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutAt A strategy hwin
      package env base hterm anchor rowAt k) :
    cutBlockMin
        (fun n ↦ A.priority
          (A.run
            (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
              env) (base + n)))
        (literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base hterm
          anchor rowAt) k =
      (literalCombinedFreshPhaseLiveCanonicalQuery A strategy env base hterm
        anchor rowAt k).blockPriority A strategy anchor.initial anchor.policy
          anchor.bank := by
  let word := literalCombinedFreshPhaseLiveActualWord A strategy hwin package
    env
  let semanticWord :=
    package.literalCombinedFreshPhaseLiveRootSemanticWord A strategy hwin env
  let cuts := literalCombinedFreshPhaseLiveCanonicalCuts A strategy env base
    hterm anchor rowAt
  let query := literalCombinedFreshPhaseLiveCanonicalQuery A strategy env base
    hterm anchor rowAt k
  have hword : semanticWord = word := by
    exact package.literalCombinedFreshPhaseLiveRootSemanticWord_eq_actualTraceWord
      A strategy hwin env
  cases cut with
  | right receiver sender past slot hpast hsegment hentry hlive hroot =>
      let state := literalRightSeamSelectedTableEntryState A strategy hwin
        (package.literalRightSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1 .both
      let block := phaseLiveOmegaSegment word (base + cuts k) past.length
      have hlength : block.length = cuts (k + 1) - cuts k - 1 := by
        simpa [block, phaseLiveOmegaSegment, cuts] using hpast
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
          base cuts k state block (by simpa [word, state, cuts] using hentry)
            hlength hslice
      have htarget :=
        hsegment.targetPriority_eq A strategy hwin package env
          (base + cuts (k + 1) - 1) (base + cuts k) past slot
            (by simpa [cuts] using hlive)
      rw [package.literalCombinedFreshPhaseLiveRootSemanticWord_eq_actualTraceWord
        A strategy hwin env] at htarget
      change
        cutBlockMin
            (fun n ↦ A.priority (A.run word (base + n))) cuts k =
          query.blockPriority A strategy anchor.initial anchor.policy
            anchor.bank
      calc
        _ = A.priority (blockMinState A state block) := hphysical
        _ = profiledRawJointThreadRootPriority A (.inl slot) := by
          simpa [state, block, semanticWord, word, cuts] using htarget.symm
        _ = profiledRawJointThreadRootPriority A
              (ProfiledRawJointUnitFixedPolicyRoot.threadRoot A anchor.policy
                (query.target A strategy anchor.initial anchor.policy
                  anchor.bank)) := by
            exact congrArg (profiledRawJointThreadRootPriority A) hroot.symm
        _ = query.blockPriority A strategy anchor.initial anchor.policy
              anchor.bank :=
            query.targetPriority A strategy anchor.initial anchor.policy
              anchor.bank
  | left receiver sender past slot hpast hsegment hentry hlive hroot =>
      let state := literalLeftSeamSelectedTableEntryState A strategy hwin
        (package.literalLeftSeamInstalled A strategy hwin receiver.1)
          receiver.2.2.1.1 .both
      let block := phaseLiveOmegaSegment word (base + cuts k) past.length
      have hlength : block.length = cuts (k + 1) - cuts k - 1 := by
        simpa [block, phaseLiveOmegaSegment, cuts] using hpast
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
          base cuts k state block (by simpa [word, state, cuts] using hentry)
            hlength hslice
      have htarget :=
        hsegment.targetPriority_eq A strategy hwin package env
          (base + cuts (k + 1) - 1) (base + cuts k) past slot
            (by simpa [cuts] using hlive)
      rw [package.literalCombinedFreshPhaseLiveRootSemanticWord_eq_actualTraceWord
        A strategy hwin env] at htarget
      change
        cutBlockMin
            (fun n ↦ A.priority (A.run word (base + n))) cuts k =
          query.blockPriority A strategy anchor.initial anchor.policy
            anchor.bank
      calc
        _ = A.priority (blockMinState A state block) := hphysical
        _ = profiledRawJointThreadRootPriority A (.inr slot) := by
          simpa [state, block, semanticWord, word, cuts] using htarget.symm
        _ = profiledRawJointThreadRootPriority A
              (ProfiledRawJointUnitFixedPolicyRoot.threadRoot A anchor.policy
                (query.target A strategy anchor.initial anchor.policy
                  anchor.bank)) := by
            exact congrArg (profiledRawJointThreadRootPriority A) hroot.symm
        _ = query.blockPriority A strategy anchor.initial anchor.policy
              anchor.bank :=
            query.targetPriority A strategy anchor.initial anchor.policy
              anchor.bank

end LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutAt

/-! ## All canonical cuts and the generic priority interface -/

/-- The exact cut witness at every member of one canonical schedule. -/
structure LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutFamily
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail env base))
    (anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy)
    (rowAt : Nat → PairedEntryRow) : Prop where
  cutAt : ∀ k : Nat,
    LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutAt A strategy hwin
      package env base hterm anchor rowAt k

namespace LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutFamily

/-- A complete family is exactly the priority-only canonical alignment.
No additional record, policy, or parity hypothesis is used here. -/
noncomputable def priorityAlignment
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail env base)}
    {anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy}
    {rowAt : Nat → PairedEntryRow}
    (family : LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutFamily A
      strategy hwin package env base hterm anchor rowAt) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment A
      strategy anchor.initial anchor.policy anchor.bank controller.globalMachine
        controller.globalOutputOne controller.globalOutputTwo env base hterm
          anchor.seed rowAt := by
  dsimp only
  refine ⟨fun k ↦ ?_⟩
  have hcut := (family.cutAt k).blockMin_eq A strategy hwin
  simpa [literalCombinedFreshPhaseLiveActualWord,
    literalCombinedFreshPhaseLiveCanonicalSchedule,
    literalCombinedFreshPhaseLiveCanonicalCuts,
    literalCombinedFreshPhaseLiveCanonicalQuery] using hcut

/-- Therefore the actual controller word is accepting whenever the anchor
starts at its policy root. -/
theorem accepts
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail env base)}
    {anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy}
    {rowAt : Nat → PairedEntryRow}
    (family : LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutFamily A
      strategy hwin package env base hterm anchor rowAt) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    A.Accepts
      (controller.globalMachine.globalMachineTraceWord
        controller.globalOutputOne controller.globalOutputTwo env) := by
  dsimp only
  exact (family.priorityAlignment A strategy hwin).accepts A strategy
    anchor.seed_state

end LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutFamily

/-! ## Acceptance-facing witness and hard-regime fields -/

/-- One proof-side anchor whose every canonical block is represented by the
actual phase-live table. -/
structure LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutWitness
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) where
  base : Nat
  anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy
  hterm : OperationalStrictRunsTerminate
    (profiledRawJointPhysicalGraphTail env base)
  rowAt : Nat → PairedEntryRow
  family :
    LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutFamily A strategy hwin
      package env base hterm anchor rowAt

namespace LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutWitness

/-- The cut witness is precisely the generic canonical acceptance witness
used by `FinitePairedPhysicalControllerPriorityAcceptance`. -/
noncomputable def canonicalAcceptanceWitness
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (witness : LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutWitness A
      strategy hwin package env) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment.CanonicalAcceptanceWitness
      A strategy controller.globalMachine controller.globalOutputOne
        controller.globalOutputTwo env := by
  dsimp only
  exact {
    base := witness.base
    anchor := witness.anchor
    hterm := witness.hterm
    rowAt := witness.rowAt
    alignment := witness.family.priorityAlignment A strategy hwin }

theorem accepts
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (witness : LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutWitness A
      strategy hwin package env) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    A.Accepts
      (controller.globalMachine.globalMachineTraceWord
        controller.globalOutputOne controller.globalOutputTwo env) := by
  dsimp only
  exact (witness.canonicalAcceptanceWitness A strategy hwin).accepts A strategy

end LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutWitness

/-- The two hard physical regimes, stated solely with the canonical cut
witness above.  The graph regime is used only to choose proof-side data. -/
structure LiteralCombinedFreshPhaseLiveHardCanonicalPhysicalCuts
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent :
    GraphBothRecurrent (fun n ↦ (env n).graph) →
      Nonempty
        (LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutWitness A strategy
          hwin package env)
  reversal :
    PersistentStrictReversalTail (fun n ↦ (env n).graph) →
      Nonempty
        (LiteralCombinedFreshPhaseLiveCanonicalPhysicalCutWitness A strategy
          hwin package env)

namespace LiteralCombinedFreshPhaseLiveHardCanonicalPhysicalCuts

/-- Recurrent `.both` field of the priority acceptance package. -/
noncomputable def recurrentAlignment
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (cuts : LiteralCombinedFreshPhaseLiveHardCanonicalPhysicalCuts A strategy
      hwin package env)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph)) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment.CanonicalAcceptanceWitness
      A strategy controller.globalMachine controller.globalOutputOne
        controller.globalOutputTwo env := by
  let witness := Classical.choice (cuts.recurrent hboth)
  exact witness.canonicalAcceptanceWitness A strategy hwin

/-- Persistent-reversal field of the same package. -/
noncomputable def reversalAlignment
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (cuts : LiteralCombinedFreshPhaseLiveHardCanonicalPhysicalCuts A strategy
      hwin package env)
    (hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment.CanonicalAcceptanceWitness
      A strategy controller.globalMachine controller.globalOutputOne
        controller.globalOutputTwo env := by
  let witness := Classical.choice (cuts.reversal hreversal)
  exact witness.canonicalAcceptanceWitness A strategy hwin

/-- Adding the already separate two fixed-tail fields gives the complete
priority acceptance package for the actual phase-live controller. -/
noncomputable def priorityAcceptance
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (cuts : LiteralCombinedFreshPhaseLiveHardCanonicalPhysicalCuts A strategy
      hwin package env)
    (fixedRight :
      EventuallyStrictRight (fun n ↦ (env n).graph) →
        ∃ start : Nat, NatSeqMinEvenParity
          (fun n ↦ A.priority
            (A.run
              (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
                env) (start + n))))
    (fixedLeft :
      EventuallyStrictLeft (fun n ↦ (env n).graph) →
        ∃ start : Nat, NatSeqMinEvenParity
          (fun n ↦ A.priority
            (A.run
              (literalCombinedFreshPhaseLiveActualWord A strategy hwin package
                env) (start + n)))) :
    let controller :=
      package.literalCombinedFreshPhaseLiveRootPhysicalController A strategy
        hwin
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalPriorityAlignment.FinitePairedPhysicalControllerPriorityAcceptance
      A strategy controller env := by
  dsimp only
  exact {
    fixedRight := by
      simpa [literalCombinedFreshPhaseLiveActualWord] using fixedRight
    fixedLeft := by
      simpa [literalCombinedFreshPhaseLiveActualWord] using fixedLeft
    recurrentAlignment := cuts.recurrentAlignment A strategy hwin
    reversalAlignment := cuts.reversalAlignment A strategy hwin }

end LiteralCombinedFreshPhaseLiveHardCanonicalPhysicalCuts

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
