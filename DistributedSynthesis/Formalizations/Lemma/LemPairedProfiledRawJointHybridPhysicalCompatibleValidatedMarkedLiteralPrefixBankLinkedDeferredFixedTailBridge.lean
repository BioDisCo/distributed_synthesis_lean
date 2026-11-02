/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFixedTailOutput
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreStrictAcceptance

/-!
# Exact fixed-tail readback for the linked retained bank

The payload-linked literal-prefix table and the ordinary physical-sibling
table are obtained by two different rationalizations.  Their descriptors and
monitor semantics agree after physical projection, but their literal output
words need not be equal.  This file therefore performs the faithful handoff:
it reads the physical word of the *linked table itself* and proves that word
accepted directly from the projected winning monitor.

This is the reusable fixed-tail interface needed by the linked deferred
controller.  No equality between independently rationalized tables is used.
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

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev LinkedTarget :=
  ProfiledRawJointHybridFinitePayloadLinkedTarget A
    (BankControl A strategy hwin)

private abbrev RightSender :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixSenderState A
    (BankControl A strategy hwin)

private abbrev RightReceiver :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

private abbrev LeftSender :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixSenderState A
    (BankControl A strategy hwin)

private abbrev LeftReceiver :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

/-! ## Physical projection of one linked occurrence -/

/-- The physical paired-right lambda read from one member of the exact
payload-linked literal-prefix table. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
      A strategy hwin state family direction semanticMember hmember
  let monitorFamily := fun descriptor :
      ProfiledRawJointRightFinitePayloadLinkedSiblingDescriptor A
        (BankControl A strategy hwin) ↦
    BlockRecordMonitor.raiseState
      (profiledRawJointRightFinitePayloadLinkedSiblingMonitor A descriptor
        false)
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ monitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController monitor anchor
  {
    blind := fun word input ↦ (controller.labeledTree word).1 input
    informedLeft := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl guard controller.labeledTree past) input
        ).physical.informedFirst
    informedBoth := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl guard controller.labeledTree past) input
        ).physical.informedBoth
    bothOneLeft := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl guard controller.labeledTree past) input
        ).physical.closingFirst
    bothOneBoth := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl guard controller.labeledTree past) input
        ).physical.closingBoth
  }

/-- Left-oriented physical projection. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
      A strategy hwin state family direction semanticMember hmember
  let monitorFamily := fun descriptor :
      ProfiledRawJointLeftFinitePayloadLinkedSiblingDescriptor A
        (BankControl A strategy hwin) ↦
    BlockRecordMonitor.raiseState.{u, v, max u v x y s, y,
      max u v y s, max x (max u v x y s)}
      (profiledRawJointLeftFinitePayloadLinkedSiblingMonitor A descriptor
        false)
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ monitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController monitor anchor
  {
    blind := fun word input ↦ (controller.labeledTree word).1 input
    informedRight := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl guard controller.labeledTree past) input
        ).physical.informedFirst
    informedBoth := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl guard controller.labeledTree past) input
        ).physical.informedBoth
    bothTwoRight := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl guard controller.labeledTree past) input
        ).physical.closingFirst
    bothTwoBoth := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl guard controller.labeledTree past) input
        ).physical.closingBoth
  }

/-- The physical block letter of the linked right play is exactly the block
letter generated by its projected lambda. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda_blockWord
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointTargetRightPhysicalLetter A
        (BlockRecordMonitor.projectReceiverPlay
          (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection
            A)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
            A strategy hwin state family direction semanticMember hmember
              anchor env) n) =
      pairedRightBlockWord
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda
          A strategy hwin state family direction semanticMember hmember anchor)
        env n := by
  simp [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda,
    profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection,
    BlockRecordMonitor.projectReceiverPlay, treePlay, narrowedInducedTree,
    blockLabelApply, profiledRawJointTargetRightPhysicalLetter,
    indexedTargetPhysicalLetter, branchNode_eq_omegaPrefix,
    pairedRightBlockWord]

/-- Left block-letter mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda_blockWord
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointTargetLeftPhysicalLetter A
        (BlockRecordMonitor.projectReceiverPlay
          (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
            A strategy hwin state family direction semanticMember hmember
              anchor env) n) =
      pairedLeftBlockWord
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda
          A strategy hwin state family direction semanticMember hmember anchor)
        env n := by
  simp [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda,
    profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection,
    BlockRecordMonitor.projectReceiverPlay, treePlay, narrowedInducedTree,
    blockLabelApply, profiledRawJointTargetLeftPhysicalLetter,
    indexedTargetPhysicalLetter, branchNode_eq_omegaPrefix,
    pairedLeftBlockWord, pairedLeftBlockLetterAt]

/-! ## Acceptance of the projected linked words -/

/-- The physical projection of a linked right table satisfies both fixed-row
DPA threads.  This is the direct monitor argument; it does not pass through
an independently rationalized physical table. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda_forever
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
        A strategy hwin family direction semanticMember hmember anchor
    let descriptor :=
      profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
    PairedRightForeverAccepts A descriptor.source.1.1
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda
        A strategy hwin state family direction semanticMember hmember anchor) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin state)
  let targetState :=
    profiledRawJointHybridFinitePayloadLinkedRightTargetProjection
      (A := A) (Payload := BankControl A strategy hwin)
  let allowed :=
    profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor
  let base := profiledRawJointTargetRightBlockMonitor A
    (LinkedTarget A strategy hwin) targetState allowed descriptor.source
  let lambda :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda
      A strategy hwin state family direction semanticMember hmember anchor
  apply pairedRightForeverAccepts_of_universalDPA A descriptor.source.1.1
    lambda
  intro env
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
      A strategy hwin state family direction semanticMember hmember anchor env
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
    linkedPlay
  have hlinked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_wins
      A strategy hwin state family direction semanticMember hmember anchor env
  have hbase : base.WinsPlay play := by
    exact (BlockRecordMonitor.comapReceiverOutput_wins_iff base
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay).mp (by
        simpa [base, targetState, allowed, descriptor, activation, linkedPlay]
          using hlinked)
  unfold BlockRecordMonitor.WinsPlay at hbase
  have heq :
      (fun n ↦ base.priority (base.run play n)) =
        fun n ↦
          ((pairedRightThreadSystem A descriptor.source.1.1
            ).universalRunDPA).priority
            ((pairedRightThreadSystem A descriptor.source.1.1
              ).universalRunDPA.run (pairedRightBlockWord lambda env) n) + 2 := by
    funext n
    have hsafe := profiledRawJointTargetRightBlockMonitor_safe_of_wins A
      targetState allowed descriptor.source play hbase n
    change (if (base.run play n).2.2.2.2 then
        ((pairedRightThreadSystem A descriptor.source.1.1
          ).universalRunDPA).priority (base.run play n).1 + 2 else 1) = _
    rw [hsafe, if_pos rfl,
      profiledRawJointTargetRightBlockMonitor_run_universal A targetState
        allowed descriptor.source play n]
    exact congrArg
      (fun q ↦
        ((pairedRightThreadSystem A descriptor.source.1.1
          ).universalRunDPA).priority
          ((pairedRightThreadSystem A descriptor.source.1.1
            ).universalRunDPA.run q n) + 2)
      (funext fun k ↦
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda_blockWord
          A strategy hwin state family direction semanticMember hmember anchor
            env k)
  rw [heq] at hbase
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hbase

/-- Left fixed-row acceptance mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda_forever
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember anchor
    let descriptor :=
      profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
    PairedLeftForeverAccepts A descriptor.source.1.1
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda
        A strategy hwin state family direction semanticMember hmember anchor) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin state)
  let targetState :=
    profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection
      (A := A) (Payload := BankControl A strategy hwin)
  let allowed :=
    profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor
  let base := profiledRawJointTargetLeftBlockMonitor A
    (LinkedTarget A strategy hwin) targetState allowed descriptor.source
  let lambda :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda
      A strategy hwin state family direction semanticMember hmember anchor
  apply pairedLeftForeverAccepts_of_universalDPA A descriptor.source.1.1
    lambda
  intro env
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin state family direction semanticMember hmember anchor env
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
    linkedPlay
  have hlinked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_wins
      A strategy hwin state family direction semanticMember hmember anchor env
  have hbase : base.WinsPlay play := by
    exact (BlockRecordMonitor.comapReceiverOutput_wins_iff base
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay).mp (by
        simpa [base, targetState, allowed, descriptor, activation, linkedPlay]
          using hlinked)
  unfold BlockRecordMonitor.WinsPlay at hbase
  have heq :
      (fun n ↦ base.priority (base.run play n)) =
        fun n ↦
          ((pairedLeftThreadSystem A descriptor.source.1.1
            ).universalRunDPA).priority
            ((pairedLeftThreadSystem A descriptor.source.1.1
              ).universalRunDPA.run (pairedLeftBlockWord lambda env) n) + 2 := by
    funext n
    have hsafe := profiledRawJointTargetLeftBlockMonitor_safe_of_wins A
      targetState allowed descriptor.source play hbase n
    change (if (base.run play n).2.2.2.2 then
        ((pairedLeftThreadSystem A descriptor.source.1.1
          ).universalRunDPA).priority (base.run play n).1 + 2 else 1) = _
    rw [hsafe, if_pos rfl,
      profiledRawJointTargetLeftBlockMonitor_run_universal A targetState
        allowed descriptor.source play n]
    exact congrArg
      (fun q ↦
        ((pairedLeftThreadSystem A descriptor.source.1.1
          ).universalRunDPA).priority
          ((pairedLeftThreadSystem A descriptor.source.1.1
            ).universalRunDPA.run q n) + 2)
      (funext fun k ↦
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda_blockWord
          A strategy hwin state family direction semanticMember hmember anchor
            env k)
  rw [heq] at hbase
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hbase

/-! ## Canonical physical words of the linked table itself -/

/-- The row-selected physical omega word read from one linked right-table
occurrence.  Unlike the older sibling word, this definition keeps the exact
linked rational table chosen by the retained bank. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (row : PairedEntryRow) (env : Nat → In₂ × In₁) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  let lambda :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda
      A strategy hwin state family direction semanticMember hmember anchor
  match row with
  | .first => pairedRightOmegaWord lambda.blind lambda.informedLeft env
  | .both => pairedRightOmegaWord lambda.blind lambda.informedBoth env

/-- Left-oriented linked physical word. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (row : PairedEntryRow) (env : Nat → In₁ × In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  let lambda :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda
      A strategy hwin state family direction semanticMember hmember anchor
  match row with
  | .first => pairedLeftOmegaWord lambda.blind lambda.informedRight env
  | .both => pairedLeftOmegaWord lambda.blind lambda.informedBoth env

/-- Every row of the retained linked right table is accepted from the source
state encoded by that exact semantic occurrence. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord_acceptsFrom
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (row : PairedEntryRow) (env : Nat → In₂ × In₁) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
        A strategy hwin family direction semanticMember hmember anchor
    let descriptor :=
      profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
    A.AcceptsFrom (pairedCodeStateForRow A row descriptor.source.1.1)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
        A strategy hwin state family direction semanticMember hmember anchor row
          env) := by
  dsimp only
  have hforever :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda_forever
      A strategy hwin state family direction semanticMember hmember anchor
  cases row
  · exact hforever.1 env
  · exact hforever.2 env

/-- Left acceptance mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord_acceptsFrom
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (row : PairedEntryRow) (env : Nat → In₁ × In₂) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember anchor
    let descriptor :=
      profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin state)
    A.AcceptsFrom (pairedCodeStateForRow A row descriptor.source.1.1)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
        A strategy hwin state family direction semanticMember hmember anchor row
          env) := by
  dsimp only
  have hforever :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda_forever
      A strategy hwin state family direction semanticMember hmember anchor
  cases row
  · exact hforever.1 env
  · exact hforever.2 env

/-! ## Exact suffix readback from an arbitrary linked prefix -/

private theorem prependList_apply_of_lt
    {Letter : Type*} (past : List Letter) (tail : OmegaWord Letter)
    (n : Nat) (hn : n < past.length) :
    OmegaWord.prependList past tail n = past[n] := by
  induction past generalizing n with
  | nil => simp at hn
  | cons head rest ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simpa using ih n (by simpa using hn)

private theorem prependList_apply_length_add
    {Letter : Type*} (past : List Letter) (tail : OmegaWord Letter)
    (n : Nat) :
    OmegaWord.prependList past tail (past.length + n) = tail n := by
  exact congrFun (OmegaWord.drop_length_prependList past tail) n

private theorem omegaPrefix_prependList_length
    {Letter : Type*} (past : List Letter) (tail : OmegaWord Letter) :
    omegaPrefix (OmegaWord.prependList past tail) past.length = past := by
  apply List.ext_get
  · simp [omegaPrefix]
  · intro n hnLeft hnRight
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [omegaPrefix, List.getElem_ofFn]
    exact prependList_apply_of_lt past tail n hnRight

private theorem omegaPrefix_prependList_length_add
    {Letter : Type*} (past : List Letter) (tail : OmegaWord Letter)
    (n : Nat) :
    omegaPrefix (OmegaWord.prependList past tail) (past.length + n) =
      past ++ omegaPrefix tail n := by
  rw [omegaPrefix_add, omegaPrefix_prependList_length]
  congr 1
  apply List.ext_get
  · simp [omegaPrefix]
  · intro k hkLeft hkRight
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [List.getElem_ofFn, omegaPrefix]
    exact prependList_apply_length_add past tail k

/-- Advancing the right pair from an arbitrary literal prefix follows the
same linked table at the concatenated proof-side prefix. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun_eq_atPrefix
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (past : List (In₂ × In₁))
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin state family direction semanticMember hmember past)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin state family direction semanticMember hmember anchor
            past)
        inputs n =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin state family direction semanticMember hmember
            (past ++ omegaPrefix (fun k ↦ ((inputs k).2, (inputs k).1)) n),
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin state family direction semanticMember hmember anchor
            (past ++ omegaPrefix (fun k ↦ ((inputs k).2, (inputs k).1)) n)) := by
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
      A strategy hwin state
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  induction n with
  | zero => simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun,
      omegaPrefix]
  | succ n ih =>
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun]
      rw [ih]
      rw [omegaPrefix_succ]
      let move :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
          A strategy hwin state family direction semanticMember hmember
      have hsender := finiteCrossAnchorSenderNoRecv_atPrefix move.2
        (past ++ omegaPrefix (fun k ↦ ((inputs k).2, (inputs k).1)) n)
        ((inputs n).2, (inputs n).1)
      have hreceiver := finiteCrossAnchorReceiverRecv_atPrefix move.2 anchor
        (past ++ omegaPrefix (fun k ↦ ((inputs k).2, (inputs k).1)) n)
        ((inputs n).2, (inputs n).1)
      apply Prod.ext
      · simpa only [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix,
          profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv,
          List.append_assoc] using congrArg
            (fun control ↦ (⟨move, control⟩ : RightSender A strategy hwin))
            hsender
      · simpa only [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix,
          profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv,
          List.append_assoc] using congrArg
            (fun control ↦ (⟨move, control⟩ : RightReceiver A strategy hwin))
            hreceiver

/-- Left pair-run mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun_eq_atPrefix
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (past : List (In₁ × In₂))
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin state family direction semanticMember hmember past)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin state family direction semanticMember hmember anchor
            past)
        inputs n =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin state family direction semanticMember hmember
            (past ++ omegaPrefix inputs n),
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin state family direction semanticMember hmember anchor
            (past ++ omegaPrefix inputs n)) := by
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
      A strategy hwin state
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  induction n with
  | zero => simp [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun,
      omegaPrefix]
  | succ n ih =>
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun]
      rw [ih]
      rw [omegaPrefix_succ]
      let move :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
          A strategy hwin state family direction semanticMember hmember
      have hsender := finiteCrossAnchorSenderNoRecv_atPrefix move.2
        (past ++ omegaPrefix inputs n) (inputs n)
      have hreceiver := finiteCrossAnchorReceiverRecv_atPrefix move.2 anchor
        (past ++ omegaPrefix inputs n) (inputs n)
      apply Prod.ext
      · simpa only [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix,
          profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv,
          List.append_assoc] using congrArg
            (fun control ↦ (⟨move, control⟩ : LeftSender A strategy hwin))
            hsender
      · simpa only [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix,
          profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv,
          List.append_assoc] using congrArg
            (fun control ↦ (⟨move, control⟩ : LeftReceiver A strategy hwin))
            hreceiver

/-- A reachable right pair emits exactly the output coordinates of its own
linked physical word, at the offset determined by the already-consumed
literal prefix. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput_eq_physicalWord
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (past : List (In₂ × In₁))
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin state family direction semanticMember hmember past)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin state family direction semanticMember hmember anchor
            past)
        row inputs n =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
        A strategy hwin state family direction semanticMember hmember anchor row
          (OmegaWord.prependList past
            (fun k ↦ ((inputs k).2, (inputs k).1)))
          (past.length + n)).outputPair := by
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
      A strategy hwin state
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  let combined :=
    past ++ omegaPrefix (fun k ↦ ((inputs k).2, (inputs k).1)) n
  let input : In₂ × In₁ := ((inputs n).2, (inputs n).1)
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
      A strategy hwin state family direction semanticMember hmember
  have hround := finiteCrossAnchor_localRound_atPrefix move.2 anchor combined
    input
  have hsender := congrArg (fun record ↦ record.2.2) hround
  have hreceiver := congrArg (fun record ↦ record.2.1.physical) hround
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun_eq_atPrefix]
  cases row
  · apply Prod.ext
    · simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
        pairedRightOmegaWord, omegaPrefix_prependList_length_add,
        prependList_apply_length_add,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix,
        profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv,
        rightRoundRecord, RoundRecord.outputPair, combined, input, move] using
          hsender
    · simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
        pairedRightOmegaWord, omegaPrefix_prependList_length_add,
        prependList_apply_length_add,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix,
        profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv,
        pairedRightInformedForRow, rightRoundRecord, RoundRecord.outputPair,
        combined, input, move] using congrArg
          (fun output ↦ output.informedFirst) hreceiver
  · apply Prod.ext
    · simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
        pairedRightOmegaWord, omegaPrefix_prependList_length_add,
        prependList_apply_length_add,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix,
        profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv,
        rightRoundRecord, RoundRecord.outputPair, combined, input, move] using
          hsender
    · simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
        pairedRightOmegaWord, omegaPrefix_prependList_length_add,
        prependList_apply_length_add,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix,
        profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv,
        pairedRightInformedForRow, rightRoundRecord, RoundRecord.outputPair,
        combined, input, move] using congrArg
          (fun output ↦ output.informedBoth) hreceiver

/-- Left output-coordinate mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput_eq_physicalWord
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (past : List (In₁ × In₂))
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin state family direction semanticMember hmember past)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin state family direction semanticMember hmember anchor
            past)
        row inputs n =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
        A strategy hwin state family direction semanticMember hmember anchor row
          (OmegaWord.prependList past inputs)
          (past.length + n)).outputPair := by
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
      A strategy hwin state
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  let combined := past ++ omegaPrefix inputs n
  let input : In₁ × In₂ := inputs n
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
      A strategy hwin state family direction semanticMember hmember
  have hround := finiteCrossAnchor_localRound_atPrefix move.2 anchor combined
    input
  have hsender := congrArg (fun record ↦ record.2.2) hround
  have hreceiver := congrArg (fun record ↦ record.2.1.physical) hround
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun_eq_atPrefix]
  cases row
  · apply Prod.ext
    · simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, omegaPrefix_prependList_length_add,
        prependList_apply_length_add,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix,
        profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv,
        pairedLeftInformedForRow, leftRoundRecord, RoundRecord.outputPair,
        combined, input, move] using congrArg
          (fun output ↦ output.informedFirst) hreceiver
    · simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, omegaPrefix_prependList_length_add,
        prependList_apply_length_add,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix,
        profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv,
        leftRoundRecord, RoundRecord.outputPair, combined, input, move] using
          hsender
  · apply Prod.ext
    · simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, omegaPrefix_prependList_length_add,
        prependList_apply_length_add,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix,
        profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv,
        pairedLeftInformedForRow, leftRoundRecord, RoundRecord.outputPair,
        combined, input, move] using congrArg
          (fun output ↦ output.informedBoth) hreceiver
    · simpa [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, omegaPrefix_prependList_length_add,
        prependList_apply_length_add,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix,
        profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv,
        leftRoundRecord, RoundRecord.outputPair, combined, input, move] using
          hsender

/-! ## Reification of an abstract reachable pair -/

/-- A proof-side right `PairAtPrefix` witness determines one accepted linked
physical word and the exact offset at which the concrete pair starts reading
it.  This is the unconditional local handoff required after locating the
final live pair. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix.physicalTail_exists
    {state : BankControl A strategy hwin}
    {sender : RightSender A strategy hwin}
    {receiver : RightReceiver A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin state sender receiver)
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂) :
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (direction : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcOnePairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).right () =
          some semanticMember,
        ∃ (anchor : Bool) (past : List (In₂ × In₁)),
          sender =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
                A strategy hwin state family direction semanticMember hmember
                  past ∧
            receiver =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
                A strategy hwin state family direction semanticMember hmember
                  anchor past ∧
            (let activation :=
                profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
                  A strategy hwin family direction semanticMember hmember anchor
              let descriptor :=
                profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A
                  activation
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren
                      A strategy hwin state)
              let tableEnv := OmegaWord.prependList past
                (fun k ↦ ((inputs k).2, (inputs k).1))
              A.AcceptsFrom
                  (pairedCodeStateForRow A row descriptor.source.1.1)
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
                    A strategy hwin state family direction semanticMember hmember
                      anchor row tableEnv) ∧
                ∀ n : Nat,
                  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput
                      A strategy hwin sender receiver row inputs n =
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
                      A strategy hwin state family direction semanticMember
                        hmember anchor row tableEnv
                        (past.length + n)).outputPair) := by
  rcases hpair with
    ⟨family, direction, semanticMember, hmember, anchor, past, hsender,
      hreceiver⟩
  refine ⟨family, direction, semanticMember, hmember, anchor, past, hsender,
    hreceiver, ?_, ?_⟩
  · exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord_acceptsFrom
        A strategy hwin state family direction semanticMember hmember anchor row
          (OmegaWord.prependList past
            (fun k ↦ ((inputs k).2, (inputs k).1)))
  · intro n
    rw [hsender, hreceiver]
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput_eq_physicalWord
        A strategy hwin state family direction semanticMember hmember anchor past
          row inputs n

/-- Left reification mirror. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix.physicalTail_exists
    {state : BankControl A strategy hwin}
    {sender : LeftSender A strategy hwin}
    {receiver : LeftReceiver A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin state sender receiver)
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂) :
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (direction : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcTwoPairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).left () =
          some semanticMember,
        ∃ (anchor : Bool) (past : List (In₁ × In₂)),
          sender =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
                A strategy hwin state family direction semanticMember hmember
                  past ∧
            receiver =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
                A strategy hwin state family direction semanticMember hmember
                  anchor past ∧
            (let activation :=
                profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
                  A strategy hwin family direction semanticMember hmember anchor
              let descriptor :=
                profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A
                  activation
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren
                      A strategy hwin state)
              let tableEnv := OmegaWord.prependList past inputs
              A.AcceptsFrom
                  (pairedCodeStateForRow A row descriptor.source.1.1)
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
                    A strategy hwin state family direction semanticMember hmember
                      anchor row tableEnv) ∧
                ∀ n : Nat,
                  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput
                      A strategy hwin sender receiver row inputs n =
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
                      A strategy hwin state family direction semanticMember
                        hmember anchor row tableEnv
                        (past.length + n)).outputPair) := by
  rcases hpair with
    ⟨family, direction, semanticMember, hmember, anchor, past, hsender,
      hreceiver⟩
  refine ⟨family, direction, semanticMember, hmember, anchor, past, hsender,
    hreceiver, ?_, ?_⟩
  · exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord_acceptsFrom
        A strategy hwin state family direction semanticMember hmember anchor row
          (OmegaWord.prependList past inputs)
  · intro n
    rw [hsender, hreceiver]
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput_eq_physicalWord
        A strategy hwin state family direction semanticMember hmember anchor past
          row inputs n

end

end DetParityAutomaton

end DistributedSynthesis
