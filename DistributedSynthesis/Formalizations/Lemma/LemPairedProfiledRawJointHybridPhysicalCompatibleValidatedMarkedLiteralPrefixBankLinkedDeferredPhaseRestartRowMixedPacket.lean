/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRowOperationalCut
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartCutPhysicalPacket
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixTargetRowBridge

/-!
# Same-occurrence packets at row-aware phase restarts

The row-aware phase-restart controller has the correct operational bank
recurrence.  At a mixed `first`/`both` round one further physical fact is
needed: a table rebuilt at the exact target payload starts with the profile
advertised by that target.  This file first exposes that root readback for the
concrete finite restart relay.  It is the fresh half of the anti-mosaic seam;
the retained half is the delayed-target law of the old table.
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

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev BankReachable (state : BankControl A strategy hwin) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
    hwin state

/-! ## Aligned restart occurrences -/

/-- Rebuilding a ready right root does not merely produce some represented
right table.  Its bare targets are the public codes of the exact marked-bank
children stored in the linked payload. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_rightReady_restartRelay_freshAlignedOccurrence
    (state : BankControl A strategy hwin)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin state) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin state false false
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
        (direction : ProfiledRawJointFamilyDirection
          (I := Unit) (In₁ := In₁) (In₂ := In₂))
        (semanticMember : ProcOnePairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).right () =
          some semanticMember,
        relay.1.1 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
              A strategy hwin state family direction semanticMember hmember
                [] ∧
          relay.1.2 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
              A strategy hwin state family direction semanticMember hmember
                false [] ∧
          ∀ (row : PairedEntryRow) (past : List (In₂ × In₁))
              (input : In₂ × In₁),
            (state.childCode A strategy hwin
                (.strict
                  (profiledRawJointUnitRightActualDirection
                    (In₁ := In₁) (In₂ := In₂) row past input))).1 =
              .oneSided
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
                  A strategy hwin family direction semanticMember hmember false
                    ).target row past input) := by
  dsimp only
  rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  rcases hrebuild with
    ⟨_hmarker, hreachable', parent, old, rawDirection, family, direction,
      semanticMember, hmember, _hsource, _hannotation, haligned, _hold,
        hlinked⟩
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  obtain ⟨source, hpacketSource, hsourceCode⟩ :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_oneSided_of_code
      A strategy hwin hreachable code hcode
  have hslot :
      profiledRawJointOneSidedCurrentSlots A .right (source.code A) () =
        some (.inl slot) := by
    rw [hsourceCode]
    simp [profiledRawJointOneSidedCurrentSlots, hlive]
  obtain ⟨currentMember, hcurrentMember, _hcurrentSlot, _⟩ :=
    source.exists_right_member_of_currentSlot A () (.inl slot) hslot
  have hpacketSource' :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
          strategy hwin state.1 state.2 hreachable').source =
        .oneSided source := by
    simpa only using hpacketSource
  have hpacketMove : packet.move.1 = some (source.move A) := by
    rw [← packet.source_move, hpacketSource]
    rfl
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
      A strategy hwin state
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  refine ⟨family, direction, semanticMember, hmember, ?_, ?_, ?_⟩
  · change
      profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A
          (state.linkedRightMove A strategy hwin) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin state family direction semanticMember hmember []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoSenderInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin state family direction semanticMember hmember) =
        ⟨_, finiteCrossAnchorSenderAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin state family direction semanticMember hmember).2 []⟩
    rw [finiteCrossAnchorSenderAtPrefix_nil]
    rfl
  · change
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A
          (state.linkedRightMove A strategy hwin) false =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin state family direction semanticMember hmember false []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoReceiverInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin state family direction semanticMember hmember) false =
        ⟨_, finiteCrossAnchorReceiverAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin state family direction semanticMember hmember).2 false []⟩
    rw [finiteCrossAnchorReceiverAtPrefix_nil]
    rfl
  · intro row past input
    let actual := profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
        A strategy hwin family direction semanticMember hmember false
    have htarget :=
      haligned source hpacketSource' currentMember hcurrentMember row past input
    rw [
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
        A strategy hwin state hreachable,
      sourceFreeBeliefParentLinkedNext_fst]
    change
      profiledRawJointHybridNext A state.2.1.1 packet.move.1
          (.strict actual) =
        .oneSided (activation.target row past input)
    rw [hcode, hpacketMove]
    apply congrArg ProfiledRawJointHybridCode.oneSided
    calc
      profiledRawJointOneSidedNext A code (source.move A) actual =
          (source.step A actual).code A := by
        rw [← hsourceCode]
        exact
          (ProfiledRawJointOneSidedSemanticState.step_code A source actual).symm
      _ = activation.target row past input := by
        simpa [activation,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations,
          profiledRawJointRightPhysicalSiblingActivation,
          profiledRawJointRightSiblingActivation, actual] using htarget

/-- Left-root mirror of the aligned restart occurrence. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_leftReady_restartRelay_freshAlignedOccurrence
    (state : BankControl A strategy hwin)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin state) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin state false false
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
        (direction : ProfiledRawJointFamilyDirection
          (I := Unit) (In₁ := In₁) (In₂ := In₂))
        (semanticMember : ProcTwoPairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).left () =
          some semanticMember,
        relay.2.1 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
              A strategy hwin state family direction semanticMember hmember
                [] ∧
          relay.2.2 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
              A strategy hwin state family direction semanticMember hmember
                false [] ∧
          ∀ (row : PairedEntryRow) (past : List (In₁ × In₂))
              (input : In₁ × In₂),
            (state.childCode A strategy hwin
                (.strict
                  (profiledRawJointUnitLeftActualDirection
                    (In₁ := In₁) (In₂ := In₂) row past input))).1 =
              .oneSided
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
                  A strategy hwin family direction semanticMember hmember false
                    ).target row past input) := by
  dsimp only
  rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  rcases hrebuild with
    ⟨_hmarker, hreachable', parent, old, rawDirection, family, direction,
      semanticMember, hmember, _hsource, _hannotation, haligned, _hold,
        hlinked⟩
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  obtain ⟨source, hpacketSource, hsourceCode⟩ :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_oneSided_of_code
      A strategy hwin hreachable code hcode
  have hslot :
      profiledRawJointOneSidedCurrentSlots A .left (source.code A) () =
        some (.inr slot) := by
    rw [hsourceCode]
    simp [profiledRawJointOneSidedCurrentSlots, hlive]
  obtain ⟨currentMember, hcurrentMember, _hcurrentSlot, _⟩ :=
    source.exists_left_member_of_currentSlot A () (.inr slot) hslot
  have hpacketSource' :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
          strategy hwin state.1 state.2 hreachable').source =
        .oneSided source := by
    simpa only using hpacketSource
  have hpacketMove : packet.move.1 = some (source.move A) := by
    rw [← packet.source_move, hpacketSource]
    rfl
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
      A strategy hwin state
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  refine ⟨family, direction, semanticMember, hmember, ?_, ?_, ?_⟩
  · change
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A
          (state.linkedLeftMove A strategy hwin) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin state family direction semanticMember hmember []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoSenderInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin state family direction semanticMember hmember) =
        ⟨_, finiteCrossAnchorSenderAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin state family direction semanticMember hmember).2 []⟩
    rw [finiteCrossAnchorSenderAtPrefix_nil]
    rfl
  · change
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A
          (state.linkedLeftMove A strategy hwin) false =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin state family direction semanticMember hmember false []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoReceiverInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin state family direction semanticMember hmember) false =
        ⟨_, finiteCrossAnchorReceiverAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin state family direction semanticMember hmember).2 false []⟩
    rw [finiteCrossAnchorReceiverAtPrefix_nil]
    rfl
  · intro row past input
    let actual := profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember false
    have htarget :=
      haligned source hpacketSource' currentMember hcurrentMember row past input
    rw [
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
        A strategy hwin state hreachable,
      sourceFreeBeliefParentLinkedNext_fst]
    change
      profiledRawJointHybridNext A state.2.1.1 packet.move.1
          (.strict actual) =
        .oneSided (activation.target row past input)
    rw [hcode, hpacketMove]
    apply congrArg ProfiledRawJointHybridCode.oneSided
    calc
      profiledRawJointOneSidedNext A code (source.move A) actual =
          (source.step A actual).code A := by
        rw [← hsourceCode]
        exact
          (ProfiledRawJointOneSidedSemanticState.step_code A source actual).symm
      _ = activation.target row past input := by
        simpa [activation,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations,
          profiledRawJointLeftPhysicalSiblingActivation,
          profiledRawJointLeftSiblingActivation, actual] using htarget

/-! ## Fresh restart roots read their certified live slot -/

set_option maxHeartbeats 800000 in

/-- A ready left root, installed through the actual finite restart lookup,
emits its certified live-slot profile on the fresh `.first` row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_leftReady_restartRelay_firstInformed
    (state : BankControl A strategy hwin)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin state)
    (input : In₁ × In₂) :
    ∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
      ∃ slot : ProfiledRawLeftSlot A,
        state.2.1.1 = .oneSided code ∧ code.family.left () = some slot ∧
          pairedLeftInformedForRow .first
              ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
                  A strategy hwin state false false).2.2 input.1
                    input.2).1.physical) = slot.2 input := by
  obtain ⟨sourceCode, sourceSlot, hsourceCode, hsourceLive, hsenderSource⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftReady_restartRelay_senderSource
      A strategy hwin state hready false false
  rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
  have hcodes : sourceCode = code := by
    exact ProfiledRawJointHybridCode.oneSided.inj
      (hsourceCode.symm.trans hcode)
  have hslots : sourceSlot = slot := by
    rw [hcodes, hlive] at hsourceLive
    exact (Option.some.inj hsourceLive).symm
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, direction,
      semanticMember, hmember, hsource, hannotation, haligned, hold,
        hlinked⟩
  have hsemanticSource :
      profiledRawLeftSlotOfSemanticPair A semanticMember = slot := by
    have hsourceAtRestart :
        profiledRawLeftSlotOfSemanticPair A semanticMember = sourceSlot := by
      simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay,
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource,
      hlinked] using hsenderSource
    exact hsourceAtRestart.trans hslots
  let env : Nat → In₁ × In₂ := fun _ ↦ input
  let physicalPlay :=
    pairPlay
      (profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember false)
      (profiledRawJointLeftSiblingSender A semanticMember) env
  have hwins :=
    profiledRawJointLeftPhysicalSiblingMonitor_realizable A hwin family
      direction semanticMember hmember false env
  have hroot :=
    profiledRawJointLeftPhysicalSiblingWinningPlay_rootProfile A
      (profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
        semanticMember) physicalPlay hwins
  have hlinkedOutput := congrArg Prod.fst
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_initial_first_pair
      A strategy hwin state family direction semanticMember hmember false input)
  refine ⟨code, slot, hcode, hlive, ?_⟩
  change
    pairedLeftInformedForRow .first
        ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
          (profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A
            (state.linkedLeftMove A strategy hwin) false)
          input.1 input.2).1.physical) = slot.2 input
  rw [hlinked]
  rw [hlinkedOutput]
  change
    pairedLeftInformedForRow .first
        (profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember false [] input).physical = slot.2 input
  simpa [physicalPlay, env, pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix, profiledRawJointLeftPhysicalSiblingDescriptorOf,
    hsemanticSource] using hroot

set_option maxHeartbeats 800000 in

/-- Ready-right mirror of the concrete fresh-root readback. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_rightReady_restartRelay_firstInformed
    (state : BankControl A strategy hwin)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin state)
    (input : In₂ × In₁) :
    ∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
      ∃ slot : ProfiledRawRightSlot A,
        state.2.1.1 = .oneSided code ∧ code.family.right () = some slot ∧
          pairedRightInformedForRow .first
              ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
                  A strategy hwin state false false).1.2 input.1
                    input.2).1.physical) = slot.2 input := by
  obtain ⟨sourceCode, sourceSlot, hsourceCode, hsourceLive, hsenderSource⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightReady_restartRelay_senderSource
      A strategy hwin state hready false false
  rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
  have hcodes : sourceCode = code := by
    exact ProfiledRawJointHybridCode.oneSided.inj
      (hsourceCode.symm.trans hcode)
  have hslots : sourceSlot = slot := by
    rw [hcodes, hlive] at hsourceLive
    exact (Option.some.inj hsourceLive).symm
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, direction,
      semanticMember, hmember, hsource, hannotation, haligned, hold,
        hlinked⟩
  have hsemanticSource :
      profiledRawRightSlotOfSemanticPair A semanticMember = slot := by
    have hsourceAtRestart :
        profiledRawRightSlotOfSemanticPair A semanticMember = sourceSlot := by
      simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay,
      profiledRawJointRightFinitePayloadLiteralPrefixSenderSource,
      hlinked] using hsenderSource
    exact hsourceAtRestart.trans hslots
  let env : Nat → In₂ × In₁ := fun _ ↦ input
  let physicalPlay :=
    pairPlay
      (profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember false)
      (profiledRawJointRightSiblingSender A semanticMember) env
  have hwins :=
    profiledRawJointRightPhysicalSiblingMonitor_realizable A hwin family
      direction semanticMember hmember false env
  have hroot :=
    profiledRawJointRightPhysicalSiblingWinningPlay_rootProfile A
      (profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
        semanticMember) physicalPlay hwins
  have hlinkedOutput := congrArg Prod.fst
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_initial_first_pair
      A strategy hwin state family direction semanticMember hmember false input)
  refine ⟨code, slot, hcode, hlive, ?_⟩
  change
    pairedRightInformedForRow .first
        ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
          (profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A
            (state.linkedRightMove A strategy hwin) false)
          input.1 input.2).1.physical) = slot.2 input
  rw [hlinked]
  rw [hlinkedOutput]
  change
    pairedRightInformedForRow .first
        (profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember false [] input).physical = slot.2 input
  simpa [physicalPlay, env, pairPlay, treePlay, treeOfPair, blockLabelApply,
    branchNode_eq_omegaPrefix, profiledRawJointRightPhysicalSiblingDescriptorOf,
    hsemanticSource] using hroot

/-- Witness-preserving form of the fresh-left readback.  In particular, a
caller that obtained a slot from the preceding target does not lose its
identity behind the existential readiness interface. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_leftReady_restartRelay_firstInformed_of_live
    (state : BankControl A strategy hwin)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawLeftSlot A)
    (hreachable : BankReachable A strategy hwin state)
    (hcode : state.2.1.1 = .oneSided code)
    (hlive : code.family.left () = some slot)
    (input : In₁ × In₂) :
    pairedLeftInformedForRow .first
        ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
            A strategy hwin state false false).2.2 input.1 input.2).1.physical) =
      slot.2 input := by
  obtain ⟨nextCode, nextSlot, hnextCode, hnextLive, houtput⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_leftReady_restartRelay_firstInformed
      A strategy hwin state ⟨code, slot, hreachable, hcode, hlive⟩ input
  have hcodes : nextCode = code :=
    ProfiledRawJointHybridCode.oneSided.inj (hnextCode.symm.trans hcode)
  have hslots : nextSlot = slot := by
    rw [hcodes] at hnextLive
    exact Option.some.inj (hnextLive.symm.trans hlive)
  simpa [hslots] using houtput

/-- Witness-preserving right mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_rightReady_restartRelay_firstInformed_of_live
    (state : BankControl A strategy hwin)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawRightSlot A)
    (hreachable : BankReachable A strategy hwin state)
    (hcode : state.2.1.1 = .oneSided code)
    (hlive : code.family.right () = some slot)
    (input : In₂ × In₁) :
    pairedRightInformedForRow .first
        ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
            A strategy hwin state false false).1.2 input.1 input.2).1.physical) =
      slot.2 input := by
  obtain ⟨nextCode, nextSlot, hnextCode, hnextLive, houtput⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_rightReady_restartRelay_firstInformed
      A strategy hwin state ⟨code, slot, hreachable, hcode, hlive⟩ input
  have hcodes : nextCode = code :=
    ProfiledRawJointHybridCode.oneSided.inj (hnextCode.symm.trans hcode)
  have hslots : nextSlot = slot := by
    rw [hcodes] at hnextLive
    exact Option.some.inj (hnextLive.symm.trans hlive)
  simpa [hslots] using houtput

/-! ## Exact target-payload restart readback -/

set_option maxHeartbeats 800000 in
/-- If a linked right target is installed as its annotated payload, the
fresh left restart reads exactly the profile exposed by that target. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_rightTargetPayload_restartLeft_firstInformed
    (target : ProfiledRawJointHybridFinitePayloadLinkedTarget A
      (BankControl A strategy hwin))
    (slot : ProfiledRawLeftSlot A)
    (hreachable : BankReachable A strategy hwin
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target))
    (hcode :
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        target).2.1.1 = .oneSided target.1)
    (htarget :
      profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A target =
        .inr (.inr slot))
    (input : In₁ × In₂) :
    pairedLeftInformedForRow .first
        ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
            A strategy hwin
              (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target)
              false false).2.2 input.1 input.2).1.physical) =
      slot.2 input := by
  have hlive : target.1.family.left () = some slot := by
    change profiledRawJointUnitRightTargetProjection A target.1 =
      .inr (.inr slot) at htarget
    cases hliveTarget : target.1.family.left () with
    | none =>
        simp [profiledRawJointUnitRightTargetProjection, hliveTarget] at htarget
    | some targetSlot =>
        have hslot : targetSlot = slot := by
          simpa [profiledRawJointUnitRightTargetProjection, hliveTarget]
            using htarget
        subst targetSlot
        rfl
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_leftReady_restartRelay_firstInformed_of_live
      A strategy hwin
        (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target)
        target.1 slot hreachable hcode hlive input

set_option maxHeartbeats 800000 in
/-- Left-target/right-restart mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_leftTargetPayload_restartRight_firstInformed
    (target : ProfiledRawJointHybridFinitePayloadLinkedTarget A
      (BankControl A strategy hwin))
    (slot : ProfiledRawRightSlot A)
    (hreachable : BankReachable A strategy hwin
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target))
    (hcode :
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        target).2.1.1 = .oneSided target.1)
    (htarget :
      profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A target =
        .inr (.inl slot))
    (input : In₂ × In₁) :
    pairedRightInformedForRow .first
        ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
            A strategy hwin
              (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target)
              false false).1.2 input.1 input.2).1.physical) =
      slot.2 input := by
  have hlive : target.1.family.right () = some slot := by
    change profiledRawJointUnitLeftTargetProjection A target.1 =
      .inr (.inl slot) at htarget
    cases hliveTarget : target.1.family.right () with
    | none =>
        simp [profiledRawJointUnitLeftTargetProjection, hliveTarget] at htarget
    | some targetSlot =>
        have hslot : targetSlot = slot := by
          simpa [profiledRawJointUnitLeftTargetProjection, hliveTarget]
            using htarget
        subst targetSlot
        rfl
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_rightReady_restartRelay_firstInformed_of_live
      A strategy hwin
        (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target)
        target.1 slot hreachable hcode hlive input

/-! ## The anti-mosaic seam -/

set_option maxHeartbeats 800000 in
/-- A continuing right-table close and the fresh left table installed from
that exact target agree on their shared round. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_rightClosing_eq_targetPayload_restartLeft_firstInformed
    (target : ProfiledRawJointHybridFinitePayloadLinkedTarget A
      (BankControl A strategy hwin))
    (slot : ProfiledRawLeftSlot A) (row : PairedEntryRow)
    (physical : PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    (input : In₁ × In₂)
    (hclosing : pairedRightClosingForRow row physical = slot.2 input)
    (hreachable : BankReachable A strategy hwin
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target))
    (hcode :
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        target).2.1.1 = .oneSided target.1)
    (htarget :
      profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A target =
        .inr (.inr slot)) :
    pairedRightClosingForRow row physical =
      pairedLeftInformedForRow .first
        ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
            A strategy hwin
              (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target)
              false false).2.2 input.1 input.2).1.physical) := by
  have hfresh :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_rightTargetPayload_restartLeft_firstInformed
      A strategy hwin target slot hreachable hcode htarget input
  exact hclosing.trans hfresh.symm

set_option maxHeartbeats 800000 in
/-- Left-close/right-restart mirror of the anti-mosaic seam. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_leftClosing_eq_targetPayload_restartRight_firstInformed
    (target : ProfiledRawJointHybridFinitePayloadLinkedTarget A
      (BankControl A strategy hwin))
    (slot : ProfiledRawRightSlot A) (row : PairedEntryRow)
    (physical : PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    (input : In₂ × In₁)
    (hclosing : pairedLeftClosingForRow row physical = slot.2 input)
    (hreachable : BankReachable A strategy hwin
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target))
    (hcode :
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        target).2.1.1 = .oneSided target.1)
    (htarget :
      profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A target =
        .inr (.inl slot)) :
    pairedLeftClosingForRow row physical =
      pairedRightInformedForRow .first
        ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
            A strategy hwin
              (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target)
              false false).1.2 input.1 input.2).1.physical) := by
  have hfresh :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_leftTargetPayload_restartRight_firstInformed
      A strategy hwin target slot hreachable hcode htarget input
  exact hclosing.trans hfresh.symm

/-! ## Retained linked tables realize a live target one round later -/

/-- Payload and row annotations do not alter the delayed right-target
profile: a live left slot emitted at `n` is the closing output at `n + 1` at
the same retained row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_delayedTargetSlot
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (tableEnv : Nat → In₂ × In₁)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (htarget :
      let linkedPlay :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
          A strategy hwin root family direction semanticMember hmember anchor
            tableEnv
      let play := BlockRecordMonitor.projectReceiverPlay
        (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
          linkedPlay
      profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A
          ((play n).2.1.target row) = .inr (.inr slot)) :
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin root family direction semanticMember hmember anchor
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay
    pairedRightClosingForRow row (play (n + 1)).2.1.physical =
      slot.2 ((play (n + 1)).1.2, (play (n + 1)).1.1) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
  change
    profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A
        ((play n).2.1.target row) = .inr (.inr slot) at htarget
  have hlinked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_wins
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  have hprojected :
      (profiledRawJointTargetRightBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A
          (BankControl A strategy hwin))
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
        (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay play := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetRightBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A
            (BankControl A strategy hwin))
          (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
          (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
          descriptor.source)
        (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay).mp hlinked
  let monitor :=
    profiledRawJointTargetRightBlockMonitor A
      (ProfiledRawJointHybridFinitePayloadLinkedTarget A
        (BankControl A strategy hwin))
      (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
      (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
      descriptor.source
  have hpending :
      (monitor.run play (n + 1)).2.2.1 row = some slot.2 := by
    rw [BlockRecordMonitor.run]
    simp [monitor, profiledRawJointTargetRightBlockMonitor,
      leftProfileOfProfiledState, htarget]
  have hsafe := profiledRawJointTargetRightBlockMonitor_safe_of_wins A
    (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
    (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
    descriptor.source play hprojected (n + 2)
  rw [show n + 2 = (n + 1) + 1 by omega, BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.1.2 row slot.2 hpending

/-- Left-table mirror of the delayed target-slot law. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_delayedTargetSlot
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (tableEnv : Nat → In₁ × In₂)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (htarget :
      let linkedPlay :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
          A strategy hwin root family direction semanticMember hmember anchor
            tableEnv
      let play := BlockRecordMonitor.projectReceiverPlay
        (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
          linkedPlay
      profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A
          ((play n).2.1.target row) = .inr (.inl slot)) :
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember anchor
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    pairedLeftClosingForRow row (play (n + 1)).2.1.physical =
      slot.2 ((play (n + 1)).1.2, (play (n + 1)).1.1) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
  change
    profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A
        ((play n).2.1.target row) = .inr (.inl slot) at htarget
  have hlinked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_wins
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  have hprojected :
      (profiledRawJointTargetLeftBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A
          (BankControl A strategy hwin))
        (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
        (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay play := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetLeftBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A
            (BankControl A strategy hwin))
          (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
          (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
          descriptor.source)
        (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay).mp hlinked
  let monitor :=
    profiledRawJointTargetLeftBlockMonitor A
      (ProfiledRawJointHybridFinitePayloadLinkedTarget A
        (BankControl A strategy hwin))
      (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
      (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
      descriptor.source
  have hpending :
      (monitor.run play (n + 1)).2.2.1 row = some slot.2 := by
    rw [BlockRecordMonitor.run]
    simp [monitor, profiledRawJointTargetLeftBlockMonitor,
      rightProfileOfProfiledState, htarget]
  have hsafe := profiledRawJointTargetLeftBlockMonitor_safe_of_wins A
    (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
    (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
    descriptor.source play hprojected (n + 2)
  rw [show n + 2 = (n + 1) + 1 by omega, BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.1.2 row slot.2 hpending

set_option maxHeartbeats 800000 in
/-- Complete right-play seam: the delayed close of a retained table is the
fresh `.first` informed output of the restart installed from that exact
annotated target payload. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_delayedTargetPayload_restartLeft_seam
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (tableEnv : Nat → In₂ × In₁)
    (n : Nat) (row : PairedEntryRow)
    (target : ProfiledRawJointHybridFinitePayloadLinkedTarget A
      (BankControl A strategy hwin))
    (slot : ProfiledRawLeftSlot A)
    (htargetAt :
      let linkedPlay :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
          A strategy hwin root family direction semanticMember hmember anchor
            tableEnv
      let play := BlockRecordMonitor.projectReceiverPlay
        (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
          linkedPlay
      target = (play n).2.1.target row)
    (htarget :
      profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A target =
        .inr (.inr slot))
    (hreachable : BankReachable A strategy hwin
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target))
    (hcode :
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        target).2.1.1 = .oneSided target.1) :
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin root family direction semanticMember hmember anchor
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay
    let input : In₁ × In₂ :=
      ((play (n + 1)).1.2, (play (n + 1)).1.1)
    pairedRightClosingForRow row (play (n + 1)).2.1.physical =
      pairedLeftInformedForRow .first
        ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
            A strategy hwin
              (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target)
              false false).2.2 input.1 input.2).1.physical) := by
  dsimp only at htargetAt ⊢
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
  have hprojectionAt :
      profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A
          ((play n).2.1.target row) = .inr (.inr slot) := by
    rw [← htargetAt]
    exact htarget
  have hclosing :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_delayedTargetSlot
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv n row slot hprojectionAt
  change pairedRightClosingForRow row (play (n + 1)).2.1.physical =
    slot.2 ((play (n + 1)).1.2, (play (n + 1)).1.1) at hclosing
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_rightClosing_eq_targetPayload_restartLeft_firstInformed
      A strategy hwin target slot row (play (n + 1)).2.1.physical
        ((play (n + 1)).1.2, (play (n + 1)).1.1) hclosing hreachable
          hcode htarget

set_option maxHeartbeats 800000 in
/-- Complete left-play mirror of the delayed-target restart seam. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_delayedTargetPayload_restartRight_seam
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (tableEnv : Nat → In₁ × In₂)
    (n : Nat) (row : PairedEntryRow)
    (target : ProfiledRawJointHybridFinitePayloadLinkedTarget A
      (BankControl A strategy hwin))
    (slot : ProfiledRawRightSlot A)
    (htargetAt :
      let linkedPlay :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
          A strategy hwin root family direction semanticMember hmember anchor
            tableEnv
      let play := BlockRecordMonitor.projectReceiverPlay
        (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
          linkedPlay
      target = (play n).2.1.target row)
    (htarget :
      profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A target =
        .inr (.inl slot))
    (hreachable : BankReachable A strategy hwin
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target))
    (hcode :
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        target).2.1.1 = .oneSided target.1) :
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember anchor
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    let input : In₂ × In₁ :=
      ((play (n + 1)).1.2, (play (n + 1)).1.1)
    pairedLeftClosingForRow row (play (n + 1)).2.1.physical =
      pairedRightInformedForRow .first
        ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
            A strategy hwin
              (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target)
              false false).1.2 input.1 input.2).1.physical) := by
  dsimp only at htargetAt ⊢
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
  have hprojectionAt :
      profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A
          ((play n).2.1.target row) = .inr (.inl slot) := by
    rw [← htargetAt]
    exact htarget
  have hclosing :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_delayedTargetSlot
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv n row slot hprojectionAt
  change pairedLeftClosingForRow row (play (n + 1)).2.1.physical =
    slot.2 ((play (n + 1)).1.2, (play (n + 1)).1.1) at hclosing
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_leftClosing_eq_targetPayload_restartRight_firstInformed
      A strategy hwin target slot row (play (n + 1)).2.1.physical
        ((play (n + 1)).1.2, (play (n + 1)).1.1) hclosing hreachable
          hcode htarget

set_option maxHeartbeats 1200000 in
/-- The right seam with all target-payload side conditions discharged by a
reachable root and the public child-code alignment of its represented
occurrence. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_aligned_delayedTargetPayload_restartLeft_seam
    (root : BankControl A strategy hwin)
    (hrootReachable : BankReachable A strategy hwin root)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool)
    (hchildAligned :
      ∀ (row : PairedEntryRow) (past : List (In₂ × In₁))
          (input : In₂ × In₁),
        (root.childCode A strategy hwin
            (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂) row past input))).1 =
          .oneSided
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
              A strategy hwin family direction semanticMember hmember anchor
                ).target row past input))
    (tableEnv : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin root family direction semanticMember hmember anchor
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay
    let target := (play n).2.1.target row
    ∃ slot : ProfiledRawLeftSlot A,
      profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A target =
          .inr (.inr slot) ∧
        pairedRightClosingForRow row (play (n + 1)).2.1.physical =
          pairedLeftInformedForRow .first
            ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
                A strategy hwin
                  (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
                    target) false false).2.2
                (play (n + 1)).1.2 (play (n + 1)).1.1).1.physical) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
  let target := (play n).2.1.target row
  obtain ⟨past, input, hrepresentation⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_targetRepresentation_exists
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv n row
  have hrepresentation' :
      target =
        (activation.target row past input,
          (row,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin root
                (.strict
                  (profiledRawJointUnitRightActualDirection
                    (In₁ := In₁) (In₂ := In₂) row past input)))) := by
    simpa [target, play, linkedPlay, activation] using hrepresentation
  obtain ⟨slot, htarget⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_targetSlot_exists
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv n row
  have htarget' :
      profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A target =
        .inr (.inr slot) := by
    simpa [target, play, linkedPlay] using htarget
  have hreachable : BankReachable A strategy hwin
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target) := by
    rw [hrepresentation']
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
        strategy hwin root hrootReachable _
  have hcode :
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        target).2.1.1 = .oneSided target.1 := by
    rw [hrepresentation']
    have hfull :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_code A
        strategy hwin root hrootReachable
          (.strict
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input))
    exact (congrArg Prod.fst hfull).trans
      (hchildAligned row past input)
  have hseam :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_delayedTargetPayload_restartLeft_seam
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv n row target slot (by rfl) htarget' hreachable hcode
  refine ⟨slot, htarget', ?_⟩
  simpa [target, play, linkedPlay] using hseam

set_option maxHeartbeats 1200000 in
/-- Fully discharged left-play mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_aligned_delayedTargetPayload_restartRight_seam
    (root : BankControl A strategy hwin)
    (hrootReachable : BankReachable A strategy hwin root)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool)
    (hchildAligned :
      ∀ (row : PairedEntryRow) (past : List (In₁ × In₂))
          (input : In₁ × In₂),
        (root.childCode A strategy hwin
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂) row past input))).1 =
          .oneSided
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
              A strategy hwin family direction semanticMember hmember anchor
                ).target row past input))
    (tableEnv : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember anchor
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    let target := (play n).2.1.target row
    ∃ slot : ProfiledRawRightSlot A,
      profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A target =
          .inr (.inl slot) ∧
        pairedLeftClosingForRow row (play (n + 1)).2.1.physical =
          pairedRightInformedForRow .first
            ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
                A strategy hwin
                  (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
                    target) false false).1.2
                (play (n + 1)).1.2 (play (n + 1)).1.1).1.physical) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
  let target := (play n).2.1.target row
  obtain ⟨past, input, hrepresentation⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_targetRepresentation_exists
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv n row
  have hrepresentation' :
      target =
        (activation.target row past input,
          (row,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin root
                (.strict
                  (profiledRawJointUnitLeftActualDirection
                    (In₁ := In₁) (In₂ := In₂) row past input)))) := by
    simpa [target, play, linkedPlay, activation] using hrepresentation
  obtain ⟨slot, htarget⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_targetSlot_exists
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv n row
  have htarget' :
      profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A target =
        .inr (.inl slot) := by
    simpa [target, play, linkedPlay] using htarget
  have hreachable : BankReachable A strategy hwin
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target) := by
    rw [hrepresentation']
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
        strategy hwin root hrootReachable _
  have hcode :
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        target).2.1.1 = .oneSided target.1 := by
    rw [hrepresentation']
    have hfull :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_code A
        strategy hwin root hrootReachable
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) row past input))
    exact (congrArg Prod.fst hfull).trans
      (hchildAligned row past input)
  have hseam :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_delayedTargetPayload_restartRight_seam
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv n row target slot (by rfl) htarget' hreachable hcode
  refine ⟨slot, htarget', ?_⟩
  simpa [target, play, linkedPlay] using hseam

set_option maxHeartbeats 1200000 in
/-- Public right-restart packet: readiness alone exposes the exact relay
occurrence and its anti-mosaic seam at every checked table depth and row. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_rightReady_restartRelay_play_seam
    (state : BankControl A strategy hwin)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin state)
    (tableEnv : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin state false false
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
        (direction : ProfiledRawJointFamilyDirection
          (I := Unit) (In₁ := In₁) (In₂ := In₂))
        (semanticMember : ProcOnePairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).right () =
          some semanticMember,
        relay.1.1 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
              A strategy hwin state family direction semanticMember hmember
                [] ∧
          relay.1.2 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
              A strategy hwin state family direction semanticMember hmember
                false [] ∧
          let linkedPlay :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
              A strategy hwin state family direction semanticMember hmember
                false tableEnv
          let play := BlockRecordMonitor.projectReceiverPlay
            (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
              linkedPlay
          let target := (play n).2.1.target row
          ∃ slot : ProfiledRawLeftSlot A,
            profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A
                  target = .inr (.inr slot) ∧
              pairedRightClosingForRow row (play (n + 1)).2.1.physical =
                pairedLeftInformedForRow .first
                  ((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
                      A strategy hwin
                        (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
                          target) false false).2.2
                      (play (n + 1)).1.2
                        (play (n + 1)).1.1).1.physical) := by
  dsimp only
  have hrootReachable : BankReachable A strategy hwin state := by
    rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
    exact hreachable
  obtain ⟨family, direction, semanticMember, hmember, hsender, hreceiver,
      hchildAligned⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_rightReady_restartRelay_freshAlignedOccurrence
      A strategy hwin state hready
  refine ⟨family, direction, semanticMember, hmember, hsender, hreceiver, ?_⟩
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_aligned_delayedTargetPayload_restartLeft_seam
      A strategy hwin state hrootReachable family direction semanticMember
        hmember false hchildAligned tableEnv n row

set_option maxHeartbeats 1200000 in
/-- Public left-restart mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_leftReady_restartRelay_play_seam
    (state : BankControl A strategy hwin)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin state)
    (tableEnv : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let relay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin state false false
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
        (direction : ProfiledRawJointFamilyDirection
          (I := Unit) (In₁ := In₁) (In₂ := In₂))
        (semanticMember : ProcTwoPairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).left () =
          some semanticMember,
        relay.2.1 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
              A strategy hwin state family direction semanticMember hmember
                [] ∧
          relay.2.2 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
              A strategy hwin state family direction semanticMember hmember
                false [] ∧
          let linkedPlay :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
              A strategy hwin state family direction semanticMember hmember
                false tableEnv
          let play := BlockRecordMonitor.projectReceiverPlay
            (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
              linkedPlay
          let target := (play n).2.1.target row
          ∃ slot : ProfiledRawRightSlot A,
            profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A
                  target = .inr (.inl slot) ∧
              pairedLeftClosingForRow row (play (n + 1)).2.1.physical =
                pairedRightInformedForRow .first
                  ((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
                      A strategy hwin
                        (profiledRawJointHybridFinitePayloadLinkedTargetPayload A
                          target) false false).1.2
                      (play (n + 1)).1.2
                        (play (n + 1)).1.1).1.physical) := by
  dsimp only
  have hrootReachable : BankReachable A strategy hwin state := by
    rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
    exact hreachable
  obtain ⟨family, direction, semanticMember, hmember, hsender, hreceiver,
      hchildAligned⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestart_leftReady_restartRelay_freshAlignedOccurrence
      A strategy hwin state hready
  refine ⟨family, direction, semanticMember, hmember, hsender, hreceiver, ?_⟩
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_aligned_delayedTargetPayload_restartRight_seam
      A strategy hwin state hrootReachable family direction semanticMember
        hmember false hchildAligned tableEnv n row

end

end DetParityAutomaton

end DistributedSynthesis
