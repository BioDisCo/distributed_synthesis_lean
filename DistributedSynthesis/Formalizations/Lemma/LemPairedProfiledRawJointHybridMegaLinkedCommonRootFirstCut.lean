/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedCommonRootTrajectory

/-!
# Physical handoff at the first common-root reversal

The common-root initialization carries hidden receiver anchors that differ
from the ordinary full-restart initialization.  This file reads the first
strict block directly, identifies its exact marked-bank child, and records
the checker state and fresh opposite-lane relay at the first reversal.
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

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev LinkedRelay :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelay A
    strategy hwin

private abbrev LinkedOne :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedOneControl
    A strategy hwin

private abbrev LinkedTwo :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedTwoControl
    A strategy hwin

private abbrev Payload :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPayload A
    strategy hwin

private abbrev OneControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedOne A strategy hwin) (Payload A strategy hwin) PUnit.{1}

private abbrev TwoControl :=
  FiniteAcknowledgedDelayedCarrier.DeferredOrRecurrent
    (LinkedTwo A strategy hwin) (Payload A strategy hwin) PUnit.{1}

noncomputable def profiledRawJointHybridMegaLinkedCommonRootLeftBlindBaseAt
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedRelay A strategy hwin :=
  let two :=
    profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt A strategy hwin tag
      env n
  if two.2.1 then
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
      A strategy hwin (two.child A strategy hwin) false false
  else two.2.2.1

noncomputable def profiledRawJointHybridMegaLinkedCommonRootRightBlindBaseAt
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    LinkedRelay A strategy hwin :=
  let one :=
    profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt A strategy hwin tag
      env n
  if one.2.1 then
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
      A strategy hwin (one.child A strategy hwin) false false
  else one.2.2.1

example (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag env
        0 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin tag.1 true true := by
  rfl

theorem profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt_succ_of_left_eq_advance
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (n : Nat) (hgraph : (env n).graph = .left) :
    profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag env
        (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedRelayAdvance
        A strategy hwin
          (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin
            tag env n)
          ((env n).inputOne, (env n).inputTwo) := by
  have hopen :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_open_of_noBoth
      A strategy hwin tag env hnoBoth n
  rcases hopen.1 with ⟨one, payloadOne, _, hone, _⟩
  rcases hopen.2 with ⟨two, payloadTwo, _, htwo, _⟩
  have hpair :
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
          tag env n =
        (.inl (false, one, payloadOne), .inl (false, two, payloadTwo)) := by
    apply Prod.ext
    · exact hone
    · exact htwo
  have hnext :
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
          tag env (n + 1) =
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag)
              (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A
                strategy hwin tag env n).1 (env n).inputOne
              (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A
                strategy hwin tag env n).2 (env n).inputTwo).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
            A strategy hwin
              (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A
                strategy hwin tag env n).2 (env n).inputTwo).1) := by
    rw [profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hgraph]
    rfl
  simp only [profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt,
    profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt,
    profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt]
  rw [hnext, hpair]
  rfl

theorem profiledRawJointHybridMegaLinkedCommonRootLeftBlindBaseAt_succ_of_left_sender
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (n : Nat) (hgraph : (env n).graph = .left) :
    (profiledRawJointHybridMegaLinkedCommonRootLeftBlindBaseAt A strategy hwin tag env (n + 1)).2.1 =
      (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A
        (profiledRawJointHybridMegaLinkedCommonRootLeftBlindBaseAt A strategy hwin tag env n).2.1
          (env n).inputTwo).2 := by
  have hopen :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_open_of_noBoth
      A strategy hwin tag env hnoBoth n
  rcases hopen.1 with ⟨one, payloadOne, _, hone, _⟩
  rcases hopen.2 with ⟨two, payloadTwo, _, htwo, _⟩
  have hpair :
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
          tag env n =
        (.inl (false, one, payloadOne), .inl (false, two, payloadTwo)) := by
    apply Prod.ext
    · exact hone
    · exact htwo
  have hnext :
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
          tag env (n + 1) =
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag)
              (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A
                strategy hwin tag env n).1 (env n).inputOne
              (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A
                strategy hwin tag env n).2 (env n).inputTwo).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
            A strategy hwin
              (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A
                strategy hwin tag env n).2 (env n).inputTwo).1) := by
    rw [profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hgraph]
    rfl
  simp only [profiledRawJointHybridMegaLinkedCommonRootLeftBlindBaseAt,
    profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt]
  rw [hnext, hpair]
  rfl

theorem profiledRawJointHybridMegaLinkedCommonRootLeftPairRun_eq_operational
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (start j : Nat)
    (hstart :
      (profiledRawJointHybridMegaLinkedCommonRootLeftBlindBaseAt A strategy hwin tag env start).2.1 =
        (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin
          tag env start).2.1)
    (hgraph : ∀ t : Nat, t < j → (env (start + t)).graph = .left) :
    let base :=
      profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env start
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env (start + t)).inputOne, (env (start + t)).inputTwo)
    ((profiledRawJointHybridMegaLinkedCommonRootLeftBlindBaseAt A strategy hwin tag env
        (start + j)).2.1,
      (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env (start + j)).2.2) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun
        A strategy hwin base.2.1 base.2.2 inputs j := by
  dsimp only
  induction j with
  | zero =>
      apply Prod.ext
      · simpa using hstart
      · rfl
  | succ j ih =>
      have hjgraph := hgraph j (Nat.lt_succ_self j)
      have hblind := profiledRawJointHybridMegaLinkedCommonRootLeftBlindBaseAt_succ_of_left_sender
        A strategy hwin tag env hnoBoth (start + j) hjgraph
      have hbase := profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt_succ_of_left_eq_advance
        A strategy hwin tag env hnoBoth (start + j) hjgraph
      have ih' := ih (fun t ht ↦ hgraph t (Nat.lt_trans ht (Nat.lt_succ_self j)))
      rw [show start + (j + 1) = start + j + 1 by omega, hblind, hbase]
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun]
      rw [← ih']
      rfl

theorem profiledRawJointHybridMegaLinkedCommonRootExpectedOutput_leftBlock_eq_pairOutput_first
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (j : Nat) (hgraph : ∀ t : Nat, t ≤ j → (env t).graph = .left) :
    let base :=
      profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0
    let inputs : Nat → In₁ × In₂ := fun t ↦
      ((env t).inputOne, (env t).inputTwo)
    (profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne A strategy hwin
        tag env j,
      profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo A strategy
        hwin tag env j) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput
        A strategy hwin base.2.1 base.2.2 .first inputs j := by
  dsimp only
  have hrun :=
    profiledRawJointHybridMegaLinkedCommonRootLeftPairRun_eq_operational A strategy hwin tag env hnoBoth
      0 j (by rfl) (fun t ht ↦ by simpa using hgraph t (Nat.le_of_lt ht))
  simp only [Nat.zero_add] at hrun
  have hopen :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_open_of_noBoth
      A strategy hwin tag env hnoBoth j
  rcases hopen.1 with ⟨one, payloadOne, _, hone, _⟩
  rcases hopen.2 with ⟨two, payloadTwo, _, htwo, _⟩
  have hpair :
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
          tag env j =
        (.inl (false, one, payloadOne), .inl (false, two, payloadTwo)) := by
    apply Prod.ext
    · exact hone
    · exact htwo
  rw [profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne,
    profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo,
    hgraph j (Nat.le_refl _), hpair]
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput,
    ← hrun]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo_open_output,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne_open_output]
  simp only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRetainedNoRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne,
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOutputOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open,
    profiledRawJointHybridMegaLinkedCommonRootLeftBlindBaseAt,
    profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt,
    profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt,
    profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt,
    hone, htwo]

theorem profiledRawJointHybridMegaLinkedCommonRoot_leftBlock_round_eq_linkedPhysicalWord
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (root :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy
        hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember true [])
    (j : Nat) (hgraph : ∀ t : Nat, t ≤ j → (env t).graph = .left) :
    profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin tag
        env j =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
        A strategy hwin root family direction semanticMember hmember true
          .first (fun t ↦ ((env t).inputOne, (env t).inputTwo)) j := by
  have hout :=
    profiledRawJointHybridMegaLinkedCommonRootExpectedOutput_leftBlock_eq_pairOutput_first A strategy
      hwin tag env hnoBoth j hgraph
  have hphysical :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput_eq_physicalWord
      A strategy hwin root family direction semanticMember hmember true []
        .first (fun t ↦ ((env t).inputOne, (env t).inputTwo)) j
  dsimp only at hout
  rw [hsender, hreceiver] at hout
  rw [hphysical] at hout
  apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
  · apply EnvironmentRound.eq_of_components <;>
      simp [profiledRawJointHybridMegaLinkedCommonRootReferenceWord,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, leftRoundRecord, RoundRecord.environment,
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord,
        hgraph j (Nat.le_refl _)]
  · simpa [profiledRawJointHybridMegaLinkedCommonRootReferenceWord_outputPair]
      using hout

theorem profiledRawJointHybridMegaLinkedCommonRoot_left_freshAlignedOccurrence
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin tag.1) :
    let root := tag.1
    let base :=
      profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
        (direction : ProfiledRawJointFamilyDirection
          (I := Unit) (In₁ := In₁) (In₂ := In₂))
        (semanticMember : ProcTwoPairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).left () =
          some semanticMember,
        base.2.1 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
              A strategy hwin root family direction semanticMember hmember [] ∧
          base.2.2 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
              A strategy hwin root family direction semanticMember hmember true
                [] ∧
          ∀ (row : PairedEntryRow) (past : List (In₁ × In₂))
              (input : In₁ × In₂),
            (root.childCode A strategy hwin
                (.strict
                  (profiledRawJointUnitLeftActualDirection
                    (In₁ := In₁) (In₂ := In₂) row past input))).1 =
              .oneSided
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
                  A strategy hwin family direction semanticMember hmember true
                    ).target row past input) := by
  dsimp only
  let root := tag.1
  let base :=
    profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag env
      0
  have hbase :
      base =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
          A strategy hwin root true true := by
    rfl
  change
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
      A strategy hwin root at hready
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
      hwin root.1 root.2 hreachable
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
          strategy hwin root.1 root.2 hreachable').source =
        .oneSided source := by
    simpa only using hpacketSource
  have hpacketMove : packet.move.1 = some (source.move A) := by
    rw [← packet.source_move, hpacketSource]
    rfl
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
      A strategy hwin root
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember true)
        [] default⟩
  refine ⟨family, direction, semanticMember, hmember, ?_, ?_, ?_⟩
  · change base.2.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
        A strategy hwin root family direction semanticMember hmember []
    rw [hbase]
    change
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A
          (root.linkedLeftMove A strategy hwin) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoSenderInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember) =
        ⟨_, finiteCrossAnchorSenderAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember).2 []⟩
    rw [finiteCrossAnchorSenderAtPrefix_nil]
    rfl
  · change base.2.2 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
        A strategy hwin root family direction semanticMember hmember true []
    rw [hbase]
    change
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A
          (root.linkedLeftMove A strategy hwin) true =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember true []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoReceiverInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember) true =
        ⟨_, finiteCrossAnchorReceiverAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember).2 true []⟩
    rw [finiteCrossAnchorReceiverAtPrefix_nil]
    rfl
  · intro row past input
    let actual := profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember true
    have htarget :=
      haligned source hpacketSource' currentMember hcurrentMember row past input
    rw [
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
        A strategy hwin root hreachable,
      sourceFreeBeliefParentLinkedNext_fst]
    change
      profiledRawJointHybridNext A root.2.1.1 packet.move.1
          (.strict actual) =
        .oneSided (activation.target row past input)
    rw [hcode, hpacketMove]
    apply congrArg ProfiledRawJointHybridCode.oneSided
    calc
      profiledRawJointOneSidedNext A code (source.move A) actual =
          (source.step A actual).code A := by
        rw [← hsourceCode]
        exact (ProfiledRawJointOneSidedSemanticState.step_code A source actual).symm
      _ = activation.target row past input := by
        simpa [activation,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations,
          profiledRawJointLeftPhysicalSiblingActivation,
          profiledRawJointLeftSiblingActivation, actual] using htarget

theorem profiledRawJointHybridMegaLinkedCommonRoot_leftFirstCut_round_eq_projectedPlayRecord
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hgraph : (env 0).graph = .left)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember true [])
    (j : Nat) (hj : j ≤ cuts.openLength 0) :
    let tableEnv : Nat → In₁ × In₂ := fun t ↦
      ((env t).inputOne, (env t).inputTwo)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember true
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin tag
        env j =
      pairedLeftRecordForRow .first
        (profiledRawJointTargetLeftPhysicalLetter A (play j)) := by
  dsimp only
  have hcurrent : (env j).graph = .left := by
    by_cases hclose : j = cuts.openLength 0
    · rw [hclose]
      have hclosing := cuts.closing_graph_eq 0
      have hindex : cuts.cuts 1 - 1 = cuts.openLength 0 := by
        rw [cuts.step_eq, cuts.cuts_zero]
        omega
      rw [hindex, cuts.cuts_zero, hgraph] at hclosing
      exact hclosing
    · have hjOpen : j < cuts.openLength 0 := by omega
      have h := cuts.homogeneous 0 j hjOpen
      rw [cuts.cuts_zero] at h
      simpa using h.trans hgraph
  have hprefix : ∀ t : Nat, t ≤ j → (env t).graph = .left := by
    intro t ht
    by_cases hclose : t = cuts.openLength 0
    · have hjeq : j = cuts.openLength 0 := by omega
      simpa [hclose, hjeq] using hcurrent
    · have htOpen : t < cuts.openLength 0 := by omega
      have h := cuts.homogeneous 0 t htOpen
      rw [cuts.cuts_zero] at h
      simpa using h.trans hgraph
  rw [profiledRawJointHybridMegaLinkedCommonRoot_leftBlock_round_eq_linkedPhysicalWord A strategy hwin
    tag env hnoBoth root family direction semanticMember hmember hsender
      hreceiver j hprefix]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda_blockWord
      A strategy hwin root family direction semanticMember hmember true
        (fun t ↦ ((env t).inputOne, (env t).inputTwo)) j]
  rfl

theorem profiledRawJointHybridMegaLinkedCommonRoot_leftFirstCut_slice_and_closing
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hgraph : (env 0).graph = .left)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember true []) :
    let tableEnv : Nat → In₁ × In₂ := fun t ↦
      ((env t).inputOne, (env t).inputTwo)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember true
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    let block := profiledRawJointTargetLeftPhysicalPrefixRecords A .first
      (omegaPrefix play (cuts.openLength 0))
    omegaPrefix
          (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy
            hwin tag env) block.length = block ∧
      profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
          tag env block.length =
        pairedLeftRecordForRow .first
          (profiledRawJointTargetLeftPhysicalLetter A
            (play (cuts.openLength 0))) := by
  dsimp only
  constructor
  · apply List.ext_get
    · simp [profiledRawJointTargetLeftPhysicalPrefixRecords, omegaPrefix]
    · intro j hjLeft hjRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn,
        profiledRawJointTargetLeftPhysicalPrefixRecords, List.getElem_map]
      exact
        profiledRawJointHybridMegaLinkedCommonRoot_leftFirstCut_round_eq_projectedPlayRecord A strategy
          hwin tag env cuts hnoBoth hgraph root family direction semanticMember
            hmember hsender hreceiver j
              (by
                have hj : j < cuts.openLength 0 := by
                  simpa [profiledRawJointTargetLeftPhysicalPrefixRecords,
                    omegaPrefix] using hjRight
                omega)
  · simp only [profiledRawJointTargetLeftPhysicalPrefixRecords,
      List.length_map, omegaPrefix, List.length_ofFn]
    exact
      profiledRawJointHybridMegaLinkedCommonRoot_leftFirstCut_round_eq_projectedPlayRecord A strategy
        hwin tag env cuts hnoBoth hgraph root family direction semanticMember
          hmember hsender hreceiver (cuts.openLength 0) (Nat.le_refl _)

theorem profiledRawJointHybridMegaLinkedCommonRoot_leftFirstCut_physicalPacket
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hgraph : (env 0).graph = .left)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember true [])
    (physicalState : A.State) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember true
    let descriptor :=
      profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin root)
    let tableEnv : Nat → In₁ × In₂ := fun t ↦
      ((env t).inputOne, (env t).inputTwo)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember true
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    let word :=
      profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin tag
        env
    A.runFrom physicalState word 0 =
        pairedCodeStateForRow A .first descriptor.source.1.1 →
      ∀ slot : ProfiledRawRightSlot A,
        profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A
            ((play (cuts.openLength 0)).2.1.target .first) =
          .inr (.inl slot) →
        cutBlockMin
              (fun j ↦ A.priority (A.runFrom physicalState word j))
              cuts.cuts 0 =
            profiledRawJointThreadRootPriority A (.inl slot) ∧
          A.runFrom physicalState word (cuts.cuts 1) =
            pairedCodeStateForRow A .first slot.1.1 := by
  dsimp only
  intro hstate slot htarget
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember true
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let tableEnv : Nat → In₁ × In₂ := fun t ↦
    ((env t).inputOne, (env t).inputTwo)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin root family direction semanticMember hmember true
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
  let word :=
    profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin tag
      env
  have hlinked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_wins
      A strategy hwin root family direction semanticMember hmember true tableEnv
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
  have halign :=
    profiledRawJointHybridMegaLinkedCommonRoot_leftFirstCut_slice_and_closing A strategy hwin tag env
      cuts hnoBoth hgraph root family direction semanticMember hmember hsender
        hreceiver
  have hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A .first
        (omegaPrefix play (cuts.openLength 0))).length =
          cuts.cuts 1 - cuts.cuts 0 - 1 := by
    simp only [profiledRawJointTargetLeftPhysicalPrefixRecords,
      List.length_map, omegaPrefix, List.length_ofFn]
    rw [cuts.step_eq]
    omega
  apply
    profiledRawJointTargetLeft_memberCutPacket_of_wins A
      (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
      (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
      descriptor.source play hprojected (cuts.openLength 0) .first slot
        htarget false physicalState word cuts.cuts 0
  · exact cuts.cuts_strictMono (Nat.lt_succ_self 0)
  · simpa [descriptor, activation, word, cuts.cuts_zero] using hstate
  · exact hlength
  · simpa [play, linkedPlay, word, cuts.cuts_zero] using halign.1
  · simpa [play, linkedPlay, word, cuts.cuts_zero] using halign.2

private theorem profiledRawJointHybridMegaLinkedCommonRootPhaseRestartParentOne_strictLeft
    (fallback : LinkedOne A strategy hwin × LinkedTwo A strategy hwin)
    (one : OneControl A strategy hwin) (inputOne : In₁)
    (two : TwoControl A strategy hwin) (inputTwo : In₂)
    (hpending :
      FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending one two) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
            A strategy hwin fallback one inputOne two inputTwo).1)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
            A strategy hwin two inputTwo).1) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
        A strategy hwin fallback one inputOne two inputTwo).child A strategy
          hwin := by
  cases one with
  | inr recurrent => exact False.elim hpending.1
  | inl onePending =>
      cases two with
      | inr recurrent => exact False.elim hpending.2
      | inl twoPending =>
          simp only [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartSelectedOne_openRecv_lastRecv,
            ↓reduceIte]
          rfl

theorem profiledRawJointHybridMegaLinkedCommonRootParentAt_succ_of_left
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ m : Nat, (env m).graph ≠ .both)
    (n : Nat) (hgraph : (env n).graph = .left) :
    profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
        (n + 1) =
      let fallback :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
          A strategy hwin tag
      let pair :=
        profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
          tag env n
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
        A strategy hwin fallback pair.1 (env n).inputOne pair.2
          (env n).inputTwo).child A strategy hwin := by
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  let pair :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin tag
      env n
  have hpending :=
    (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_invariant A
      strategy hwin tag env n).1
  rw [profiledRawJointHybridMegaLinkedCommonRootParentAt,
    profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt,
    profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt]
  change
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
        A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
          A strategy hwin fallback.1
            (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
              hwin tag env (n + 1)).1)
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
          A strategy hwin fallback.2
            (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
              hwin tag env (n + 1)).2) = _
  rw [profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hgraph]
  exact profiledRawJointHybridMegaLinkedCommonRootPhaseRestartParentOne_strictLeft A strategy hwin fallback pair.1
    (env n).inputOne pair.2 (env n).inputTwo hpending

theorem profiledRawJointHybridMegaLinkedCommonRoot_leftFirstCut_targetPayload_eq_nextParent
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hgraph : (env 0).graph = .left)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy hwin tag
        env 0).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember true []) :
    let tableEnv : Nat → In₁ × In₂ := fun t ↦
      ((env t).inputOne, (env t).inputTwo)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember true
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
        (cuts.cuts 1) =
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((play (cuts.openLength 0)).2.1.target .first) := by
  dsimp only
  let n := cuts.openLength 0
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env t).inputOne, (env t).inputTwo)
  let tableEnv : Nat → In₁ × In₂ := fun t ↦
    ((env t).inputOne, (env t).inputTwo)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin root family direction semanticMember hmember true tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
  have hhomogeneous : ∀ t : Nat, t < n → (env t).graph = .left := by
    intro t ht
    have h := cuts.homogeneous 0 t ht
    rw [cuts.cuts_zero] at h
    simpa using h.trans hgraph
  have hrun :=
    profiledRawJointHybridMegaLinkedCommonRootLeftPairRun_eq_operational A strategy hwin tag env hnoBoth
      0 n (by rfl) (fun t ht ↦ by simpa using hhomogeneous t ht)
  simp only [Nat.zero_add] at hrun
  rw [hsender, hreceiver,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun_eq_atPrefix]
      at hrun
  simp only [List.nil_append] at hrun
  have hreceiverClosing := congrArg Prod.snd hrun
  have hbridge :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix_payload_eq_moveOfPlay
      A strategy hwin root family direction semanticMember hmember true
        (omegaPrefix tableEnv n) (tableEnv n) tableEnv
        (by simp [omegaPrefix]) (by simp [omegaPrefix]) .first
  have hactualPayload :
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          (((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
            (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy
              hwin tag env n).2.2
            (env n).inputOne (env n).inputTwo).1.target .first).1) =
        profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((play n).2.1.target .first) := by
    rw [hreceiverClosing]
    simpa [tableEnv, linkedPlay, play, omegaPrefix] using hbridge
  have hclosingGraph : (env n).graph = .left := by
    have hclosing := cuts.closing_graph_eq 0
    have hindex : cuts.cuts 1 - 1 = n := by
      dsimp only [n]
      rw [cuts.step_eq, cuts.cuts_zero]
      omega
    rw [hindex, cuts.cuts_zero, hgraph] at hclosing
    exact hclosing
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin tag
  let pair :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin tag
      env n
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 pair.1
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 pair.2
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
      A strategy hwin selectedOne selectedTwo
  rw [cuts.step_eq, cuts.cuts_zero]
  simp only [Nat.zero_add]
  rw [profiledRawJointHybridMegaLinkedCommonRootParentAt_succ_of_left A strategy hwin tag env hnoBoth n
    hclosingGraph]
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
      A strategy hwin fallback pair.1 (env n).inputOne pair.2
        (env n).inputTwo).child A strategy hwin = _
  simpa only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
    profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt,
    selectedTwo, selectedOne, base, n] using hactualPayload

theorem profiledRawJointHybridMegaLinkedCommonRoot_leftFirstCut_freshPhysicalHandoff
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hgraph : (env 0).graph = .left)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin tag.1)
    (physicalState : A.State)
    (hstate :
      A.runFrom physicalState
          (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy
            hwin tag env) 0 =
        pairedCodeStateForRow A .first
          (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy
                hwin tag env 0).2.1 false).1.1) :
    ∃ (past : List (In₁ × In₂)) (input : In₁ × In₂)
        (slot : ProfiledRawRightSlot A),
      profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag
          env (cuts.cuts 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin tag.1
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂) .first past input)) ∧
      A.runFrom physicalState
          (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy
            hwin tag env) (cuts.cuts 1) =
          pairedCodeStateForRow A .first slot.1.1 ∧
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
          A strategy hwin
            (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin
              tag env (cuts.cuts 1)) ∧
        profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
                A strategy hwin
                  (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy
                    hwin tag env (cuts.cuts 1)) false false).1.1 false =
          slot := by
  let root := tag.1
  have hrootReachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
        hwin root := by
    rcases hready with ⟨_, _, hreachable, _, _⟩
    exact hreachable
  rcases profiledRawJointHybridMegaLinkedCommonRoot_left_freshAlignedOccurrence A strategy hwin tag env
      hready with
    ⟨family, direction, semanticMember, hmember, hsender, hreceiver,
      hchildAligned⟩
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember true
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let tableEnv : Nat → In₁ × In₂ := fun t ↦
    ((env t).inputOne, (env t).inputTwo)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin root family direction semanticMember hmember true tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
  let target := ((play (cuts.openLength 0)).2.1.target .first)
  obtain ⟨past, input, htargetRepresentation⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_targetRepresentation_exists
      A strategy hwin root family direction semanticMember hmember true tableEnv
        (cuts.openLength 0) .first
  have htargetRepresentation' :
      target =
        (activation.target .first past input,
          (.first,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin root
                (.strict
                  (profiledRawJointUnitLeftActualDirection
                    (In₁ := In₁) (In₂ := In₂) .first past input)))) := by
    simpa [target, play, linkedPlay, activation] using htargetRepresentation
  obtain ⟨slot, htarget⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_targetSlot_exists
      A strategy hwin root family direction semanticMember hmember true tableEnv
        (cuts.openLength 0) .first
  have hsource :
      descriptor.source =
        profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource A strategy
          hwin
            (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy
              hwin tag env 0).2.1 false := by
    rw [hsender]
    simp [descriptor, activation,
      profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf]
  have hstate' :
      A.runFrom physicalState
          (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy
            hwin tag env) 0 =
        pairedCodeStateForRow A .first descriptor.source.1.1 := by
    rw [hsource]
    exact hstate
  have hpacket :=
    profiledRawJointHybridMegaLinkedCommonRoot_leftFirstCut_physicalPacket A strategy hwin tag env cuts
      hnoBoth hgraph root family direction semanticMember hmember hsender
        hreceiver physicalState hstate' slot htarget
  have hparent :=
    profiledRawJointHybridMegaLinkedCommonRoot_leftFirstCut_targetPayload_eq_nextParent A strategy hwin
      tag env cuts hnoBoth hgraph root family direction semanticMember hmember
        hsender hreceiver
  have hparent' :
      profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
          (cuts.cuts 1) =
        profiledRawJointHybridFinitePayloadLinkedTargetPayload A target := by
    simpa [target, play, linkedPlay, tableEnv] using hparent
  have htarget' :
      profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A target =
        .inr (.inl slot) := by
    simpa [target, play, linkedPlay] using htarget
  have htargetLive : target.1.family.right () = some slot := by
    change profiledRawJointUnitLeftTargetProjection A target.1 =
      .inr (.inl slot) at htarget'
    cases hliveTarget : target.1.family.right () with
    | none =>
        simp [profiledRawJointUnitLeftTargetProjection, hliveTarget] at htarget'
    | some targetSlot =>
        have hslotTarget : targetSlot = slot := by
          simpa [profiledRawJointUnitLeftTargetProjection, hliveTarget]
            using htarget'
        subst targetSlot
        rfl
  have htargetCode :
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target).2.1.1 =
        .oneSided target.1 := by
    rw [htargetRepresentation']
    have hfull :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_code A
        strategy hwin root hrootReachable
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) .first past input))
    exact (congrArg Prod.fst hfull).trans
      (hchildAligned .first past input)
  have hnextReady :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin
          (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin
            tag env (cuts.cuts 1)) := by
    rw [hparent']
    refine ⟨target.1, slot, ?_, htargetCode, htargetLive⟩
    rw [htargetRepresentation']
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
        strategy hwin root hrootReachable
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) .first past input))
  obtain ⟨nextCode, nextSlot, hnextCode, hnextLive, hnextSender⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightReady_restartRelay_senderSource
      A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag
          env (cuts.cuts 1)) hnextReady false false
  have hnextTargetCode :
      (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag
          env (cuts.cuts 1)).2.1.1 = .oneSided target.1 := by
    rw [hparent']
    exact htargetCode
  have hnextCodeEq : nextCode = target.1 :=
    ProfiledRawJointHybridCode.oneSided.inj
      (hnextCode.symm.trans hnextTargetCode)
  have hnextSlotEq : nextSlot = slot := by
    rw [hnextCodeEq] at hnextLive
    exact Option.some.inj (hnextLive.symm.trans htargetLive)
  have hparentChild :
      profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
          (cuts.cuts 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin root
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂) .first past input)) := by
    rw [hparent']
    simp [htargetRepresentation',
      profiledRawJointHybridFinitePayloadLinkedTargetPayload]
  exact ⟨past, input, slot, hparentChild, hpacket.2, hnextReady,
    hnextSender.trans hnextSlotEq⟩

/-- Acceptance of the complete common-root word when its first strict block
is left-oriented.  The old front child is path level one; the first common
close is path level two, where the canonical full-restart suffix begins. -/
theorem
    profiledRawJointHybridMegaLinkedCommonRootReferenceWord_acceptsFrom_of_leftFirstExactChild
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hgraph : (env 0).graph = .left)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin tag.1)
    (physicalState : A.State)
    (hstate :
      A.runFrom physicalState
          (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy
            hwin tag env) 0 =
        pairedCodeStateForRow A .first
          (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridMegaLinkedCommonRootLeftBaseAt A strategy
                hwin tag env 0).2.1 false).1.1)
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (hfirstSide : first.side = .right)
    (htagChild : tag.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
            strategy hwin control) (.strict first)) :
    A.AcceptsFrom physicalState
      (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        tag env) := by
  let cut := cuts.cuts 1
  have hcutEq : cut = cuts.openLength 0 + 1 := by
    dsimp only [cut]
    rw [cuts.step_eq, cuts.cuts_zero]
    omega
  let closing := cuts.openLength 0
  have hprev : (env closing).graph = .left := by
    have hclose := cuts.closing_graph_eq 0
    have hindex : cuts.cuts 1 - 1 = closing := by
      rw [show cuts.cuts 1 = cut by rfl, hcutEq]
      dsimp only [closing]
      omega
    rw [hindex, cuts.cuts_zero, hgraph] at hclose
    exact hclose
  have hcurrent : (env cut).graph = .right := by
    have hchange := cuts.maximal_of_strict 0 (hnoBoth (cuts.cuts 0))
    rw [cuts.cuts_zero, hgraph] at hchange
    cases hnext : (env cut).graph with
    | right => rfl
    | left => exact False.elim (hchange (by simpa [cut]))
    | both => exact False.elim (hnoBoth cut (by simpa))
  obtain ⟨past, input, slot, hparentChild, hstateCut, hnextReady,
      hnextSource⟩ :=
    profiledRawJointHybridMegaLinkedCommonRoot_leftFirstCut_freshPhysicalHandoff
      A strategy hwin tag env cuts hnoBoth hgraph hready physicalState hstate
  let parent :=
    profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
      cut
  let second :=
    profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) .first past input
  let restartTag : RetainedTag A strategy hwin := (parent, (false, false))
  let tailEnv := OmegaWord.drop env cut
  let tailCuts : OperationalCloseCutPackage
      (fun n ↦ (tailEnv n).graph) := by
    simpa [tailEnv, OmegaWord.drop_apply] using cuts.dropAt 1
  let cutState :=
    A.runFrom physicalState
      (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        tag env) cut
  have hnoBothTail : ∀ n : Nat, (tailEnv n).graph ≠ .both := by
    intro n
    simpa [tailEnv, OmegaWord.drop_apply] using hnoBoth (cut + n)
  have htailGraph : (tailEnv 0).graph = .right := by
    simpa [tailEnv, OmegaWord.drop_apply] using hcurrent
  have htailFirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin restartTag tailEnv := by
    simp [
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady,
      htailGraph, restartTag, parent]
    simpa [parent, cut] using hnextReady
  have htailInitial :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
        A strategy hwin restartTag tailEnv tailCuts cutState 0 := by
    rw [
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut,
      tailCuts.cuts_zero, htailGraph]
    change
      cutState =
        pairedCodeStateForRow A .first
          (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
                A strategy hwin parent false false).1.1 false).1.1
    rw [show cutState =
        A.runFrom physicalState
          (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy
            hwin tag env) (cuts.cuts 1) by simp [cutState, cut], hstateCut]
    rw [show
      profiledRawJointRightFinitePayloadLiteralPrefixSenderSource A strategy
          hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
              A strategy hwin parent false false).1.1 false = slot by
      simpa [parent, cut] using hnextSource]
  have hfirstRoot : ∃ targetRoot : ProfiledRawJointThreadRoot A,
      profiledRawJointHybridCurrentSlots A first.side.other
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
                strategy hwin control) (.strict first)).2.1.1 () =
        some targetRoot := by
    rcases hready with ⟨code, rootSlot, _hreachable, hcode, hlive⟩
    refine ⟨Sum.inr rootSlot, ?_⟩
    rw [← htagChild, hcode]
    rw [hfirstSide]
    simp [IndexedLineageSide.other,
      profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots, hlive]
  have hsecondSide : second.side = first.side.other := by
    rw [hfirstSide]
    rfl
  have hsecondChild : restartTag.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
                strategy hwin control) (.strict first))
          (.strict second) := by
    change parent = _
    rw [show parent =
        profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag
          env (cuts.cuts 1) by simp [parent, cut]]
    rw [hparentChild, htagChild]
  have hsecondGraph : (tailEnv 0).graph =
      profiledRawJointStrictGraphOfSide second.side.other := by
    simpa [second, profiledRawJointStrictGraphOfSide] using htailGraph
  have hsuffix : A.AcceptsFrom cutState
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin restartTag tailEnv) :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_acceptsFrom_of_exactSecondChild
      A strategy hwin restartTag tailEnv tailCuts hnoBothTail htailFirst
        cutState htailInitial control first second hsecondSide hfirstRoot
          hsecondChild hsecondGraph
  have hdrop :
      OmegaWord.drop
          (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy
            hwin tag env) cut =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
          A strategy hwin restartTag tailEnv := by
    have hswitch :=
      profiledRawJointHybridMegaLinkedCommonRootrightSwitch_drop_eq_fullRestartWord
        A strategy hwin tag env hnoBoth closing hprev
          (by simpa [hcutEq, closing] using hcurrent)
    simpa [cut, closing, hcutEq, restartTag, parent, tailEnv] using hswitch
  have htail : A.AcceptsFrom cutState
      (OmegaWord.drop
        (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
          tag env) cut) := by
    rw [hdrop]
    exact hsuffix
  exact
    (A.acceptsFrom_runFrom_drop_iff physicalState
      (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
        tag env) cut).mp htail

end
end DetParityAutomaton
end DistributedSynthesis
