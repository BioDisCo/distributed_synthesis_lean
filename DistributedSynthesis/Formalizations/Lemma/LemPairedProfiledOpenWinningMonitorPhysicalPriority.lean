/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPhysicalScanPriority
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceBoundaryOverlayInstall

/-!
# Winning open monitors certify literal physical epoch priorities

The open block monitor makes its target check sticky: after one failed check
its priority is forever odd.  A winning play therefore supplies, at every
round, the exact close-target erasure equation consumed by the physical-scan
priority endpoint.

This is the public policy-free counterpart of the private extraction in `ThmPairedProfiledOpenFamilyHandoff`.  It talks about the outputs
actually emitted by the rational controller and never identifies its blind
sender with the raw realizing strategy.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Public extraction of the sticky target check -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every target emitted by a winning open right-monitor play has the exact
erasure checked against the literal scan state, together with the rational
continuation certificate checked in the same table entry. -/
theorem profiledOpenRight_targetsSafe_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (profiledOpenRightBlockMonitor.{u, v, x, y, s, 1}
      A code minimum profile).WinsPlay
      play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedRightCloseTarget A
            (((profiledOpenRightBlockMonitor.{u, v, x, y, s, 1}
              A code minimum profile).run
              play n).2.1) row (profiledRightPhysicalLetter A (play n)) ∧
        (pairedProfiledEntryRunAutomaton A
          ((play n).2.1.target row)).HasRationalRun := by
  classical
  let base := profiledOpenRightBlockMonitor.{u, v, x, y, s, 1}
    A code minimum profile
  have hwin' : (base.restartAt base.initial).WinsPlay play := by
    simpa [base, BlockRecordMonitor.restartAt] using hwin
  have hsafe := base.restartAt_safe_of_wins
    (fun state ↦ state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change ((state.2.2.2.2 && _ && decide _ && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    base.initial play hwin' (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, profiledOpenRightBlockMonitor,
    BlockRecordMonitor.restartAt, Bool.and_eq_true, decide_eq_true_eq] at hsafe
  exact hsafe.2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror. -/
theorem profiledOpenLeft_targetsSafe_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (profiledOpenLeftBlockMonitor.{u, v, x, y, s, 1}
      A code minimum profile).WinsPlay
      play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedLeftCloseTarget A
            (((profiledOpenLeftBlockMonitor.{u, v, x, y, s, 1}
              A code minimum profile).run
              play n).2.1) row (profiledLeftPhysicalLetter A (play n)) ∧
        (pairedProfiledEntryRunAutomaton A
          ((play n).2.1.target row)).HasRationalRun := by
  classical
  let base := profiledOpenLeftBlockMonitor.{u, v, x, y, s, 1}
    A code minimum profile
  have hwin' : (base.restartAt base.initial).WinsPlay play := by
    simpa [base, BlockRecordMonitor.restartAt] using hwin
  have hsafe := base.restartAt_safe_of_wins
    (fun state ↦ state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change ((state.2.2.2.2 && _ && decide _ && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    base.initial play hwin' (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, profiledOpenLeftBlockMonitor,
    BlockRecordMonitor.restartAt, Bool.and_eq_true, decide_eq_true_eq] at hsafe
  exact hsafe.2

/-! ## One-arrow physical priority consequences -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Winning the right open monitor discharges the sole close-target premise
of the literal physical-prefix priority theorem. -/
theorem pairedProfiledEntryPriority_eq_rightPhysicalPrefixBlockMin_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : (profiledOpenRightBlockMonitor.{u, v, x, y, s, 1}
      A code minimum profile).WinsPlay
      play) (n : Nat) (row : PairedEntryRow) :
    pairedProfiledEntryPriority A ((play n).2.1.target row) =
      A.priority
        (blockMinState A (pairedCodeStateForRow A row code)
          (profiledRightPhysicalPrefixRecords A row
            (omegaPrefix play n))) := by
  exact pairedProfiledEntryPriority_eq_rightPhysicalPrefixBlockMin_of_close.{u,
    v, x, y, s, 1} A
    code minimum profile play n row ((play n).2.1.target row)
      (profiledOpenRight_targetsSafe_of_wins A code minimum profile play hwin n
        row).1

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left winning-monitor consequence. -/
theorem pairedProfiledEntryPriority_eq_leftPhysicalPrefixBlockMin_of_wins
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : (profiledOpenLeftBlockMonitor.{u, v, x, y, s, 1}
      A code minimum profile).WinsPlay
      play) (n : Nat) (row : PairedEntryRow) :
    pairedProfiledEntryPriority A ((play n).2.1.target row) =
      A.priority
        (blockMinState A (pairedCodeStateForRow A row code)
          (profiledLeftPhysicalPrefixRecords A row
            (omegaPrefix play n))) := by
  exact pairedProfiledEntryPriority_eq_leftPhysicalPrefixBlockMin_of_close.{u,
    v, x, y, s, 1} A
    code minimum profile play n row ((play n).2.1.target row)
      (profiledOpenLeft_targetsSafe_of_wins A code minimum profile play hwin n
        row).1

/-! ## Installed-overlay finite prefixes with a winning base extension -/

/-- Forget the hidden member/root tag and the classified successor annotation
from one right overlay record.  This is the literal play read by the selected
open root monitor. -/
def profiledOpenWitnessedRightOverlayBaseRecord
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    (record : RealizedBlockRound
      ((Sigma fun member : ProfiledOpenHiddenDescriptorRightCarrier A
        value.1 ↦ ProfiledOpenHiddenDescriptorRightRoot A member.1) × In₂)
      In₁ (ProfiledOpenRightClassifiedOutput A) Out₁) :
    RealizedBlockRound In₂ In₁ (ProfiledRightReceiverOutput A) Out₁ :=
  ((record.1.1.2, record.1.2), record.2.1.1, record.2.2)

/-- Left base-record projection. -/
def profiledOpenWitnessedLeftOverlayBaseRecord
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    (record : RealizedBlockRound
      ((Sigma fun member : ProfiledOpenHiddenDescriptorLeftCarrier A
        value.1 ↦ ProfiledOpenHiddenDescriptorLeftRoot A member.1) × In₁)
      In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂) :
    RealizedBlockRound In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂ :=
  ((record.1.1.2, record.1.2), record.2.1.1, record.2.2)

/-- Base-monitor record prefix emitted by a right installed overlay. -/
def profiledOpenWitnessedRightOverlayBaseRecords
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂)) :
    List (RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁) :=
  (profiledOpenWitnessedRightRoundOverlayRecords A initialCode overlay
    inputs).map (profiledOpenWitnessedRightOverlayBaseRecord A initialCode)

/-- Left base-monitor prefix. -/
def profiledOpenWitnessedLeftOverlayBaseRecords
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂)) :
    List (RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂) :=
  (profiledOpenWitnessedLeftRoundOverlayRecords A initialCode overlay
    inputs).map (profiledOpenWitnessedLeftOverlayBaseRecord A initialCode)

/-! ## The classified closing root is the emitted target -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Semantic re-anchoring retains the complete classified receiver-table
law.  Hence the left root advertised by a right overlay record is exactly
the record's target, for any retained hidden root and any sticky row. -/
theorem
    profiledOpenWitnessedRightRoundRecord_target_eq_classifiedRoot_of_semanticallyReanchored
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (hsemantic : overlay.SemanticallyReanchored A strategy hwin basis
      initialCode)
    (inputOne : In₁) (inputTwo : In₂) (row : PairedEntryRow) :
    (profiledOpenWitnessedRightRoundRecord A initialCode overlay inputOne
        inputTwo).2.1.1.target row =
      .inr (.inr
        ((profiledOpenWitnessedRightRoundRecord A initialCode overlay inputOne
          inputTwo).2.1.2 row).1.1) := by
  rcases hsemantic with ⟨current, hroot⟩
  rcases hroot with
    ⟨witness, hmember, lane, hlane, hdescriptor, hmove, taggedPast,
      hpast⟩
  let table := ((lane.realization.coherentTable A).table
    |>.toClassified A lane.source)
  let decodedRoot := profiledOpenHiddenDescriptorRightRootToEq A
    overlay.member.1 lane.source table hmove overlay.root
  change
    (profiledOpenFixedRightQueryResponses A initialCode overlay.value
      overlay.query overlay.member
        ((overlay.root, inputTwo), inputOne)).1.target row =
      .inr (.inr
        ((profiledOpenFixedRightQueryResponses A initialCode overlay.value
          overlay.query overlay.member
            ((overlay.root, inputTwo), inputOne)).2 row).1.1)
  have hinverse :
      profiledOpenHiddenDescriptorRightRootOfEq A overlay.member.1 lane.source
          table hmove decodedRoot = overlay.root :=
    profiledOpenHiddenDescriptorRightRootOfEq_rootToEq A initialCode
      overlay.member.1 lane.source table hmove overlay.root
  rw [← hinverse]
  have hat := congrFun hpast ((decodedRoot, inputTwo), inputOne)
  rw [hat]
  exact
    (profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A lane.source
      strategy hwin lane.realization.entry
        (fun member ↦ member.1.1.1.2) basis taggedPast decodedRoot
          (inputTwo, inputOne) row).1

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-to-right classified target law. -/
theorem
    profiledOpenWitnessedLeftRoundRecord_target_eq_classifiedRoot_of_semanticallyReanchored
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (hsemantic : overlay.SemanticallyReanchored A strategy hwin basis
      initialCode)
    (inputOne : In₁) (inputTwo : In₂) (row : PairedEntryRow) :
    (profiledOpenWitnessedLeftRoundRecord A initialCode overlay inputOne
        inputTwo).2.1.1.target row =
      .inr (.inl
        ((profiledOpenWitnessedLeftRoundRecord A initialCode overlay inputOne
          inputTwo).2.1.2 row).1.1) := by
  rcases hsemantic with ⟨current, hroot⟩
  rcases hroot with
    ⟨witness, hmember, lane, hlane, hdescriptor, hmove, taggedPast,
      hpast⟩
  let table := ((lane.realization.coherentTable A).table
    |>.toClassified A lane.source)
  let decodedRoot := profiledOpenHiddenDescriptorLeftRootToEq A
    overlay.member.1 lane.source table hmove overlay.root
  change
    (profiledOpenFixedLeftQueryResponses A initialCode overlay.value
      overlay.query overlay.member
        ((overlay.root, inputOne), inputTwo)).1.target row =
      .inr (.inl
        ((profiledOpenFixedLeftQueryResponses A initialCode overlay.value
          overlay.query overlay.member
            ((overlay.root, inputOne), inputTwo)).2 row).1.1)
  have hinverse :
      profiledOpenHiddenDescriptorLeftRootOfEq A overlay.member.1 lane.source
          table hmove decodedRoot = overlay.root :=
    profiledOpenHiddenDescriptorLeftRootOfEq_rootToEq A initialCode
      overlay.member.1 lane.source table hmove overlay.root
  rw [← hinverse]
  have hat := congrFun hpast ((decodedRoot, inputOne), inputTwo)
  rw [hat]
  exact
    (profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A lane.source
      strategy hwin lane.realization.entry
        (fun member ↦ member.1.1.1.2) basis taggedPast decodedRoot
          (inputOne, inputTwo) row).1

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- If the literal right overlay prefix and its closing record admit a
winning continuation in the retained root's base monitor, the selected
closing target carries exactly the original-DPA minimum of the physical
records emitted by the overlay.  The continuation is proof-only; the finite
controller does not receive the retained root or the side. -/
theorem
    profiledOpenWitnessedRightClosingTargetPriority_eq_physicalBlockMin_of_winningExtension
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (root : ProfiledOpenRightRoot A)
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂)) (inputOne : In₁) (inputTwo : In₂)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hprefix : omegaPrefix play inputs.length =
      profiledOpenWitnessedRightOverlayBaseRecords A initialCode overlay
        inputs)
    (hcurrent : play inputs.length =
      profiledOpenWitnessedRightOverlayBaseRecord A initialCode
        (profiledOpenWitnessedRightRoundRecord A initialCode
          (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay
            inputs) inputOne inputTwo))
    (hwin : (profiledOpenRightRootMonitor.{u, v, x, y, s, 1} A root).WinsPlay
      play) :
    pairedProfiledEntryPriority A
        ((profiledOpenWitnessedRightRoundRecord A initialCode
          (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay
            inputs) inputOne inputTwo).2.1.1.target overlay.entryRow) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A overlay.entryRow root.1.1.1)
          (profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode
            overlay inputs)) := by
  have hpriority :=
    pairedProfiledEntryPriority_eq_rightPhysicalPrefixBlockMin_of_wins A
      root.1.1.1 root.1.1.2 root.1.2 play hwin inputs.length
        overlay.entryRow
  rw [hcurrent, hprefix] at hpriority
  simpa only [profiledOpenWitnessedRightOverlayBaseRecord,
    profiledOpenWitnessedRightOverlayBaseRecords,
    profiledRightPhysicalPrefixRecords,
    profiledOpenWitnessedRightOverlayPhysicalRecords, List.map_map,
    Function.comp_apply] using hpriority

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left installed-overlay mirror. -/
theorem
    profiledOpenWitnessedLeftClosingTargetPriority_eq_physicalBlockMin_of_winningExtension
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (root : ProfiledOpenLeftRoot A)
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputs : List (In₁ × In₂)) (inputOne : In₁) (inputTwo : In₂)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hprefix : omegaPrefix play inputs.length =
      profiledOpenWitnessedLeftOverlayBaseRecords A initialCode overlay inputs)
    (hcurrent : play inputs.length =
      profiledOpenWitnessedLeftOverlayBaseRecord A initialCode
        (profiledOpenWitnessedLeftRoundRecord A initialCode
          (profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay
            inputs) inputOne inputTwo))
    (hwin : (profiledOpenLeftRootMonitor.{u, v, x, y, s, 1} A root).WinsPlay
      play) :
    pairedProfiledEntryPriority A
        ((profiledOpenWitnessedLeftRoundRecord A initialCode
          (profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay
            inputs) inputOne inputTwo).2.1.1.target overlay.entryRow) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A overlay.entryRow root.1.1.1)
          (profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode
            overlay inputs)) := by
  have hpriority :=
    pairedProfiledEntryPriority_eq_leftPhysicalPrefixBlockMin_of_wins A
      root.1.1.1 root.1.1.2 root.1.2 play hwin inputs.length
        overlay.entryRow
  rw [hcurrent, hprefix] at hpriority
  simpa only [profiledOpenWitnessedLeftOverlayBaseRecord,
    profiledOpenWitnessedLeftOverlayBaseRecords,
    profiledLeftPhysicalPrefixRecords,
    profiledOpenWitnessedLeftOverlayPhysicalRecords, List.map_map,
    Function.comp_apply] using hpriority

/-! ## Classified boundary-root endpoints -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The strongest right endpoint used at a boundary: under the installed
overlay's retained semantic invariant and a winning base-monitor extension,
the *advertised next classified root* has exactly the minimum priority of the
literal physical prefix. -/
theorem
    profiledOpenWitnessedRightClosingRootPriority_eq_physicalBlockMin_of_winningExtension
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (root : ProfiledOpenRightRoot A)
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (hstart : overlay.SemanticallyReanchored A strategy hwin basis initialCode)
    (hrows : ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin
      basis initialCode overlay.value)
    (inputs : List (In₁ × In₂)) (inputOne : In₁) (inputTwo : In₂)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hprefix : omegaPrefix play inputs.length =
      profiledOpenWitnessedRightOverlayBaseRecords A initialCode overlay
        inputs)
    (hcurrent : play inputs.length =
      profiledOpenWitnessedRightOverlayBaseRecord A initialCode
        (profiledOpenWitnessedRightRoundRecord A initialCode
          (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay
            inputs) inputOne inputTwo))
    (hmonitorWin :
      (profiledOpenRightRootMonitor.{u, v, x, y, s, 1} A root).WinsPlay play) :
    profiledOpenClassifiedAnchorPriority A
        (.left
          ((profiledOpenWitnessedRightRoundRecord A initialCode
            (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay
              inputs) inputOne inputTwo).2.1.2 overlay.entryRow).1) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A overlay.entryRow root.1.1.1)
          (profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode
            overlay inputs)) := by
  let closingOverlay :=
    profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay inputs
  have hclosingSemantic : closingOverlay.SemanticallyReanchored A strategy
      hwin basis initialCode :=
    profiledOpenWitnessedRightRoundOverlayRun_semanticallyReanchored_of_hasRows
      A strategy hwin basis initialCode overlay hstart hrows inputs
  have htarget :=
    profiledOpenWitnessedRightRoundRecord_target_eq_classifiedRoot_of_semanticallyReanchored
      A strategy hwin basis initialCode closingOverlay hclosingSemantic
        inputOne inputTwo overlay.entryRow
  have hpriority :=
    profiledOpenWitnessedRightClosingTargetPriority_eq_physicalBlockMin_of_winningExtension
      A initialCode root overlay inputs inputOne inputTwo play hprefix hcurrent
        hmonitorWin
  rw [htarget] at hpriority
  simpa only [profiledOpenClassifiedAnchorPriority] using hpriority

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left classified-root endpoint. -/
theorem
    profiledOpenWitnessedLeftClosingRootPriority_eq_physicalBlockMin_of_winningExtension
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (root : ProfiledOpenLeftRoot A)
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (hstart : overlay.SemanticallyReanchored A strategy hwin basis initialCode)
    (hrows : ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
      initialCode overlay.value)
    (inputs : List (In₁ × In₂)) (inputOne : In₁) (inputTwo : In₂)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hprefix : omegaPrefix play inputs.length =
      profiledOpenWitnessedLeftOverlayBaseRecords A initialCode overlay inputs)
    (hcurrent : play inputs.length =
      profiledOpenWitnessedLeftOverlayBaseRecord A initialCode
        (profiledOpenWitnessedLeftRoundRecord A initialCode
          (profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay
            inputs) inputOne inputTwo))
    (hmonitorWin :
      (profiledOpenLeftRootMonitor.{u, v, x, y, s, 1} A root).WinsPlay play) :
    profiledOpenClassifiedAnchorPriority A
        (.right
          ((profiledOpenWitnessedLeftRoundRecord A initialCode
            (profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay
              inputs) inputOne inputTwo).2.1.2 overlay.entryRow).1) =
      A.priority
        (blockMinState A
          (pairedCodeStateForRow A overlay.entryRow root.1.1.1)
          (profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode
            overlay inputs)) := by
  let closingOverlay :=
    profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay inputs
  have hclosingSemantic : closingOverlay.SemanticallyReanchored A strategy
      hwin basis initialCode :=
    profiledOpenWitnessedLeftRoundOverlayRun_semanticallyReanchored_of_hasRows
      A strategy hwin basis initialCode overlay hstart hrows inputs
  have htarget :=
    profiledOpenWitnessedLeftRoundRecord_target_eq_classifiedRoot_of_semanticallyReanchored
      A strategy hwin basis initialCode closingOverlay hclosingSemantic
        inputOne inputTwo overlay.entryRow
  have hpriority :=
    profiledOpenWitnessedLeftClosingTargetPriority_eq_physicalBlockMin_of_winningExtension
      A initialCode root overlay inputs inputOne inputTwo play hprefix hcurrent
        hmonitorWin
  rw [htarget] at hpriority
  simpa only [profiledOpenClassifiedAnchorPriority] using hpriority

end

end DetParityAutomaton

end DistributedSynthesis
