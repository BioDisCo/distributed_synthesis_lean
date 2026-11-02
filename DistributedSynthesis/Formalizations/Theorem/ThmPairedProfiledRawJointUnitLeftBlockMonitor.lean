/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFinitePolicyAllowedTargetBlockMonitor
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPhysicalPolicyClose
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledBlockMonitor

/-!
# The singleton raw-joint left-block controller

This is the fail-fast integration test for the finite-code policy route.  At
one reachable process-two/left state, one installed raw joint move supplies
the physical lambda.  Each physical close emits a state in the finite image
of the *same* rational policy.  A finite block monitor checks simultaneously:

* the universal two-row parity objective;
* the exact paired scan and physical closing target;
* the initial and delayed boundary-action profiles; and
* membership of every emitted target in the fixed policy image.

The left/right orientation and the `Unit` lineage are proof-tree data.  They
are not arguments of either local block strategy.  In particular, this file
does not assume that a process knows which side is the strict leader.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## One installed left-block activation -/

/-- One lambda and its complete finite-policy target table at a reachable
left-live state.  The target table is proof-side certificate data emitted by
the full-information receiver; it is not observable by the blind sender. -/
structure ProfiledRawJointUnitLeftBlockActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (source : ProfiledRawLeftSlot A) where
  lambda : ProcTwoPairedLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  lambda_selected : move.leftLambda () = some lambda
  initial_profile : leftInitialFirstProfile lambda = source.2
  forever : PairedLeftForeverAccepts A source.1.1 lambda
  target : PairedEntryRow → List (In₁ × In₂) → In₁ × In₂ →
    ProfiledRawJointOneSidedProvenancePolicyState A strategy initialCode
  target_allowed : ∀ row past input,
    ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy initialCode
      policy state (target row past input)
  target_active_slot : ∀ row past input,
    (target row past input).1.family.right () =
      some (profiledRawLeftChildSlot A source lambda row past input)

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The monitor-facing close packages assemble into one activation.  A seed
package fixes the one selected lambda; all other package lambdas equal it
because they are selected by the same `move.leftLambda ()`. -/
theorem nonempty_profiledRawJointUnitLeftBlockActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      (initial.code A))
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedFiniteCodeNext A)
      policy state)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (hmove : ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
      (initial.code A) policy state move)
    (source : ProfiledRawLeftSlot A)
    (hsource : state.1.family.left () = some source) :
    Nonempty (ProfiledRawJointUnitLeftBlockActivation A strategy
      (initial.code A) policy state move source) := by
  classical
  let seed := Classical.choice
    (nonempty_profiledRawJointUnitLeftPhysicalClosePackage A strategy initial
      policy state hreachable move hmove source hsource .first [] default)
  let packageAt := fun row past input ↦ Classical.choice
    (nonempty_profiledRawJointUnitLeftPhysicalClosePackage A strategy initial
      policy state hreachable move hmove source hsource row past input)
  refine ⟨{
    lambda := seed.lambda
    lambda_selected := seed.lambda_selected
    initial_profile := seed.initial_profile
    forever := seed.forever
    target := fun row past input ↦ (packageAt row past input).target
    target_allowed := ?_
    target_active_slot := ?_ }⟩
  · intro row past input
    exact (packageAt row past input).allowed
  · intro row past input
    have hlambda : (packageAt row past input).lambda = seed.lambda := by
      exact Option.some.inj
        ((packageAt row past input).lambda_selected.symm.trans
          seed.lambda_selected)
    simpa [hlambda] using (packageAt row past input).active_slot

/-! ## Certificate output and finite target projection -/

/-- Receiver output for the raw-joint left monitor. -/
abbrev ProfiledRawJointUnitLeftReceiverOutput
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit)) :=
  IndexedTargetReceiverOutput
    (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow
    (ProfiledRawJointOneSidedProvenancePolicyState A strategy initialCode)

/-- The policy-state alphabet has the canonical root control as an inhabitant.
This instance is needed only by the generic sender-narrowing readback. -/
noncomputable instance profiledRawJointOneSidedProvenancePolicyStateInhabitedLeft
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)} :
    Inhabited (ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode) :=
  ⟨(initialCode,
    (profiledRawJointOneSidedCodeParityDPA A initialCode).initial)⟩

/-- Read the active singleton right slot of a policy target as an ordinary
profiled entry state.  Missing slots map to the harmless initial constructor;
the monitor rejects such a target whenever a physical close is expected. -/
def profiledRawJointUnitLeftTargetProfiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode) : PairedProfiledTreeState A :=
  match target.1.family.right () with
  | some slot => .inr (.inl slot)
  | none => .inl PUnit.unit

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointUnitLeftTargetProfiledState_eq_of_active_slot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (slot : ProfiledRawRightSlot A)
    (hslot : target.1.family.right () = some slot) :
    profiledRawJointUnitLeftTargetProfiledState A target =
      .inr (.inl slot) := by
  simp [profiledRawJointUnitLeftTargetProfiledState, hslot]

/-- Physical projection of one raw-joint left certificate letter. -/
def profiledRawJointUnitLeftPhysicalLetter
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (letter : RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂) :
    PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  indexedTargetPhysicalLetter letter

/-! ## The finite left-block monitor -/

/-- Left recurrent monitor at one fixed finite-policy source. -/
noncomputable def profiledRawJointUnitLeftBlockMonitor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (source : ProfiledRawLeftSlot A) :
    BlockRecordMonitor In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) Out₂ := by
  classical
  let U := (pairedLeftThreadSystem A source.1.1).universalRunDPA
  exact {
    State := ProfiledLeftBlockMonitorState A U.State
    stateFinite := inferInstance
    initial := (U.initial, pairedLeftScanInitial A source.1.1,
      fun _ ↦ none, true, true)
    step := fun monitorState letter ↦
      let physical := profiledRawJointUnitLeftPhysicalLetter A letter
      let rootMatches := !monitorState.2.2.2.1 ||
        decide (pairedLeftInformedForRow .first letter.2.1.physical =
          source.2 letter.1)
      let overlaps := ∀ row expected,
        monitorState.2.2.1 row = some expected →
          pairedLeftClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A
            (profiledRawJointUnitLeftTargetProfiledState A
              (letter.2.1.target row)) =
          pairedLeftCloseTarget A monitorState.2.1 row physical ∧
        ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
          initialCode policy state (letter.2.1.target row)
      (U.step monitorState.1 physical,
        pairedLeftScanStep A monitorState.2.1 physical,
        fun row ↦ rightProfileOfProfiledState A
          (profiledRawJointUnitLeftTargetProfiledState A
            (letter.2.1.target row)),
        false,
        monitorState.2.2.2.2 && rootMatches &&
          decide overlaps && decide targetsSafe)
    priority := fun monitorState ↦
      if monitorState.2.2.2.2 then U.priority monitorState.1 + 2 else 1
  }

/-! ## Exact semantic certificate stream -/

/-- Full-information receiver induced by one installed activation. -/
def profiledRawJointUnitLeftReceiverStrategy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source) :
    ReceiverBlockStrategy In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy initialCode) :=
  fun past input ↦ {
    physical := pairedLeftReceiverStrategy activation.lambda past input
    target := fun row ↦ activation.target row past input }

section
omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂]

@[simp] theorem profiledRawJointUnitLeftReceiverStrategy_physical
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    (profiledRawJointUnitLeftReceiverStrategy A activation past input).physical =
      pairedLeftReceiverStrategy activation.lambda past input := rfl

theorem profiledRawJointUnitLeftReceiverStrategy_target_profile
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    rightProfileOfProfiledState A
        (profiledRawJointUnitLeftTargetProfiledState A
          ((profiledRawJointUnitLeftReceiverStrategy A activation past input).target
            row)) =
      some (leftClosingProfile activation.lambda row past input) := by
  rw [profiledRawJointUnitLeftReceiverStrategy]
  rw [profiledRawJointUnitLeftTargetProfiledState_eq_of_active_slot A
    (activation.target row past input)
    (profiledRawLeftChildSlot A source activation.lambda row past input)
    (activation.target_active_slot row past input)]
  rfl

/-- The semantic enriched play has the expected literal letter. -/
theorem profiledRawJointUnitLeft_pairPlay_eq_letterAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source)
    (env : Nat → In₁ × In₂) (n : Nat) :
    pairPlay (profiledRawJointUnitLeftReceiverStrategy A activation)
        (pairedLeftSenderStrategy activation.lambda) env n =
      (env n,
        profiledRawJointUnitLeftReceiverStrategy A activation
          (omegaPrefix env n) (env n),
        activation.lambda.blind (senderWord (omegaPrefix env n)) (env n).2) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, pairedLeftSenderStrategy, senderWord, omegaPrefix]

/-- Erasing finite-policy certificates gives the ordinary paired block word. -/
theorem profiledRawJointUnitLeft_pairPlay_physical
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source)
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointUnitLeftPhysicalLetter A
        (pairPlay (profiledRawJointUnitLeftReceiverStrategy A activation)
          (pairedLeftSenderStrategy activation.lambda) env n) =
      pairedLeftBlockWord activation.lambda env n := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, profiledRawJointUnitLeftPhysicalLetter,
    indexedTargetPhysicalLetter, profiledRawJointUnitLeftReceiverStrategy,
    pairedLeftReceiverStrategy, pairedLeftSenderStrategy,
    pairedLeftBlockWord, pairedLeftBlockLetterAt, senderWord, omegaPrefix]

end

/-! ## Monitor realization -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact raw-joint certificate stream has the expected finite monitor
run. -/
theorem profiledRawJointUnitLeftBlockMonitor_run_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source)
    (env : Nat → In₁ × In₂) : ∀ n,
    (profiledRawJointUnitLeftBlockMonitor A strategy initialCode policy state
      source).run
        (pairPlay (profiledRawJointUnitLeftReceiverStrategy A activation)
          (pairedLeftSenderStrategy activation.lambda) env) n =
      ((pairedLeftThreadSystem A source.1.1).universalRunDPA.run
          (pairedLeftBlockWord activation.lambda env) n,
        pairedLeftScanAfter A source.1.1 activation.lambda
          (omegaPrefix env n),
        profiledLeftPendingAfter activation.lambda (omegaPrefix env n),
        decide (n = 0), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        profiledRawJointUnitLeft_pairPlay_eq_letterAt A activation env n,
        omegaPrefix_succ, pairedLeftScanAfter_append,
        profiledLeftPendingAfter_append]
      have hoverlaps : ∀ row expected,
          profiledLeftPendingAfter activation.lambda (omegaPrefix env n) row =
              some expected →
            pairedLeftClosingForRow row
                (profiledRawJointUnitLeftReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).physical =
              expected ((env n).2, (env n).1) := by
        simpa [profiledRawJointUnitLeftReceiverStrategy,
          profiledLeftReceiverStrategy] using
          (profiledLeftPendingAfter_realizes A source.1.1 activation.lambda
            (omegaPrefix env n) (env n))
      have htargets : ∀ row,
          erasePairedProfiledState A
              (profiledRawJointUnitLeftTargetProfiledState A
                ((profiledRawJointUnitLeftReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).target row)) =
            pairedLeftCloseTarget A
              (pairedLeftScanAfter A source.1.1 activation.lambda
                (omegaPrefix env n)) row
              (pairedLeftBlockLetterAt activation.lambda
                (omegaPrefix env n) (env n)) ∧
          ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
            initialCode policy state
              ((profiledRawJointUnitLeftReceiverStrategy A activation
                (omegaPrefix env n) (env n)).target row) := by
        intro row
        constructor
        · rw [profiledRawJointUnitLeftReceiverStrategy]
          rw [profiledRawJointUnitLeftTargetProfiledState_eq_of_active_slot A
            (activation.target row (omegaPrefix env n) (env n))
            (profiledRawLeftChildSlot A source activation.lambda row
              (omegaPrefix env n) (env n))
            (activation.target_active_slot row (omegaPrefix env n) (env n))]
          rw [← pairedProfiledTwoChild_eq_profiledRawLeftChildSlot A source
            activation.lambda row (omegaPrefix env n) (env n),
            erase_pairedProfiledTwoChild,
            pairedLeftCloseTarget_scanAfter]
        · exact activation.target_allowed row (omegaPrefix env n) (env n)
      have hphysicalAt :
          profiledRawJointUnitLeftPhysicalLetter A
              (env n,
                profiledRawJointUnitLeftReceiverStrategy A activation
                  (omegaPrefix env n) (env n),
                activation.lambda.blind
                  (senderWord (omegaPrefix env n)) (env n).2) =
            pairedLeftBlockLetterAt activation.lambda
              (omegaPrefix env n) (env n) := rfl
      simp only [profiledRawJointUnitLeftBlockMonitor]
      rw [hphysicalAt, decide_eq_true hoverlaps, decide_eq_true htargets]
      change
        ((pairedLeftThreadSystem A source.1.1).universalRunDPA.step
            ((pairedLeftThreadSystem A source.1.1).universalRunDPA.run
              (pairedLeftBlockWord activation.lambda env) n)
            (pairedLeftBlockWord activation.lambda env n), _, _, _, _) = _
      by_cases hn : n = 0
      · subst n
        have hroot :
            pairedLeftInformedForRow .first
                (pairedLeftReceiverStrategy activation.lambda [] (env 0)) =
              source.2 (env 0) := by
          simpa [leftInitialFirstProfile] using
            congrFun activation.initial_profile (env 0)
        simp [omegaPrefix, hroot,
          profiledRawJointUnitLeftReceiverStrategy_target_profile]
      · simp [hn,
          profiledRawJointUnitLeftReceiverStrategy_target_profile]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The installed semantic left block realizes the complete finite monitor. -/
theorem profiledRawJointUnitLeftBlockMonitor_realizable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointUnitLeftBlockActivation A strategy
      initialCode policy state move source) :
    ∀ env : Nat → In₁ × In₂,
      (profiledRawJointUnitLeftBlockMonitor A strategy initialCode policy state
        source).WinsPlay
        (pairPlay (profiledRawJointUnitLeftReceiverStrategy A activation)
          (pairedLeftSenderStrategy activation.lambda) env) := by
  intro env
  have huniversal := pairedLeftUniversalDPA_accepts_of_forever
    A source.1.1 activation.lambda activation.forever env
  have hparity : NatSeqMinEvenParity
      (fun n ↦
        (pairedLeftThreadSystem A source.1.1).universalRunDPA.priority
          ((pairedLeftThreadSystem A source.1.1).universalRunDPA.run
            (pairedLeftBlockWord activation.lambda env) n)) := huniversal
  have hshifted : NatSeqMinEvenParity
      (fun n ↦
        (pairedLeftThreadSystem A source.1.1).universalRunDPA.priority
          ((pairedLeftThreadSystem A source.1.1).universalRunDPA.run
            (pairedLeftBlockWord activation.lambda env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hparity
  unfold BlockRecordMonitor.WinsPlay
  convert hshifted using 1
  funext n
  rw [profiledRawJointUnitLeftBlockMonitor_run_eq A policy state source
    activation env n]
  simp [profiledRawJointUnitLeftBlockMonitor]
  rfl

/-! ## Unconditional finite left controller -/

/-- A reachable installed left-live state has an unconditional finite
sender-narrowed controller whose every emitted target is checked against the
one fixed finite-code policy. -/
theorem exists_profiledRawJointUnitLeftController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      (initial.code A))
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedFiniteCodeNext A)
      policy state)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (hmove : ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
      (initial.code A) policy state move)
    (source : ProfiledRawLeftSlot A)
    (hsource : state.1.family.left () = some source) :
    ∃ controller :
        TransitionRationalTree.{v, max u v x y s, max u v x y s} In₂
        (NarrowedBlockLabel In₁ In₂
          (ProfiledRawJointUnitLeftReceiverOutput A strategy (initial.code A))
          Out₂
          (profiledRawJointUnitLeftBlockMonitor A strategy (initial.code A)
            policy state source).State),
      NarrowedAllThreadsWin
        (profiledRawJointUnitLeftBlockMonitor A strategy (initial.code A)
          policy state source) controller.labeledTree := by
  let activation := Classical.choice
    (nonempty_profiledRawJointUnitLeftBlockActivation A strategy initial policy
      state hreachable move hmove source hsource)
  have hrealizable :
      ∃ receiver : ReceiverBlockStrategy In₁ In₂
          (ProfiledRawJointUnitLeftReceiverOutput A strategy (initial.code A)),
        ∃ sender : SenderBlockStrategy In₂ Out₂,
          ∀ env : Nat → In₁ × In₂,
            (profiledRawJointUnitLeftBlockMonitor A strategy (initial.code A)
              policy state source).WinsPlay
              (pairPlay receiver sender env) := by
    exact ⟨profiledRawJointUnitLeftReceiverStrategy A activation,
      pairedLeftSenderStrategy activation.lambda,
      profiledRawJointUnitLeftBlockMonitor_realizable A policy state source
        activation⟩
  exact (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointUnitLeftBlockMonitor A strategy (initial.code A)
      policy state source)).mp hrealizable

end

end DetParityAutomaton

end DistributedSynthesis
