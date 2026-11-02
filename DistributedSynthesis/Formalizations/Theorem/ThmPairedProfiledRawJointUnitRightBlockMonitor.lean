/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFinitePolicyAllowedTargetBlockMonitor
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPhysicalPolicyClose
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledBlockMonitor

/-!
# The singleton raw-joint right-block controller

This is the fail-fast integration test for the finite-code policy route.  At
one reachable process-one/right state, one installed raw joint move supplies
the physical lambda.  Each physical close emits a state in the finite image
of the *same* rational policy.  A finite block monitor checks simultaneously:

* the universal two-row parity objective;
* the exact paired scan and physical closing target;
* the initial and delayed boundary-action profiles; and
* membership of every emitted target in the fixed policy image.

The right/left orientation and the `Unit` lineage are proof-tree data.  They
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

/-! ## One installed right-block activation -/

/-- One lambda and its complete finite-policy target table at a reachable
right-live state.  The target table is proof-side certificate data emitted by
the full-information receiver; it is not observable by the blind sender. -/
structure ProfiledRawJointUnitRightBlockActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (source : ProfiledRawRightSlot A) where
  lambda : ProcOnePairedRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  lambda_selected : move.rightLambda () = some lambda
  initial_profile : rightInitialFirstProfile lambda = source.2
  forever : PairedRightForeverAccepts A source.1.1 lambda
  target : PairedEntryRow → List (In₂ × In₁) → In₂ × In₁ →
    ProfiledRawJointOneSidedProvenancePolicyState A strategy initialCode
  target_allowed : ∀ row past input,
    ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy initialCode
      policy state (target row past input)
  target_active_slot : ∀ row past input,
    (target row past input).1.family.left () =
      some (profiledRawRightChildSlot A source lambda row past input)

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The monitor-facing close packages assemble into one activation.  A seed
package fixes the one selected lambda; all other package lambdas equal it
because they are selected by the same `move.rightLambda ()`. -/
theorem nonempty_profiledRawJointUnitRightBlockActivation
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
    (source : ProfiledRawRightSlot A)
    (hsource : state.1.family.right () = some source) :
    Nonempty (ProfiledRawJointUnitRightBlockActivation A strategy
      (initial.code A) policy state move source) := by
  classical
  let seed := Classical.choice
    (nonempty_profiledRawJointUnitRightPhysicalClosePackage A strategy initial
      policy state hreachable move hmove source hsource .first [] default)
  let packageAt := fun row past input ↦ Classical.choice
    (nonempty_profiledRawJointUnitRightPhysicalClosePackage A strategy initial
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

/-- Receiver output for the raw-joint right monitor. -/
abbrev ProfiledRawJointUnitRightReceiverOutput
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit)) :=
  IndexedTargetReceiverOutput
    (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow
    (ProfiledRawJointOneSidedProvenancePolicyState A strategy initialCode)

/-- The policy-state alphabet has the canonical root control as an inhabitant.
This instance is needed only by the generic sender-narrowing readback. -/
noncomputable instance profiledRawJointOneSidedProvenancePolicyStateInhabited
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)} :
    Inhabited (ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode) :=
  ⟨(initialCode,
    (profiledRawJointOneSidedCodeParityDPA A initialCode).initial)⟩

/-- Read the active singleton left slot of a policy target as an ordinary
profiled entry state.  Missing slots map to the harmless initial constructor;
the monitor rejects such a target whenever a physical close is expected. -/
def profiledRawJointUnitRightTargetProfiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode) : PairedProfiledTreeState A :=
  match target.1.family.left () with
  | some slot => .inr (.inr slot)
  | none => .inl PUnit.unit

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointUnitRightTargetProfiledState_eq_of_active_slot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (slot : ProfiledRawLeftSlot A)
    (hslot : target.1.family.left () = some slot) :
    profiledRawJointUnitRightTargetProfiledState A target =
      .inr (.inr slot) := by
  simp [profiledRawJointUnitRightTargetProfiledState, hslot]

/-- Physical projection of one raw-joint right certificate letter. -/
def profiledRawJointUnitRightPhysicalLetter
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (letter : RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁) :
    PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  indexedTargetPhysicalLetter letter

/-! ## The finite right-block monitor -/

/-- Right recurrent monitor at one fixed finite-policy source. -/
noncomputable def profiledRawJointUnitRightBlockMonitor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (source : ProfiledRawRightSlot A) :
    BlockRecordMonitor In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) Out₁ := by
  classical
  let U := (pairedRightThreadSystem A source.1.1).universalRunDPA
  exact {
    State := ProfiledRightBlockMonitorState A U.State
    stateFinite := inferInstance
    initial := (U.initial, pairedRightScanInitial A source.1.1,
      fun _ ↦ none, true, true)
    step := fun monitorState letter ↦
      let physical := profiledRawJointUnitRightPhysicalLetter A letter
      let rootMatches := !monitorState.2.2.2.1 ||
        decide (pairedRightInformedForRow .first letter.2.1.physical =
          source.2 letter.1)
      let overlaps := ∀ row expected,
        monitorState.2.2.1 row = some expected →
          pairedRightClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A
            (profiledRawJointUnitRightTargetProfiledState A
              (letter.2.1.target row)) =
          pairedRightCloseTarget A monitorState.2.1 row physical ∧
        ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
          initialCode policy state (letter.2.1.target row)
      (U.step monitorState.1 physical,
        pairedRightScanStep A monitorState.2.1 physical,
        fun row ↦ leftProfileOfProfiledState A
          (profiledRawJointUnitRightTargetProfiledState A
            (letter.2.1.target row)),
        false,
        monitorState.2.2.2.2 && rootMatches &&
          decide overlaps && decide targetsSafe)
    priority := fun monitorState ↦
      if monitorState.2.2.2.2 then U.priority monitorState.1 + 2 else 1
  }

/-! ## Exact semantic certificate stream -/

/-- Full-information receiver induced by one installed activation. -/
def profiledRawJointUnitRightReceiverStrategy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointUnitRightBlockActivation A strategy
      initialCode policy state move source) :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy initialCode) :=
  fun past input ↦ {
    physical := pairedRightReceiverStrategy activation.lambda past input
    target := fun row ↦ activation.target row past input }

section
omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂]

@[simp] theorem profiledRawJointUnitRightReceiverStrategy_physical
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointUnitRightBlockActivation A strategy
      initialCode policy state move source)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    (profiledRawJointUnitRightReceiverStrategy A activation past input).physical =
      pairedRightReceiverStrategy activation.lambda past input := rfl

theorem profiledRawJointUnitRightReceiverStrategy_target_profile
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointUnitRightBlockActivation A strategy
      initialCode policy state move source)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    leftProfileOfProfiledState A
        (profiledRawJointUnitRightTargetProfiledState A
          ((profiledRawJointUnitRightReceiverStrategy A activation past input).target
            row)) =
      some (rightClosingProfile activation.lambda row past input) := by
  rw [profiledRawJointUnitRightReceiverStrategy]
  rw [profiledRawJointUnitRightTargetProfiledState_eq_of_active_slot A
    (activation.target row past input)
    (profiledRawRightChildSlot A source activation.lambda row past input)
    (activation.target_active_slot row past input)]
  rfl

/-- The semantic enriched play has the expected literal letter. -/
theorem profiledRawJointUnitRight_pairPlay_eq_letterAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointUnitRightBlockActivation A strategy
      initialCode policy state move source)
    (env : Nat → In₂ × In₁) (n : Nat) :
    pairPlay (profiledRawJointUnitRightReceiverStrategy A activation)
        (pairedRightSenderStrategy activation.lambda) env n =
      (env n,
        profiledRawJointUnitRightReceiverStrategy A activation
          (omegaPrefix env n) (env n),
        activation.lambda.blind (senderWord (omegaPrefix env n)) (env n).2) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, pairedRightSenderStrategy, senderWord, omegaPrefix]

/-- Erasing finite-policy certificates gives the ordinary paired block word. -/
theorem profiledRawJointUnitRight_pairPlay_physical
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    {state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode}
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointUnitRightBlockActivation A strategy
      initialCode policy state move source)
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointUnitRightPhysicalLetter A
        (pairPlay (profiledRawJointUnitRightReceiverStrategy A activation)
          (pairedRightSenderStrategy activation.lambda) env n) =
      pairedRightBlockWord activation.lambda env n := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, profiledRawJointUnitRightPhysicalLetter,
    indexedTargetPhysicalLetter, profiledRawJointUnitRightReceiverStrategy,
    pairedRightReceiverStrategy, pairedRightSenderStrategy,
    pairedRightBlockWord, senderWord, omegaPrefix]

end

/-! ## Monitor realization -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact raw-joint certificate stream has the expected finite monitor
run. -/
theorem profiledRawJointUnitRightBlockMonitor_run_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointUnitRightBlockActivation A strategy
      initialCode policy state move source)
    (env : Nat → In₂ × In₁) : ∀ n,
    (profiledRawJointUnitRightBlockMonitor A strategy initialCode policy state
      source).run
        (pairPlay (profiledRawJointUnitRightReceiverStrategy A activation)
          (pairedRightSenderStrategy activation.lambda) env) n =
      ((pairedRightThreadSystem A source.1.1).universalRunDPA.run
          (pairedRightBlockWord activation.lambda env) n,
        pairedRightScanAfter A source.1.1 activation.lambda
          (omegaPrefix env n),
        profiledRightPendingAfter activation.lambda (omegaPrefix env n),
        decide (n = 0), true) := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih,
        profiledRawJointUnitRight_pairPlay_eq_letterAt A activation env n,
        omegaPrefix_succ, pairedRightScanAfter_append,
        profiledRightPendingAfter_append]
      have hoverlaps : ∀ row expected,
          profiledRightPendingAfter activation.lambda (omegaPrefix env n) row =
              some expected →
            pairedRightClosingForRow row
                (profiledRawJointUnitRightReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).physical =
              expected ((env n).2, (env n).1) := by
        simpa [profiledRawJointUnitRightReceiverStrategy,
          profiledRightReceiverStrategy] using
          (profiledRightPendingAfter_realizes A source.1.1 activation.lambda
            (omegaPrefix env n) (env n))
      have htargets : ∀ row,
          erasePairedProfiledState A
              (profiledRawJointUnitRightTargetProfiledState A
                ((profiledRawJointUnitRightReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).target row)) =
            pairedRightCloseTarget A
              (pairedRightScanAfter A source.1.1 activation.lambda
                (omegaPrefix env n)) row
              (pairedRightBlockLetterAt activation.lambda
                (omegaPrefix env n) (env n)) ∧
          ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
            initialCode policy state
              ((profiledRawJointUnitRightReceiverStrategy A activation
                (omegaPrefix env n) (env n)).target row) := by
        intro row
        constructor
        · rw [profiledRawJointUnitRightReceiverStrategy]
          rw [profiledRawJointUnitRightTargetProfiledState_eq_of_active_slot A
            (activation.target row (omegaPrefix env n) (env n))
            (profiledRawRightChildSlot A source activation.lambda row
              (omegaPrefix env n) (env n))
            (activation.target_active_slot row (omegaPrefix env n) (env n))]
          rw [← pairedProfiledOneChild_eq_profiledRawRightChildSlot A source
            activation.lambda row (omegaPrefix env n) (env n),
            erase_pairedProfiledOneChild,
            pairedRightCloseTarget_scanAfter]
        · exact activation.target_allowed row (omegaPrefix env n) (env n)
      have hphysicalAt :
          profiledRawJointUnitRightPhysicalLetter A
              (env n,
                profiledRawJointUnitRightReceiverStrategy A activation
                  (omegaPrefix env n) (env n),
                activation.lambda.blind
                  (senderWord (omegaPrefix env n)) (env n).2) =
            pairedRightBlockLetterAt activation.lambda
              (omegaPrefix env n) (env n) := rfl
      simp only [profiledRawJointUnitRightBlockMonitor]
      rw [hphysicalAt, decide_eq_true hoverlaps, decide_eq_true htargets]
      rw [← pairedRightBlockWord_eq_letterAt activation.lambda env n]
      by_cases hn : n = 0
      · subst n
        have hroot :
            pairedRightInformedForRow .first
                (pairedRightReceiverStrategy activation.lambda [] (env 0)) =
              source.2 (env 0) := by
          simpa [rightInitialFirstProfile] using
            congrFun activation.initial_profile (env 0)
        simp [omegaPrefix, hroot,
          profiledRawJointUnitRightReceiverStrategy_target_profile]
      · simp [hn,
          profiledRawJointUnitRightReceiverStrategy_target_profile]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The installed semantic right block realizes the complete finite monitor. -/
theorem profiledRawJointUnitRightBlockMonitor_realizable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    {move : ProfiledRawJointLambdaFamilyMove A (I := Unit)}
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointUnitRightBlockActivation A strategy
      initialCode policy state move source) :
    ∀ env : Nat → In₂ × In₁,
      (profiledRawJointUnitRightBlockMonitor A strategy initialCode policy state
        source).WinsPlay
        (pairPlay (profiledRawJointUnitRightReceiverStrategy A activation)
          (pairedRightSenderStrategy activation.lambda) env) := by
  intro env
  have huniversal := pairedRightUniversalDPA_accepts_of_forever
    A source.1.1 activation.lambda activation.forever env
  have hparity : NatSeqMinEvenParity
      (fun n ↦
        (pairedRightThreadSystem A source.1.1).universalRunDPA.priority
          ((pairedRightThreadSystem A source.1.1).universalRunDPA.run
            (pairedRightBlockWord activation.lambda env) n)) := huniversal
  have hshifted : NatSeqMinEvenParity
      (fun n ↦
        (pairedRightThreadSystem A source.1.1).universalRunDPA.priority
          ((pairedRightThreadSystem A source.1.1).universalRunDPA.run
            (pairedRightBlockWord activation.lambda env) n) + 2) :=
    (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hparity
  unfold BlockRecordMonitor.WinsPlay
  convert hshifted using 1
  funext n
  rw [profiledRawJointUnitRightBlockMonitor_run_eq A policy state source
    activation env n]
  simp [profiledRawJointUnitRightBlockMonitor]
  rfl

/-! ## Unconditional finite right controller -/

/-- A reachable installed right-live state has an unconditional finite
sender-narrowed controller whose every emitted target is checked against the
one fixed finite-code policy. -/
theorem exists_profiledRawJointUnitRightController
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
    (source : ProfiledRawRightSlot A)
    (hsource : state.1.family.right () = some source) :
    ∃ controller :
        TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
        (NarrowedBlockLabel In₂ In₁
          (ProfiledRawJointUnitRightReceiverOutput A strategy (initial.code A))
          Out₁
          (profiledRawJointUnitRightBlockMonitor A strategy (initial.code A)
            policy state source).State),
      NarrowedAllThreadsWin
        (profiledRawJointUnitRightBlockMonitor A strategy (initial.code A)
          policy state source) controller.labeledTree := by
  let activation := Classical.choice
    (nonempty_profiledRawJointUnitRightBlockActivation A strategy initial policy
      state hreachable move hmove source hsource)
  have hrealizable :
      ∃ receiver : ReceiverBlockStrategy In₂ In₁
          (ProfiledRawJointUnitRightReceiverOutput A strategy (initial.code A)),
        ∃ sender : SenderBlockStrategy In₁ Out₁,
          ∀ env : Nat → In₂ × In₁,
            (profiledRawJointUnitRightBlockMonitor A strategy (initial.code A)
              policy state source).WinsPlay
              (pairPlay receiver sender env) := by
    exact ⟨profiledRawJointUnitRightReceiverStrategy A activation,
      pairedRightSenderStrategy activation.lambda,
      profiledRawJointUnitRightBlockMonitor_realizable A policy state source
        activation⟩
  exact (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointUnitRightBlockMonitor A strategy (initial.code A)
      policy state source)).mp hrealizable

end

end DetParityAutomaton

end DistributedSynthesis
