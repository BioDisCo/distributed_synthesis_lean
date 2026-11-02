/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedFirstBlockActivation
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitLeftBlockMonitor

/-!
# The root-pinned exceptional left-block controller

The first recurrent left block differs from the ordinary fixed-policy block
in exactly one respect: its source move is the one-shot root-pinned move.  Its
receiver therefore emits the finite literal-child code of the semantic source
which provenance selected for that installed move.  The output alphabet is a
subtype, so every controller-visible target is a genuine raw child; the
semantic realizing receiver emits the child of the concrete physical row,
past, and input definitionally.

The sticky monitor checks the same physical scan, two-row parity, erased
closing target, and delayed profile coupling as the recurrent monitor.  Once
the block closes, the literal-child code indexes the fresh ordinary policy
bank from `LemPairedProfiledRawJointGuardedFirstPolicyBank`.

No side or strict-leader signal occurs in either local strategy.
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

/-! ## Finite target alphabet and projections -/

abbrev ProfiledRawJointGuardedFirstLeftReceiverOutput
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred) :=
  IndexedTargetReceiverOutput
    (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow
    (ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
        package))

/-- Project the live process-two slot carried by a literal child code. -/
def profiledRawJointGuardedFirstLeftTargetProfiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (target : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
        package)) : PairedProfiledTreeState A :=
  match target.1.family.right () with
  | some slot => .inr (.inl slot)
  | none => .inl PUnit.unit

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointGuardedFirstLeftTargetProfiledState_eq_of_active_slot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (target : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
        package))
    (slot : ProfiledRawRightSlot A)
    (hslot : target.1.family.right () = some slot) :
    profiledRawJointGuardedFirstLeftTargetProfiledState A target =
      .inr (.inl slot) := by
  simp [profiledRawJointGuardedFirstLeftTargetProfiledState, hslot]

/-- Forget the literal-child certificate from one realized letter. -/
def profiledRawJointGuardedFirstLeftPhysicalLetter
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (letter : RealizedBlockRound In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂) :
    PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  indexedTargetPhysicalLetter letter

/-! ## Sticky exceptional monitor -/

/-- The exceptional left monitor.  Literal-child membership is enforced by
the finite target type itself; the sticky predicate checks that its profiled
projection is the physical close selected at the current row. -/
noncomputable def profiledRawJointGuardedFirstLeftBlockMonitor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A) :
    BlockRecordMonitor In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) Out₂ := by
  classical
  let U := (pairedLeftThreadSystem A source.1.1).universalRunDPA
  exact {
    State := ProfiledLeftBlockMonitorState A U.State
    stateFinite := inferInstance
    initial := (U.initial, pairedLeftScanInitial A source.1.1,
      fun _ ↦ none, true, true)
    step := fun monitorState letter ↦
      let physical := profiledRawJointGuardedFirstLeftPhysicalLetter A letter
      let rootMatches := !monitorState.2.2.2.1 ||
        decide (pairedLeftInformedForRow .first letter.2.1.physical =
          source.2 letter.1)
      let overlaps := ∀ row expected,
        monitorState.2.2.1 row = some expected →
          pairedLeftClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A
            (profiledRawJointGuardedFirstLeftTargetProfiledState A
              (letter.2.1.target row)) =
          pairedLeftCloseTarget A monitorState.2.1 row physical
      (U.step monitorState.1 physical,
        pairedLeftScanStep A monitorState.2.1 physical,
        fun row ↦ rightProfileOfProfiledState A
          (profiledRawJointGuardedFirstLeftTargetProfiledState A
            (letter.2.1.target row)),
        false,
        monitorState.2.2.2.2 && rootMatches &&
          decide overlaps && decide targetsSafe)
    priority := fun monitorState ↦
      if monitorState.2.2.2.2 then U.priority monitorState.1 + 2 else 1
  }

/-! ## Exact semantic certificate stream -/

/-- The realizing full-information receiver emits the exact raw child of the
concrete physical row/past/input. -/
def profiledRawJointGuardedFirstLeftReceiverStrategy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source) :
    ReceiverBlockStrategy In₁ In₂
      (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
        RootPred package) :=
  fun past input ↦ {
    physical := pairedLeftReceiverStrategy activation.lambda past input
    target := fun row ↦ profiledRawJointGuardedFirstLeftTarget A strategy
      initial RootPred package row past input }

section
omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂]

@[simp] theorem profiledRawJointGuardedFirstLeftReceiverStrategy_physical
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    (profiledRawJointGuardedFirstLeftReceiverStrategy A activation past
      input).physical =
      pairedLeftReceiverStrategy activation.lambda past input :=
  rfl

/-- The target value is the exact one-sided raw child, not merely a code with
the correct physical projection. -/
@[simp] theorem profiledRawJointGuardedFirstLeftReceiverStrategy_target_val
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedFirstLeftReceiverStrategy A activation past
      input).target row).1 =
      let selected := profiledRawJointRootPinnedSelectedSource A strategy
        initial RootPred package
      profiledRawJointOneSidedNext A (selected.code A) (selected.move A)
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input) :=
  rfl

theorem profiledRawJointGuardedFirstLeftReceiverStrategy_target_profile
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    rightProfileOfProfiledState A
        (profiledRawJointGuardedFirstLeftTargetProfiledState A
          ((profiledRawJointGuardedFirstLeftReceiverStrategy A activation
            past input).target row)) =
      some (leftClosingProfile activation.lambda row past input) := by
  rw [profiledRawJointGuardedFirstLeftReceiverStrategy]
  rw [profiledRawJointGuardedFirstLeftTargetProfiledState_eq_of_active_slot A
    (profiledRawJointGuardedFirstLeftTarget A strategy initial RootPred
      package row past input)
    (profiledRawLeftChildSlot A source activation.lambda row past input)
    (activation.target_active_slot row past input)]
  rfl

theorem profiledRawJointGuardedFirstLeft_pairPlay_eq_letterAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source)
    (env : Nat → In₁ × In₂) (n : Nat) :
    pairPlay (profiledRawJointGuardedFirstLeftReceiverStrategy A activation)
        (pairedLeftSenderStrategy activation.lambda) env n =
      (env n,
        profiledRawJointGuardedFirstLeftReceiverStrategy A activation
          (omegaPrefix env n) (env n),
        activation.lambda.blind (senderWord (omegaPrefix env n)) (env n).2) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, pairedLeftSenderStrategy, senderWord, omegaPrefix]

theorem profiledRawJointGuardedFirstLeft_pairPlay_physical
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawLeftSlot A}
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source)
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointGuardedFirstLeftPhysicalLetter A
        (pairPlay
          (profiledRawJointGuardedFirstLeftReceiverStrategy A activation)
          (pairedLeftSenderStrategy activation.lambda) env n) =
      pairedLeftBlockWord activation.lambda env n := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, profiledRawJointGuardedFirstLeftPhysicalLetter,
    indexedTargetPhysicalLetter,
    profiledRawJointGuardedFirstLeftReceiverStrategy,
    pairedLeftReceiverStrategy, pairedLeftSenderStrategy,
    pairedLeftBlockWord, pairedLeftBlockLetterAt, senderWord, omegaPrefix]

end

/-! ## Monitor realization -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointGuardedFirstLeftBlockMonitor_run_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source)
    (env : Nat → In₁ × In₂) : ∀ n,
    (profiledRawJointGuardedFirstLeftBlockMonitor A strategy initial RootPred
      package source).run
        (pairPlay
          (profiledRawJointGuardedFirstLeftReceiverStrategy A activation)
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
        profiledRawJointGuardedFirstLeft_pairPlay_eq_letterAt A activation env n,
        omegaPrefix_succ, pairedLeftScanAfter_append,
        profiledLeftPendingAfter_append]
      have hoverlaps : ∀ row expected,
          profiledLeftPendingAfter activation.lambda (omegaPrefix env n) row =
              some expected →
            pairedLeftClosingForRow row
                (profiledRawJointGuardedFirstLeftReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).physical =
              expected ((env n).2, (env n).1) := by
        simpa [profiledRawJointGuardedFirstLeftReceiverStrategy,
          profiledLeftReceiverStrategy] using
          (profiledLeftPendingAfter_realizes A source.1.1 activation.lambda
            (omegaPrefix env n) (env n))
      have htargets : ∀ row,
          erasePairedProfiledState A
              (profiledRawJointGuardedFirstLeftTargetProfiledState A
                ((profiledRawJointGuardedFirstLeftReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).target row)) =
            pairedLeftCloseTarget A
              (pairedLeftScanAfter A source.1.1 activation.lambda
                (omegaPrefix env n)) row
              (pairedLeftBlockLetterAt activation.lambda
                (omegaPrefix env n) (env n)) := by
        intro row
        rw [profiledRawJointGuardedFirstLeftReceiverStrategy]
        rw [profiledRawJointGuardedFirstLeftTargetProfiledState_eq_of_active_slot
          A
          (profiledRawJointGuardedFirstLeftTarget A strategy initial RootPred
            package row (omegaPrefix env n) (env n))
          (profiledRawLeftChildSlot A source activation.lambda row
            (omegaPrefix env n) (env n))
          (activation.target_active_slot row (omegaPrefix env n) (env n))]
        rw [← pairedProfiledTwoChild_eq_profiledRawLeftChildSlot A source
          activation.lambda row (omegaPrefix env n) (env n),
          erase_pairedProfiledTwoChild, pairedLeftCloseTarget_scanAfter]
      have hphysicalAt :
          profiledRawJointGuardedFirstLeftPhysicalLetter A
              (env n,
                profiledRawJointGuardedFirstLeftReceiverStrategy A activation
                  (omegaPrefix env n) (env n),
                activation.lambda.blind
                  (senderWord (omegaPrefix env n)) (env n).2) =
            pairedLeftBlockLetterAt activation.lambda
              (omegaPrefix env n) (env n) := rfl
      simp only [profiledRawJointGuardedFirstLeftBlockMonitor]
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
          profiledRawJointGuardedFirstLeftReceiverStrategy_target_profile]
      · simp [hn,
          profiledRawJointGuardedFirstLeftReceiverStrategy_target_profile]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact semantic exceptional block realizes the finite monitor. -/
theorem profiledRawJointGuardedFirstLeftBlockMonitor_realizable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source) :
    ∀ env : Nat → In₁ × In₂,
      (profiledRawJointGuardedFirstLeftBlockMonitor A strategy initial RootPred
        package source).WinsPlay
        (pairPlay
          (profiledRawJointGuardedFirstLeftReceiverStrategy A activation)
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
  rw [profiledRawJointGuardedFirstLeftBlockMonitor_run_eq A source activation
    env n]
  simp [profiledRawJointGuardedFirstLeftBlockMonitor]
  rfl

/-! ## Unconditional narrowing -/

/-- Every installed guarded-root left activation admits a finite narrowed
controller.  Its output target alphabet is precisely the finite bank of
literal children of the selected semantic source. -/
theorem exists_profiledRawJointGuardedFirstLeftController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source) :
    ∃ controller :
        TransitionRationalTree.{v, max u v x y s, max u v x y s} In₂
        (NarrowedBlockLabel In₁ In₂
          (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
            RootPred package) Out₂
          (profiledRawJointGuardedFirstLeftBlockMonitor A strategy initial
            RootPred package source).State),
      NarrowedAllThreadsWin
        (profiledRawJointGuardedFirstLeftBlockMonitor A strategy initial
          RootPred package source) controller.labeledTree := by
  have hrealizable :
      ∃ receiver : ReceiverBlockStrategy In₁ In₂
          (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy initial
            RootPred package),
        ∃ sender : SenderBlockStrategy In₂ Out₂,
          ∀ env : Nat → In₁ × In₂,
            (profiledRawJointGuardedFirstLeftBlockMonitor A strategy initial
              RootPred package source).WinsPlay
              (pairPlay receiver sender env) := by
    exact ⟨profiledRawJointGuardedFirstLeftReceiverStrategy A activation,
      pairedLeftSenderStrategy activation.lambda,
      profiledRawJointGuardedFirstLeftBlockMonitor_realizable A source
        activation⟩
  exact (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointGuardedFirstLeftBlockMonitor A strategy initial RootPred
      package source)).mp hrealizable

end


end DetParityAutomaton

end DistributedSynthesis
