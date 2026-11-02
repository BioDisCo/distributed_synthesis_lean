/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedFirstBlockActivation
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitRightBlockMonitor

/-!
# The root-pinned exceptional right-block controller

The first recurrent right block differs from the ordinary fixed-policy block
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

abbrev ProfiledRawJointGuardedFirstRightReceiverOutput
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred) :=
  IndexedTargetReceiverOutput
    (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow
    (ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
        package))

/-- Project the live process-two slot carried by a literal child code. -/
def profiledRawJointGuardedFirstRightTargetProfiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (target : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
        package)) : PairedProfiledTreeState A :=
  match target.1.family.left () with
  | some slot => .inr (.inr slot)
  | none => .inl PUnit.unit

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointGuardedFirstRightTargetProfiledState_eq_of_active_slot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (target : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
        package))
    (slot : ProfiledRawLeftSlot A)
    (hslot : target.1.family.left () = some slot) :
    profiledRawJointGuardedFirstRightTargetProfiledState A target =
      .inr (.inr slot) := by
  simp [profiledRawJointGuardedFirstRightTargetProfiledState, hslot]

/-- Forget the literal-child certificate from one realized letter. -/
def profiledRawJointGuardedFirstRightPhysicalLetter
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (letter : RealizedBlockRound In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁) :
    PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  indexedTargetPhysicalLetter letter

/-! ## Sticky exceptional monitor -/

/-- The exceptional right monitor.  Literal-child membership is enforced by
the finite target type itself; the sticky predicate checks that its profiled
projection is the physical close selected at the current row. -/
noncomputable def profiledRawJointGuardedFirstRightBlockMonitor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A) :
    BlockRecordMonitor In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) Out₁ := by
  classical
  let U := (pairedRightThreadSystem A source.1.1).universalRunDPA
  exact {
    State := ProfiledRightBlockMonitorState A U.State
    stateFinite := inferInstance
    initial := (U.initial, pairedRightScanInitial A source.1.1,
      fun _ ↦ none, true, true)
    step := fun monitorState letter ↦
      let physical := profiledRawJointGuardedFirstRightPhysicalLetter A letter
      let rootMatches := !monitorState.2.2.2.1 ||
        decide (pairedRightInformedForRow .first letter.2.1.physical =
          source.2 letter.1)
      let overlaps := ∀ row expected,
        monitorState.2.2.1 row = some expected →
          pairedRightClosingForRow row letter.2.1.physical =
            expected (letter.1.2, letter.1.1)
      let targetsSafe := ∀ row,
        erasePairedProfiledState A
            (profiledRawJointGuardedFirstRightTargetProfiledState A
              (letter.2.1.target row)) =
          pairedRightCloseTarget A monitorState.2.1 row physical
      (U.step monitorState.1 physical,
        pairedRightScanStep A monitorState.2.1 physical,
        fun row ↦ leftProfileOfProfiledState A
          (profiledRawJointGuardedFirstRightTargetProfiledState A
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
def profiledRawJointGuardedFirstRightReceiverStrategy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source) :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
        RootPred package) :=
  fun past input ↦ {
    physical := pairedRightReceiverStrategy activation.lambda past input
    target := fun row ↦ profiledRawJointGuardedFirstRightTarget A strategy
      initial RootPred package row past input }

section
omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂]

@[simp] theorem profiledRawJointGuardedFirstRightReceiverStrategy_physical
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    (profiledRawJointGuardedFirstRightReceiverStrategy A activation past
      input).physical =
      pairedRightReceiverStrategy activation.lambda past input :=
  rfl

/-- The target value is the exact one-sided raw child, not merely a code with
the correct physical projection. -/
@[simp] theorem profiledRawJointGuardedFirstRightReceiverStrategy_target_val
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ((profiledRawJointGuardedFirstRightReceiverStrategy A activation past
      input).target row).1 =
      let selected := profiledRawJointRootPinnedSelectedSource A strategy
        initial RootPred package
      profiledRawJointOneSidedNext A (selected.code A) (selected.move A)
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input) :=
  rfl

theorem profiledRawJointGuardedFirstRightReceiverStrategy_target_profile
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    leftProfileOfProfiledState A
        (profiledRawJointGuardedFirstRightTargetProfiledState A
          ((profiledRawJointGuardedFirstRightReceiverStrategy A activation
            past input).target row)) =
      some (rightClosingProfile activation.lambda row past input) := by
  rw [profiledRawJointGuardedFirstRightReceiverStrategy]
  rw [profiledRawJointGuardedFirstRightTargetProfiledState_eq_of_active_slot A
    (profiledRawJointGuardedFirstRightTarget A strategy initial RootPred
      package row past input)
    (profiledRawRightChildSlot A source activation.lambda row past input)
    (activation.target_active_slot row past input)]
  rfl

theorem profiledRawJointGuardedFirstRight_pairPlay_eq_letterAt
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source)
    (env : Nat → In₂ × In₁) (n : Nat) :
    pairPlay (profiledRawJointGuardedFirstRightReceiverStrategy A activation)
        (pairedRightSenderStrategy activation.lambda) env n =
      (env n,
        profiledRawJointGuardedFirstRightReceiverStrategy A activation
          (omegaPrefix env n) (env n),
        activation.lambda.blind (senderWord (omegaPrefix env n)) (env n).2) := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, pairedRightSenderStrategy, senderWord, omegaPrefix]

theorem profiledRawJointGuardedFirstRight_pairPlay_physical
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    {source : ProfiledRawRightSlot A}
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source)
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointGuardedFirstRightPhysicalLetter A
        (pairPlay
          (profiledRawJointGuardedFirstRightReceiverStrategy A activation)
          (pairedRightSenderStrategy activation.lambda) env n) =
      pairedRightBlockWord activation.lambda env n := by
  rw [pairPlay, treePlay, treeOfPair, branchNode_eq_omegaPrefix]
  simp [blockLabelApply, profiledRawJointGuardedFirstRightPhysicalLetter,
    indexedTargetPhysicalLetter,
    profiledRawJointGuardedFirstRightReceiverStrategy,
    pairedRightReceiverStrategy, pairedRightSenderStrategy,
    pairedRightBlockWord, senderWord, omegaPrefix]

end

/-! ## Monitor realization -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointGuardedFirstRightBlockMonitor_run_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source)
    (env : Nat → In₂ × In₁) : ∀ n,
    (profiledRawJointGuardedFirstRightBlockMonitor A strategy initial RootPred
      package source).run
        (pairPlay
          (profiledRawJointGuardedFirstRightReceiverStrategy A activation)
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
        profiledRawJointGuardedFirstRight_pairPlay_eq_letterAt A activation env n,
        omegaPrefix_succ, pairedRightScanAfter_append,
        profiledRightPendingAfter_append]
      have hoverlaps : ∀ row expected,
          profiledRightPendingAfter activation.lambda (omegaPrefix env n) row =
              some expected →
            pairedRightClosingForRow row
                (profiledRawJointGuardedFirstRightReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).physical =
              expected ((env n).2, (env n).1) := by
        simpa [profiledRawJointGuardedFirstRightReceiverStrategy,
          profiledRightReceiverStrategy] using
          (profiledRightPendingAfter_realizes A source.1.1 activation.lambda
            (omegaPrefix env n) (env n))
      have htargets : ∀ row,
          erasePairedProfiledState A
              (profiledRawJointGuardedFirstRightTargetProfiledState A
                ((profiledRawJointGuardedFirstRightReceiverStrategy A activation
                  (omegaPrefix env n) (env n)).target row)) =
            pairedRightCloseTarget A
              (pairedRightScanAfter A source.1.1 activation.lambda
                (omegaPrefix env n)) row
              (pairedRightBlockLetterAt activation.lambda
                (omegaPrefix env n) (env n)) := by
        intro row
        rw [profiledRawJointGuardedFirstRightReceiverStrategy]
        rw [profiledRawJointGuardedFirstRightTargetProfiledState_eq_of_active_slot
          A
          (profiledRawJointGuardedFirstRightTarget A strategy initial RootPred
            package row (omegaPrefix env n) (env n))
          (profiledRawRightChildSlot A source activation.lambda row
            (omegaPrefix env n) (env n))
          (activation.target_active_slot row (omegaPrefix env n) (env n))]
        rw [← pairedProfiledOneChild_eq_profiledRawRightChildSlot A source
          activation.lambda row (omegaPrefix env n) (env n),
          erase_pairedProfiledOneChild, pairedRightCloseTarget_scanAfter]
      have hphysicalAt :
          profiledRawJointGuardedFirstRightPhysicalLetter A
              (env n,
                profiledRawJointGuardedFirstRightReceiverStrategy A activation
                  (omegaPrefix env n) (env n),
                activation.lambda.blind
                  (senderWord (omegaPrefix env n)) (env n).2) =
            pairedRightBlockLetterAt activation.lambda
              (omegaPrefix env n) (env n) := rfl
      simp only [profiledRawJointGuardedFirstRightBlockMonitor]
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
          profiledRawJointGuardedFirstRightReceiverStrategy_target_profile]
      · simp [hn,
          profiledRawJointGuardedFirstRightReceiverStrategy_target_profile]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact semantic exceptional block realizes the finite monitor. -/
theorem profiledRawJointGuardedFirstRightBlockMonitor_realizable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source) :
    ∀ env : Nat → In₂ × In₁,
      (profiledRawJointGuardedFirstRightBlockMonitor A strategy initial RootPred
        package source).WinsPlay
        (pairPlay
          (profiledRawJointGuardedFirstRightReceiverStrategy A activation)
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
  rw [profiledRawJointGuardedFirstRightBlockMonitor_run_eq A source activation
    env n]
  simp [profiledRawJointGuardedFirstRightBlockMonitor]
  rfl

/-! ## Unconditional narrowing -/

/-- Every installed guarded-root right activation admits a finite narrowed
controller.  Its output target alphabet is precisely the finite bank of
literal children of the selected semantic source. -/
theorem exists_profiledRawJointGuardedFirstRightController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop}
    {package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred}
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source) :
    ∃ controller :
        TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
        (NarrowedBlockLabel In₂ In₁
          (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
            RootPred package) Out₁
          (profiledRawJointGuardedFirstRightBlockMonitor A strategy initial
            RootPred package source).State),
      NarrowedAllThreadsWin
        (profiledRawJointGuardedFirstRightBlockMonitor A strategy initial
          RootPred package source) controller.labeledTree := by
  have hrealizable :
      ∃ receiver : ReceiverBlockStrategy In₂ In₁
          (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy initial
            RootPred package),
        ∃ sender : SenderBlockStrategy In₁ Out₁,
          ∀ env : Nat → In₂ × In₁,
            (profiledRawJointGuardedFirstRightBlockMonitor A strategy initial
              RootPred package source).WinsPlay
              (pairPlay receiver sender env) := by
    exact ⟨profiledRawJointGuardedFirstRightReceiverStrategy A activation,
      pairedRightSenderStrategy activation.lambda,
      profiledRawJointGuardedFirstRightBlockMonitor_realizable A source
        activation⟩
  exact (block_realizable_iff_implementable_controller_unconditional
    (profiledRawJointGuardedFirstRightBlockMonitor A strategy initial RootPred
      package source)).mp hrealizable

end


end DetParityAutomaton

end DistributedSynthesis
