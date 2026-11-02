/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreStrictTrace

/-!
# Acceptance of fixed strict guarded-common tails

This file projects a guarded finite sibling controller's universal monitor
run to the two concrete DPA entry rows.  It then connects the row-`both`
controller word to the concrete all-strict tail-core trace.

The orientation remains proof-side: no graph, leader, or strict-side bit is
added to a local transition.
-/

namespace DistributedSynthesis

universe u v x y s t

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

/-! ## Universal DPA component of target monitors -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
theorem profiledRawJointTargetRightBlockMonitor_run_universal
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop) (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁) :
    ∀ n,
    ((profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
      source).run play n).1 =
      (pairedRightThreadSystem A source.1.1).universalRunDPA.run
        (fun k ↦ profiledRawJointTargetRightPhysicalLetter A (play k)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show
        (pairedRightThreadSystem A source.1.1).universalRunDPA.step
            ((profiledRawJointTargetRightBlockMonitor A Target targetState
              Allowed source).run play n).1
            (profiledRawJointTargetRightPhysicalLetter A (play n)) =
          (pairedRightThreadSystem A source.1.1).universalRunDPA.step
            ((pairedRightThreadSystem A source.1.1).universalRunDPA.run
              (fun k ↦
                profiledRawJointTargetRightPhysicalLetter A (play k)) n)
            (profiledRawJointTargetRightPhysicalLetter A (play n))
      rw [ih]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
theorem profiledRawJointTargetLeftBlockMonitor_run_universal
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop) (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂) :
    ∀ n,
    ((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
      source).run play n).1 =
      (pairedLeftThreadSystem A source.1.1).universalRunDPA.run
        (fun k ↦ profiledRawJointTargetLeftPhysicalLetter A (play k)) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show
        (pairedLeftThreadSystem A source.1.1).universalRunDPA.step
            ((profiledRawJointTargetLeftBlockMonitor A Target targetState
              Allowed source).run play n).1
            (profiledRawJointTargetLeftPhysicalLetter A (play n)) =
          (pairedLeftThreadSystem A source.1.1).universalRunDPA.step
            ((pairedLeftThreadSystem A source.1.1).universalRunDPA.run
              (fun k ↦
                profiledRawJointTargetLeftPhysicalLetter A (play k)) n)
            (profiledRawJointTargetLeftPhysicalLetter A (play n))
      rw [ih]

/-! ## Physical lambdas of guarded member controllers -/

/-- Forget target certificates in a guarded right member controller. -/
noncomputable def profiledRawJointGuardedRightControllerLambda
    (move : ProfiledRawJointGuardedRightPhysicalSiblingMove A) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  {
    blind := fun word input ↦ (controller.labeledTree word).1 input
    informedLeft := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl monitor controller.labeledTree past) input
        ).physical.informedFirst
    informedBoth := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl monitor controller.labeledTree past) input
        ).physical.informedBoth
    bothOneLeft := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl monitor controller.labeledTree past) input
        ).physical.closingFirst
    bothOneBoth := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl monitor controller.labeledTree past) input
        ).physical.closingBoth
  }

/-- Left guarded member-controller lambda. -/
noncomputable def profiledRawJointGuardedLeftControllerLambda
    (move : ProfiledRawJointGuardedLeftPhysicalSiblingMove A) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
    false
  let controller := move.memberController A false
  {
    blind := fun word input ↦ (controller.labeledTree word).1 input
    informedRight := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl monitor controller.labeledTree past) input
        ).physical.informedFirst
    informedBoth := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl monitor controller.labeledTree past) input
        ).physical.informedBoth
    bothTwoRight := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl monitor controller.labeledTree past) input
        ).physical.closingFirst
    bothTwoBoth := fun past input ↦
      ((controller.labeledTree (senderWord past)).2
        (narrowedControl monitor controller.labeledTree past) input
        ).physical.closingBoth
  }

omit [Inhabited Out₁] [Inhabited Out₂] [Inhabited In₁] [Inhabited In₂] in
theorem profiledRawJointGuardedRightControllerLambda_blockWord
    (move : ProfiledRawJointGuardedRightPhysicalSiblingMove A)
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointTargetRightPhysicalLetter A
        (treePlay
          (narrowedInducedTree
            (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
              false)
            (move.memberController A false).labeledTree) env n) =
      pairedRightBlockWord
        (profiledRawJointGuardedRightControllerLambda A move) env n := by
  simp [treePlay, narrowedInducedTree, blockLabelApply,
    profiledRawJointTargetRightPhysicalLetter, indexedTargetPhysicalLetter,
    profiledRawJointGuardedRightControllerLambda,
    branchNode_eq_omegaPrefix, pairedRightBlockWord]

omit [Inhabited Out₁] [Inhabited Out₂] [Inhabited In₁] [Inhabited In₂] in
theorem profiledRawJointGuardedLeftControllerLambda_blockWord
    (move : ProfiledRawJointGuardedLeftPhysicalSiblingMove A)
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointTargetLeftPhysicalLetter A
        (treePlay
          (narrowedInducedTree
            (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 false)
            (move.memberController A false).labeledTree) env n) =
      pairedLeftBlockWord
        (profiledRawJointGuardedLeftControllerLambda A move) env n := by
  simp [treePlay, narrowedInducedTree, blockLabelApply,
    profiledRawJointTargetLeftPhysicalLetter, indexedTargetPhysicalLetter,
    profiledRawJointGuardedLeftControllerLambda,
    branchNode_eq_omegaPrefix, pairedLeftBlockWord, pairedLeftBlockLetterAt]

/-! ## Monitor winning projected to the two DPA entry rows -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointGuardedRightPhysicalSiblingMove.memberController_forever
    (move : ProfiledRawJointGuardedRightPhysicalSiblingMove A) :
    PairedRightForeverAccepts A move.1.base.source.1.1
      (profiledRawJointGuardedRightControllerLambda A move) := by
  let guard := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
    false
  let base := profiledRawJointRightPhysicalSiblingMonitor A move.1.base false
  let controller := move.memberController A false
  let lambda := profiledRawJointGuardedRightControllerLambda A move
  apply pairedRightForeverAccepts_of_universalDPA A move.1.base.source.1.1
    lambda
  intro env
  let play := treePlay
    (narrowedInducedTree guard controller.labeledTree) env
  have htree : guard.lift.WinningTree
      (narrowedInducedTree guard controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin guard
      (move.memberController_wins A false)
  have hguard : guard.WinsPlay play :=
    (guard.lift_winningTree_iff
      (narrowedInducedTree guard controller.labeledTree)).mp htree env
  have hbase : base.WinsPlay play :=
    BlockRecordMonitor.firstLetterGuard_base_wins_of_wins base
      move.1.firstAllowed play hguard
  have hword :
      (fun k ↦ profiledRawJointTargetRightPhysicalLetter A (play k)) =
        pairedRightBlockWord lambda env := by
    funext k
    simpa [play, guard, controller, lambda] using
      profiledRawJointGuardedRightControllerLambda_blockWord A move env k
  unfold BlockRecordMonitor.WinsPlay at hbase
  have heq :
      (fun n ↦ base.priority (base.run play n)) =
        fun n ↦
          ((pairedRightThreadSystem A move.1.base.source.1.1
            ).universalRunDPA).priority
            ((pairedRightThreadSystem A move.1.base.source.1.1
              ).universalRunDPA.run (pairedRightBlockWord lambda env) n) + 2 := by
    funext n
    have hsafe := profiledRawJointTargetRightBlockMonitor_safe_of_wins A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A move.1.base)
      move.1.base.source play hbase n
    change (if (base.run play n).2.2.2.2 then
        ((pairedRightThreadSystem A move.1.base.source.1.1
          ).universalRunDPA).priority (base.run play n).1 + 2 else 1) = _
    rw [hsafe, if_pos rfl,
      profiledRawJointTargetRightBlockMonitor_run_universal A
        (profiledRawJointUnitRightTargetProjection A)
        (profiledRawJointRightPhysicalSiblingAllowed A move.1.base)
        move.1.base.source play n,
      hword]
  rw [heq] at hbase
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hbase

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointGuardedLeftPhysicalSiblingMove.memberController_forever
    (move : ProfiledRawJointGuardedLeftPhysicalSiblingMove A) :
    PairedLeftForeverAccepts A move.1.base.source.1.1
      (profiledRawJointGuardedLeftControllerLambda A move) := by
  let guard := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 false
  let base := profiledRawJointLeftPhysicalSiblingMonitor A move.1.base false
  let controller := move.memberController A false
  let lambda := profiledRawJointGuardedLeftControllerLambda A move
  apply pairedLeftForeverAccepts_of_universalDPA A move.1.base.source.1.1 lambda
  intro env
  let play := treePlay
    (narrowedInducedTree guard controller.labeledTree) env
  have htree : guard.lift.WinningTree
      (narrowedInducedTree guard controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin guard
      (move.memberController_wins A false)
  have hguard : guard.WinsPlay play :=
    (guard.lift_winningTree_iff
      (narrowedInducedTree guard controller.labeledTree)).mp htree env
  have hbase : base.WinsPlay play :=
    BlockRecordMonitor.firstLetterGuard_base_wins_of_wins base
      move.1.firstAllowed play hguard
  have hword :
      (fun k ↦ profiledRawJointTargetLeftPhysicalLetter A (play k)) =
        pairedLeftBlockWord lambda env := by
    funext k
    simpa [play, guard, controller, lambda] using
      profiledRawJointGuardedLeftControllerLambda_blockWord A move env k
  unfold BlockRecordMonitor.WinsPlay at hbase
  have heq :
      (fun n ↦ base.priority (base.run play n)) =
        fun n ↦
          ((pairedLeftThreadSystem A move.1.base.source.1.1
            ).universalRunDPA).priority
            ((pairedLeftThreadSystem A move.1.base.source.1.1
              ).universalRunDPA.run (pairedLeftBlockWord lambda env) n) + 2 := by
    funext n
    have hsafe := profiledRawJointTargetLeftBlockMonitor_safe_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A move.1.base)
      move.1.base.source play hbase n
    change (if (base.run play n).2.2.2.2 then
        ((pairedLeftThreadSystem A move.1.base.source.1.1
          ).universalRunDPA).priority (base.run play n).1 + 2 else 1) = _
    rw [hsafe, if_pos rfl,
      profiledRawJointTargetLeftBlockMonitor_run_universal A
        (profiledRawJointUnitLeftTargetProjection A)
        (profiledRawJointLeftPhysicalSiblingAllowed A move.1.base)
        move.1.base.source play n,
      hword]
  rw [heq] at hbase
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hbase

/-! ## Natural controller words -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The row-`both` omega word of the guarded-right lambda is literally the
physical projection of its narrowed tree play. -/
theorem profiledRawJointGuardedRightControllerLambda_omegaWord_apply
    (move : ProfiledRawJointGuardedRightPhysicalSiblingMove A)
    (env : Nat → In₂ × In₁) (n : Nat) :
    pairedRightOmegaWord
        (profiledRawJointGuardedRightControllerLambda A move).blind
        (profiledRawJointGuardedRightControllerLambda A move).informedBoth
        env n =
      pairedRightRecordForRow .both
        (profiledRawJointTargetRightPhysicalLetter A
          (treePlay
            (narrowedInducedTree
              (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
                false)
              (move.memberController A false).labeledTree) env n)) := by
  simp [pairedRightOmegaWord, pairedRightRecordForRow,
    profiledRawJointGuardedRightControllerLambda, treePlay,
    narrowedInducedTree, blockLabelApply, branchNode_eq_omegaPrefix,
    profiledRawJointTargetRightPhysicalLetter, indexedTargetPhysicalLetter]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left natural word. -/
theorem profiledRawJointGuardedLeftControllerLambda_omegaWord_apply
    (move : ProfiledRawJointGuardedLeftPhysicalSiblingMove A)
    (env : Nat → In₁ × In₂) (n : Nat) :
    pairedLeftOmegaWord
        (profiledRawJointGuardedLeftControllerLambda A move).blind
        (profiledRawJointGuardedLeftControllerLambda A move).informedBoth
        env n =
      pairedLeftRecordForRow .both
        (profiledRawJointTargetLeftPhysicalLetter A
          (treePlay
            (narrowedInducedTree
              (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
                false)
              (move.memberController A false).labeledTree) env n)) := by
  simp [pairedLeftOmegaWord, pairedLeftRecordForRow,
    profiledRawJointGuardedLeftControllerLambda, treePlay,
    narrowedInducedTree, blockLabelApply, branchNode_eq_omegaPrefix,
    profiledRawJointTargetLeftPhysicalLetter, indexedTargetPhysicalLetter]

/-! ## Closed-form resolved-state invariant -/

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonControl :=
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

/-- One concrete right input advances the closed-form finite state by the
same controller/monitor step used by the local strict carrier. -/
theorem profiledRawJointGuardedCommonRightFiniteStateAfter_append_one
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin pair
        (past ++ [input]) =
      let state :=
        profiledRawJointGuardedCommonRightFiniteStateAfter A strategy hwin
          pair past
      let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
        pair.1.1.1 false
      let controller := (pair.1.1).memberController A false
      (controller.step state.1 input.2,
        monitor.step state.2
          (narrowedRecord monitor (controller.labelOf state.1) state.2
            input)) := by
  rw [profiledRawJointGuardedCommonRightFiniteStateAfter_eq A strategy hwin,
    profiledRawJointGuardedCommonRightFiniteStateAfter_eq A strategy hwin,
    senderWord_append, TransitionRationalTree.controlAt_append,
    narrowedControl_append]
  rfl

/-- Left mirror of the one-input finite-state law. -/
theorem profiledRawJointGuardedCommonLeftFiniteStateAfter_append_one
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin pair
        (past ++ [input]) =
      let state :=
        profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy hwin pair
          past
      let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
        pair.1.2.1 false
      let controller := (pair.1.2).memberController A false
      (controller.step state.1 input.2,
        monitor.step state.2
          (narrowedRecord monitor (controller.labelOf state.1) state.2
            input)) := by
  rw [profiledRawJointGuardedCommonLeftFiniteStateAfter_eq A strategy hwin,
    profiledRawJointGuardedCommonLeftFiniteStateAfter_eq A strategy hwin,
    senderWord_append, TransitionRationalTree.controlAt_append,
    narrowedControl_append]
  rfl

set_option maxHeartbeats 800000 in
/-- The strict part of the first resolved right trace state contains exactly
the controller and guarded-monitor state after the literal two-letter prefix.
The latest target is retained existentially because it does not participate
in the next physical controller letter. -/
theorem profiledRawJointGuardedCommonTailStrictRightStateTrace_zero_aligned
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    let pair := profiledRawJointGuardedInitialCommonControlPair A strategy hwin
      root
    let finite := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair (omegaPrefix env 2)
    ∃ target : Option (ProfiledRawJointUnitTarget A),
      (profiledRawJointGuardedCommonTailStrictRightStateTrace A strategy hwin
        root env 0).strict =
        { owner := ⟨pair, finite.1⟩
          receiver := ⟨pair, finite.2, target⟩
          source_eq := rfl } := by
  dsimp only
  rw [profiledRawJointGuardedCommonRightFiniteStateAfter_eq A strategy hwin]
  refine ⟨(profiledRawJointGuardedCommonTailStrictRightStateTrace A strategy
    hwin root env 0).strict.receiver.2.2, ?_⟩
  simp [profiledRawJointGuardedCommonTailStrictRightStateTrace,
    profiledRawJointGuardedCommonTailInitialRightPending,
    profiledRawJointGuardedCommonTailResolveRightStep,
    profiledRawJointGuardedCommonResolveStrictRight,
    profiledRawJointGuardedCommonRightOwnerFor,
    profiledRawJointGuardedCommonRightOwnerNoRecv,
    profiledRawJointGuardedCommonTwoShadowRecvRightOwner,
    profiledRawJointGuardedCommonNoRecvOne,
    profiledRawJointGuardedInitialCommonStartTwo,
    omegaPrefix]
  constructor <;> rfl

set_option maxHeartbeats 800000 in
/-- First resolved-left strict-state alignment. -/
theorem profiledRawJointGuardedCommonTailStrictLeftStateTrace_zero_aligned
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    let pair := profiledRawJointGuardedInitialCommonControlPair A strategy hwin
      root
    let finite := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair (omegaPrefix env 2)
    ∃ target : Option (ProfiledRawJointUnitTarget A),
      (profiledRawJointGuardedCommonTailStrictLeftStateTrace A strategy hwin
        root env 0).strict =
        { receiver := ⟨pair, finite.2, target⟩
          owner := ⟨pair, finite.1⟩
          source_eq := rfl } := by
  dsimp only
  rw [profiledRawJointGuardedCommonLeftFiniteStateAfter_eq A strategy hwin]
  refine ⟨(profiledRawJointGuardedCommonTailStrictLeftStateTrace A strategy
    hwin root env 0).strict.receiver.2.2, ?_⟩
  simp [profiledRawJointGuardedCommonTailStrictLeftStateTrace,
    profiledRawJointGuardedCommonTailInitialLeftPending,
    profiledRawJointGuardedCommonTailResolveLeftStep,
    profiledRawJointGuardedCommonResolveStrictLeft,
    profiledRawJointGuardedCommonLeftOwnerFor,
    profiledRawJointGuardedCommonLeftOwnerNoRecv,
    profiledRawJointGuardedCommonOneShadowRecvLeftOwner,
    profiledRawJointGuardedCommonNoRecvTwo,
    profiledRawJointGuardedInitialCommonStartOne,
    omegaPrefix]
  constructor <;> rfl

/-- Every resolved right trace state is the closed-form controller/monitor
state after the physical prefix that has actually been consumed. -/
theorem profiledRawJointGuardedCommonTailStrictRightStateTrace_aligned
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    ∀ n,
    let pair := profiledRawJointGuardedInitialCommonControlPair A strategy hwin
      root
    let finite := profiledRawJointGuardedCommonRightFiniteStateAfter A strategy
      hwin pair (omegaPrefix env (n + 2))
    ∃ target : Option (ProfiledRawJointUnitTarget A),
      (profiledRawJointGuardedCommonTailStrictRightStateTrace A strategy hwin
        root env n).strict =
        { owner := ⟨pair, finite.1⟩
          receiver := ⟨pair, finite.2, target⟩
          source_eq := rfl } := by
  intro n
  induction n with
  | zero =>
      simpa using
        profiledRawJointGuardedCommonTailStrictRightStateTrace_zero_aligned A
          strategy hwin root env
  | succ n ih =>
      dsimp only at ih ⊢
      rcases ih with ⟨target, ih⟩
      rw [profiledRawJointGuardedCommonTailStrictRightStateTrace]
      simp only [profiledRawJointGuardedCommonTailStrictRightStep]
      rw [ih]
      have hprefix :
          omegaPrefix env (Nat.succ n + 2) =
            omegaPrefix env (n + 2) ++ [env (n + 2)] := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using omegaPrefix_succ env (n + 2)
      rw [hprefix,
        profiledRawJointGuardedCommonRightFiniteStateAfter_append_one A
          strategy hwin]
      refine ⟨(profiledRawJointGuardedCommonTailStrictRightStep A strategy hwin
        { strict :=
            { owner :=
                ⟨profiledRawJointGuardedInitialCommonControlPair A strategy
                    hwin root,
                  (profiledRawJointGuardedCommonRightFiniteStateAfter A
                    strategy hwin
                    (profiledRawJointGuardedInitialCommonControlPair A
                      strategy hwin root) (omegaPrefix env (n + 2))).1⟩
              receiver :=
                ⟨profiledRawJointGuardedInitialCommonControlPair A strategy
                    hwin root,
                  (profiledRawJointGuardedCommonRightFiniteStateAfter A
                    strategy hwin
                    (profiledRawJointGuardedInitialCommonControlPair A
                      strategy hwin root) (omegaPrefix env (n + 2))).2,
                  target⟩
              source_eq := rfl }
          close :=
            (profiledRawJointGuardedCommonTailStrictRightStateTrace A strategy
              hwin root env n).close }
        (env (n + 2))).2.strict.receiver.2.2, ?_⟩
      simp [profiledRawJointGuardedCommonTailStrictRightStep,
        profiledRawJointGuardedCommonStrictRightStep,
        profiledRawJointGuardedCommonRightStrictOwnerFor,
        profiledRawJointGuardedCommonRightOwnerNoRecv,
        profiledRawJointGuardedCommonRightStrictReceiverRecvOwner,
        narrowedRecord]

/-- Left resolved-state invariant. -/
theorem profiledRawJointGuardedCommonTailStrictLeftStateTrace_aligned
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    ∀ n,
    let pair := profiledRawJointGuardedInitialCommonControlPair A strategy hwin
      root
    let finite := profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
      hwin pair (omegaPrefix env (n + 2))
    ∃ target : Option (ProfiledRawJointUnitTarget A),
      (profiledRawJointGuardedCommonTailStrictLeftStateTrace A strategy hwin
        root env n).strict =
        { receiver := ⟨pair, finite.2, target⟩
          owner := ⟨pair, finite.1⟩
          source_eq := rfl } := by
  intro n
  induction n with
  | zero =>
      simpa using
        profiledRawJointGuardedCommonTailStrictLeftStateTrace_zero_aligned A
          strategy hwin root env
  | succ n ih =>
      dsimp only at ih ⊢
      rcases ih with ⟨target, ih⟩
      rw [profiledRawJointGuardedCommonTailStrictLeftStateTrace]
      simp only [profiledRawJointGuardedCommonTailStrictLeftStep]
      rw [ih]
      have hprefix :
          omegaPrefix env (Nat.succ n + 2) =
            omegaPrefix env (n + 2) ++ [env (n + 2)] := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using omegaPrefix_succ env (n + 2)
      rw [hprefix,
        profiledRawJointGuardedCommonLeftFiniteStateAfter_append_one A
          strategy hwin]
      refine ⟨(profiledRawJointGuardedCommonTailStrictLeftStep A strategy hwin
        { strict :=
            { receiver :=
                ⟨profiledRawJointGuardedInitialCommonControlPair A strategy
                    hwin root,
                  (profiledRawJointGuardedCommonLeftFiniteStateAfter A
                    strategy hwin
                    (profiledRawJointGuardedInitialCommonControlPair A
                      strategy hwin root) (omegaPrefix env (n + 2))).2,
                  target⟩
              owner :=
                ⟨profiledRawJointGuardedInitialCommonControlPair A strategy
                    hwin root,
                  (profiledRawJointGuardedCommonLeftFiniteStateAfter A strategy
                    hwin
                    (profiledRawJointGuardedInitialCommonControlPair A
                      strategy hwin root) (omegaPrefix env (n + 2))).1⟩
              source_eq := rfl }
          close :=
            (profiledRawJointGuardedCommonTailStrictLeftStateTrace A strategy
              hwin root env n).close }
        (env (n + 2))).2.strict.receiver.2.2, ?_⟩
      simp [profiledRawJointGuardedCommonTailStrictLeftStep,
        profiledRawJointGuardedCommonStrictLeftStep,
        profiledRawJointGuardedCommonLeftStrictOwnerFor,
        profiledRawJointGuardedCommonLeftOwnerNoRecv,
        profiledRawJointGuardedCommonLeftStrictReceiverRecvOwner,
        narrowedRecord]

/-! ## Identification of the concrete and natural controller words -/

/-- The natural guarded-right lambda reads exactly the closed-form finite
controller record at each prefix. -/
theorem profiledRawJointGuardedRightControllerLambda_omegaWord_eq_recordAt
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (env : Nat → In₂ × In₁) (n : Nat) :
    pairedRightOmegaWord
        (profiledRawJointGuardedRightControllerLambda A pair.1.1).blind
        (profiledRawJointGuardedRightControllerLambda A pair.1.1).informedBoth
        env n =
      profiledRawJointGuardedCommonTailRightPhysicalRecordAt A strategy hwin
        pair (omegaPrefix env n) (env n) := by
  rw [profiledRawJointGuardedRightControllerLambda_omegaWord_apply A]
  simp [profiledRawJointGuardedCommonTailRightPhysicalRecordAt,
    profiledRawJointGuardedCommonTailRightControllerRecordAt,
    profiledRawJointGuardedCommonRightFiniteStateAfter_eq,
    treePlay, narrowedInducedTree, blockLabelApply,
    branchNode_eq_omegaPrefix, narrowedRecord,
    TransitionRationalTree.labeledTree]

/-- Left natural controller record. -/
theorem profiledRawJointGuardedLeftControllerLambda_omegaWord_eq_recordAt
    (pair : ProfiledRawJointGuardedCommonPair A strategy hwin)
    (env : Nat → In₁ × In₂) (n : Nat) :
    pairedLeftOmegaWord
        (profiledRawJointGuardedLeftControllerLambda A pair.1.2).blind
        (profiledRawJointGuardedLeftControllerLambda A pair.1.2).informedBoth
        env n =
      profiledRawJointGuardedCommonTailLeftPhysicalRecordAt A strategy hwin
        pair (omegaPrefix env n) (env n) := by
  rw [profiledRawJointGuardedLeftControllerLambda_omegaWord_apply A]
  simp [profiledRawJointGuardedCommonTailLeftPhysicalRecordAt,
    profiledRawJointGuardedCommonTailLeftControllerRecordAt,
    profiledRawJointGuardedCommonLeftFiniteStateAfter_eq,
    treePlay, narrowedInducedTree, blockLabelApply,
    branchNode_eq_omegaPrefix, narrowedRecord,
    TransitionRationalTree.labeledTree]

/-- The concrete strict-right carrier word is the natural row-`both` word of
the guarded finite member controller. -/
theorem
    profiledRawJointGuardedCommonTailStrictRightControllerWord_eq_lambdaOmega
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁) :
    profiledRawJointGuardedCommonTailStrictRightControllerWord A strategy hwin
        root env =
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin root
      pairedRightOmegaWord
        (profiledRawJointGuardedRightControllerLambda A pair.1.1).blind
        (profiledRawJointGuardedRightControllerLambda A pair.1.1).informedBoth
        env := by
  dsimp only
  funext n
  rw [profiledRawJointGuardedRightControllerLambda_omegaWord_eq_recordAt A
    strategy hwin]
  cases n with
  | zero =>
      simp [profiledRawJointGuardedCommonTailStrictRightControllerWord,
        profiledRawJointGuardedCommonTailRightPhysicalRecordAt,
        profiledRawJointGuardedCommonTailRightControllerRecordAt,
        profiledRawJointGuardedCommonRightFiniteStateAfter_eq,
        ProfiledRawJointGuardedCommonPair.rightRootRecord, omegaPrefix,
        senderWord, narrowedRecord, narrowedControl, narrowedControlAux,
        TransitionRationalTree.controlAt,
        TransitionRationalTree.labeledTree]
  | succ n =>
      cases n with
      | zero =>
          simp [profiledRawJointGuardedCommonTailStrictRightControllerWord,
            profiledRawJointGuardedCommonTailRightPhysicalRecordAt,
            profiledRawJointGuardedCommonTailRightControllerRecordAt,
            profiledRawJointGuardedCommonRightFiniteStateAfter_eq,
            profiledRawJointGuardedCommonTailInitialRightPending,
            profiledRawJointGuardedCommonTailResolveRightRecord,
            profiledRawJointGuardedInitialCommonStartTwo,
            profiledRawJointGuardedCommonStartTwoShadowOfSuccessor,
            profiledRawJointGuardedCommonStartTwoShadow,
            ProfiledRawJointGuardedCommonPair.rightRootRecord,
            profiledRawJointGuardedCommonNoRecvOne,
            profiledRawJointGuardedCommonRightOwnerFor, omegaPrefix,
            narrowedRecord, narrowedControl, narrowedControlAux, senderWord,
            TransitionRationalTree.controlAt,
            TransitionRationalTree.labeledTree]
      | succ n =>
          rcases
              profiledRawJointGuardedCommonTailStrictRightStateTrace_aligned A
                strategy hwin root env n with
            ⟨target, halign⟩
          simp only [profiledRawJointGuardedCommonTailStrictRightControllerWord]
          unfold profiledRawJointGuardedCommonTailStrictRightRecord
          rw [halign]
          simp [profiledRawJointGuardedCommonTailRightPhysicalRecordAt,
            profiledRawJointGuardedCommonTailRightControllerRecordAt,
            profiledRawJointGuardedCommonRightStrictOwnerFor,
            Nat.add_assoc]

/-- Left concrete/natural controller-word equality. -/
theorem
    profiledRawJointGuardedCommonTailStrictLeftControllerWord_eq_lambdaOmega
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂) :
    profiledRawJointGuardedCommonTailStrictLeftControllerWord A strategy hwin
        root env =
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin root
      pairedLeftOmegaWord
        (profiledRawJointGuardedLeftControllerLambda A pair.1.2).blind
        (profiledRawJointGuardedLeftControllerLambda A pair.1.2).informedBoth
        env := by
  dsimp only
  funext n
  rw [profiledRawJointGuardedLeftControllerLambda_omegaWord_eq_recordAt A
    strategy hwin]
  cases n with
  | zero =>
      simp [profiledRawJointGuardedCommonTailStrictLeftControllerWord,
        profiledRawJointGuardedCommonTailLeftPhysicalRecordAt,
        profiledRawJointGuardedCommonTailLeftControllerRecordAt,
        profiledRawJointGuardedCommonLeftFiniteStateAfter_eq,
        ProfiledRawJointGuardedCommonPair.leftRootRecord, omegaPrefix,
        senderWord, narrowedRecord, narrowedControl, narrowedControlAux,
        TransitionRationalTree.controlAt,
        TransitionRationalTree.labeledTree]
  | succ n =>
      cases n with
      | zero =>
          simp [profiledRawJointGuardedCommonTailStrictLeftControllerWord,
            profiledRawJointGuardedCommonTailLeftPhysicalRecordAt,
            profiledRawJointGuardedCommonTailLeftControllerRecordAt,
            profiledRawJointGuardedCommonLeftFiniteStateAfter_eq,
            profiledRawJointGuardedCommonTailInitialLeftPending,
            profiledRawJointGuardedCommonTailResolveLeftRecord,
            profiledRawJointGuardedInitialCommonStartOne,
            profiledRawJointGuardedCommonStartOneShadowOfSuccessor,
            profiledRawJointGuardedCommonStartOneShadow,
            ProfiledRawJointGuardedCommonPair.leftRootRecord,
            profiledRawJointGuardedCommonNoRecvTwo,
            profiledRawJointGuardedCommonLeftOwnerFor, omegaPrefix,
            narrowedRecord, narrowedControl, narrowedControlAux, senderWord,
            TransitionRationalTree.controlAt,
            TransitionRationalTree.labeledTree]
      | succ n =>
          rcases
              profiledRawJointGuardedCommonTailStrictLeftStateTrace_aligned A
                strategy hwin root env n with
            ⟨target, halign⟩
          simp only [profiledRawJointGuardedCommonTailStrictLeftControllerWord]
          unfold profiledRawJointGuardedCommonTailStrictLeftRecord
          rw [halign]
          simp [profiledRawJointGuardedCommonTailLeftPhysicalRecordAt,
            profiledRawJointGuardedCommonTailLeftControllerRecordAt,
            profiledRawJointGuardedCommonLeftStrictOwnerFor,
            Nat.add_assoc]

/-! ## Discharge of the exact acceptance residuals -/

/-- The right `.both` entry state stored in a finite common control is the
literal DPA state of the semantic occurrence represented by that control. -/
theorem profiledRawJointGuardedInitialCommonControlPair_rightEntryState
    (control : CommonControl A strategy hwin) :
    (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control
      ).1.1.1.base.source.1.1.2 =
      (((profiledRawJointGuardedCommonControlPoint A strategy hwin control
        ).world A strategy).procOne A).code.2 := by
  have hmove :=
    profiledRawJointGuardedCommonControlPoint_move A strategy hwin control
  rw [← hmove]
  simp [ProfiledRawJointGuardedCommonSemanticPoint.move,
    profiledRawJointGuardedCommonPairOfWorld,
    profiledRawJointGuardedCommonRightMoveOfWorld,
    profiledRawJointGuardedRightPhysicalSiblingMoveOf,
    profiledRawJointRightPhysicalSiblingDescriptorOf,
    profiledRawRightSlotOfSemanticPair,
    ProfiledRawJointGuardedCommonSemanticPoint.world,
    ProfiledRawJointCommonBaseWorld.procOneMember]

/-- The left guarded descriptor stores the same literal simultaneous-entry
state. -/
theorem profiledRawJointGuardedInitialCommonControlPair_leftEntryState
    (control : CommonControl A strategy hwin) :
    (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control
      ).1.2.1.base.source.1.1.2 =
      (((profiledRawJointGuardedCommonControlPoint A strategy hwin control
        ).world A strategy).procOne A).code.2 := by
  have hmove :=
    profiledRawJointGuardedCommonControlPoint_move A strategy hwin control
  rw [← hmove]
  simp [ProfiledRawJointGuardedCommonSemanticPoint.move,
    profiledRawJointGuardedCommonPairOfWorld,
    profiledRawJointGuardedCommonLeftMoveOfWorld,
    profiledRawJointGuardedLeftPhysicalSiblingMoveOf,
    profiledRawJointLeftPhysicalSiblingDescriptorOf,
    profiledRawLeftSlotOfSemanticPair,
    ProfiledRawJointGuardedCommonSemanticPoint.world,
    ProfiledRawJointCommonBaseWorld.procTwoMember]

/-- The concrete all-strict-right controller word is accepted from the
represented `.both` entry state. -/
theorem
    profiledRawJointGuardedCommonTailStrictRightControllerAcceptsFromEntry
    (root : CommonControl A strategy hwin) :
    ProfiledRawJointGuardedCommonTailStrictRightControllerAcceptsFromEntry A
      strategy hwin root := by
  unfold ProfiledRawJointGuardedCommonTailStrictRightControllerAcceptsFromEntry
  dsimp only
  intro env
  rw [profiledRawJointGuardedCommonTailStrictRightControllerWord_eq_lambdaOmega
    A strategy hwin root env]
  exact
    ((profiledRawJointGuardedInitialCommonControlPair A strategy hwin root
      ).1.1.memberController_forever A).2 env

/-- Left `.both` entry acceptance. -/
theorem
    profiledRawJointGuardedCommonTailStrictLeftControllerAcceptsFromEntry
    (root : CommonControl A strategy hwin) :
    ProfiledRawJointGuardedCommonTailStrictLeftControllerAcceptsFromEntry A
      strategy hwin root := by
  unfold ProfiledRawJointGuardedCommonTailStrictLeftControllerAcceptsFromEntry
  dsimp only
  intro env
  rw [profiledRawJointGuardedCommonTailStrictLeftControllerWord_eq_lambdaOmega
    A strategy hwin root env]
  exact
    ((profiledRawJointGuardedInitialCommonControlPair A strategy hwin root
      ).1.2.memberController_forever A).2 env

/-! ## Finite-prefix splice -/

/-- Any finite prefix that reaches the represented right entry state can be
spliced in front of the concrete strict-right tail.  This is the exact DPA
handoff needed by an outer physical trace; it makes no claim that the
unprefixed tail starts at `A.initial`. -/
theorem
    profiledRawJointGuardedCommonTailStrictRight_accepts_prependList
    (root : CommonControl A strategy hwin) (env : Nat → In₂ × In₁)
    (pre : List (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hentry : pre.foldl A.step A.initial =
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin root
        ).1.1.1.base.source.1.1.2) :
    A.Accepts
      (OmegaWord.prependList pre
        (profiledRawJointGuardedCommonTailStrictRightControllerWord A strategy
          hwin root env)) := by
  rw [accepts_prependList_iff_acceptsFrom A, hentry]
  exact
    profiledRawJointGuardedCommonTailStrictRightControllerAcceptsFromEntry A
      strategy hwin root env

/-- Left finite-prefix splice. -/
theorem
    profiledRawJointGuardedCommonTailStrictLeft_accepts_prependList
    (root : CommonControl A strategy hwin) (env : Nat → In₁ × In₂)
    (pre : List (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hentry : pre.foldl A.step A.initial =
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin root
        ).1.2.1.base.source.1.1.2) :
    A.Accepts
      (OmegaWord.prependList pre
        (profiledRawJointGuardedCommonTailStrictLeftControllerWord A strategy
          hwin root env)) := by
  rw [accepts_prependList_iff_acceptsFrom A, hentry]
  exact
    profiledRawJointGuardedCommonTailStrictLeftControllerAcceptsFromEntry A
      strategy hwin root env

/-! ## The literal two-round seed reaches both strict entry states -/

/-- The original two simultaneous seed rounds reach the right `.both` entry
state stored by the selected guarded-common bank root. -/
theorem profiledRawJointGuardedCommonSeedPrefix_rightEntryState
    (inputs : Nat → In₁ × In₂) :
    let root := profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
      (inputs 0, inputs 1)
    let pre :=
      [profiledRawJointGuardedForeverCommonFirstRound strategy inputs,
        profiledRawJointGuardedForeverCommonSecondRound A strategy inputs]
    pre.foldl A.step A.initial =
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin root
        ).1.1.1.base.source.1.1.2 := by
  dsimp only
  let pre : List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
    [profiledRawJointGuardedForeverCommonFirstRound strategy inputs,
      profiledRawJointGuardedForeverCommonSecondRound A strategy inputs]
  let tail :=
    profiledRawJointGuardedForeverCommonTailWord A strategy hwin inputs
  have hfold :
      A.run
          (profiledRawJointGuardedForeverCommonPhysicalWord A strategy hwin
            inputs) 2 =
        pre.foldl A.step A.initial := by
    simpa [profiledRawJointGuardedForeverCommonPhysicalWord, pre, tail] using
      (runFrom_prependList_length A pre tail A.initial)
  calc
    pre.foldl A.step A.initial =
        A.run
          (profiledRawJointGuardedForeverCommonPhysicalWord A strategy hwin
            inputs) 2 := hfold.symm
    _ = (((profiledRawJointGuardedCommonControlPoint A strategy hwin
          (profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
            (inputs 0, inputs 1))).world A strategy).procOne A).code.2 := by
      simpa using
        profiledRawJointGuardedForeverCommon_run_two A strategy hwin inputs
    _ = (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          (profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
            (inputs 0, inputs 1))).1.1.1.base.source.1.1.2 :=
      (profiledRawJointGuardedInitialCommonControlPair_rightEntryState A
        strategy hwin _).symm

/-- The same literal seed reaches the left guarded descriptor's `.both`
entry state. -/
theorem profiledRawJointGuardedCommonSeedPrefix_leftEntryState
    (inputs : Nat → In₁ × In₂) :
    let root := profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
      (inputs 0, inputs 1)
    let pre :=
      [profiledRawJointGuardedForeverCommonFirstRound strategy inputs,
        profiledRawJointGuardedForeverCommonSecondRound A strategy inputs]
    pre.foldl A.step A.initial =
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin root
        ).1.2.1.base.source.1.1.2 := by
  dsimp only
  rw [profiledRawJointGuardedCommonSeedPrefix_rightEntryState A strategy hwin
    inputs]
  exact
    (profiledRawJointGuardedInitialCommonControlPair_rightEntryState A strategy
      hwin _).trans
      (profiledRawJointGuardedInitialCommonControlPair_leftEntryState A
        strategy hwin _).symm

/-- Fully prefixed strict-right physical acceptance from the literal bank
seed. -/
theorem profiledRawJointGuardedCommonSeedStrictRightWord_accepts
    (inputs : Nat → In₁ × In₂) (env : Nat → In₂ × In₁) :
    let root := profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
      (inputs 0, inputs 1)
    let pre :=
      [profiledRawJointGuardedForeverCommonFirstRound strategy inputs,
        profiledRawJointGuardedForeverCommonSecondRound A strategy inputs]
    A.Accepts
      (OmegaWord.prependList pre
        (profiledRawJointGuardedCommonTailStrictRightControllerWord A strategy
          hwin root env)) := by
  dsimp only
  apply
    profiledRawJointGuardedCommonTailStrictRight_accepts_prependList A strategy
      hwin
  exact profiledRawJointGuardedCommonSeedPrefix_rightEntryState A strategy hwin
    inputs

/-- Fully prefixed strict-left physical acceptance. -/
theorem profiledRawJointGuardedCommonSeedStrictLeftWord_accepts
    (inputs : Nat → In₁ × In₂) (env : Nat → In₁ × In₂) :
    let root := profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
      (inputs 0, inputs 1)
    let pre :=
      [profiledRawJointGuardedForeverCommonFirstRound strategy inputs,
        profiledRawJointGuardedForeverCommonSecondRound A strategy inputs]
    A.Accepts
      (OmegaWord.prependList pre
        (profiledRawJointGuardedCommonTailStrictLeftControllerWord A strategy
          hwin root env)) := by
  dsimp only
  apply
    profiledRawJointGuardedCommonTailStrictLeft_accepts_prependList A strategy
      hwin
  exact profiledRawJointGuardedCommonSeedPrefix_leftEntryState A strategy hwin
    inputs

end

end DetParityAutomaton

end DistributedSynthesis
