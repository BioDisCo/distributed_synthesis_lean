/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactTailHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactMirrorSeam
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreStrictAcceptance

/-!
# Direct acceptance of the heterogeneous literal seam

The code-erased (`false`) member of each literal seam is already checked by
the corresponding physical sibling monitor.  This file reads that monitor
directly from the shared heterogeneous table.  It deliberately does not
identify the resulting omega word with an ordinary rerooted policy word;
the first-two guard supplies no such arbitrary-depth equality.
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

/-! ## Right seam: the code-erased left physical member -/

/-- Physical projection of the `false` member of the right/`both` literal
seam. -/
noncomputable def profiledRawJointLiteralRightBothExactFalsePlay
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointLiteralRightBothExactFalseReceiverOutput A) Out₂ :=
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed
  let controller := table.memberController false
  BlockRecordMonitor.projectReceiverPlay Prod.fst
    (treePlay (narrowedInducedTree _ controller.labeledTree) env)

/-- The projected `false` play wins its unguarded physical sibling monitor.
This is a direct consequence of the table member's monitor obligation. -/
theorem profiledRawJointLiteralRightBothExactFalsePlay_wins
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) :
    (profiledRawJointLeftPhysicalSiblingMonitor A
      (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
        installed) false).WinsPlay
      (profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
        installed env) := by
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed
  let controller := table.memberController false
  let productPlay := treePlay
    (narrowedInducedTree _ controller.labeledTree) env
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A
    (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
      installed) false
  have hproduct := table.memberController_base_wins false env
  have hcomap :
      (monitor.restartAt monitor.initial |>.comapReceiverOutput
        Prod.fst).WinsPlay productPlay := by
    simpa [table, controller, productPlay, monitor,
      finiteCrossAnchorRestartFamily,
      finiteCrossAnchorHeterogeneousMonitor,
      finiteCrossAnchorHeterogeneousStart,
      BlockRecordMonitor.restartAt,
      BlockRecordMonitor.comapReceiverOutput] using hproduct
  have hmonitorRestart :=
    (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (monitor.restartAt monitor.initial) Prod.fst productPlay).mp hcomap
  simpa [profiledRawJointLiteralRightBothExactFalsePlay, table, controller,
    productPlay, monitor, BlockRecordMonitor.restartAt] using hmonitorRestart

/-- Reachable-state form of the preceding theorem.  The restart state is the
one actually reached by the heterogeneous member play, not an arbitrary
state of the finite controller. -/
theorem profiledRawJointLiteralRightBothExactFalsePlay_wins_suffix
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) (cut : Nat) :
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor A
      (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
        installed) false
    let play := profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
      installed env
    (monitor.restartAt (monitor.run play cut)).WinsPlay
      (fun k ↦ play (cut + k)) := by
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A
    (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
      installed) false
  let play := profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
    installed env
  exact monitor.restartAt_wins_suffix play cut
    (profiledRawJointLiteralRightBothExactFalsePlay_wins A strategy hwin
      installed env)

/-- The model-facing process-two lambda stored by the `false` member.  The
receiver reads only the active first product coordinate; the hidden member
bit is not an input of either local map. -/
noncomputable def profiledRawJointLiteralRightBothExactFalseLambda
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed
  let controller := table.memberController false
  {
    blind := fun word input ↦ (controller.labeledTree word).1 input
    informedRight := fun past input ↦
      (((controller.labeledTree (senderWord past)).2
        (narrowedControl _ controller.labeledTree past) input).1
        ).physical.informedFirst
    informedBoth := fun past input ↦
      (((controller.labeledTree (senderWord past)).2
        (narrowedControl _ controller.labeledTree past) input).1
        ).physical.informedBoth
    bothTwoRight := fun past input ↦
      (((controller.labeledTree (senderWord past)).2
        (narrowedControl _ controller.labeledTree past) input).1
        ).physical.closingFirst
    bothTwoBoth := fun past input ↦
      (((controller.labeledTree (senderWord past)).2
        (narrowedControl _ controller.labeledTree past) input).1
        ).physical.closingBoth
  }

theorem profiledRawJointLiteralRightBothExactFalseLambda_blockWord
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointTargetLeftPhysicalLetter A
        (profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
          installed env n) =
      pairedLeftBlockWord
        (profiledRawJointLiteralRightBothExactFalseLambda A strategy hwin
          installed) env n := by
  simp [profiledRawJointLiteralRightBothExactFalsePlay,
    profiledRawJointLiteralRightBothExactFalseLambda,
    treePlay, narrowedInducedTree, blockLabelApply,
    BlockRecordMonitor.projectReceiverPlay,
    profiledRawJointTargetLeftPhysicalLetter, indexedTargetPhysicalLetter,
    branchNode_eq_omegaPrefix, pairedLeftBlockWord, pairedLeftBlockLetterAt]

/-- A fixed continuation in the right literal seam is accepted directly by
the table's active physical monitor. -/
theorem profiledRawJointLiteralRightBothExactFalseLambda_forever
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    PairedLeftForeverAccepts A
      (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
        installed).source.1.1
      (profiledRawJointLiteralRightBothExactFalseLambda A strategy hwin
        installed) := by
  let descriptor :=
    profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin installed
  let base := profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let lambda :=
    profiledRawJointLiteralRightBothExactFalseLambda A strategy hwin installed
  apply pairedLeftForeverAccepts_of_universalDPA A descriptor.source.1.1 lambda
  intro env
  let play :=
    profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin installed env
  have hbase : base.WinsPlay play := by
    simpa [base, descriptor, play] using
      profiledRawJointLiteralRightBothExactFalsePlay_wins A strategy hwin
        installed env
  have hword :
      (fun k ↦ profiledRawJointTargetLeftPhysicalLetter A (play k)) =
        pairedLeftBlockWord lambda env := by
    funext k
    simpa [play, lambda] using
      profiledRawJointLiteralRightBothExactFalseLambda_blockWord A strategy
        hwin installed env k
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
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
      descriptor.source play hbase n
    change (if (base.run play n).2.2.2.2 then
        ((pairedLeftThreadSystem A descriptor.source.1.1
          ).universalRunDPA).priority (base.run play n).1 + 2 else 1) = _
    rw [hsafe, if_pos rfl,
      profiledRawJointTargetLeftBlockMonitor_run_universal A
        (profiledRawJointUnitLeftTargetProjection A)
        (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
        descriptor.source play n,
      hword]
  rw [heq] at hbase
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hbase

/-! ## Left seam: the code-erased right physical member -/

/-- Physical projection of the `false` member of the left/`both` literal
seam. -/
noncomputable def profiledRawJointLiteralLeftBothExactFalsePlay
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointLiteralLeftBothExactFalseReceiverOutput A) Out₁ :=
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed
  let controller := table.memberController false
  BlockRecordMonitor.projectReceiverPlay Prod.fst
    (treePlay (narrowedInducedTree _ controller.labeledTree) env)

/-- Mirror direct monitor proof for the left/`both` literal seam. -/
theorem profiledRawJointLiteralLeftBothExactFalsePlay_wins
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) :
    (profiledRawJointRightPhysicalSiblingMonitor A
      (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
        installed) false).WinsPlay
      (profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
        installed env) := by
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed
  let controller := table.memberController false
  let productPlay := treePlay
    (narrowedInducedTree _ controller.labeledTree) env
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A
    (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
      installed) false
  have hproduct := table.memberController_base_wins false env
  have hcomap :
      (monitor.restartAt monitor.initial |>.comapReceiverOutput
        Prod.fst).WinsPlay productPlay := by
    simpa [table, controller, productPlay, monitor,
      finiteCrossAnchorRestartFamily,
      finiteCrossAnchorHeterogeneousMonitor,
      finiteCrossAnchorHeterogeneousStart,
      BlockRecordMonitor.restartAt,
      BlockRecordMonitor.comapReceiverOutput] using hproduct
  have hmonitorRestart :=
    (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (monitor.restartAt monitor.initial) Prod.fst productPlay).mp hcomap
  simpa [profiledRawJointLiteralLeftBothExactFalsePlay, table, controller,
    productPlay, monitor, BlockRecordMonitor.restartAt] using hmonitorRestart

/-- Mirror reachable-state suffix theorem. -/
theorem profiledRawJointLiteralLeftBothExactFalsePlay_wins_suffix
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) (cut : Nat) :
    let monitor := profiledRawJointRightPhysicalSiblingMonitor A
      (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
        installed) false
    let play := profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
      installed env
    (monitor.restartAt (monitor.run play cut)).WinsPlay
      (fun k ↦ play (cut + k)) := by
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A
    (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
      installed) false
  let play := profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
    installed env
  exact monitor.restartAt_wins_suffix play cut
    (profiledRawJointLiteralLeftBothExactFalsePlay_wins A strategy hwin
      installed env)

/-- Model-facing process-one lambda stored by the mirror table's `false`
member. -/
noncomputable def profiledRawJointLiteralLeftBothExactFalseLambda
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
      hwin installed
  let controller := table.memberController false
  {
    blind := fun word input ↦ (controller.labeledTree word).1 input
    informedLeft := fun past input ↦
      (((controller.labeledTree (senderWord past)).2
        (narrowedControl _ controller.labeledTree past) input).1
        ).physical.informedFirst
    informedBoth := fun past input ↦
      (((controller.labeledTree (senderWord past)).2
        (narrowedControl _ controller.labeledTree past) input).1
        ).physical.informedBoth
    bothOneLeft := fun past input ↦
      (((controller.labeledTree (senderWord past)).2
        (narrowedControl _ controller.labeledTree past) input).1
        ).physical.closingFirst
    bothOneBoth := fun past input ↦
      (((controller.labeledTree (senderWord past)).2
        (narrowedControl _ controller.labeledTree past) input).1
        ).physical.closingBoth
  }

theorem profiledRawJointLiteralLeftBothExactFalseLambda_blockWord
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointTargetRightPhysicalLetter A
        (profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
          installed env n) =
      pairedRightBlockWord
        (profiledRawJointLiteralLeftBothExactFalseLambda A strategy hwin
          installed) env n := by
  simp [profiledRawJointLiteralLeftBothExactFalsePlay,
    profiledRawJointLiteralLeftBothExactFalseLambda,
    treePlay, narrowedInducedTree, blockLabelApply,
    BlockRecordMonitor.projectReceiverPlay,
    profiledRawJointTargetRightPhysicalLetter, indexedTargetPhysicalLetter,
    branchNode_eq_omegaPrefix, pairedRightBlockWord]

/-- Mirror fixed-continuation acceptance, again read directly from the
heterogeneous table monitor. -/
theorem profiledRawJointLiteralLeftBothExactFalseLambda_forever
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    PairedRightForeverAccepts A
      (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
        installed).source.1.1
      (profiledRawJointLiteralLeftBothExactFalseLambda A strategy hwin
        installed) := by
  let descriptor :=
    profiledRawJointHybridExactRightUniformDescriptor A strategy hwin installed
  let base := profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let lambda :=
    profiledRawJointLiteralLeftBothExactFalseLambda A strategy hwin installed
  apply pairedRightForeverAccepts_of_universalDPA A descriptor.source.1.1 lambda
  intro env
  let play :=
    profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin installed env
  have hbase : base.WinsPlay play := by
    simpa [base, descriptor, play] using
      profiledRawJointLiteralLeftBothExactFalsePlay_wins A strategy hwin
        installed env
  have hword :
      (fun k ↦ profiledRawJointTargetRightPhysicalLetter A (play k)) =
        pairedRightBlockWord lambda env := by
    funext k
    simpa [play, lambda] using
      profiledRawJointLiteralLeftBothExactFalseLambda_blockWord A strategy
        hwin installed env k
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
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
      descriptor.source play hbase n
    change (if (base.run play n).2.2.2.2 then
        ((pairedRightThreadSystem A descriptor.source.1.1
          ).universalRunDPA).priority (base.run play n).1 + 2 else 1) = _
    rw [hsafe, if_pos rfl,
      profiledRawJointTargetRightBlockMonitor_run_universal A
        (profiledRawJointUnitRightTargetProjection A)
        (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
        descriptor.source play n,
      hword]
  rw [heq] at hbase
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hbase

end


end DetParityAutomaton

end DistributedSynthesis
