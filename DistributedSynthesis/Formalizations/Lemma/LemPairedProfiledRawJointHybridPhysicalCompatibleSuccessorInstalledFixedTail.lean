/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorActualHandlerCut
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreStrictAcceptance

/-!
# Fixed homogeneous tails of an installed compatible successor table

An installed physical sibling table already carries a universal winning
monitor.  This file reads acceptance directly from that monitor, independently
of the phase-live controller and independently of the simplified
deferred controller.

The model-specific live overlay owes only `InstalledPhysicalTailAligned`: the
actual physical word and DPA state at an eventual homogeneous cut are the same
suffix of one canonical installed-table play.  Orientation occurs only in this
proof-side alignment statement; it is not passed to either endpoint.
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

/-! ## Physical lambdas and canonical words -/

/-- Forget target certificates in one right physical sibling controller. -/
noncomputable def profiledRawJointRightPhysicalSiblingControllerLambda
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 false
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

/-- Left mirror. -/
noncomputable def profiledRawJointLeftPhysicalSiblingControllerLambda
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 false
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

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRightPhysicalSiblingControllerLambda_blockWord
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (env : Nat → In₂ × In₁) (n : Nat) :
    profiledRawJointTargetRightPhysicalLetter A
        (treePlay
          (narrowedInducedTree
            (profiledRawJointRightPhysicalSiblingMonitor A move.1 false)
            (move.memberController A false).labeledTree) env n) =
      pairedRightBlockWord
        (profiledRawJointRightPhysicalSiblingControllerLambda A move) env n := by
  simp [treePlay, narrowedInducedTree, blockLabelApply,
    profiledRawJointTargetRightPhysicalLetter, indexedTargetPhysicalLetter,
    profiledRawJointRightPhysicalSiblingControllerLambda,
    branchNode_eq_omegaPrefix, pairedRightBlockWord]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftPhysicalSiblingControllerLambda_blockWord
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (env : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointTargetLeftPhysicalLetter A
        (treePlay
          (narrowedInducedTree
            (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false)
            (move.memberController A false).labeledTree) env n) =
      pairedLeftBlockWord
        (profiledRawJointLeftPhysicalSiblingControllerLambda A move) env n := by
  simp [treePlay, narrowedInducedTree, blockLabelApply,
    profiledRawJointTargetLeftPhysicalLetter, indexedTargetPhysicalLetter,
    profiledRawJointLeftPhysicalSiblingControllerLambda,
    branchNode_eq_omegaPrefix, pairedLeftBlockWord, pairedLeftBlockLetterAt]

/-- The literal right word of one installed finite move at a fixed entry row. -/
noncomputable def profiledRawJointRightPhysicalSiblingWord
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (row : PairedEntryRow) (env : Nat → In₂ × In₁) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦ pairedRightRecordForRow row
    (profiledRawJointTargetRightPhysicalLetter A
      (treePlay
        (narrowedInducedTree
          (profiledRawJointRightPhysicalSiblingMonitor A move.1 false)
          (move.memberController A false).labeledTree) env n))

/-- Left mirror. -/
noncomputable def profiledRawJointLeftPhysicalSiblingWord
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (row : PairedEntryRow) (env : Nat → In₁ × In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦ pairedLeftRecordForRow row
    (profiledRawJointTargetLeftPhysicalLetter A
      (treePlay
        (narrowedInducedTree
          (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false)
          (move.memberController A false).labeledTree) env n))

/-! ## Universal monitor acceptance -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The unguarded right sibling move is already a winning fixed-tail
controller for both latent entry rows. -/
theorem ProfiledRawJointRightPhysicalSiblingMove.memberController_forever
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    PairedRightForeverAccepts A move.1.source.1.1
      (profiledRawJointRightPhysicalSiblingControllerLambda A move) := by
  let base := profiledRawJointRightPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let lambda := profiledRawJointRightPhysicalSiblingControllerLambda A move
  apply pairedRightForeverAccepts_of_universalDPA A move.1.source.1.1 lambda
  intro env
  let play := treePlay
    (narrowedInducedTree base controller.labeledTree) env
  have htree : base.lift.WinningTree
      (narrowedInducedTree base controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin base
      (move.memberController_wins A false)
  have hbase : base.WinsPlay play :=
    (base.lift_winningTree_iff
      (narrowedInducedTree base controller.labeledTree)).mp htree env
  have hword :
      (fun k ↦ profiledRawJointTargetRightPhysicalLetter A (play k)) =
        pairedRightBlockWord lambda env := by
    funext k
    simpa [play, base, controller, lambda] using
      profiledRawJointRightPhysicalSiblingControllerLambda_blockWord A move
        env k
  unfold BlockRecordMonitor.WinsPlay at hbase
  have heq :
      (fun n ↦ base.priority (base.run play n)) =
        fun n ↦
          ((pairedRightThreadSystem A move.1.source.1.1
            ).universalRunDPA).priority
            ((pairedRightThreadSystem A move.1.source.1.1
              ).universalRunDPA.run (pairedRightBlockWord lambda env) n) + 2 := by
    funext n
    have hsafe := profiledRawJointTargetRightBlockMonitor_safe_of_wins A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A move.1)
      move.1.source play hbase n
    change (if (base.run play n).2.2.2.2 then
        ((pairedRightThreadSystem A move.1.source.1.1
          ).universalRunDPA).priority (base.run play n).1 + 2 else 1) = _
    rw [hsafe, if_pos rfl,
      profiledRawJointTargetRightBlockMonitor_run_universal A
        (profiledRawJointUnitRightTargetProjection A)
        (profiledRawJointRightPhysicalSiblingAllowed A move.1)
        move.1.source play n,
      hword]
  rw [heq] at hbase
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hbase

/-- Left mirror. -/
theorem ProfiledRawJointLeftPhysicalSiblingMove.memberController_forever
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    PairedLeftForeverAccepts A move.1.source.1.1
      (profiledRawJointLeftPhysicalSiblingControllerLambda A move) := by
  let base := profiledRawJointLeftPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let lambda := profiledRawJointLeftPhysicalSiblingControllerLambda A move
  apply pairedLeftForeverAccepts_of_universalDPA A move.1.source.1.1 lambda
  intro env
  let play := treePlay
    (narrowedInducedTree base controller.labeledTree) env
  have htree : base.lift.WinningTree
      (narrowedInducedTree base controller.labeledTree) :=
    narrowedInducedTree_winningTree_of_allThreadsWin base
      (move.memberController_wins A false)
  have hbase : base.WinsPlay play :=
    (base.lift_winningTree_iff
      (narrowedInducedTree base controller.labeledTree)).mp htree env
  have hword :
      (fun k ↦ profiledRawJointTargetLeftPhysicalLetter A (play k)) =
        pairedLeftBlockWord lambda env := by
    funext k
    simpa [play, base, controller, lambda] using
      profiledRawJointLeftPhysicalSiblingControllerLambda_blockWord A move env k
  unfold BlockRecordMonitor.WinsPlay at hbase
  have heq :
      (fun n ↦ base.priority (base.run play n)) =
        fun n ↦
          ((pairedLeftThreadSystem A move.1.source.1.1
            ).universalRunDPA).priority
            ((pairedLeftThreadSystem A move.1.source.1.1
              ).universalRunDPA.run (pairedLeftBlockWord lambda env) n) + 2 := by
    funext n
    have hsafe := profiledRawJointTargetLeftBlockMonitor_safe_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A move.1)
      move.1.source play hbase n
    change (if (base.run play n).2.2.2.2 then
        ((pairedLeftThreadSystem A move.1.source.1.1
          ).universalRunDPA).priority (base.run play n).1 + 2 else 1) = _
    rw [hsafe, if_pos rfl,
      profiledRawJointTargetLeftBlockMonitor_run_universal A
        (profiledRawJointUnitLeftTargetProjection A)
        (profiledRawJointLeftPhysicalSiblingAllowed A move.1)
        move.1.source play n,
      hword]
  rw [heq] at hbase
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hbase

/-- The canonical right word is accepted from its row-selected source. -/
theorem ProfiledRawJointRightPhysicalSiblingMove.physical_acceptsFrom
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (row : PairedEntryRow) (env : Nat → In₂ × In₁) :
    A.AcceptsFrom (pairedCodeStateForRow A row move.1.source.1.1)
      (profiledRawJointRightPhysicalSiblingWord A move row env) := by
  let lambda := profiledRawJointRightPhysicalSiblingControllerLambda A move
  have hforever := move.memberController_forever A
  have hword :
      profiledRawJointRightPhysicalSiblingWord A move row env =
        match row with
        | .first => pairedRightOmegaWord lambda.blind lambda.informedLeft env
        | .both => pairedRightOmegaWord lambda.blind lambda.informedBoth env := by
    funext n
    have hphysical :=
      profiledRawJointRightPhysicalSiblingControllerLambda_blockWord A move env n
    change pairedRightRecordForRow row
        (profiledRawJointTargetRightPhysicalLetter A
          (treePlay
            (narrowedInducedTree
              (profiledRawJointRightPhysicalSiblingMonitor A move.1 false)
              (move.memberController A false).labeledTree) env n)) = _
    rw [hphysical]
    cases row <;> rfl
  rw [hword]
  cases row
  · exact hforever.1 env
  · exact hforever.2 env

/-- Left canonical-word acceptance. -/
theorem ProfiledRawJointLeftPhysicalSiblingMove.physical_acceptsFrom
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (row : PairedEntryRow) (env : Nat → In₁ × In₂) :
    A.AcceptsFrom (pairedCodeStateForRow A row move.1.source.1.1)
      (profiledRawJointLeftPhysicalSiblingWord A move row env) := by
  let lambda := profiledRawJointLeftPhysicalSiblingControllerLambda A move
  have hforever := move.memberController_forever A
  have hword :
      profiledRawJointLeftPhysicalSiblingWord A move row env =
        match row with
        | .first => pairedLeftOmegaWord lambda.blind lambda.informedRight env
        | .both => pairedLeftOmegaWord lambda.blind lambda.informedBoth env := by
    funext n
    have hphysical :=
      profiledRawJointLeftPhysicalSiblingControllerLambda_blockWord A move env n
    change pairedLeftRecordForRow row
        (profiledRawJointTargetLeftPhysicalLetter A
          (treePlay
            (narrowedInducedTree
              (profiledRawJointLeftPhysicalSiblingMonitor A move.1 false)
              (move.memberController A false).labeledTree) env n)) = _
    rw [hphysical]
    cases row <;> rfl
  rw [hword]
  cases row
  · exact hforever.1 env
  · exact hforever.2 env

end

/-! ## The exact live-overlay interface and parity adapter -/

/-- Exact proof-side alignment owed by a strict-right live overlay.  The
actual tail starts at the same DPA state and emits the same suffix as one
canonical installed-table play. -/
structure ProfiledRawJointHybridPhysicalCompatibleRightInstalledPhysicalTailAligned
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (row : PairedEntryRow) (tableEnv : Nat → In₂ × In₁)
    (tableCut : Nat)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) : Prop where
  state : A.run word start =
    A.runFrom (pairedCodeStateForRow A row move.1.source.1.1)
      (profiledRawJointRightPhysicalSiblingWord A move row tableEnv) tableCut
  word : OmegaWord.drop word start =
    OmegaWord.drop
      (profiledRawJointRightPhysicalSiblingWord A move row tableEnv) tableCut

/-- Left mirror. -/
structure ProfiledRawJointHybridPhysicalCompatibleLeftInstalledPhysicalTailAligned
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (row : PairedEntryRow) (tableEnv : Nat → In₁ × In₂)
    (tableCut : Nat)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) : Prop where
  state : A.run word start =
    A.runFrom (pairedCodeStateForRow A row move.1.source.1.1)
      (profiledRawJointLeftPhysicalSiblingWord A move row tableEnv) tableCut
  word : OmegaWord.drop word start =
    OmegaWord.drop
      (profiledRawJointLeftPhysicalSiblingWord A move row tableEnv) tableCut

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- Any actual strict-right tail satisfying the two alignment equations is
accepted from its actual post-prefix DPA state. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleRightInstalledPhysicalTailAligned.acceptsFrom
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (row : PairedEntryRow) (tableEnv : Nat → In₂ × In₁)
    (tableCut : Nat)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (aligned :
      ProfiledRawJointHybridPhysicalCompatibleRightInstalledPhysicalTailAligned
        A move row tableEnv tableCut word start) :
    A.AcceptsFrom (A.run word start) (OmegaWord.drop word start) := by
  rw [aligned.state, aligned.word]
  exact
    (A.acceptsFrom_runFrom_drop_iff
      (pairedCodeStateForRow A row move.1.source.1.1)
      (profiledRawJointRightPhysicalSiblingWord A move row tableEnv)
      tableCut).mpr
        (move.physical_acceptsFrom A row tableEnv)

/-- Left acceptance mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleLeftInstalledPhysicalTailAligned.acceptsFrom
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (row : PairedEntryRow) (tableEnv : Nat → In₁ × In₂)
    (tableCut : Nat)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (aligned :
      ProfiledRawJointHybridPhysicalCompatibleLeftInstalledPhysicalTailAligned
        A move row tableEnv tableCut word start) :
    A.AcceptsFrom (A.run word start) (OmegaWord.drop word start) := by
  rw [aligned.state, aligned.word]
  exact
    (A.acceptsFrom_runFrom_drop_iff
      (pairedCodeStateForRow A row move.1.source.1.1)
      (profiledRawJointLeftPhysicalSiblingWord A move row tableEnv)
      tableCut).mpr
        (move.physical_acceptsFrom A row tableEnv)

/-- Exact eventual strict-right parity in the original physical run. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleRightInstalledPhysicalTailAligned.tailParity
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (row : PairedEntryRow) (tableEnv : Nat → In₂ × In₁)
    (tableCut : Nat)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (aligned :
      ProfiledRawJointHybridPhysicalCompatibleRightInstalledPhysicalTailAligned
        A move row tableEnv tableCut word start) :
    NatSeqMinEvenParity
      (fun n ↦ A.priority (A.run word (start + n))) := by
  have haccepts := aligned.acceptsFrom A move row tableEnv tableCut word start
  have hparity : NatSeqMinEvenParity
      (fun n ↦ A.priority
        (A.runFrom (A.run word start) (OmegaWord.drop word start) n)) :=
    haccepts
  have heq :
      (fun n ↦ A.priority
        (A.runFrom (A.run word start) (OmegaWord.drop word start) n)) =
      (fun n ↦ A.priority (A.run word (start + n))) := by
    funext n
    exact congrArg A.priority (A.runFrom_drop A.initial word start n)
  rw [heq] at hparity
  exact hparity

/-- Exact eventual strict-left parity. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleLeftInstalledPhysicalTailAligned.tailParity
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (row : PairedEntryRow) (tableEnv : Nat → In₁ × In₂)
    (tableCut : Nat)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (aligned :
      ProfiledRawJointHybridPhysicalCompatibleLeftInstalledPhysicalTailAligned
        A move row tableEnv tableCut word start) :
    NatSeqMinEvenParity
      (fun n ↦ A.priority (A.run word (start + n))) := by
  have haccepts := aligned.acceptsFrom A move row tableEnv tableCut word start
  have hparity : NatSeqMinEvenParity
      (fun n ↦ A.priority
        (A.runFrom (A.run word start) (OmegaWord.drop word start) n)) :=
    haccepts
  have heq :
      (fun n ↦ A.priority
        (A.runFrom (A.run word start) (OmegaWord.drop word start) n)) =
      (fun n ↦ A.priority (A.run word (start + n))) := by
    funext n
    exact congrArg A.priority (A.runFrom_drop A.initial word start n)
  rw [heq] at hparity
  exact hparity

end

end


end DetParityAutomaton

end DistributedSynthesis
