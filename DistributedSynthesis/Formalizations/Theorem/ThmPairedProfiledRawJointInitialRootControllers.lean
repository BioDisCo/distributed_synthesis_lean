/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointInitialGuardedKeyMonitor
import DistributedSynthesis.Formalizations.Theorem.ThmRootPinnedBlockNarrowing

/-!
# Root-compatible guarded raw-joint initial controllers

The guarded initial monitors already stage the finite key needed by the
exceptional block.  Their two sender-narrowed controllers must additionally
agree at the unique physical root: on an immediate `both` round process one
uses the initial-left receiver table while process two uses the initial-right
receiver table.  Independent narrowing would not preserve the two crossed
outputs.

We therefore root-pin both guarded monitors to the literal record of the
original winning strategy before narrowing.  The resulting finite
controllers retain all guarded-key checks and their crossed root outputs are
definitionally the outputs of one original strategy round.  This is a
one-round compatibility pin, not an orientation or strict-leader signal.
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

/-! ## Literal root records -/

/-- Literal guarded initial-left record at the empty block history. -/
def profiledRawJointInitialLeftRootRecord
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (move : In₁ × In₂) :
    RealizedBlockRound In₁ In₂
      (ProfiledRawJointInitialLeftReceiverOutput A strategy) Out₂ :=
  (move,
    profiledRawJointInitialLeftReceiverStrategy A strategy [] move,
    initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy) []
      move.2)

/-- Literal guarded initial-right record, with the physical move in the
receiver/sender order of that monitor. -/
def profiledRawJointInitialRightRootRecord
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (move : In₂ × In₁) :
    RealizedBlockRound In₂ In₁
      (ProfiledRawJointInitialRightReceiverOutput A strategy) Out₁ :=
  (move,
    profiledRawJointInitialRightReceiverStrategy A strategy [] move,
    initialRightSenderStrategy (initialRightLambdaOfStrategy strategy) []
      move.2)

/-! ## Simultaneously selected finite controllers -/

/-- The two guarded initial controllers, narrowed only after their literal
root records have been pinned. -/
structure ProfiledRawJointRootCompatibleInitialControllers
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) where
  leftController :
    TransitionRationalTree.{v, max u v x y s, max u v x y s} In₂
      (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointInitialLeftReceiverOutput A strategy) Out₂
        ((profiledRawJointInitialLeftBlockMonitor A strategy).rootPinned
          (profiledRawJointInitialLeftRootRecord A strategy)).State)
  leftWins : NarrowedAllThreadsWin
    ((profiledRawJointInitialLeftBlockMonitor A strategy).rootPinned
      (profiledRawJointInitialLeftRootRecord A strategy))
    leftController.labeledTree
  rightController :
    TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
      (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointInitialRightReceiverOutput A strategy) Out₁
        ((profiledRawJointInitialRightBlockMonitor A strategy).rootPinned
          (profiledRawJointInitialRightRootRecord A strategy)).State)
  rightWins : NarrowedAllThreadsWin
    ((profiledRawJointInitialRightBlockMonitor A strategy).rootPinned
      (profiledRawJointInitialRightRootRecord A strategy))
    rightController.labeledTree

/-- A winning strategy supplies both root-compatible guarded controllers.
The two choices are made proof-side once; neither local controller receives a
side or graph argument. -/
noncomputable def profiledRawJointRootCompatibleInitialControllersOfWinning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    ProfiledRawJointRootCompatibleInitialControllers A strategy := by
  classical
  let leftMonitor := profiledRawJointInitialLeftBlockMonitor A strategy
  let leftExpected := profiledRawJointInitialLeftRootRecord A strategy
  have hleftRoot : ∀ move : In₁ × In₂,
      pairPlay (profiledRawJointInitialLeftReceiverStrategy A strategy)
          (initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy))
          (fun _ ↦ move) 0 = leftExpected move := by
    intro move
    rfl
  have hleftRealizable :
      ∃ receiver : ReceiverBlockStrategy In₁ In₂
          (ProfiledRawJointInitialLeftReceiverOutput A strategy),
        ∃ sender : SenderBlockStrategy In₂ Out₂,
          ∀ env : Nat → In₁ × In₂,
            (leftMonitor.rootPinned leftExpected).WinsPlay
              (pairPlay receiver sender env) := by
    refine ⟨profiledRawJointInitialLeftReceiverStrategy A strategy,
      initialLeftSenderStrategy (initialLeftLambdaOfStrategy strategy), ?_⟩
    exact leftMonitor.rootPinned_realizable leftExpected _ _
      (profiledRawJointInitialLeftBlockMonitor_wins A strategy hwin) hleftRoot
  have hleft :=
    (block_realizable_iff_implementable_controller_unconditional
      (leftMonitor.rootPinned leftExpected)).mp hleftRealizable

  let rightMonitor := profiledRawJointInitialRightBlockMonitor A strategy
  let rightExpected := profiledRawJointInitialRightRootRecord A strategy
  have hrightRoot : ∀ move : In₂ × In₁,
      pairPlay (profiledRawJointInitialRightReceiverStrategy A strategy)
          (initialRightSenderStrategy (initialRightLambdaOfStrategy strategy))
          (fun _ ↦ move) 0 = rightExpected move := by
    intro move
    rfl
  have hrightRealizable :
      ∃ receiver : ReceiverBlockStrategy In₂ In₁
          (ProfiledRawJointInitialRightReceiverOutput A strategy),
        ∃ sender : SenderBlockStrategy In₁ Out₁,
          ∀ env : Nat → In₂ × In₁,
            (rightMonitor.rootPinned rightExpected).WinsPlay
              (pairPlay receiver sender env) := by
    refine ⟨profiledRawJointInitialRightReceiverStrategy A strategy,
      initialRightSenderStrategy (initialRightLambdaOfStrategy strategy), ?_⟩
    exact rightMonitor.rootPinned_realizable rightExpected _ _
      (profiledRawJointInitialRightBlockMonitor_wins A strategy hwin)
      hrightRoot
  have hright :=
    (block_realizable_iff_implementable_controller_unconditional
      (rightMonitor.rootPinned rightExpected)).mp hrightRealizable
  exact {
    leftController := Classical.choose hleft
    leftWins := Classical.choose_spec hleft
    rightController := Classical.choose hright
    rightWins := Classical.choose_spec hright }

/-! ## Immediate-`both` compatibility -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process one's actual receive output from the left controller equals the
process-one crossed output stored by the right controller. -/
theorem profiledRawJointInitialRoot_outputOne_compatible
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers :
      ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (move : In₁ × In₂) :
    ((controllers.leftController.labelOf
        controllers.leftController.initial).2
      ((profiledRawJointInitialLeftBlockMonitor A strategy).rootPinned
        (profiledRawJointInitialLeftRootRecord A strategy)).initial
      move).1.informedOne =
    ((controllers.rightController.labelOf
        controllers.rightController.initial).2
      ((profiledRawJointInitialRightBlockMonitor A strategy).rootPinned
        (profiledRawJointInitialRightRootRecord A strategy)).initial
      (move.2, move.1)).1.reversingOne := by
  have hleft :=
    (profiledRawJointInitialLeftBlockMonitor A strategy).rootPinned_root_record
      (profiledRawJointInitialLeftRootRecord A strategy)
      controllers.leftController.labeledTree controllers.leftWins move
  have hright :=
    (profiledRawJointInitialRightBlockMonitor A strategy).rootPinned_root_record
      (profiledRawJointInitialRightRootRecord A strategy)
      controllers.rightController.labeledTree controllers.rightWins
      (move.2, move.1)
  have hleftOut := congrArg (fun letter ↦ letter.2.1.1.informedOne) hleft
  have hrightOut := congrArg (fun letter ↦ letter.2.1.1.reversingOne) hright
  have hleftOut' :
      ((controllers.leftController.labelOf
          controllers.leftController.initial).2
        ((profiledRawJointInitialLeftBlockMonitor A strategy).rootPinned
          (profiledRawJointInitialLeftRootRecord A strategy)).initial
        move).1.informedOne =
      (profiledRawJointInitialLeftRootRecord A strategy
        move).2.1.1.informedOne := by
    simpa [narrowedRecord, TransitionRationalTree.labeledTree,
      TransitionRationalTree.controlAt] using hleftOut
  have hrightOut' :
      ((controllers.rightController.labelOf
          controllers.rightController.initial).2
        ((profiledRawJointInitialRightBlockMonitor A strategy).rootPinned
          (profiledRawJointInitialRightRootRecord A strategy)).initial
        (move.2, move.1)).1.reversingOne =
      (profiledRawJointInitialRightRootRecord A strategy
        (move.2, move.1)).2.1.1.reversingOne := by
    simpa [narrowedRecord, TransitionRationalTree.labeledTree,
      TransitionRationalTree.controlAt] using hrightOut
  rw [hleftOut', hrightOut']
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two mirror of the crossed root compatibility. -/
theorem profiledRawJointInitialRoot_outputTwo_compatible
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (controllers :
      ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (move : In₁ × In₂) :
    ((controllers.leftController.labelOf
        controllers.leftController.initial).2
      ((profiledRawJointInitialLeftBlockMonitor A strategy).rootPinned
        (profiledRawJointInitialLeftRootRecord A strategy)).initial
      move).1.reversingTwo =
    ((controllers.rightController.labelOf
        controllers.rightController.initial).2
      ((profiledRawJointInitialRightBlockMonitor A strategy).rootPinned
        (profiledRawJointInitialRightRootRecord A strategy)).initial
      (move.2, move.1)).1.informedTwo := by
  have hleft :=
    (profiledRawJointInitialLeftBlockMonitor A strategy).rootPinned_root_record
      (profiledRawJointInitialLeftRootRecord A strategy)
      controllers.leftController.labeledTree controllers.leftWins move
  have hright :=
    (profiledRawJointInitialRightBlockMonitor A strategy).rootPinned_root_record
      (profiledRawJointInitialRightRootRecord A strategy)
      controllers.rightController.labeledTree controllers.rightWins
      (move.2, move.1)
  have hleftOut := congrArg (fun letter ↦ letter.2.1.1.reversingTwo) hleft
  have hrightOut := congrArg (fun letter ↦ letter.2.1.1.informedTwo) hright
  have hleftOut' :
      ((controllers.leftController.labelOf
          controllers.leftController.initial).2
        ((profiledRawJointInitialLeftBlockMonitor A strategy).rootPinned
          (profiledRawJointInitialLeftRootRecord A strategy)).initial
        move).1.reversingTwo =
      (profiledRawJointInitialLeftRootRecord A strategy
        move).2.1.1.reversingTwo := by
    simpa [narrowedRecord, TransitionRationalTree.labeledTree,
      TransitionRationalTree.controlAt] using hleftOut
  have hrightOut' :
      ((controllers.rightController.labelOf
          controllers.rightController.initial).2
        ((profiledRawJointInitialRightBlockMonitor A strategy).rootPinned
          (profiledRawJointInitialRightRootRecord A strategy)).initial
        (move.2, move.1)).1.informedTwo =
      (profiledRawJointInitialRightRootRecord A strategy
        (move.2, move.1)).2.1.1.informedTwo := by
    simpa [narrowedRecord, TransitionRationalTree.labeledTree,
      TransitionRationalTree.controlAt] using hrightOut
  rw [hleftOut', hrightOut']
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
