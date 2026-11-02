/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialPolicyBank
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointInitialLeaderFreeCarrier

/-!
# The finite initial common/strict shadow

At the physical root, a receiving process cannot distinguish its strict
receive from a simultaneous receive.  Its finite next control must therefore
retain both honest consequences: the old strict-root cross and the common
control reached if the round was simultaneous.  This file packages that
local ambiguity without storing a graph, an orientation, or a leader bit.

The physical root output remains the root-pinned output of the old carrier.
The common control is post-root data: it is consumed only from the following
physical round onward.
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
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)

/-! ## The literal physical root output -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The old root cross emits exactly the literal output of the original
strategy on the first simultaneous round. -/
theorem profiledRawJointHybridInitialRootCross_outputs_eq_literalBoth
    (move : In₁ × In₂) :
    (profiledRawJointInitialRootCrossStep A strategy controllers move).1 =
      let round := nextRound strategy []
        ⟨move.1, move.2, Graph.both⟩
      (round.outputOne, round.outputTwo) := by
  apply Prod.ext
  · have hleft :=
      (profiledRawJointInitialLeftBlockMonitor A strategy).rootPinned_root_record
        (profiledRawJointInitialLeftRootRecord A strategy)
        controllers.leftController.labeledTree controllers.leftWins move
    have hleftOut := congrArg (fun letter ↦ letter.2.1.1.informedOne) hleft
    have hleftOut' :
        ((controllers.leftController.labelOf
            controllers.leftController.initial).2
          (ProfiledRawJointInitialLeftRootMonitor A strategy).initial
          move).1.informedOne =
        (profiledRawJointInitialLeftRootRecord A strategy
          move).2.1.1.informedOne := by
      simpa [narrowedRecord, TransitionRationalTree.labeledTree,
        TransitionRationalTree.controlAt] using hleftOut
    change
      ((controllers.leftController.labelOf
          controllers.leftController.initial).2
        (ProfiledRawJointInitialLeftRootMonitor A strategy).initial
        move).1.informedOne =
      strategy.one
        (nextView Proc.one [] ⟨move.1, move.2, Graph.both⟩)
    rw [hleftOut']
    exact blockReceiverOne_eq_both strategy [] [] move
  · have hright :=
      (profiledRawJointInitialRightBlockMonitor A strategy).rootPinned_root_record
        (profiledRawJointInitialRightRootRecord A strategy)
        controllers.rightController.labeledTree controllers.rightWins
        (move.2, move.1)
    have hrightOut := congrArg (fun letter ↦ letter.2.1.1.informedTwo) hright
    have hrightOut' :
        ((controllers.rightController.labelOf
            controllers.rightController.initial).2
          (ProfiledRawJointInitialRightRootMonitor A strategy).initial
          (move.2, move.1)).1.informedTwo =
        (profiledRawJointInitialRightRootRecord A strategy
          (move.2, move.1)).2.1.1.informedTwo := by
      simpa [narrowedRecord, TransitionRationalTree.labeledTree,
        TransitionRationalTree.controlAt] using hrightOut
    change
      ((controllers.rightController.labelOf
          controllers.rightController.initial).2
        (ProfiledRawJointInitialRightRootMonitor A strategy).initial
        (move.2, move.1)).1.informedTwo =
      strategy.two
        (nextView Proc.two [] ⟨move.1, move.2, Graph.both⟩)
    rw [hrightOut']
    exact blockReceiverTwo_eq_both strategy [] [] (move.2, move.1)

/-! ## The two local finite ambiguity controls -/

/-- Process one's root-receive control retains both the old strict
contingencies and the post-root common candidate. -/
structure ProfiledRawJointHybridInitialOneShadow where
  cross : ProfiledRawJointInitialRootCross A strategy controllers
  common : ProfiledRawJointHybridCommonControl A strategy hwin

/-- Process-two mirror.  It has the same proof-side fields but remains a
separate local control type. -/
structure ProfiledRawJointHybridInitialTwoShadow where
  cross : ProfiledRawJointInitialRootCross A strategy controllers
  common : ProfiledRawJointHybridCommonControl A strategy hwin

noncomputable instance profiledRawJointHybridInitialOneShadowFintype :
    Fintype
      (ProfiledRawJointHybridInitialOneShadow A strategy hwin controllers) := by
  classical
  let Rep :=
    ProfiledRawJointInitialRootCross A strategy controllers ×
      ProfiledRawJointHybridCommonControl A strategy hwin
  let equiv :
      ProfiledRawJointHybridInitialOneShadow A strategy hwin controllers ≃
        Rep := {
    toFun := fun state ↦ (state.cross, state.common)
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨cross, common⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance profiledRawJointHybridInitialTwoShadowFintype :
    Fintype
      (ProfiledRawJointHybridInitialTwoShadow A strategy hwin controllers) := by
  classical
  let Rep :=
    ProfiledRawJointInitialRootCross A strategy controllers ×
      ProfiledRawJointHybridCommonControl A strategy hwin
  let equiv :
      ProfiledRawJointHybridInitialTwoShadow A strategy hwin controllers ≃
        Rep := {
    toFun := fun state ↦ (state.cross, state.common)
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨cross, common⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-! ## Local root-receive steps -/

/-- Process one's root receive, shared operationally by `left` and `both`.
Its physical output is unchanged from the old carrier. -/
noncomputable def profiledRawJointHybridInitialRootRecvOne
    (move : In₁ × In₂) :
    Out₁ ×
      ProfiledRawJointHybridInitialOneShadow A strategy hwin controllers :=
  let next := profiledRawJointInitialRootCrossStep A strategy controllers move
  (next.1.1,
    ⟨next.2,
      profiledRawJointHybridInitialCommonControl A strategy hwin move⟩)

/-- Process-two root receive, shared operationally by `right` and `both`. -/
noncomputable def profiledRawJointHybridInitialRootRecvTwo
    (move : In₁ × In₂) :
    Out₂ ×
      ProfiledRawJointHybridInitialTwoShadow A strategy hwin controllers :=
  let next := profiledRawJointInitialRootCrossStep A strategy controllers move
  (next.1.2,
    ⟨next.2,
      profiledRawJointHybridInitialCommonControl A strategy hwin move⟩)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointHybridInitialRootRecvOne_output
    (move : In₁ × In₂) :
    (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
      move).1 =
      (profiledRawJointInitialRootRecvOne A strategy controllers move).1 :=
  rfl

@[simp] theorem profiledRawJointHybridInitialRootRecvTwo_output
    (move : In₁ × In₂) :
    (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
      move).1 =
      (profiledRawJointInitialRootRecvTwo A strategy controllers move).1 :=
  rfl

/-- Consequently the two local root receives together emit the literal
first simultaneous output. -/
theorem profiledRawJointHybridInitialRootRecv_outputs_eq_literalBoth
    (move : In₁ × In₂) :
    ((profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        move).1,
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        move).1) =
      let round := nextRound strategy []
        ⟨move.1, move.2, Graph.both⟩
      (round.outputOne, round.outputTwo) := by
  exact profiledRawJointHybridInitialRootCross_outputs_eq_literalBoth A
    strategy controllers move

/-- On an actual simultaneous root, both local ambiguity controls retain the
same post-root common candidate. -/
@[simp] theorem profiledRawJointHybridInitialRootRecv_common_agree
    (move : In₁ × In₂) :
    (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
      move).2.common =
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        move).2.common :=
  rfl

@[simp] theorem profiledRawJointHybridInitialRootRecvOne_common
    (move : In₁ × In₂) :
    (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
      move).2.common =
      profiledRawJointHybridInitialCommonControl A strategy hwin move :=
  rfl

@[simp] theorem profiledRawJointHybridInitialRootRecvTwo_common
    (move : In₁ × In₂) :
    (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
      move).2.common =
      profiledRawJointHybridInitialCommonControl A strategy hwin move :=
  rfl

end

/-! ## Strict projections back to the old carrier -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointHybridInitialRootRecvOne_cross
    (move : In₁ × In₂) :
    (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
      move).2.cross =
      (profiledRawJointInitialRootCrossStep A strategy controllers move).2 :=
  rfl

@[simp] theorem profiledRawJointHybridInitialRootRecvTwo_cross
    (move : In₁ × In₂) :
    (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
      move).2.cross =
      (profiledRawJointInitialRootCrossStep A strategy controllers move).2 :=
  rfl

/-- Projecting process one's ambiguous receive to the old cross and pairing
it with process two's old blind owner recovers the strict-left matched shape. -/
theorem profiledRawJointHybridInitialRoot_left_hasMatchedOldShape
    (move : In₁ × In₂) :
    ProfiledRawJointInitialHasMatchedLeftRootShape A strategy controllers
      (.cross
          (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
            move).2.cross,
        (profiledRawJointInitialRootNoRecvTwo A strategy controllers
          move.2).2) := by
  simpa using
    (profiledRawJointInitialRoot_left_hasMatchedShape A strategy controllers
      move)

/-- Strict-right mirror. -/
theorem profiledRawJointHybridInitialRoot_right_hasMatchedOldShape
    (move : In₁ × In₂) :
    ProfiledRawJointInitialHasMatchedRightRootShape A strategy controllers
      ((profiledRawJointInitialRootNoRecvOne A strategy controllers
          move.1).2,
        .cross
          (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
            move).2.cross) := by
  simpa using
    (profiledRawJointInitialRoot_right_hasMatchedShape A strategy controllers
      move)

end

end

end DetParityAutomaton

end DistributedSynthesis
