/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedInitialLocalHandoff

/-!
# The locally indistinguishable root pair

On the first synchronizing round process one must take the same receive branch
as on a strict-left round, while process two must take the same receive branch
as on a strict-right round.  Each side therefore advances both of its locally
computable initial shadows.  The root pin proves that the hybrid physical
output is simultaneously the initial-left and initial-right physical output.

This is the fail-fast locality test missing from the post-initial overlap
calculation.  It uses no graph, phase, or strict-leader input.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (rightBasis : ∀ target profile,
    (rightProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (leftBasis : ∀ target profile,
    (leftProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (controllers : LocallyConsistentProfiledGuardedInitialControllers
    A strategy hwin rightBasis leftBasis)

/-- Process one's finite state after its root receive branch: the complete
initial-left receiver state and the simultaneously advanced initial-right
blind control. -/
abbrev ProfiledRootHybridOne :=
  (ProfiledGuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers × Option (ProfiledGuardedFirstRightMacro A)) ×
    controllers.rightController.Control

/-- Process-two mirror. -/
abbrev ProfiledRootHybridTwo :=
  controllers.leftController.Control ×
    (ProfiledGuardedInitialRightFiniteReadbackState A strategy hwin rightBasis
      leftBasis controllers × Option (ProfiledGuardedFirstLeftMacro A))

/-- The root receive branch of process one.  Both local shadows are advanced,
but the emitted output is the initial-left informed component. -/
noncomputable def profiledRootRecvOne (move : In₁ × In₂) :
    Out₁ × ProfiledRootHybridOne A strategy hwin rightBasis leftBasis
      controllers :=
  let left := profiledGuardedInitialLeftFiniteReadbackInitial A strategy hwin
    rightBasis leftBasis controllers
  let answer := (controllers.leftController.labelOf left.1).2 left.2 move
  (answer.1.informedOne,
    ((stepProfiledGuardedInitialLeftFiniteReadback A strategy hwin rightBasis
        leftBasis controllers left move,
      profiledGuardedInitialLeftLocalFirstMacro A strategy hwin rightBasis
        leftBasis controllers left move),
      controllers.rightController.step controllers.rightController.initial
        move.1))

/-- The locally indistinguishable root receive branch of process two. -/
noncomputable def profiledRootRecvTwo (move : In₁ × In₂) :
    Out₂ × ProfiledRootHybridTwo A strategy hwin rightBasis leftBasis
      controllers :=
  let right := profiledGuardedInitialRightFiniteReadbackInitial A strategy hwin
    rightBasis leftBasis controllers
  let answer := (controllers.rightController.labelOf right.1).2 right.2
    (move.2, move.1)
  (answer.1.informedTwo,
    (controllers.leftController.step controllers.leftController.initial move.2,
      (stepProfiledGuardedInitialRightFiniteReadback A strategy hwin rightBasis
        leftBasis controllers right (move.2, move.1),
      profiledGuardedInitialRightLocalFirstMacro A strategy hwin rightBasis
        leftBasis controllers right (move.2, move.1))))

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledRootRecvOne_output
    (move : In₁ × In₂) :
    (profiledRootRecvOne A strategy hwin rightBasis leftBasis controllers
      move).1 =
      (profiledGuardedInitialLeftReceiverOfController A strategy hwin
        rightBasis leftBasis controllers [] move).1.informedOne := by
  rfl

theorem profiledRootRecvTwo_output
    (move : In₁ × In₂) :
    (profiledRootRecvTwo A strategy hwin rightBasis leftBasis controllers
      move).1 =
      (profiledGuardedInitialRightReceiverOfController A strategy hwin
        rightBasis leftBasis controllers [] (move.2, move.1)).1.informedTwo := by
  rfl

/-- The hybrid root pair is exactly the initial-left physical pair. -/
theorem profiledRootHybrid_output_eq_left
    (move : In₁ × In₂) :
    ((profiledRootRecvOne A strategy hwin rightBasis leftBasis controllers
        move).1,
      (profiledRootRecvTwo A strategy hwin rightBasis leftBasis controllers
        move).1) =
      ((profiledGuardedInitialLeftReceiverOfController A strategy hwin
          rightBasis leftBasis controllers [] move).1.informedOne,
        (profiledGuardedInitialLeftReceiverOfController A strategy hwin
          rightBasis leftBasis controllers [] move).1.reversingTwo) := by
  apply Prod.ext
  · exact profiledRootRecvOne_output A strategy hwin rightBasis leftBasis
      controllers move
  · rw [profiledRootRecvTwo_output]
    exact (profiledGuardedInitialControllers_root_outputTwo A strategy hwin
      rightBasis leftBasis controllers move).symm

/-- The same hybrid pair is exactly the initial-right physical pair. -/
theorem profiledRootHybrid_output_eq_right
    (move : In₁ × In₂) :
    ((profiledRootRecvOne A strategy hwin rightBasis leftBasis controllers
        move).1,
      (profiledRootRecvTwo A strategy hwin rightBasis leftBasis controllers
        move).1) =
      ((profiledGuardedInitialRightReceiverOfController A strategy hwin
          rightBasis leftBasis controllers [] (move.2, move.1)).1.reversingOne,
        (profiledGuardedInitialRightReceiverOfController A strategy hwin
          rightBasis leftBasis controllers [] (move.2, move.1)).1.informedTwo) := by
  apply Prod.ext
  · rw [profiledRootRecvOne_output]
    exact profiledGuardedInitialControllers_root_outputOne A strategy hwin
      rightBasis leftBasis controllers move
  · exact profiledRootRecvTwo_output A strategy hwin rightBasis leftBasis
      controllers move

/-- Both root receive branches carry the exact one-step finite readbacks and
their handoff options are populated. -/
theorem profiledRootHybrid_states_real
    (move : In₁ × In₂) :
    let one := profiledRootRecvOne A strategy hwin rightBasis leftBasis
      controllers move
    let two := profiledRootRecvTwo A strategy hwin rightBasis leftBasis
      controllers move
    one.2.1.1 =
        profiledGuardedInitialLeftFiniteReadbackAfter A strategy hwin
          rightBasis leftBasis controllers [move] ∧
      one.2.1.2 = some
        (profiledGuardedInitialLeftController_firstMacroAt A strategy hwin
          rightBasis leftBasis controllers [] move) ∧
      two.2.2.1 =
        profiledGuardedInitialRightFiniteReadbackAfter A strategy hwin
          rightBasis leftBasis controllers [(move.2, move.1)] ∧
      two.2.2.2 = some
        (profiledGuardedInitialRightController_firstMacroAt A strategy hwin
          rightBasis leftBasis controllers [] (move.2, move.1)) := by
  dsimp only
  constructor
  · rfl
  constructor
  · exact profiledGuardedInitialLeftLocalFirstMacro_eq_some A strategy hwin
      rightBasis leftBasis controllers [] move
  constructor
  · rfl
  · exact profiledGuardedInitialRightLocalFirstMacro_eq_some A strategy hwin
      rightBasis leftBasis controllers [] (move.2, move.1)

end

/-! ## The second synchronizing round resolves the root ambiguity -/

/-- On a second receive, process one can advance the initial-left component
of its hybrid state.  The partner hybrid tells it that the preceding round
was synchronizing; no graph bit is consulted. -/
noncomputable def profiledRootHybridBothAgainOne
    (hybrid : ProfiledRootHybridOne A strategy hwin rightBasis leftBasis
      controllers) (move : In₁ × In₂) : Out₁ :=
  let left := hybrid.1.1
  let answer := (controllers.leftController.labelOf left.1).2 left.2 move
  answer.1.informedOne

/-- Process two advances the initial-left blind component that it retained in
the same root hybrid. -/
noncomputable def profiledRootHybridBothAgainTwo
    (hybrid : ProfiledRootHybridTwo A strategy hwin rightBasis leftBasis
      controllers) (inputTwo : In₂) : Out₂ :=
  (controllers.leftController.labelOf hybrid.1).1 inputTwo

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- After one hybrid root round, the next `both` output is already one
ordinary initial-left controller round.  Thus the special root ambiguity has
depth exactly one. -/
theorem profiledRootHybrid_secondBoth_eq_initialLeft
    (first second : In₁ × In₂) :
    (profiledRootHybridBothAgainOne A strategy hwin rightBasis leftBasis
        controllers
        (profiledRootRecvOne A strategy hwin rightBasis leftBasis controllers
          first).2 second,
      profiledRootHybridBothAgainTwo A strategy hwin rightBasis leftBasis
        controllers
        (profiledRootRecvTwo A strategy hwin rightBasis leftBasis controllers
          first).2 second.2) =
      ((profiledGuardedInitialLeftReceiverOfController A strategy hwin
          rightBasis leftBasis controllers [first] second).1.informedOne,
        profiledGuardedInitialLeftSenderOfController A strategy hwin
          rightBasis leftBasis controllers [first.2] second.2) := by
  apply Prod.ext
  · have hstate :=
      (profiledRootHybrid_states_real A strategy hwin rightBasis leftBasis
        controllers first).1
    unfold profiledRootHybridBothAgainOne
    rw [hstate, profiledGuardedInitialLeftFiniteReadbackAfter_eq]
    rfl
  · simp [profiledRootHybridBothAgainTwo, profiledRootRecvTwo,
      profiledGuardedInitialLeftSenderOfController,
      TransitionRationalTree.labeledTree, TransitionRationalTree.controlAt]

end

end


end DetParityAutomaton

end DistributedSynthesis
