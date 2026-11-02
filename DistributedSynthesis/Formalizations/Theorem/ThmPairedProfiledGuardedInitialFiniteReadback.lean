/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedInitialLocallyConsistentNarrowing
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedInitialHandoff

/-!
# Finite local readback of profiled guarded initial controllers

The informed process maintains the product of the rational-tree control and
the pinned-monitor control.  The blind process maintains the same rational
tree along its own input word.  The no-receive output is read from a default
partner-input column; table locality proves that this equals every real hidden
partner-input column.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

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

abbrev ProfiledGuardedInitialLeftFiniteReadbackState :=
  controllers.leftController.Control ×
    (profiledGuardedInitialLeftPinnedMonitor A strategy hwin rightBasis).State

abbrev ProfiledGuardedInitialRightFiniteReadbackState :=
  controllers.rightController.Control ×
    (profiledGuardedInitialRightPinnedMonitor A strategy hwin leftBasis).State

noncomputable def profiledGuardedInitialLeftFiniteReadbackInitial :
    ProfiledGuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  (controllers.leftController.initial,
    (profiledGuardedInitialLeftPinnedMonitor A strategy hwin rightBasis).initial)

noncomputable def profiledGuardedInitialRightFiniteReadbackInitial :
    ProfiledGuardedInitialRightFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  (controllers.rightController.initial,
    (profiledGuardedInitialRightPinnedMonitor A strategy hwin leftBasis).initial)

noncomputable def stepProfiledGuardedInitialLeftFiniteReadback
    (state : ProfiledGuardedInitialLeftFiniteReadbackState
      A strategy hwin rightBasis leftBasis controllers)
    (move : In₁ × In₂) :
    ProfiledGuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  let monitor := profiledGuardedInitialLeftPinnedMonitor A strategy hwin rightBasis
  let label := controllers.leftController.labelOf state.1
  (controllers.leftController.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def stepProfiledGuardedInitialRightFiniteReadback
    (state : ProfiledGuardedInitialRightFiniteReadbackState
      A strategy hwin rightBasis leftBasis controllers)
    (move : In₂ × In₁) :
    ProfiledGuardedInitialRightFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  let monitor := profiledGuardedInitialRightPinnedMonitor A strategy hwin leftBasis
  let label := controllers.rightController.labelOf state.1
  (controllers.rightController.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def profiledGuardedInitialLeftFiniteReadbackAfter
    (past : List (In₁ × In₂)) :
    ProfiledGuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  past.foldl
    (stepProfiledGuardedInitialLeftFiniteReadback A strategy hwin rightBasis leftBasis controllers)
    (profiledGuardedInitialLeftFiniteReadbackInitial A strategy hwin rightBasis leftBasis controllers)

noncomputable def profiledGuardedInitialRightFiniteReadbackAfter
    (past : List (In₂ × In₁)) :
    ProfiledGuardedInitialRightFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  past.foldl
    (stepProfiledGuardedInitialRightFiniteReadback A strategy hwin rightBasis leftBasis controllers)
    (profiledGuardedInitialRightFiniteReadbackInitial A strategy hwin rightBasis leftBasis controllers)

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledGuardedInitialLeftFiniteReadbackAfter_eq :
    ∀ past : List (In₁ × In₂),
    profiledGuardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis leftBasis
        controllers past =
      (controllers.leftController.controlAt (senderWord past),
        narrowedControl (profiledGuardedInitialLeftPinnedMonitor A strategy hwin rightBasis)
          controllers.leftController.labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledGuardedInitialLeftFiniteReadbackAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledGuardedInitialLeftFiniteReadback A strategy hwin rightBasis
        leftBasis controllers
        (profiledGuardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move = _
      rw [ih, senderWord_append,
        TransitionRationalTree.controlAt_append, narrowedControl_append]
      rfl

theorem profiledGuardedInitialRightFiniteReadbackAfter_eq :
    ∀ past : List (In₂ × In₁),
    profiledGuardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis leftBasis
        controllers past =
      (controllers.rightController.controlAt (senderWord past),
        narrowedControl (profiledGuardedInitialRightPinnedMonitor A strategy hwin leftBasis)
          controllers.rightController.labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledGuardedInitialRightFiniteReadbackAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledGuardedInitialRightFiniteReadback A strategy hwin rightBasis
        leftBasis controllers
        (profiledGuardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move = _
      rw [ih, senderWord_append,
        TransitionRationalTree.controlAt_append, narrowedControl_append]
      rfl

/-- The underlying guarded monitor component retains exactly the finite DPA
scan used to form the delayed right-block key. -/
theorem profiledGuardedInitialLeftFiniteReadback_scan :
    ∀ past : List (In₁ × In₂),
    (profiledGuardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis leftBasis
      controllers past).2.base.1.1 =
      initialLeftScanAfter A
        (initialLeftLambdaOfProfiledGuardedPair A
          (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (profiledGuardedInitialLeftSenderOfController A strategy hwin rightBasis
            leftBasis controllers)) past := by
  intro past
  rw [profiledGuardedInitialLeftFiniteReadbackAfter_eq]
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [narrowedControl_append, initialLeftScanAfter_append]
      change initialLeftScanStep A
        (narrowedControl
          (profiledGuardedInitialLeftPinnedMonitor A strategy hwin rightBasis)
          controllers.leftController.labeledTree past).base.1.1
        (initialLeftLetterAt
          (initialLeftLambdaOfProfiledGuardedPair A
            (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis
              leftBasis controllers)
            (profiledGuardedInitialLeftSenderOfController A strategy hwin rightBasis
              leftBasis controllers)) past move) = _
      rw [ih]

/-- Process-two mirror. -/
theorem profiledGuardedInitialRightFiniteReadback_scan :
    ∀ past : List (In₂ × In₁),
    (profiledGuardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis leftBasis
      controllers past).2.base.1.1 =
      initialRightScanAfter A
        (initialRightLambdaOfProfiledGuardedPair A
          (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (profiledGuardedInitialRightSenderOfController A strategy hwin rightBasis
            leftBasis controllers)) past := by
  intro past
  rw [profiledGuardedInitialRightFiniteReadbackAfter_eq]
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [narrowedControl_append, initialRightScanAfter_append]
      change initialRightScanStep A
        (narrowedControl
          (profiledGuardedInitialRightPinnedMonitor A strategy hwin leftBasis)
          controllers.rightController.labeledTree past).base.1.1
        (initialRightLetterAt
          (initialRightLambdaOfProfiledGuardedPair A
            (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis
              leftBasis controllers)
            (profiledGuardedInitialRightSenderOfController A strategy hwin rightBasis
              leftBasis controllers)) past move) = _
      rw [ih]

end

/-- Locally executable process-one action at a right close. -/
noncomputable def profiledGuardedInitialLeftNoRecvOneOutput
    (state : ProfiledGuardedInitialLeftFiniteReadbackState
      A strategy hwin rightBasis leftBasis controllers)
    (inputOne : In₁) : Out₁ :=
  ((controllers.leftController.labelOf state.1).2 state.2
    (inputOne, default)).1.reversingOne

/-- Process-two mirror. -/
noncomputable def profiledGuardedInitialRightNoRecvTwoOutput
    (state : ProfiledGuardedInitialRightFiniteReadbackState
      A strategy hwin rightBasis leftBasis controllers)
    (inputTwo : In₂) : Out₂ :=
  ((controllers.rightController.labelOf state.1).2 state.2
    (inputTwo, default)).1.reversingTwo

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedInitialLeftNoRecvOneOutput_eq
    (past : List (In₁ × In₂)) (inputOne : In₁) (inputTwo : In₂) :
    profiledGuardedInitialLeftNoRecvOneOutput A strategy hwin rightBasis leftBasis controllers
        (profiledGuardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis leftBasis
          controllers past) inputOne =
      (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis
        controllers past (inputOne, inputTwo)).1.reversingOne := by
  rw [profiledGuardedInitialLeftFiniteReadbackAfter_eq]
  change
    (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis
      controllers past (inputOne, default)).1.reversingOne = _
  exact profiledGuardedInitialLeftController_reversingOne_independent
    A strategy hwin rightBasis leftBasis controllers past inputOne default inputTwo

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledGuardedInitialRightNoRecvTwoOutput_eq
    (past : List (In₂ × In₁)) (inputTwo : In₂) (inputOne : In₁) :
    profiledGuardedInitialRightNoRecvTwoOutput A strategy hwin rightBasis leftBasis controllers
        (profiledGuardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis leftBasis
          controllers past) inputTwo =
      (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis
        controllers past (inputTwo, inputOne)).1.reversingTwo := by
  rw [profiledGuardedInitialRightFiniteReadbackAfter_eq]
  change
    (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis
      controllers past (inputTwo, default)).1.reversingTwo = _
  exact profiledGuardedInitialRightController_reversingTwo_independent
    A strategy hwin rightBasis leftBasis controllers past inputTwo default inputOne

/-- Concrete profiled exceptional key emitted by the finite initial-left
controller at a boundary. -/
noncomputable def profiledGuardedInitialLeftController_firstMacroAt
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ProfiledGuardedFirstRightMacro A :=
  profiledGuardedInitialLeftFirstMacroAt A
    (profiledGuardedInitialLeftReceiverOfController A strategy hwin rightBasis
      leftBasis controllers)
    (profiledGuardedInitialLeftSenderOfController A strategy hwin rightBasis
      leftBasis controllers)
    (profiledGuardedInitialLeftController_baseWins A strategy hwin rightBasis
      leftBasis controllers) past move

/-- Initial-right mirror. -/
noncomputable def profiledGuardedInitialRightController_firstMacroAt
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ProfiledGuardedFirstLeftMacro A :=
  profiledGuardedInitialRightFirstMacroAt A
    (profiledGuardedInitialRightReceiverOfController A strategy hwin rightBasis
      leftBasis controllers)
    (profiledGuardedInitialRightSenderOfController A strategy hwin rightBasis
      leftBasis controllers)
    (profiledGuardedInitialRightController_baseWins A strategy hwin rightBasis
      leftBasis controllers) past move

end

end DetParityAutomaton

end DistributedSynthesis
