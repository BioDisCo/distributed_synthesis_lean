/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedInitialLocallyConsistentNarrowing

/-!
# Finite local readback of guarded initial controllers

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

variable [Inhabited In₁] [Inhabited In₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (rightBasis : ∀ target profile,
    (rightProfileGuardedAutomaton A target profile).RationalRunBasis)
  (leftBasis : ∀ target profile,
    (leftProfileGuardedAutomaton A target profile).RationalRunBasis)
  (controllers : LocallyConsistentGuardedInitialControllers
    A strategy hwin rightBasis leftBasis)

abbrev GuardedInitialLeftFiniteReadbackState :=
  controllers.leftController.Control ×
    (guardedInitialLeftPinnedMonitor A strategy hwin rightBasis).State

abbrev GuardedInitialRightFiniteReadbackState :=
  controllers.rightController.Control ×
    (guardedInitialRightPinnedMonitor A strategy hwin leftBasis).State

noncomputable def guardedInitialLeftFiniteReadbackInitial :
    GuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  (controllers.leftController.initial,
    (guardedInitialLeftPinnedMonitor A strategy hwin rightBasis).initial)

noncomputable def guardedInitialRightFiniteReadbackInitial :
    GuardedInitialRightFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  (controllers.rightController.initial,
    (guardedInitialRightPinnedMonitor A strategy hwin leftBasis).initial)

noncomputable def stepGuardedInitialLeftFiniteReadback
    (state : GuardedInitialLeftFiniteReadbackState
      A strategy hwin rightBasis leftBasis controllers)
    (move : In₁ × In₂) :
    GuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  let monitor := guardedInitialLeftPinnedMonitor A strategy hwin rightBasis
  let label := controllers.leftController.labelOf state.1
  (controllers.leftController.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def stepGuardedInitialRightFiniteReadback
    (state : GuardedInitialRightFiniteReadbackState
      A strategy hwin rightBasis leftBasis controllers)
    (move : In₂ × In₁) :
    GuardedInitialRightFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  let monitor := guardedInitialRightPinnedMonitor A strategy hwin leftBasis
  let label := controllers.rightController.labelOf state.1
  (controllers.rightController.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def guardedInitialLeftFiniteReadbackAfter
    (past : List (In₁ × In₂)) :
    GuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  past.foldl
    (stepGuardedInitialLeftFiniteReadback A strategy hwin rightBasis leftBasis controllers)
    (guardedInitialLeftFiniteReadbackInitial A strategy hwin rightBasis leftBasis controllers)

noncomputable def guardedInitialRightFiniteReadbackAfter
    (past : List (In₂ × In₁)) :
    GuardedInitialRightFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers :=
  past.foldl
    (stepGuardedInitialRightFiniteReadback A strategy hwin rightBasis leftBasis controllers)
    (guardedInitialRightFiniteReadbackInitial A strategy hwin rightBasis leftBasis controllers)

theorem guardedInitialLeftFiniteReadbackAfter_eq :
    ∀ past : List (In₁ × In₂),
    guardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis leftBasis
        controllers past =
      (controllers.leftController.controlAt (senderWord past),
        narrowedControl (guardedInitialLeftPinnedMonitor A strategy hwin rightBasis)
          controllers.leftController.labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [guardedInitialLeftFiniteReadbackAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepGuardedInitialLeftFiniteReadback A strategy hwin rightBasis
        leftBasis controllers
        (guardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move = _
      rw [ih, senderWord_append,
        TransitionRationalTree.controlAt_append, narrowedControl_append]
      rfl

theorem guardedInitialRightFiniteReadbackAfter_eq :
    ∀ past : List (In₂ × In₁),
    guardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis leftBasis
        controllers past =
      (controllers.rightController.controlAt (senderWord past),
        narrowedControl (guardedInitialRightPinnedMonitor A strategy hwin leftBasis)
          controllers.rightController.labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [guardedInitialRightFiniteReadbackAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepGuardedInitialRightFiniteReadback A strategy hwin rightBasis
        leftBasis controllers
        (guardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis
          leftBasis controllers past) move = _
      rw [ih, senderWord_append,
        TransitionRationalTree.controlAt_append, narrowedControl_append]
      rfl

/-- The underlying guarded monitor component retains exactly the finite DPA
scan used to form the delayed right-block key. -/
theorem guardedInitialLeftFiniteReadback_scan :
    ∀ past : List (In₁ × In₂),
    (guardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis leftBasis
      controllers past).2.base.1.1 =
      initialLeftScanAfter A
        (initialLeftLambdaOfGuardedPair A
          (guardedInitialLeftReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (guardedInitialLeftSenderOfController A strategy hwin rightBasis
            leftBasis controllers)) past := by
  intro past
  rw [guardedInitialLeftFiniteReadbackAfter_eq]
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [narrowedControl_append, initialLeftScanAfter_append]
      change initialLeftScanStep A
        (narrowedControl
          (guardedInitialLeftPinnedMonitor A strategy hwin rightBasis)
          controllers.leftController.labeledTree past).base.1.1
        (initialLeftLetterAt
          (initialLeftLambdaOfGuardedPair A
            (guardedInitialLeftReceiverOfController A strategy hwin rightBasis
              leftBasis controllers)
            (guardedInitialLeftSenderOfController A strategy hwin rightBasis
              leftBasis controllers)) past move) = _
      rw [ih]

/-- Process-two mirror. -/
theorem guardedInitialRightFiniteReadback_scan :
    ∀ past : List (In₂ × In₁),
    (guardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis leftBasis
      controllers past).2.base.1.1 =
      initialRightScanAfter A
        (initialRightLambdaOfGuardedPair A
          (guardedInitialRightReceiverOfController A strategy hwin rightBasis
            leftBasis controllers)
          (guardedInitialRightSenderOfController A strategy hwin rightBasis
            leftBasis controllers)) past := by
  intro past
  rw [guardedInitialRightFiniteReadbackAfter_eq]
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [narrowedControl_append, initialRightScanAfter_append]
      change initialRightScanStep A
        (narrowedControl
          (guardedInitialRightPinnedMonitor A strategy hwin leftBasis)
          controllers.rightController.labeledTree past).base.1.1
        (initialRightLetterAt
          (initialRightLambdaOfGuardedPair A
            (guardedInitialRightReceiverOfController A strategy hwin rightBasis
              leftBasis controllers)
            (guardedInitialRightSenderOfController A strategy hwin rightBasis
              leftBasis controllers)) past move) = _
      rw [ih]

/-- Locally executable process-one action at a right close. -/
noncomputable def guardedInitialLeftNoRecvOneOutput
    (state : GuardedInitialLeftFiniteReadbackState
      A strategy hwin rightBasis leftBasis controllers)
    (inputOne : In₁) : Out₁ :=
  ((controllers.leftController.labelOf state.1).2 state.2
    (inputOne, default)).1.reversingOne

/-- Process-two mirror. -/
noncomputable def guardedInitialRightNoRecvTwoOutput
    (state : GuardedInitialRightFiniteReadbackState
      A strategy hwin rightBasis leftBasis controllers)
    (inputTwo : In₂) : Out₂ :=
  ((controllers.rightController.labelOf state.1).2 state.2
    (inputTwo, default)).1.reversingTwo

theorem guardedInitialLeftNoRecvOneOutput_eq
    (past : List (In₁ × In₂)) (inputOne : In₁) (inputTwo : In₂) :
    guardedInitialLeftNoRecvOneOutput A strategy hwin rightBasis leftBasis controllers
        (guardedInitialLeftFiniteReadbackAfter A strategy hwin rightBasis leftBasis
          controllers past) inputOne =
      (guardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis
        controllers past (inputOne, inputTwo)).1.reversingOne := by
  rw [guardedInitialLeftFiniteReadbackAfter_eq]
  change
    (guardedInitialLeftReceiverOfController A strategy hwin rightBasis leftBasis
      controllers past (inputOne, default)).1.reversingOne = _
  exact guardedInitialLeftController_reversingOne_independent
    A strategy hwin rightBasis leftBasis controllers past inputOne default inputTwo

theorem guardedInitialRightNoRecvTwoOutput_eq
    (past : List (In₂ × In₁)) (inputTwo : In₂) (inputOne : In₁) :
    guardedInitialRightNoRecvTwoOutput A strategy hwin rightBasis leftBasis controllers
        (guardedInitialRightFiniteReadbackAfter A strategy hwin rightBasis leftBasis
          controllers past) inputTwo =
      (guardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis
        controllers past (inputTwo, inputOne)).1.reversingTwo := by
  rw [guardedInitialRightFiniteReadbackAfter_eq]
  change
    (guardedInitialRightReceiverOfController A strategy hwin rightBasis leftBasis
      controllers past (inputTwo, default)).1.reversingTwo = _
  exact guardedInitialRightController_reversingTwo_independent
    A strategy hwin rightBasis leftBasis controllers past inputTwo default inputOne

end

end DetParityAutomaton

end DistributedSynthesis
